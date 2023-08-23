{- |
Module      :  ./CommonLogic/Print_KIF.hs
Description :  Pretty Printer for KIF
Copyright   :  (c) Soeren Schulze, Uni Bremen 2012
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  s.schulze@uni-bremen.de
Stability   :  provisional
Portability :  portable

Pretty Printer for KIF.  Partially based on "pretty" instances in AS_CommonLogic.
Note that the output does not perfectly match the input, as CommonLogic does
not have the concept of "free variables" (as opposed to variables bound by a
quantifier).  Thus, any free variables are converted into constants and lose
their '?' prefix.  When CommonLogic code is emitted as KIF, the comments in
commented sentences and terms get lost, and modules are inlined.
-}

module CommonLogic.Print_KIF where

import Common.Id as Id
import Common.Doc
import Common.DocUtils
import Common.Keywords
import CommonLogic.ModuleElimination
import qualified CommonLogic.AS_CommonLogic as AS
import qualified Common.AS_Annotation as AS_Anno
import qualified Data.Set as Set

printBasicSpec :: AS.BASIC_SPEC -> Doc
printBasicSpec (AS.Basic_spec xs) = vcat $ map (printAnnoted printBasicItems) xs

printBasicItems :: AS.BASIC_ITEMS -> Doc
printBasicItems (AS.Axiom_items xs) = vcat $ map (printAnnoted printTextMeta) xs

printTextMeta :: AS.TEXT_META -> Doc
printTextMeta tm = printText $ AS.getText $ eliminateModules tm

exportKIF :: [AS_Anno.Named AS.TEXT_META] -> Doc
exportKIF xs = vsep $ map (printTextMeta . AS_Anno.sentence) xs

printText :: AS.TEXT -> Doc
printText s = case s of
  AS.Text x _ -> fsep $ map printPhrase x
  AS.Named_text _ x _ -> printText x

printPhrase :: AS.PHRASE -> Doc
printPhrase s = case s of
  AS.Module _ -> error "printPhrase: \"module\" found"
  AS.Sentence x -> printSentence Set.empty x
  AS.Importation _ -> error "printPhrase: \"import\" found"
  AS.Comment_text _ t _ -> printText t

printQuant :: AS.QUANT -> Doc
printQuant = AS.printQuant

printAndOr :: AS.AndOr -> Doc
printAndOr = AS.printAndOr

printImplEq :: AS.ImplEq -> Doc
printImplEq s = case s of
  AS.Implication -> text implS
  AS.Biconditional -> text equivS

getQuantVarName :: AS.NAME_OR_SEQMARK -> String
getQuantVarName v = stripVar $ tokStr $ case v of
  AS.Name x -> x
  AS.SeqMark x -> x

{- The "bv" argument contains a set of variables that are bound by quantifiers.
These variables are prepended by a '?' sign when printed.
Sequence markers are always prepended by '@', without checking if they
are bounded. -}

printSentence :: Set.Set String -> AS.SENTENCE -> Doc
printSentence bv s = case s of
  AS.Quant_sent q vs is _ ->
    parens $ printQuant q <+> parens (sep $ map (printNameOrSeqMark bv') vs) <+>
    printSentence bv' is
    where bv' = Set.union (Set.fromList $ map getQuantVarName vs) bv
  AS.Bool_sent xs _ -> parens $ printBoolSent bv xs
  AS.Atom_sent xs _ -> printAtom bv xs
  AS.Comment_sent _ y _ -> printSentence bv y
  AS.Irregular_sent xs _ -> printSentence bv xs

printBoolSent :: Set.Set String -> AS.BOOL_SENT -> Doc
printBoolSent bv s = case s of
  AS.Junction q xs -> printAndOr q <+> fsep (map (printSentence bv) xs)
  AS.Negation xs -> text notS <+> printSentence bv xs
  AS.BinOp q x y -> printImplEq q <+> printSentence bv x <+> printSentence bv y

printAtom :: Set.Set String -> AS.ATOM -> Doc
printAtom bv s = case s of
  AS.Equation a b -> parens $ equals <+> printTerm bv a <+> printTerm bv b
  AS.Atom t [] -> printTerm bv t
  AS.Atom t ts -> parens $ printTerm bv t <+> sep (map (printTermSeq bv) ts)

stripVar :: String -> String
stripVar = dropWhile (`elem` "?@.")

printName :: Set.Set String -> AS.NAME -> Doc
printName bv name = text $ if Set.member cleanName bv
                           then '?' : cleanName
                           else cleanName
  where cleanName = stripVar $ tokStr name

printRowVar :: Token -> Doc
printRowVar name = text $ '@' : stripVar (tokStr name)

printTerm :: Set.Set String -> AS.TERM -> Doc
printTerm bv s = case s of
  AS.Name_term a -> printName bv a
  AS.Funct_term t ts _ -> parens $ printTerm bv t
                          <+> sep (map (printTermSeq bv) ts)
  AS.Comment_term t _ _ -> printTerm bv t
  AS.That_term sent _ -> printSentence bv sent

printTermSeq :: Set.Set String -> AS.TERM_SEQ -> Doc
printTermSeq bv s = case s of
  AS.Term_seq t -> printTerm bv t
  AS.Seq_marks m -> printRowVar m

printNameOrSeqMark :: Set.Set String -> AS.NAME_OR_SEQMARK -> Doc
printNameOrSeqMark bv s = case s of
  AS.Name x -> printName bv x
  AS.SeqMark x -> printRowVar x
