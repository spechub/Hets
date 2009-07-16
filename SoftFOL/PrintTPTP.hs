{- |
Module      :  $Header$
Description :  Pretty printing for SPASS signatures in TPTP syntax.
Copyright   :  (c) Rene Wagner, Rainer Grabbe, Uni Bremen 2005-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  rainer25@informatik.uni-bremen.de
Stability   :  provisional
Portability :  unknown

Pretty printing for SoftFOL signatures in TPTP syntax.
   Refer to <http://www.cs.miami.edu/~tptp/TPTP/SyntaxBNF.html>
   for the TPTP syntax documentation.

-}

module SoftFOL.PrintTPTP where

import Data.Maybe

import Common.AS_Annotation
import Common.Doc
import Common.DocUtils

import SoftFOL.Sign
import SoftFOL.Conversions

-- | This type class allows pretty printing in TPTP syntax of instantiated data
--   types
class PrintTPTP a where
    printTPTP :: a -> Doc

{- |
  Helper function. Generates a separating comment line.
-}
separator :: String
separator = '%' : replicate 75 '-'

instance PrintTPTP Sign where
    printTPTP = printTPTP . signToSPLogicalPart

{- |
  Creates a Doc from a SoftFOL Problem.
-}
instance PrintTPTP SPProblem where
    printTPTP p = text separator
      $+$ text "% Problem" <+> colon <+> text (identifier p)
      $+$ printTPTP (description p)
      $+$ vcat (map printTPTP $ settings p)
      $+$ text separator
      $+$ printTPTP (logicalPart p)

{- |
  Creates a Doc from a SoftFOL Logical Part.
-}
instance PrintTPTP SPLogicalPart where
    printTPTP lp =
      let decls = declarationList lp
          validDeclarations = filter (\ decl -> case decl of
              SPSubsortDecl {}   -> True
              SPTermDecl {}      -> True
              SPSimpleTermDecl _ -> True
              _                  -> False)
                     $ (maybe [] id decls)
          fs = formulaLists lp
      in if null validDeclarations && null fs then
            text "fof" <> parens
              (text "empty" <> comma <> printTPTP SPOriginAxioms
               <> comma <> printTPTP SPTrue) <> dot
         else vcat (map (\ (decl, i) ->
                    text "fof" <>
                    parens (text ("declaration" ++ show i) <> comma <>
                    printTPTP SPOriginAxioms <> comma
                    $+$ printTPTP decl) <> dot)
                $ zip validDeclarations [(0::Int)..])
         $+$ vcat (map printTPTP fs)

{- |
 Creates a Doc from a SoftFOL Declaration.
 A subsort declaration will be rewritten as a special SPQuantTerm.
-}
instance PrintTPTP SPDeclaration where
    printTPTP decl = case decl of
      SPSubsortDecl{sortSymA= sortA, sortSymB= sortB}
        -> let subsortVar = spTerms $ genVarList sortA [sortB]
           in  printTPTP SPQuantTerm
             { quantSym=SPForall,
               variableList=subsortVar,
               qFormula=compTerm SPImplies
                 [ compTerm (spSym sortA) subsortVar
                 , compTerm (spSym sortB) subsortVar] }
      SPTermDecl{termDeclTermList= tlist, termDeclTerm= tt}
        -> printTPTP SPQuantTerm{
                       quantSym=SPForall,
                       variableList=tlist,
                       qFormula=tt}
      SPSimpleTermDecl stsym -> printTPTP stsym
      pd@(SPPredDecl {}) -> maybe empty printTPTP $ predDecl2Term pd
      _ -> empty

{- |
  Creates a Doc from a SoftFOL Formula List.
-}
instance PrintTPTP SPFormulaList where
    printTPTP l = vcat $ map (printFormula $ originType l) $ formulae l

{- |
  Creates a Doc from a SoftFOL Origin Type.
-}
instance PrintTPTP SPOriginType where
    printTPTP t = text $ case t of
        SPOriginAxioms      -> "axiom"
        SPOriginConjectures -> "conjecture"

{- |
  Creates a Doc from a SoftFOL Formula. Needed since SPFormula is just a
  'type SPFormula = Named SPTerm' and thus instanciating PrintTPTP is not
  possible.
-}
printFormula :: SPOriginType -> SPFormula -> Doc
-- printFormula ot f = printFormulaText ot (senAttr f) (sentence f)
printFormula ot f =
    text "fof" <> parens (text (senAttr f) <> comma <> printTPTP ot <> comma
                          $+$ printTPTP (sentence f)) <> dot

{- |
  Creates a Doc from a SoftFOL Term.
-}
instance PrintTPTP SPTerm where
    printTPTP t = case t of
      SPQuantTerm{quantSym= qsym, variableList= tlist, qFormula= tt} -> let
        isComplexTerm tm = case tm of
            SPComplexTerm _ [] -> False
            _ -> True
        getVars tm = case tm of
            SPComplexTerm _ args ->
              if null args then [tm] else concatMap getVars args
            _ -> []
        cl = filter isComplexTerm tlist
        conj = case qsym of
                 SPExists -> compTerm SPAnd $ cl ++ [tt]
                 _ -> compTerm SPImplies $ (case cl of
                   [hd] -> hd
                   _ -> compTerm SPAnd cl) : [tt]
        in printTPTP qsym
           <+> brackets (printCommaSeparated $ concatMap getVars tlist)
           <+> colon
           -- either all variables are simple terms
           <+> if null cl then parPrintTPTP tt
               -- or there are none simple terms
               else
          -- construct premiss for implication out of variableList (Forall)
          -- construct conjunction out of variableList (Exists)
               parens $ printTPTP conj
      SPComplexTerm{symbol= ctsym, arguments= args}
        -> printTermList ctsym args

{- |
  Creates a Doc from a list of SoftFOL Terms connected by a SoftFOL Symbol.
-}
printTermList :: SPSymbol -> [SPTerm] -> Doc
printTermList symb terms = let
  sbd = printTPTP symb
  d = if null terms then sbd else sbd <> parens (printCommaSeparated terms)
  in case symb of
  SPNot -> case terms of
        [t] -> sbd <+> parPrintTPTP t
        _ -> d
  _ -> if elem symb $ SPEqual : binLogOps then
     fsep $ prepPunctuate (sbd <> space) $ map parPrintTPTP terms
     else d

{- |
  Helper function. Generates a comma separated list of SoftFOL Terms as a Doc.
-}
printCommaSeparated :: [SPTerm] -> Doc
printCommaSeparated = sepByCommas . map printTPTP

parPrintTPTP :: SPTerm -> Doc
parPrintTPTP t = (if isUnitary t then id else parens) $ printTPTP t

isUnitary :: SPTerm -> Bool
isUnitary t = case t of
    SPComplexTerm{symbol = ctsym, arguments = _ : _ : _} ->
       not $ elem ctsym binLogOps
    _ -> True

binLogOps :: [SPSymbol]
binLogOps = [SPOr, SPAnd, SPImplies, SPImplied, SPEquiv]

{- |
  Creates a Doc from a SoftFOL Quantifier Symbol.
-}
instance PrintTPTP SPQuantSym where
    printTPTP qs = text $ case qs of
        SPForall             -> "!"
        SPExists             -> "?"
        SPCustomQuantSym cst -> show cst

{- |
  Creates a Doc from a SoftFOL Symbol.
-}
instance PrintTPTP SPSymbol where
    printTPTP s = text $ case s of
        SPEqual            -> "="
        SPTrue             -> "$true"
        SPFalse            -> "$false"
        SPOr               -> "|"
        SPAnd              -> "&"
        SPNot              -> "~"
        SPImplies          -> "=>"
        SPImplied          -> "<="
        SPEquiv            -> "<=>"
        SPCustomSymbol cst -> show cst
        _ -> showSPSymbol s

{- |
  Creates a Doc from a SoftFOL description.
-}
instance PrintTPTP SPDescription where
    printTPTP d = spCommentText "Name   " (name d)
      $+$ spCommentText "Author " (author d)
      $+$ maybe empty (spCommentText "Version") (version d)
      $+$ maybe empty (spCommentText "Logic  ") (logic d)
      $+$ text "% Status " <+> colon <+> printTPTP (status d)
      $+$ spCommentText "Desc   " (desc d)
      $+$ maybe empty (spCommentText "Date   ") (date d)

{- |
  Helper function. Creates a formatted comment output for a description field.
  On left side will be displayed the field's name, on right side its content.
-}
spCommentText :: String -> String -> Doc
spCommentText fieldName fieldDesc =
    hsep [text "%", text fieldName, colon, text fieldDesc]

{- |
  Creates a Doc from an 'SPLogState'.
-}
instance PrintTPTP SPLogState where
    printTPTP s = text $ case s of
      SPStateSatisfiable   -> "satisfiable"
      SPStateUnsatisfiable -> "unsatisfiable"
      SPStateUnknown       -> "unknown"

instance PrintTPTP SPSetting where
    printTPTP s = case s of
      SPGeneralSettings e ->
        hsep [text "% Option ", colon, text $ show e]
      SPSettings _ settingText ->
          hsep $ (text "% Option " <+> colon) : map printTPTP settingText

instance PrintTPTP SPSettingBody where
    printTPTP s = case s of
      SPFlag sw v ->
          cat [text sw, if null v then empty else parens (ppWithCommas v)]
      _ -> empty
