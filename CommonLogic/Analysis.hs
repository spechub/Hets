{- |
Module      :  $Header$
Description :  Basic analysis for common logic
Copyright   :  (c) Karl Luc, Uni Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  kluc@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

Basic and static analysis for common logic
-}

module CommonLogic.Analysis
    where

import Common.ExtSign
import Common.Result as Result
import qualified Common.AS_Annotation as AS_Anno
import qualified Common.Id as Id

import CommonLogic.Symbol as Symbol
import qualified CommonLogic.AS_CommonLogic as CL
import CommonLogic.Morphism as Morphism
import CommonLogic.Sign as Sign

import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.List as List

data DIAG_FORM = DiagForm
    {
        formula :: AS_Anno.Named CL.TEXT,
      diagnosis :: Result.Diagnosis
    }

-- | retrieves the signature out of a basic spec
makeSig :: CL.BASIC_SPEC -> Sign.Sign -> Sign.Sign
makeSig (CL.Basic_spec spec) sig = List.foldl retrieveBasicItem sig spec

retrieveBasicItem :: Sign.Sign -> AS_Anno.Annoted CL.BASIC_ITEMS -> Sign.Sign
retrieveBasicItem sig x = case AS_Anno.item x of
                            CL.Axiom_items xs -> retrieveSign sig xs

retrieveSign :: Sign.Sign -> AS_Anno.Annoted CL.TEXT -> Sign.Sign
retrieveSign sig = Sign.unite sig . propsOfFormula . AS_Anno.item

-- retrieve CL.Sentence out of BASIC_SPEC

-- retrieveSentence :: CL.BASIC_SPEC -> [AS_Anno.Named (CL.SENTENCE)]

-- | retrieve sentences
makeFormulas :: CL.BASIC_SPEC -> Sign.Sign -> [DIAG_FORM]
makeFormulas (CL.Basic_spec bspec) sig =
  List.foldl (\ xs bs -> retrieveFormulaItem xs bs sig) [] bspec

retrieveFormulaItem :: [DIAG_FORM] -> AS_Anno.Annoted CL.BASIC_ITEMS
                       -> Sign.Sign -> [DIAG_FORM]
retrieveFormulaItem axs x sig =
   case AS_Anno.item x of
      CL.Axiom_items ax -> addFormula axs (numberFormulae ax 0) sig

data NUM_FORM = NumForm
    {
      nfformula :: AS_Anno.Annoted CL.TEXT
    , nfnum :: Int
    }

numberFormulae :: AS_Anno.Annoted CL.TEXT -> Int -> NUM_FORM
numberFormulae x i =
  if null $ AS_Anno.getRLabel x
  then NumForm {nfformula = x, nfnum = i}
  else NumForm {nfformula = x, nfnum = 0}

addFormula :: [DIAG_FORM]
           -> NUM_FORM
           -> Sign.Sign
           -> [DIAG_FORM]
addFormula formulae nf _ = formulae ++
                          [DiagForm {
                             formula = makeNamed f i
                           , diagnosis = Result.Diag
                           {
                             Result.diagKind = Result.Hint
                           , Result.diagString = "All fine"
                           , Result.diagPos = lnum
                           }
                         }]
    where
      f = nfformula nf
      i = nfnum nf
      lnum = AS_Anno.opt_pos f

-- | generates a named formula
makeNamed :: AS_Anno.Annoted CL.TEXT -> Int -> AS_Anno.Named CL.TEXT
makeNamed f i = (AS_Anno.makeNamed (if null label then "Ax_" ++ show i
                                       else label) $ AS_Anno.item f)
                    { AS_Anno.isAxiom = not isTheorem }
   where
      label = AS_Anno.getRLabel f
      annos = AS_Anno.r_annos f
      isImplies = any AS_Anno.isImplies annos
      isImplied = any AS_Anno.isImplied annos
      isTheorem = isImplies || isImplied

-- | Retrives the signature of a sentence
propsOfFormula :: CL.TEXT -> Sign.Sign
propsOfFormula (CL.Named_text _ txt _) = propsOfFormula txt
propsOfFormula (CL.Text phrs _) = Sign.uniteL $ map propsOfPhrase phrs

propsOfPhrase :: CL.PHRASE -> Sign.Sign
propsOfPhrase (CL.Module m) = propsOfModule m
propsOfPhrase (CL.Sentence s) = propsOfSentence s
propsOfPhrase (CL.Comment_text _ txt _) = propsOfFormula txt
propsOfPhrase (CL.Importation _) = Sign.emptySig

propsOfModule :: CL.MODULE -> Sign.Sign
propsOfModule m = case m of
  (CL.Mod n txt _) -> Sign.unite (propsOfFormula txt) $ nameToSign n
  (CL.Mod_ex n exs txt _) -> Sign.unite (propsOfFormula txt)
      $ Sign.uniteL $ nameToSign n : map nameToSign exs
  where nameToSign x = Sign.Sign {
            Sign.items = Set.singleton $ Id.simpleIdToId x,
            Sign.discourseItems = Set.singleton $ Id.simpleIdToId x
          }

propsOfSentence :: CL.SENTENCE -> Sign.Sign
propsOfSentence (CL.Atom_sent form _) = case form of
    CL.Equation term1 term2 -> Sign.unite (propsOfTerm term1)
      (propsOfTerm term2)
    CL.Atom term ts -> Sign.unite (propsOfTerm term)
      (uniteMap propsOfTermSeq ts)
propsOfSentence (CL.Quant_sent qs _) = case qs of
    CL.Universal xs s -> Sign.sigDiff (propsOfSentence s)
                                      (uniteMap propsOfNames xs)
    CL.Existential xs s -> Sign.sigDiff (propsOfSentence s)
                                        (uniteMap propsOfNames xs)
propsOfSentence (CL.Bool_sent bs _) = case bs of
    CL.Conjunction xs -> uniteMap propsOfSentence xs
    CL.Disjunction xs -> uniteMap propsOfSentence xs
    CL.Negation x -> propsOfSentence x
    CL.Implication s1 s2 -> Sign.unite (propsOfSentence s1) (propsOfSentence s2)
    CL.Biconditional s1 s2 -> Sign.unite (propsOfSentence s1) (propsOfSentence s2)
propsOfSentence (CL.Comment_sent _ s _) = propsOfSentence s
propsOfSentence (CL.Irregular_sent s _) = propsOfSentence s

propsOfTerm :: CL.TERM -> Sign.Sign
propsOfTerm term = case term of
    CL.Name_term x -> Sign.Sign {
            Sign.items = Set.singleton $ Id.simpleIdToId x,
            Sign.discourseItems = Set.singleton $ Id.simpleIdToId x
        }
    CL.Funct_term t ts _ -> Sign.unite (propsOfTerm t)
                                       (uniteMap propsOfTermSeq ts)
    CL.Comment_term t _ _ -> propsOfTerm t -- fix

propsOfNames :: CL.NAME_OR_SEQMARK -> Sign.Sign
propsOfNames (CL.Name x) = Sign.Sign {
        Sign.items = Set.singleton $ Id.simpleIdToId x,
        Sign.discourseItems = Set.singleton $ Id.simpleIdToId x
    }
propsOfNames (CL.SeqMark x) = Sign.Sign {
        Sign.items = Set.singleton $ Id.simpleIdToId x,
        Sign.discourseItems = Set.singleton $ Id.simpleIdToId x
    }

propsOfTermSeq :: CL.TERM_SEQ -> Sign.Sign
propsOfTermSeq s = case s of
    CL.Term_seq term -> propsOfTerm term
    CL.Seq_marks sqm -> Sign.Sign {
            Sign.items = Set.singleton $ Id.simpleIdToId sqm,
            Sign.discourseItems = Set.singleton $ Id.simpleIdToId sqm
        }

uniteMap :: (a -> Sign.Sign) -> [a] -> Sign
uniteMap p = List.foldl (\ sig -> Sign.unite sig . p)
   Sign.emptySig

basicCommonLogicAnalysis :: (CL.BASIC_SPEC, Sign.Sign, a)
  -> Result (CL.BASIC_SPEC,
             ExtSign Sign.Sign Symbol.Symbol,
             [AS_Anno.Named CL.TEXT])
basicCommonLogicAnalysis (bs, sig, _) =
   Result.Result [] $ if exErrs then Nothing else
     Just (bs, ExtSign sigItems newSyms, sentences)
    where
      sigItems = makeSig bs sig
      newSyms = Set.map Symbol.Symbol
                    $ Set.difference (items sigItems) $ items sig
      bsform = makeFormulas bs sigItems
  -- [DIAG_FORM] signature and list of sentences
      sentences = map formula bsform
  -- Annoted Sentences (Ax_), numbering, DiagError
      exErrs = False

inducedFromMorphism :: Map.Map Symbol.Symbol Symbol.Symbol
                    -> Sign.Sign
                    -> Result.Result Morphism.Morphism
inducedFromMorphism m s = let
  p = Map.fromList . map (\ (s1, s2) -> (symName s1, symName s2))
       $ Map.toList m
  t = Sign.emptySig { items = Set.map (applyMap p) $ items s }
  in return $ mkMorphism s t p



-- negate sentence (text) - propagates negation to sentences
negForm :: CL.TEXT -> CL.TEXT
negForm t = case t of
  CL.Text phrs r -> CL.Text (map negForm_phr phrs) r
  CL.Named_text n txt r -> CL.Named_text n (negForm txt) r

-- negate phrase - propagates negation to sentences
negForm_phr :: CL.PHRASE -> CL.PHRASE
negForm_phr phr = case phr of
  CL.Module m -> CL.Module $ negForm_mod m
  CL.Sentence s -> CL.Sentence $ negForm_sen s
  CL.Comment_text c t r -> CL.Comment_text c (negForm t) r
  x -> x

-- negate module - propagates negation to sentences
negForm_mod ::CL.MODULE -> CL.MODULE
negForm_mod m = case m of
  CL.Mod n t r -> CL.Mod n (negForm t) r
  CL.Mod_ex n exs t r -> CL.Mod_ex n exs (negForm t) r

-- negate sentence
negForm_sen :: CL.SENTENCE -> CL.SENTENCE
negForm_sen f = case f of
  CL.Quant_sent _ r -> CL.Bool_sent (CL.Negation f) r
  CL.Bool_sent bs r -> case bs of
    CL.Negation s -> s
    _ -> CL.Bool_sent (CL.Negation f) r
  _ -> CL.Bool_sent (CL.Negation f) Id.nullRange
