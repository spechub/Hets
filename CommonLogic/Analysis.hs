{- |
Module      :  $Header$
Description :  Basic analysis for common logic
Copyright   :  (c) Eugen Kuksa, Karl Luc, Uni Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  eugenk@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

Basic and static analysis for common logic
-}

module CommonLogic.Analysis
    ( basicCommonLogicAnalysis
    , negForm
    , symsOfTextMeta
    , mkStatSymbItems
    , mkStatSymbMapItem
    , inducedFromMorphism
    , inducedFromToMorphism
    , signColimit
    )
    where

import Common.ExtSign
import Common.Result as Result
import Common.GlobalAnnotations
import qualified Common.AS_Annotation as AS_Anno
import Common.Id as Id
import Common.IRI (parseIRIReference)
import Common.DocUtils
import Common.Lib.Graph
import Common.SetColimit

import CommonLogic.Symbol as Symbol
import qualified CommonLogic.AS_CommonLogic as AS
import CommonLogic.Morphism as Morphism
import CommonLogic.Sign as Sign
import CommonLogic.ExpandCurie

import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Common.Lib.MapSet as MapSet
import qualified Data.List as List
import Data.Graph.Inductive.Graph as Graph

data DIAG_FORM = DiagForm
    {
        formula :: AS_Anno.Named AS.TEXT_META,
      diagnosis :: Result.Diagnosis
    }

-- | retrieves the signature out of a basic spec
makeSig :: AS.BASIC_SPEC -> Sign.Sign -> Sign.Sign
makeSig (AS.Basic_spec spec) sig = List.foldl retrieveBasicItem sig spec

retrieveBasicItem :: Sign.Sign -> AS_Anno.Annoted AS.BASIC_ITEMS -> Sign.Sign
retrieveBasicItem sig x = case AS_Anno.item x of
                            AS.Axiom_items xs -> List.foldl retrieveSign sig xs

retrieveSign :: Sign.Sign -> AS_Anno.Annoted AS.TEXT_META -> Sign.Sign
retrieveSign sig (AS_Anno.Annoted tm _ _ _) =
  Sign.unite (Sign.unite sig $ nondiscItems $ AS.nondiscourseNames tm)
             (propsOfFormula $ AS.getText tm)

nondiscItems :: Maybe (Set.Set AS.NAME) -> Sign.Sign
nondiscItems s = case s of
  Nothing -> Sign.emptySig
  Just ns -> Sign.emptySig {Sign.nondiscourseNames = Set.map Id.simpleIdToId ns}

-- | retrieve sentences
makeFormulas :: AS.BASIC_SPEC -> Sign.Sign -> [DIAG_FORM]
makeFormulas (AS.Basic_spec bspec) sig =
  List.foldl (\ xs bs -> retrieveFormulaItem xs bs sig) [] bspec

retrieveFormulaItem :: [DIAG_FORM] -> AS_Anno.Annoted AS.BASIC_ITEMS
                       -> Sign.Sign -> [DIAG_FORM]
retrieveFormulaItem axs x sig =
   case AS_Anno.item x of
      AS.Axiom_items ax ->
          List.foldl (\ xs bs -> addFormula xs bs sig) axs $ numberFormulae ax 0

data NUM_FORM = NumForm
    {
      nfformula :: AS_Anno.Annoted AS.TEXT_META
    , nfnum :: Int
    }

numberFormulae :: [AS_Anno.Annoted AS.TEXT_META] -> Int -> [NUM_FORM]
numberFormulae [] _ = []
numberFormulae (x : xs) i =
  if null $ AS_Anno.getRLabel x
  then NumForm {nfformula = x, nfnum = i} : numberFormulae xs (i + 1)
  else NumForm {nfformula = x, nfnum = 0} : numberFormulae xs i

addFormula :: [DIAG_FORM]
           -> NUM_FORM
           -> Sign.Sign
           -> [DIAG_FORM]
addFormula formulae nf _ = formulae ++
                          [DiagForm {
                             formula = makeNamed (setTextIRI f) i
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
makeNamed :: AS_Anno.Annoted AS.TEXT_META -> Int
             -> AS_Anno.Named AS.TEXT_META
makeNamed f i =
  (AS_Anno.makeNamed (
      if null label
        then case text of
                AS.Named_text n _ _ -> Id.tokStr n
                _ -> "Ax_" ++ show i
        else label
    ) $ AS_Anno.item f)
  { AS_Anno.isAxiom = not isTheorem }
   where
      text = AS.getText $ AS_Anno.item f
      label = AS_Anno.getRLabel f
      annos = AS_Anno.r_annos f
      isImplies = any AS_Anno.isImplies annos
      isImplied = any AS_Anno.isImplied annos
      isTheorem = isImplies || isImplied

setTextIRI :: AS_Anno.Annoted AS.TEXT_META -> AS_Anno.Annoted AS.TEXT_META
setTextIRI atm@(AS_Anno.Annoted { AS_Anno.item = tm }) =
  let mi = case AS.getText tm of
            AS.Named_text n _ _ -> parseIRIReference $ init $ tail $ Id.tokStr n
            _ -> Nothing
  in atm { AS_Anno.item = tm { AS.textIri = mi } }

-- | Retrives the signature of a sentence
propsOfFormula :: AS.TEXT -> Sign.Sign
propsOfFormula (AS.Named_text _ txt _) = propsOfFormula txt
propsOfFormula (AS.Text phrs _) = Sign.uniteL $ map propsOfPhrase phrs

propsOfPhrase :: AS.PHRASE -> Sign.Sign
propsOfPhrase (AS.Module m) = propsOfModule m
propsOfPhrase (AS.Sentence s) = propsOfSentence s
propsOfPhrase (AS.Comment_text _ txt _) = propsOfFormula txt
propsOfPhrase (AS.Importation _) = Sign.emptySig

propsOfModule :: AS.MODULE -> Sign.Sign
propsOfModule m = case m of
  (AS.Mod n txt _) -> Sign.unite (propsOfFormula txt) $ nameToSign n
  (AS.Mod_ex n exs txt _) -> Sign.unite (propsOfFormula txt)
      $ Sign.uniteL $ nameToSign n : map nameToSign exs
  where nameToSign x = Sign.emptySig {
            Sign.discourseNames = Set.singleton $ Id.simpleIdToId x
          }

propsOfSentence :: AS.SENTENCE -> Sign.Sign
propsOfSentence (AS.Atom_sent form _) = case form of
    AS.Equation term1 term2 -> Sign.unite (propsOfTerm term1)
      (propsOfTerm term2)
    AS.Atom term ts -> Sign.unite (propsOfTerm term)
      (uniteMap propsOfTermSeq ts)
propsOfSentence (AS.Quant_sent _ xs s _) =
    Sign.sigDiff (propsOfSentence s) (uniteMap propsOfNames xs)
propsOfSentence (AS.Bool_sent bs _) = case bs of
    AS.Junction _ xs -> uniteMap propsOfSentence xs
    AS.Negation x -> propsOfSentence x
    AS.BinOp _ s1 s2 -> Sign.unite (propsOfSentence s1) (propsOfSentence s2)
propsOfSentence (AS.Comment_sent _ s _) = propsOfSentence s
propsOfSentence (AS.Irregular_sent s _) = propsOfSentence s

propsOfTerm :: AS.TERM -> Sign.Sign
propsOfTerm term = case term of
    AS.Name_term x -> Sign.emptySig {
            Sign.discourseNames = Set.singleton $ Id.simpleIdToId x
          }
    AS.Funct_term t ts _ -> Sign.unite (propsOfTerm t)
                                       (uniteMap propsOfTermSeq ts)
    AS.Comment_term t _ _ -> propsOfTerm t -- fix
    AS.That_term s _ -> propsOfSentence s

propsOfNames :: AS.NAME_OR_SEQMARK -> Sign.Sign
propsOfNames (AS.Name x) = Sign.emptySig {
            Sign.discourseNames = Set.singleton $ Id.simpleIdToId x
          }
propsOfNames (AS.SeqMark x) = Sign.emptySig {
            Sign.sequenceMarkers = Set.singleton $ Id.simpleIdToId x
          }

propsOfTermSeq :: AS.TERM_SEQ -> Sign.Sign
propsOfTermSeq s = case s of
    AS.Term_seq term -> propsOfTerm term
    AS.Seq_marks x -> Sign.emptySig {
            Sign.sequenceMarkers = Set.singleton $ Id.simpleIdToId x
          }

uniteMap :: (a -> Sign.Sign) -> [a] -> Sign
uniteMap p = List.foldl (\ sig -> Sign.unite sig . p)
   Sign.emptySig

-- | Common Logic static analysis
basicCommonLogicAnalysis :: (AS.BASIC_SPEC, Sign.Sign, GlobalAnnos)
  -> Result (AS.BASIC_SPEC,
             ExtSign Sign.Sign Symbol.Symbol,
             [AS_Anno.Named AS.TEXT_META])
basicCommonLogicAnalysis (bs', sig, ga) =
   Result.Result [] $ if exErrs then Nothing else
     Just (bs', ExtSign sigItems newSyms, sentences)
    where
      bs = expandCurieBS (prefix_map ga) bs'
      sigItems = makeSig bs sig
      newSyms = Set.map Symbol.Symbol
                  $ Set.difference (Sign.allItems sigItems) $ Sign.allItems sig
      bsform = makeFormulas bs sigItems
  -- [DIAG_FORM] signature and list of sentences
      sentences = map formula bsform
  -- Annoted Sentences (Ax_), numbering, DiagError
      exErrs = False

-- | creates a morphism from a symbol map
inducedFromMorphism :: Map.Map Symbol.Symbol Symbol.Symbol
                    -> Sign.Sign
                    -> Result.Result Morphism.Morphism
inducedFromMorphism m s = let
  p = Map.mapKeys symName $ Map.map symName m
  t = Sign.emptySig { discourseNames = Set.map (applyMap p) $ discourseNames s
                    , nondiscourseNames = Set.map (applyMap p) $ nondiscourseNames s
                    , sequenceMarkers = Set.map (applyMap p) $ sequenceMarkers s
                    }
  in return $ mkMorphism s t p

splitFragment :: Id -> (String, String)
splitFragment = span (/= '#') . show

inducedFromToMorphism :: Map.Map Symbol.Symbol Symbol.Symbol
                    -> ExtSign Sign.Sign Symbol.Symbol
                    -> ExtSign Sign.Sign Symbol.Symbol
                    -> Result.Result Morphism.Morphism
inducedFromToMorphism m (ExtSign s sys) (ExtSign t ty) = let
  tsy = Set.fold (\ r -> let (q, f) = splitFragment $ symName r
          in MapSet.insert f q) MapSet.empty ty
  p = Set.fold (\ sy -> let n = symName sy in case Map.lookup sy m of
         Just r -> Map.insert n $ symName r
         Nothing -> if Set.member sy ty then id else
           let (_, f) = splitFragment n
           in case Set.toList $ MapSet.lookup f tsy of
                [q] -> Map.insert n $ simpleIdToId
                    $ mkSimpleId $ q ++ f
                _ -> id) Map.empty sys
  t2 = Sign.emptySig
       { discourseNames = Set.map (applyMap p) $ discourseNames s
       , nondiscourseNames = Set.map (applyMap p) $ nondiscourseNames s
       , sequenceMarkers = Set.map (applyMap p) $ sequenceMarkers s
       }
  in if isSubSigOf t2 t then return $ mkMorphism s t p else
        fail $ "cannot map symbols from\n" ++ showDoc (sigDiff t2 t) "\nto\n"
          ++ showDoc t ""

-- | negate sentence (text) - propagates negation to sentences
negForm :: AS.TEXT_META -> AS.TEXT_META
negForm tm = tm { AS.getText = negForm_txt $ AS.getText tm }

negForm_txt :: AS.TEXT -> AS.TEXT
negForm_txt t = case t of
  AS.Text phrs r -> AS.Text (map negForm_phr phrs) r
  AS.Named_text n txt r -> AS.Named_text n (negForm_txt txt) r

-- negate phrase - propagates negation to sentences
negForm_phr :: AS.PHRASE -> AS.PHRASE
negForm_phr phr = case phr of
  AS.Module m -> AS.Module $ negForm_mod m
  AS.Sentence s -> AS.Sentence $ negForm_sen s
  AS.Comment_text c t r -> AS.Comment_text c (negForm_txt t) r
  x -> x

-- negate module - propagates negation to sentences
negForm_mod :: AS.MODULE -> AS.MODULE
negForm_mod m = case m of
  AS.Mod n t r -> AS.Mod n (negForm_txt t) r
  AS.Mod_ex n exs t r -> AS.Mod_ex n exs (negForm_txt t) r

-- negate sentence
negForm_sen :: AS.SENTENCE -> AS.SENTENCE
negForm_sen f = case f of
  AS.Quant_sent _ _ _ r -> AS.Bool_sent (AS.Negation f) r
  AS.Bool_sent bs r -> case bs of
    AS.Negation s -> s
    _ -> AS.Bool_sent (AS.Negation f) r
  _ -> AS.Bool_sent (AS.Negation f) Id.nullRange

-- | Static analysis for symbol maps
mkStatSymbMapItem :: [AS.SYMB_MAP_ITEMS]
                  -> Result.Result (Map.Map Symbol.Symbol Symbol.Symbol)
mkStatSymbMapItem xs =
    Result.Result
    {
      Result.diags = []
    , Result.maybeResult = Just $
                           foldl
                           (
                            \ smap x ->
                                case x of
                                  AS.Symb_map_items sitem _ ->
                                       Map.union smap $ statSymbMapItem sitem
                           )
                           Map.empty
                           xs
    }

statSymbMapItem :: [AS.SYMB_OR_MAP] -> Map.Map Symbol.Symbol Symbol.Symbol
statSymbMapItem =
    foldl
    (
     \ mmap x ->
         case x of
           AS.Symb sym -> Map.insert (nosToSymbol sym) (nosToSymbol sym) mmap
           AS.Symb_mapN s1 s2 _
             -> Map.insert (symbToSymbol s1) (symbToSymbol s2) mmap
           AS.Symb_mapS s1 s2 _
             -> Map.insert (symbToSymbol s1) (symbToSymbol s2) mmap
    )
    Map.empty

-- | Retrieve raw symbols
mkStatSymbItems :: [AS.SYMB_ITEMS] -> Result.Result [Symbol.Symbol]
mkStatSymbItems a = Result.Result
                    {
                      Result.diags = []
                    , Result.maybeResult = Just $ statSymbItems a
                    }

statSymbItems :: [AS.SYMB_ITEMS] -> [Symbol.Symbol]
statSymbItems = concatMap symbItemsToSymbol

symbItemsToSymbol :: AS.SYMB_ITEMS -> [Symbol.Symbol]
symbItemsToSymbol (AS.Symb_items syms _) = map nosToSymbol syms

nosToSymbol :: AS.NAME_OR_SEQMARK -> Symbol.Symbol
nosToSymbol nos = case nos of
  AS.Name tok -> symbToSymbol tok
  AS.SeqMark tok -> symbToSymbol tok

symbToSymbol :: Id.Token -> Symbol.Symbol
symbToSymbol tok = Symbol.Symbol {Symbol.symName = Id.simpleIdToId tok}

-- | retrieves all symbols from the text
symsOfTextMeta :: AS.TEXT_META -> [Symbol.Symbol]
symsOfTextMeta tm =
  Set.toList $ Symbol.symOf $ retrieveSign Sign.emptySig $ AS_Anno.emptyAnno tm

-- | compute colimit of CL signatures
signColimit :: Gr Sign.Sign (Int, Morphism.Morphism)
                           -> Result (Sign.Sign, Map.Map Int Morphism.Morphism)
signColimit diag = do
 let mor2fun (x,mor) = (x, Morphism.propMap mor)
     dGraph = emap mor2fun $ nmap Sign.discourseNames diag
     (dCol, dmap) = addIntToSymbols $ computeColimitSet dGraph
     ndGraph = emap mor2fun $ nmap Sign.nondiscourseNames diag
     (ndCol, ndmap) = addIntToSymbols $ computeColimitSet ndGraph
     sGraph = emap mor2fun $ nmap Sign.sequenceMarkers diag
     (sCol, smap) = addIntToSymbols $ computeColimitSet sGraph
     sig = Sign { Sign.discourseNames = dCol
                 , Sign.nondiscourseNames = ndCol
                 , Sign.sequenceMarkers = sCol
                 }
     mors = Map.unions $ map (\ (x, nsig) -> 
                   let m = Morphism.Morphism {
                              Morphism.source = nsig
                            , Morphism.target = sig
                            , Morphism.propMap = Map.unions 
                                [ Map.findWithDefault (error "dmap") x dmap, 
                                  Map.findWithDefault (error "ndmap") x ndmap, 
                                  Map.findWithDefault (error "smap") x smap]
                           }
                            in Map.insert x m Map.empty) $ labNodes diag
 return (sig, mors)
