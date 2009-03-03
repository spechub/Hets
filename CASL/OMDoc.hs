{- |
Module      :  $Header$
Description :  Hets-to-OMDoc conversion
Copyright   :  (c) Ewaryst Schulz, DFKI 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  ewaryst.schulz@dfki.de
Stability   :  provisional
Portability :  non-portable(Logic)

CASL implementation of the interface functions export_signToOmdoc, export_morphismToOmdoc, export_senToOmdoc from class Logic. The actual instantiation can be found in module CASL.Logic_CASL.
-}

module CASL.OMDoc
    ( exportSignToOmdoc
    , exportMorphismToOmdoc
    , exportSenToOmdoc
    ) where

import OMDoc.DataTypes

import Common.AS_Annotation
import Common.Id
import Common.LibName
import Common.Result

import CASL.AS_Basic_CASL
import CASL.ATC_CASL ()
import CASL.Sign
import CASL.Morphism
import CASL.Fold
import CASL.Quantification

import Data.Map as Map
import Data.Set as Set

exportSignToOmdoc :: SIMPLE_ID -> LIB_ID -> Sign f e -> [TCElement]
exportSignToOmdoc _ _ sign =
    Set.toList (Set.map (sortSignToOmdoc sign) (sortSet sign))
 ++ Map.elems (mapWithKey (funSignToOmdoc sign) (opMap sign))
 ++ Map.elems (mapWithKey (predSignToOmdoc sign) (predMap sign))

{-
    [TCComment $ "sortSet\n" ++ show (sortSet sign)
     ++ "\n___________________\nemptySortSet\n" ++ show (emptySortSet sign)
     ++ "\n___________________\nopMap\n" ++ show (opMap sign)
     ++ "\n___________________\npredMap\n" ++ show (predMap sign)
     ++ "\n___________________\ndeclaredSymbols\n" ++ show (declaredSymbols sign)]
-}

exportMorphismToOmdoc :: SIMPLE_ID -> LIB_ID -> Morphism f e ()
                      -> [TCElement]
-- exportMorphismToOmdoc sid lid morphism = []
exportMorphismToOmdoc _ _ _ = []

exportSenToOmdoc :: SIMPLE_ID -> LIB_ID -> Sign f e -> Named(FORMULA f)
                 -> [TCElement]
exportSenToOmdoc sid lid sign formula = 
    [TCAxiomOrTheorem True (senAttr formula) $ foldFormula 
     (omdocRec (SPEC_ID (simpleIdToId sid) (Just lid))
               sign (\_ -> error "CASL extension not supported."))
     (sentence formula)]


sfail :: String -> Range -> a
sfail s r = error $ show (Diag Error ("unexpected " ++ s) r)

idToOmdoc :: SPEC_ID -> Id -> OMElement
idToOmdoc spid s
    | isQualName s = buildOMS "yesqual" (SPEC_ID (getNodeId s) Nothing) (unQualName s)
    | otherwise = buildOMS "noqual" spid s


-- | probably outsource this to a generic module
buildOMS :: String -> SPEC_ID -> Id -> OMElement
buildOMS str (SPEC_ID sid lid) i = OMS 
                                 (CD (str ++ (show sid)) (case lid of
                                                   Nothing -> Nothing
                                                   (Just l) -> Just (show l)))
                                 $ OMName $ show i

sortToOmdoc :: SPEC_ID -> Id -> OMElement
sortToOmdoc = idToOmdoc

funToOmdoc :: SPEC_ID -> OP_SYMB -> OMElement
funToOmdoc spid (Qual_op_name i _ _) = idToOmdoc spid i
funToOmdoc spid (Op_name i) = idToOmdoc spid i

predToOmdoc :: SPEC_ID -> PRED_SYMB -> OMElement
predToOmdoc spid (Qual_pred_name i _ _) = idToOmdoc spid i
predToOmdoc spid (Pred_name i) = idToOmdoc spid i

-- | type attributes for terms can only consist of a single sort
sortToOmdocAttribute :: SPEC_ID -> Id -> OMAttribute
sortToOmdocAttribute spid s = OMAttr (st_const "type") $ sortToOmdoc spid s

varToOmdoc :: Token -> OMElement
varToOmdoc v = OMV $ OMName $ tokStr v

-- | typed vars can only be typed by a single sort
varDeclToOMDoc :: SPEC_ID -> (VAR, SORT) -> OMElement
varDeclToOMDoc spid (v, s) = OMATTT (varToOmdoc v) (sortToOmdocAttribute spid s)



-- | Predefined truthval constants: false, true
tv_const :: String -> OMElement
tv_const n = OMS (CD "truthval" Nothing) $ OMName n

-- | Predefined simpletypes constants: funtype, type
st_const :: String -> OMElement
st_const n = OMS (CD "simpletypes" Nothing) $ OMName n

-- | Predefined pl0 constants: not, and, or, implies, implied, equivalent
pl0_const :: String -> OMElement
pl0_const n = OMS (CD "pl0" Nothing) $ OMName n

-- | Predefined pl1 constants: forall, exists
pl1_const :: String -> OMElement
pl1_const n = OMS (CD "pl1" Nothing) $ OMName n

-- | Predefined casl constants: eq, eeq, existsunique, defined, in, if, cast
casl_const :: String -> OMElement
casl_const n = OMS (CD "casl" Nothing) $ OMName n



omdocRec :: SPEC_ID -> Sign f e -> (f -> OMElement)
         -> Record f OMElement OMElement
omdocRec spid sign mf = Record
    { foldQuantification = \ _ q vs f _ ->
      let s = case q of
                Universal -> pl1_const "forall"
                Existential -> pl1_const "exists"
                Unique_existential -> casl_const "existsunique"
          vl = Prelude.map (varDeclToOMDoc spid) $ flatVAR_DECLs vs
      in OMBIND s vl f
    , foldConjunction = \ _ fs _ -> OMA $ (pl0_const "and") : fs
    , foldDisjunction = \ _ fs _ -> OMA $ (pl0_const "or") : fs
    , foldImplication = \ _ f1 f2 b _ ->
        if b then (OMA [(pl0_const "implies") , f1, f2])
        else (OMA [(pl0_const "implied") , f1, f2])
    , foldEquivalence = \ _ f1 f2 _ ->
                        (OMA [(pl0_const "equivalent") , f1, f2])
    , foldNegation = \ _ f _ -> (OMA [(pl0_const "not") , f])
    , foldTrue_atom = \ _ _ -> tv_const "true"
    , foldFalse_atom = \ _ _ -> tv_const "false"
    , foldPredication = \ _ p ts _ -> OMA $ (predToOmdoc spid p) : ts
    , foldDefinedness = \ _ t _ -> OMA [(casl_const "def"), t]
    , foldExistl_equation = \ _ t1 t2 _ -> (OMA [(casl_const "eeq") , t1, t2])
    , foldStrong_equation = \ _ t1 t2 _ -> (OMA [(casl_const "eq") , t1, t2])
    , foldMembership = \ _ t s _ ->
                       (OMA [(casl_const "in") , t, sortToOmdoc spid s])
    , foldMixfix_formula = \ t _ -> sfail "Mixfix_formula" $ getRange t
    , foldSort_gen_ax = \ t _ _ -> OMA []
    , foldExtFORMULA = \ _ f -> mf f
    , foldQual_var = \ _ v _ _ -> varToOmdoc v
    , foldApplication = \ _ o ts _ -> OMA $ (funToOmdoc spid o) : ts
    , foldSorted_term = \ _ r _ _ -> r
    , foldCast = \ _ t s _ ->
                 (OMA [(casl_const "cast") , t, sortToOmdoc spid s])
    , foldConditional = \ _ e f t _ -> (OMA [(casl_const "if") , e , t, f])
    , foldMixfix_qual_pred = \ _ p -> sfail "Mixfix_qual_pred" $ getRange p
    , foldMixfix_term = \ (Mixfix_term ts) _ ->
        sfail "Mixfix_term" $ getRange ts
    , foldMixfix_token = \ _ t -> sfail "Mixfix_token" $ tokPos t
    , foldMixfix_sorted_term = \ _ _ r -> sfail "Mixfix_sorted_term" r
    , foldMixfix_cast = \ _ _ r -> sfail "Mixfix_cast" r
    , foldMixfix_parenthesized = \ _ _ r -> sfail "Mixfix_parenthesized" r
    , foldMixfix_bracketed = \ _ _ r -> sfail "Mixfix_bracketed" r
    , foldMixfix_braced = \ _ _ r -> sfail "Mixfix_braced" r }


sortSignToOmdoc :: Sign a e -> SORT -> TCElement
sortSignToOmdoc sign s = TCComment $ show s
{-
    SList (SSymbol "sorts"
      : map sortToSSymbol (Set.toList $ sortSet sign))
-}

predSignToOmdoc :: Sign a e -> Id -> (Set.Set PredType) -> TCElement
predSignToOmdoc sign p ptypes = TCComment $ (show p) ++ "\n" ++ (show ptypes)

{-
    concatMap (\ (p, ts) -> map (\ t ->
       SList [ SSymbol "predicate"
             , predIdToSSymbol sign p t
             , SList $ map sortToSSymbol $ predArgs t ]) $ Set.toList ts)
      $ Map.toList pm
-}

funSignToOmdoc :: Sign a e -> Id -> (Set.Set OpType) -> TCElement
funSignToOmdoc sign f ftypes = TCComment $ (show f) ++ "\n" ++ (show ftypes)

{-
    concatMap (\ (p, ts) -> map (\ t ->
       SList [ SSymbol "function"
             , opIdToSSymbol sign p t
             , SList $ map sortToSSymbol $ opArgs t
             , sortToSSymbol $ opRes t ]) $ Set.toList ts)
      $ Map.toList om
-}
