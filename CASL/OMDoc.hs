{- |
Module      :  $Header$
Description :  Hets-to-OMDoc conversion
Copyright   :  (c) Ewaryst Schulz, DFKI 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  ewaryst.schulz@dfki.de
Stability   :  provisional
Portability :  non-portable(Logic)

Implementation of the interface functions from Logic
-}
module CASL.OMDoc
  where

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

exportSignToOmdoc :: SIMPLE_ID -> LIB_ID -> Sign f e -> [TCElement]
-- exportSignToOmdoc sid libid sign = []
exportSignToOmdoc _ _ _ = []

exportMorphismToOmdoc :: SIMPLE_ID -> LIB_ID -> Morphism f e ()
                      -> [TCElement]
-- exportMorphismToOmdoc sid libid morphism = []
exportMorphismToOmdoc _ _ _ = []

exportSenToOmdoc :: SIMPLE_ID -> LIB_ID -> Sign f e -> Named(FORMULA f)
                 -> [TCElement]
-- exportSenToOmdoc sid libid sign formula = 
exportSenToOmdoc _ _ sign formula = 
    [TCAxiomOrTheorem True (senAttr formula) $ foldFormula 
                 (omdocRec sign (\_ -> mydummy1 "extension not supported"))
                 (sentence formula)]


-- Name unter: (senAttr formula)

sfail :: String -> Range -> a
sfail s r = error $ show (Diag Error ("unexpected " ++ s) r)

{- 
need functions:
predefined casl-content dictionaries
-}

mydummy1 :: String -> OMElement
mydummy1 = OMC

mydummy :: OMElement
mydummy = mydummy1 "dummy"

showElem :: Show a => String -> a -> String
showElem s x = s ++ "[" ++ show x ++ "]"

showDummy :: Show a => String -> a -> OMElement
showDummy s = mydummy1 . (showElem s)



sortToOmdoc :: Id -> OMElement
sortToOmdoc s = showDummy "sort" s

sortToOmdocAttribute :: Id -> OMAttribute
sortToOmdocAttribute s = OMAttr (st_const "Type") $ sortToOmdoc s

varToOmdoc :: Token -> OMElement
varToOmdoc v = OMV $ OMName $ showElem "var" v

varDeclToOMDoc :: (VAR, SORT) -> OMElement
varDeclToOMDoc (v, s) = OMATTT (varToOmdoc v) (sortToOmdocAttribute s)



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



omdocRec :: Sign f e -> (f -> OMElement)
         -> Record f OMElement OMElement
-- omdocRec sign mf = Record
omdocRec _ mf = Record
    { foldQuantification = \ _ q vs f _ ->
      let s = case q of
                Universal -> pl1_const "forall"
                Existential -> pl1_const "exists"
                Unique_existential -> casl_const "existsunique"
          vl = map varDeclToOMDoc $ flatVAR_DECLs vs
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
    , foldPredication = \ _ p ts _ -> OMA $ (showDummy "pred" p) : ts
    , foldDefinedness = \ _ t _ -> OMA [(casl_const "def"), t]
    , foldExistl_equation = \ _ t1 t2 _ -> (OMA [(casl_const "eeq") , t1, t2])
    , foldStrong_equation = \ _ t1 t2 _ -> (OMA [(casl_const "eq") , t1, t2])
    , foldMembership = \ _ t s _ -> (OMA [(casl_const "in") , t, sortToOmdoc s])
    , foldMixfix_formula = \ t _ -> sfail "Mixfix_formula" $ getRange t
    , foldSort_gen_ax = \ t _ _ -> sfail "Sort_gen_ax" $ getRange t
    , foldExtFORMULA = \ _ f -> mf f
    , foldQual_var = \ _ v _ _ -> varToOmdoc v
    , foldApplication = \ _ o ts _ -> OMA $ (showDummy "fun" o) : ts
    , foldSorted_term = \ _ r _ _ -> r
    , foldCast = \ _ t s _ -> (OMA [(casl_const "cast") , t, sortToOmdoc s])
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
