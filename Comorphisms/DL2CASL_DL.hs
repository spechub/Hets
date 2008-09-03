{- |
Module      :  $Header$
Description :  Comorphism from DL to CASL_DL
Copyright   :  (c) Dominik Luecke and Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

The translating comorphism from DL to CASL_DL basically this is an
identity comorphism from SROIQ(D) to SROIQ(D)
-}

module Comorphisms.DL2CASL_DL
    (
     DL2CASL_DL(..)
    )
    where

import Logic.Logic
import Logic.Comorphism
import Common.AS_Annotation
import Common.Result
import Common.Id
import qualified Data.Set as Set
import qualified Data.Map as Map

-- DL
import DL.Logic_DL as LDL
import DL.AS as ADL
import qualified DL.Sign as SDL

--CASL_DL = codomain
import CASL_DL.Logic_CASL_DL
import CASL_DL.AS_CASL_DL
import CASL_DL.StatAna -- DLSign
import CASL.AS_Basic_CASL
import CASL.Sign
import CASL_DL.Sign
import CASL_DL.Sublogics
import CASL.Morphism
import qualified CASL_DL.PredefinedSign as PS

data DL2CASL_DL = DL2CASL_DL deriving (Show)

instance Language DL2CASL_DL

thing :: SORT
thing = PS.topSort

dataD :: SORT
dataD = PS.topSortD

instance Comorphism
    DL2CASL_DL      -- comorphism
    DL              -- lid domain
    ()              -- sublogics domain
    DLBasic         -- Basic spec domain
    DLBasicItem     -- sentence domain
    ()              -- symbol items domain
    ()              -- symbol map items domain
    SDL.Sign        -- signature domain
    SDL.DLMorphism  -- morphism domain
    SDL.DLSymbol    -- symbol domain
    SDL.RawDLSymbol -- rawsymbol domain
    ()              -- proof tree codomain
    CASL_DL         -- lid codomain
    CASL_DL_SL      -- sublogics codomain
    DL_BASIC_SPEC   -- Basic spec codomain
    DLFORMULA       -- sentence codomain
    SYMB_ITEMS      -- symbol items codomain
    SYMB_MAP_ITEMS  -- symbol map items codomain
    DLSign          -- signature codomain
    DLMor           -- morphism codomain
    Symbol          -- symbol codomain
    RawSymbol       -- rawsymbol codomain
    Q_ProofTree     -- proof tree domain
        where
          sourceLogic DL2CASL_DL    = DL
          sourceSublogic DL2CASL_DL = ()
          targetLogic DL2CASL_DL    = CASL_DL
          mapSublogic DL2CASL_DL _  = Just SROIQ
          map_theory DL2CASL_DL     = map_DL_theory
          map_morphism DL2CASL_DL   = mapMorphism
          isInclusionComorphism DL2CASL_DL = True


mapMorphism :: SDL.DLMorphism -> Result DLMor
mapMorphism phi = do
    ssign <- mapt_sign $ SDL.msource phi
    tsign <- mapt_sign $ SDL.mtarget phi
    let cm = Map.mapKeys (\x -> (x, PredType [thing])) $ SDL.c_map phi
        om = Map.mapKeys (\x -> (x, PredType [thing,thing])) $
             Map.mapKeys SDL.nameO $ Map.map SDL.nameO $ SDL.op_map phi
        dm = Map.mapKeys (\x -> (x, PredType [thing,dataD])) $
             Map.mapKeys SDL.nameD $ Map.map SDL.nameD $ SDL.dp_map phi
        pm = cm `Map.union` om `Map.union` dm
        im = Map.map (\x -> (x, Total)) $
             Map.mapKeys (\x -> (x, OpType Total [] (thing))) $
             Map.mapKeys SDL.iid $ Map.map SDL.iid $ SDL.i_map phi
    return Morphism {
                 msource = ssign,
                 mtarget = tsign,
                 morKind = InclMor,
                 sort_map = Map.empty,
                 fun_map =  im,
                 pred_map = pm,
                 extended_map = ()
                }

map_DL_theory :: (SDL.Sign, [Named DLBasicItem]) ->
                 Result (DLSign, [Named DLFORMULA])
map_DL_theory (sig, n_sens) =
    do
      osig <- mapt_sign sig
      oforms <- mapM (map_named_basic_item sig) n_sens
      return (osig, concat $ oforms)

isObjProp :: SDL.Sign -> Id -> Bool
isObjProp inSig pName =
    let
        inObjProps  = Set.map (SDL.nameO) $ SDL.objectProps inSig
    in
      pName `Set.member` inObjProps

isDataProp :: SDL.Sign -> Id -> Bool
isDataProp inSig pName =
    let
        inDataProps = Set.map (SDL.nameD) $ SDL.dataProps inSig
    in
      pName `Set.member` inDataProps

-- Generation of a CASL_DL Signature
mapt_sign :: SDL.Sign -> Result DLSign
mapt_sign inSig =
    let
        inClasses   = SDL.classes inSig
        inDataProps = Set.map (SDL.nameD) $ SDL.dataProps inSig
        inObjProps  = Set.map (SDL.nameO) $ SDL.objectProps inSig
        indis       = Set.map (SDL.iid)   $SDL.individuals inSig
        oClasses    = map (\x -> (x,
                         Set.fromList
                           [PredType
                              [thing]])) $ Set.toList $ Set.delete SDL.bottomSort $ Set.delete SDL.topSort $ inClasses
        oObjs       = map (\x -> (x,
                         Set.fromList
                           [PredType
                              [thing,thing]])) $ Set.toList $ inObjProps
        oDtProps    = map (\x -> (x,
                         Set.fromList
                           [PredType
                              [thing,dataD]])) $ Set.toList $ inDataProps
        oIndis     = map (\x -> (x,
                         Set.fromList
                           [OpType Total [] (thing)])) $ Set.toList $ indis

    in
      return ((emptySign emptyCASL_DLSign)
              {
                opMap   = Map.fromList oIndis
              , predMap = Map.fromList (oClasses ++ oObjs ++ oDtProps)
             })

-- Preservation of the names
map_named_basic_item :: SDL.Sign -> Named DLBasicItem -> Result [Named DLFORMULA]
map_named_basic_item sign sens =
    let
        s = sentence sens
    in
      do
        os <- map_basic_item sign s
        return $ map (\x -> sens {sentence = x}) os

-- the top mapping function
map_basic_item :: SDL.Sign -> DLBasicItem ->  Result [DLFORMULA]
map_basic_item sig sent =
    case sent of
      DLClass iid props _ _ ->
          do
            propsM <- mapM (map_class_property sig iid) props
            return $ concat $ propsM
      DLObjectProperty iid dc rc prel chars _ _ ->
          do
            opDom  <- map_object_domain sig iid dc
            opCod  <- map_object_codomain sig iid rc
            oPrel  <- mapM (map_prel sig iid) prel
            oChars <- mapM (map_chars sig iid) chars
            return $ opDom ++ opCod ++ (concat oPrel) ++ oChars
      DLDataProperty iid dc rc prel chars _ _ ->
          do
            dDom <- map_data_domain sig iid dc
            dCod <- map_data_codomain sig iid rc
            dPrel <- mapM (map_prel sig iid) prel
            oChars <- case chars of
                        Nothing -> return $ []
                        Just c  ->
                            do
                              y <- map_chars sig iid c
                              return $ [y]
            return $ dDom ++ dCod ++ (concat dPrel) ++ oChars
      DLIndividual iid tp fts irel _ _ ->
          do
            tps  <- map_types sig iid tp
            ofts <- mapM (map_facts sig iid) fts
            orel <- mapM (map_irel sig iid) irel
            return $ (tps ++ ofts ++ (concat orel))
      DLMultiIndi _ _ _ _ _ rn -> fatal_error
        "DL2CASL_DL: Multi-Individual was not expanded." rn

map_irel :: SDL.Sign -> Id -> DLIndRel -> Result [DLFORMULA]
map_irel _ indi rel =
    case rel of
      DLSameAs ids rn -> mapM (\x -> return $ Strong_equation
                 (Application
                    (Qual_op_name indi (Op_type Total [] thing nullRange) nullRange)
                    []
                    nullRange)
                 (Application
                    (Qual_op_name x (Op_type Total [] thing nullRange) nullRange)
                    []
                    nullRange)
                 rn) ids
      DLDifferentFrom ids rn -> mapM (\x -> return $ Negation
                 (Strong_equation
                    (Application
                       (Qual_op_name indi (Op_type Total [] thing nullRange) nullRange)
                       []
                       nullRange)
                    (Application
                       (Qual_op_name x (Op_type Total [] thing nullRange) nullRange)
                       []
                       nullRange)
                    nullRange)
                 rn) ids

-- translation of facts
map_facts :: SDL.Sign -> Id -> DLFacts -> Result DLFORMULA
map_facts _ indi fact =
    case fact of
      DLPosFact (prop, i2) rn ->  return $ Predication
                 (Qual_pred_name prop (Pred_type [thing, thing] nullRange)
                    nullRange)
                 [Application
                    (Qual_op_name indi (Op_type Total [] thing nullRange) nullRange)
                    []
                    nullRange,
                  Application
                    (Qual_op_name i2 (Op_type Total [] thing nullRange) nullRange)
                    []
                    nullRange]
                 rn
      DLNegFact (prop, i2) rn -> return $ Negation
                 (Predication
                    (Qual_pred_name prop (Pred_type [thing, thing] nullRange)
                       nullRange)
                    [Application
                       (Qual_op_name indi (Op_type Total [] thing nullRange) nullRange)
                       []
                       nullRange,
                     Application
                       (Qual_op_name i2 (Op_type Total [] thing nullRange) nullRange)
                       []
                       nullRange]
                    nullRange)
                 rn

map_types :: SDL.Sign -> Id -> Maybe DLType -> Result [DLFORMULA]
map_types _ iid mt =
    case mt of
      Nothing -> return $ []
      Just t  ->
          case t of DLType cids rn ->
                        mapM (\x -> return $ Predication
                              (Qual_pred_name x (Pred_type [thing] nullRange) nullRange)
                              [Application
                               (Qual_op_name iid (Op_type Total [] thing nullRange) nullRange)
                               []
                               nullRange]
                              rn) cids

-- mapping of characteristics
map_chars :: SDL.Sign ->
             Id ->
             DLChars ->
             Result DLFORMULA
map_chars sig oid chs =
   let
        a = mkSimpleId "a"
        b = mkSimpleId "b"
        c = mkSimpleId "c"
   in
   if isObjProp sig oid
   then
    case chs of
      DLFunctional ->
          return $ Quantification Universal [Var_decl [a, b, c] thing nullRange]
                 (Implication
                    (Conjunction
                       [Predication
                          (Qual_pred_name oid (Pred_type [thing, thing] nullRange) nullRange)
                          [Qual_var a thing nullRange, Qual_var b thing nullRange]
                          nullRange,
                        Predication
                          (Qual_pred_name oid (Pred_type [thing, thing] nullRange) nullRange)
                          [Qual_var a thing nullRange, Qual_var c thing nullRange]
                          nullRange]
                       nullRange)
                    (Strong_equation (Qual_var b thing nullRange)
                       (Qual_var c thing nullRange)
                       nullRange)
                    True
                    nullRange)
                 nullRange
      DLInvFuntional ->
          return $ Quantification Universal [Var_decl [a, b, c] thing nullRange]
                 (Implication
                    (Conjunction
                       [Predication
                          (Qual_pred_name oid (Pred_type [thing, thing] nullRange) nullRange)
                          [Qual_var a thing nullRange, Qual_var b thing nullRange]
                          nullRange,
                        Predication
                          (Qual_pred_name oid (Pred_type [thing, thing] nullRange) nullRange)
                          [Qual_var c thing nullRange, Qual_var b thing nullRange]
                          nullRange]
                       nullRange)
                    (Strong_equation (Qual_var a thing nullRange)
                       (Qual_var c thing nullRange)
                       nullRange)
                    True
                    nullRange)
                 nullRange
      DLSymmetric ->
          return $ Quantification Universal [Var_decl [a, b] thing nullRange]
                 (Implication
                    (Predication
                       (Qual_pred_name oid (Pred_type [thing, thing] nullRange) nullRange)
                       [Qual_var a thing nullRange, Qual_var b thing nullRange]
                       nullRange)
                    (Predication
                       (Qual_pred_name oid (Pred_type [thing, thing] nullRange) nullRange)
                       [Qual_var b thing nullRange, Qual_var a thing nullRange]
                       nullRange)
                    True
                    nullRange)
                 nullRange
      DLTransitive ->
          return $ Quantification Universal [Var_decl [a, b, c] thing nullRange]
                 (Implication
                    (Conjunction
                       [Predication
                          (Qual_pred_name oid (Pred_type [thing, thing] nullRange) nullRange)
                          [Qual_var a thing nullRange, Qual_var b thing nullRange]
                          nullRange,
                        Predication
                          (Qual_pred_name oid (Pred_type [thing, thing] nullRange) nullRange)
                          [Qual_var b thing nullRange, Qual_var c thing nullRange]
                          nullRange]
                       nullRange)
                    (Predication
                       (Qual_pred_name oid (Pred_type [thing, thing] nullRange) nullRange)
                       [Qual_var a thing nullRange, Qual_var c thing nullRange]
                       nullRange)
                    True
                    nullRange)
                 nullRange
      DLReflexive ->
          return $ Quantification Universal [Var_decl [a] thing nullRange]
                 (Predication
                    (Qual_pred_name oid (Pred_type [thing, thing] nullRange) nullRange)
                    [Qual_var a thing nullRange, Qual_var a thing nullRange]
                    nullRange)
                 nullRange
      DLIrreflexive ->
          return $ Quantification Universal [Var_decl [a] thing nullRange]
                 (Negation
                    (Predication
                       (Qual_pred_name oid (Pred_type [thing, thing] nullRange) nullRange)
                       [Qual_var a thing nullRange, Qual_var a thing nullRange]
                       nullRange)
                    nullRange)
                 nullRange
   else
         fatal_error "handling of Data props nyi" nullRange

map_prel :: SDL.Sign ->
            Id ->                           -- Id of the property
            DLPropsRel ->
            Result [DLFORMULA]
map_prel sig oid prel =
   let
        a = mkSimpleId "a"
        b = mkSimpleId "b"
   in
   if isObjProp sig oid
   then
    case prel of
      DLInverses ids rn ->
          mapM (\x -> return $
               Quantification Universal [Var_decl [a, b] thing nullRange]
                 (Equivalence
                    (Predication
                       (Qual_pred_name oid (Pred_type [thing, thing] nullRange) nullRange)
                       [Qual_var a thing nullRange, Qual_var b thing nullRange]
                       nullRange)
                    (Predication
                       (Qual_pred_name x (Pred_type [thing, thing] nullRange) nullRange)
                       [Qual_var b thing nullRange, Qual_var a thing nullRange]
                       nullRange)
                    nullRange)
                 rn) ids
      DLSubProperty ids rn ->
          mapM (\x -> return $
                Quantification Universal [Var_decl [a, b] thing nullRange]
                 (Implication
                    (Predication
                       (Qual_pred_name oid (Pred_type [thing, thing] nullRange) nullRange)
                       [Qual_var a thing nullRange, Qual_var b thing nullRange]
                       nullRange)
                    (Predication
                       (Qual_pred_name x (Pred_type [thing, thing] nullRange) nullRange)
                       [Qual_var a thing nullRange, Qual_var b thing nullRange]
                       nullRange)
                    True
                    nullRange)
                 rn) ids
      DLEquivalent ids rn ->
          mapM (\x -> return $
               Quantification Universal [Var_decl [a, b] thing nullRange]
                 (Equivalence
                    (Predication
                       (Qual_pred_name oid (Pred_type [thing, thing] nullRange) nullRange)
                       [Qual_var a thing nullRange, Qual_var b thing nullRange]
                       nullRange)
                    (Predication
                       (Qual_pred_name x (Pred_type [thing, thing] nullRange) nullRange)
                       [Qual_var a thing nullRange, Qual_var b thing nullRange]
                       nullRange)
                    nullRange)
                 rn) ids
      DLDisjoint ids rn ->
          mapM (\x -> return $
               Quantification Universal [Var_decl [a, b] thing nullRange]
                 (Negation
                    (Conjunction
                       [Predication
                          (Qual_pred_name oid (Pred_type [thing, thing] nullRange) nullRange)
                          [Qual_var a thing nullRange, Qual_var b thing nullRange]
                          nullRange,
                        Predication
                          (Qual_pred_name x (Pred_type [thing, thing] nullRange) nullRange)
                          [Qual_var a thing nullRange, Qual_var b thing nullRange]
                          nullRange]
                       nullRange)
                    nullRange)
                 rn) ids
      DLSuperProperty _ rn -> fatal_error "DLSuperProperty nyi" rn
    else
        error "handling of Data Props nyi"

map_object_domain :: SDL.Sign -> Id -> Maybe DLConcept -> Result [DLFORMULA]
map_object_domain sig iid mcons =
    let
        a = mkSimpleId "a"
        b = mkSimpleId "b"
    in
    case mcons of
      Nothing   -> return []
      Just cons ->
          do
            cs <- map_concept sig "a" a cons
            return $ [Quantification Universal [Var_decl [a] thing nullRange]
                   (Implication
                    (Quantification Existential [Var_decl [b] thing nullRange]
                     (Predication
                      (Qual_pred_name iid (Pred_type [thing, thing] nullRange) nullRange)
                      [Qual_var a thing nullRange, Qual_var b thing nullRange]
                      nullRange)
                     nullRange)
                    cs
                    True
                    nullRange)
                   nullRange]

map_data_codomain :: SDL.Sign -> Id -> Maybe DLConcept -> Result [DLFORMULA]
map_data_codomain sig iid mcons =
    let
        a = mkSimpleId "a"
        b = mkSimpleId "b"
    in
    case mcons of
      Nothing   -> return []
      Just cons ->
          do
            cs <- map_concept sig "b" b cons
            return $ [Quantification Universal [Var_decl [b] dataD nullRange]
                   (Implication
                    (Quantification Existential [Var_decl [a] thing nullRange]
                     (Predication
                      (Qual_pred_name iid (Pred_type [thing, dataD] nullRange) nullRange)
                      [Qual_var a thing nullRange, Qual_var b dataD nullRange]
                      nullRange)
                     nullRange)
                    cs
                    True
                    nullRange)
                   nullRange]

map_object_codomain :: SDL.Sign -> Id -> Maybe DLConcept -> Result [DLFORMULA]
map_object_codomain sig iid mcons =
    let
        a = mkSimpleId "a"
        b = mkSimpleId "b"
    in
    case mcons of
      Nothing   -> return []
      Just cons ->
          do
            cs <- map_concept sig "b" b cons
            return $ [Quantification Universal [Var_decl [b] thing nullRange]
                   (Implication
                    (Quantification Existential [Var_decl [a] thing nullRange]
                     (Predication
                      (Qual_pred_name iid (Pred_type [thing, thing] nullRange) nullRange)
                      [Qual_var a thing nullRange, Qual_var b thing nullRange]
                      nullRange)
                     nullRange)
                    cs
                    True
                    nullRange)
                   nullRange]

map_data_domain :: SDL.Sign -> Id -> Maybe DLConcept -> Result [DLFORMULA]
map_data_domain sig iid mcons =
    let
        a = mkSimpleId "a"
        b = mkSimpleId "b"
    in
    case mcons of
      Nothing   -> return []
      Just cons ->
          do
            cs <- map_concept sig "a" a cons
            return $ [Quantification Universal [Var_decl [a] thing nullRange]
                   (Implication
                    (Quantification Existential [Var_decl [b] dataD nullRange]
                     (Predication
                      (Qual_pred_name iid (Pred_type [thing, dataD] nullRange) nullRange)
                      [Qual_var a thing nullRange, Qual_var b dataD nullRange]
                      nullRange)
                     nullRange)
                    cs
                    True
                    nullRange)
                   nullRange]

map_class_property :: SDL.Sign -> Id -> DLClassProperty -> Result [DLFORMULA]
map_class_property sig iid dcp =
    let
        a = mkSimpleId "a"
    in
    case dcp of
      DLSubClassof con rn   ->
          mapM (\x ->
                do
                  ct <- (map_concept sig "a" a x)
                  return $ Quantification Universal [Var_decl [a] thing nullRange]
                             (Implication
                              (Predication
                               (Qual_pred_name iid (Pred_type [thing] nullRange) nullRange)
                               [Qual_var a thing nullRange]
                               nullRange)
                              ct
                              True
                              nullRange) rn) con
      DLEquivalentTo con rn ->
          mapM (\x ->
                do
                  ct <- (map_concept sig "a" a x)
                  return $ Quantification Universal [Var_decl [a] thing nullRange]
                             (Equivalence
                              (Predication
                               (Qual_pred_name iid (Pred_type [thing] nullRange) nullRange)
                               [Qual_var a thing nullRange]
                               nullRange)
                              ct
                              nullRange) rn) con
      DLDisjointWith con rn ->
          do
            mapM (\x ->
                  do
                    ct <- (map_concept sig "a" a x)
                    return $ Quantification Universal [Var_decl [a] thing nullRange]
                               (Negation
                                (Conjunction
                                 [Predication
                                  (Qual_pred_name iid (Pred_type [thing] nullRange) nullRange)
                                  [Qual_var a thing nullRange]
                                  nullRange,
                                  ct]
                                 nullRange)
                                nullRange)
                               rn) con

next_str :: String -> String
next_str str =
    case str of
      [] -> "a"
      _  ->
          let h = head str
              t = tail str
          in
            case h of
              'a' -> 'b' : t
              'b' -> 'c' : t
              'c' -> 'd' : t
              'e' -> 'f' : t
              'f' -> 'g' : t
              'g' -> 'h' : t
              'h' -> 'i' : t
              'i' -> 'j' : t
              'j' -> 'k' : t
              'k' -> 'l' : t
              'l' -> 'm' : t
              'm' -> 'n' : t
              'n' -> 'o' : t
              'o' -> 'p' : t
              'p' -> 'q' : t
              'q' -> 'r' : t
              'r' -> 's' : t
              's' -> 't' : t
              't' -> 'u' : t
              'u' -> 'v' : t
              'v' -> 'w' : t
              'w' -> 'x' : t
              'x' -> 'y' : t
              'y' -> 'z' : t
              'z' -> 'a' : str
              _   -> error "Nope"


map_concept :: SDL.Sign -> String -> Token -> DLConcept -> Result DLFORMULA
map_concept sign str iid con =
    let
        a = mkSimpleId "a"
        b = mkSimpleId str
    in
    case con of
      DLAnd c1 c2 rn ->
          do
            c1t <- map_concept sign str b c1
            c2t <- map_concept sign str b c2
            return $   Conjunction [c1t,c2t] rn
      DLOr c1 c2 rn ->
          do
            c1t <- map_concept sign str b c1
            c2t <- map_concept sign str b c2
            return $   Disjunction [c1t,c2t] rn
      DLXor c1 c2 rn ->
          do
            c1t <- map_concept sign str b c1
            c2t <- map_concept sign str b c2
            return $ Conjunction
                 [Disjunction [c1t,c2t] nullRange,
                  Negation (Conjunction [c1t,c2t] nullRange)
                    nullRange]
                 rn
      DLNot c1 rn ->
          do
            c1t <- map_concept sign str b c1
            return $ Negation c1t rn
      DLClassId c1 rn ->
          do
            return $ Predication
                       (Qual_pred_name c1 (Pred_type [thing] nullRange) nullRange)
                       [Qual_var iid thing nullRange]
                       rn
      DLOneOf _ rn  -> fatal_error "oneOf nyi" rn
      DLSome rid conc rn ->
          if isDataProp sign rid
          then
              let
                  dataDA = case conc of
                          DLClassId c _ -> c
                          _             -> error "NO"
              in
                do
                  return $ Quantification Existential [Var_decl [mkSimpleId $ next_str str] dataDA nullRange]
                             (Predication
                              (Qual_pred_name rid (Pred_type [thing, dataDA] nullRange) nullRange)
                              [Qual_var iid thing nullRange, Qual_var (mkSimpleId $ next_str str) dataDA nullRange]
                              nullRange)
                             nullRange
          else
              do
                ct <- map_concept sign (next_str str) (mkSimpleId $ next_str str) conc
                return $ Quantification Existential [Var_decl [mkSimpleId $ next_str str] thing nullRange]
                           (Conjunction
                            [Predication
                             (Qual_pred_name rid (Pred_type [thing, thing] nullRange) nullRange)
                             [Qual_var iid thing nullRange, Qual_var (mkSimpleId $ next_str str) thing nullRange]
                             nullRange,
                             ct]
                            nullRange)
                           rn
      DLHas rid indi rn ->
          if isDataProp sign rid
          then
              fatal_error "handling of data props nyi" rn
          else
             return $ Predication
                (Qual_pred_name rid (Pred_type [thing, thing] nullRange) nullRange)
                [Qual_var iid thing nullRange, Qual_var (restoreToken indi) thing nullRange]
                rn
      DLValue rid indi rn ->
          if isDataProp sign rid
          then
              fatal_error "handling of data props nyi" rn
          else
             return $ Predication
                (Qual_pred_name rid (Pred_type [thing, thing] nullRange) nullRange)
                [Qual_var iid thing nullRange, Qual_var (restoreToken indi) thing nullRange]
                rn
      DLOnlysome rel cons rn ->  map_concept sign str iid $ expand (DLOnlysome rel cons rn)
      DLOnly rel cons rn ->
          if isDataProp sign rel
          then
              let
                  dataDA = case cons of
                          DLClassId c _ -> c
                          _             -> error "NO"
              in
                do
                  return $ Quantification Universal [Var_decl [mkSimpleId $ next_str str] dataDA nullRange]
                             (Predication
                              (Qual_pred_name rel (Pred_type [thing, dataDA] nullRange) nullRange)
                              [Qual_var iid thing nullRange, Qual_var (mkSimpleId $ next_str str) dataDA nullRange]
                              nullRange)
                             nullRange
          else
             do
               ct <- map_concept sign (next_str str) (mkSimpleId $ next_str str) cons
               return $ Quantification Universal [Var_decl [mkSimpleId $ next_str str] thing nullRange]
                 (Implication
                    (Predication
                       (Qual_pred_name rel (Pred_type [thing, thing] nullRange) nullRange)
                       [Qual_var iid thing nullRange,
                        Qual_var (mkSimpleId $ next_str str) thing nullRange]
                       nullRange)
                    ct
                    True
                    nullRange)
                 rn
      DLMin rid num mcons rn ->
          if isDataProp sign rid
          then
              fatal_error "handling of data props nyi" rn
          else
              do
                ocons <- case mcons of
                           Nothing -> return $ Nothing
                           Just  x ->
                               do
                                 o <- map_concept sign str a x
                                 return $ Just o
                return $
                    Quantification Universal [Var_decl [a] thing nullRange]
                       (ExtFORMULA
                           (
                            Cardinality CMin
                                            (Qual_pred_name rid (Pred_type [thing, thing] nullRange) nullRange)
                                            (Qual_var a thing nullRange)
                                            (makeCASLNumber num)
                                            ocons
                                            rn
                           )) rn
      DLMax rid num mcons rn ->
          if isDataProp sign rid
          then
              fatal_error "handling of data props nyi" rn
          else
              do
                ocons <- case mcons of
                           Nothing -> return $ Nothing
                           Just  x ->
                               do
                                 o <- map_concept sign str a x
                                 return $ Just o
                return $
                    Quantification Universal [Var_decl [a] thing nullRange]
                       (ExtFORMULA
                           (
                            Cardinality CMax
                                            (Qual_pred_name rid (Pred_type [thing, thing] nullRange) nullRange)
                                            (Qual_var a thing nullRange)
                                            (makeCASLNumber num)
                                            ocons
                                            rn
                           )) rn
      DLExactly rid num mcons rn ->
          if isDataProp sign rid
          then
              fatal_error "handling of data props nyi" rn
          else
              do
                ocons <- case mcons of
                           Nothing -> return $ Nothing
                           Just  x ->
                               do
                                 o <- map_concept sign str a x
                                 return $ Just o
                return $
                    Quantification Universal [Var_decl [a] thing nullRange]
                       (ExtFORMULA
                           (
                            Cardinality CExact
                                            (Qual_pred_name rid (Pred_type [thing, thing] nullRange) nullRange)
                                            (Qual_var a thing nullRange)
                                            (makeCASLNumber num)
                                            ocons
                                            rn
                           )) rn
      DLSelf rn -> return $ Strong_equation (Qual_var iid thing nullRange)
                    (Qual_var b thing nullRange)
                    rn


makeCASLNumber :: Int -> TERM DL_FORMULA
makeCASLNumber num = (Simple_id $ mkSimpleId $ show num) -- placeholder

restoreToken :: Id -> Token
restoreToken = head . getTokens
