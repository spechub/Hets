{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich and Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

The translating comorphism from CASL to SPASS.
-}

{- todo

   - implement translation of Sort_gen_ax (FORMULA f) 
   - add codeOutConditionalF  of Conditional of TERM f 
   - are all free type definitions a source of partial functions /
     partiallity? No...

-}

module Comorphisms.CASL2SPASS where

-- Debuging and Warning
import Debug.Trace

import Logic.Logic as Logic
import Logic.Comorphism

import Common.AS_Annotation
import Common.Id
import Common.Result
import Common.PrettyPrint

import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Rel as Rel

import Data.List as List
import Data.Maybe

-- CASL
import CASL.Logic_CASL 
import CASL.AS_Basic_CASL
import CASL.Sublogic
import qualified CASL.Sign as CSign
import CASL.Morphism
import CASL.Quantification 
import CASL.Overload
import CASL.Utils

-- SPASS
import SPASS.Sign as SPSign
import SPASS.Logic_SPASS
import SPASS.Translate

-- | The identity of the comorphism
data CASL2SPASS = CASL2SPASS deriving (Show)

-- | SPASS theories
type SPASSTheory = (SPSign.Sign,[Named SPTerm])

-- | A data type for storing the type of a CASL Id
data CType = CSort
           | CVar SORT
           | CPred CSign.PredType
           | COp   CSign.OpType
             deriving (Eq,Ord,Show)
-- | CASL Ids with Types mapped to SPIdentifier
type IdType_SPId_Map = Map.Map Id (Map.Map CType SPIdentifier)

-- | specialized lookup for IdType_SPId_Map
lookupSPId :: Id -> CType -> IdType_SPId_Map ->
          Maybe SPIdentifier
lookupSPId i t m = maybe Nothing (\ m' -> Map.lookup t m') (Map.lookup i m)

-- | specialized insert (with error) for IdType_SPId_Map
insertSPId :: Id -> CType -> 
              SPIdentifier ->
              IdType_SPId_Map ->
              IdType_SPId_Map
insertSPId i t spid m = 
    Map.insertWith (Map.unionWith err) i (Map.insert t spid Map.empty) m
    where err = error ("CASL2SPASS: for Id \""++show i ++
                       "\" the type \""++ show t ++ 
                       "\" can't be mapped to different SPASS identifiers")

-- | specialized elems into a set for IdType_SPId_Map
elemsSPId_Set :: IdType_SPId_Map -> Set.Set SPIdentifier
elemsSPId_Set = Map.fold (\ m res -> Set.union res 
                                      (Set.fromList (Map.elems m)))
                         Set.empty 
                  

 
-- extended signature translation
type SignTranslator f e = CSign.Sign f e -> e -> SPASSTheory -> SPASSTheory

-- extended signature translation for CASL
sigTrCASL :: SignTranslator () ()
sigTrCASL _ _ = id

-- extended formula translation
type FormulaTranslator f e = 
    CSign.Sign f e -> IdType_SPId_Map -> f -> SPTerm

-- extended formula translation for CASL
formTrCASL :: FormulaTranslator () ()
formTrCASL _ _ = error "CASL2SPASS: No extended formulas allowed in CASL"

instance Language CASL2SPASS -- default definition is okay

instance Comorphism CASL2SPASS
               CASL CASL.Sublogic.CASL_Sublogics
               CASLBasicSpec CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CASLSign 
               CASLMor
               CASL.Morphism.Symbol CASL.Morphism.RawSymbol ()
               SPASS () () SPTerm () ()
               SPSign.Sign 
               SPASSMorphism () () ()  where
    sourceLogic _ = CASL
    sourceSublogic _ = CASL_SL
                      { has_sub = True, 
                        has_part = False, -- no partiality yet ...
                        has_cons = True,
                        has_eq = True,
                        has_pred = True,
                        which_logic = FOL
                      }
    targetLogic _ = SPASS
    targetSublogic _ = ()
    map_theory _ = transTheory sigTrCASL formTrCASL
    map_morphism CASL2SPASS mor = do
       (sig1,_) <- map_sign CASL2SPASS (Logic.dom CASL mor)
       (sig2,_) <- map_sign CASL2SPASS (cod CASL mor)
       inclusion SPASS sig1 sig2
    map_sentence _ sign =
      return . mapSen formTrCASL sign
    map_symbol _ _ = error "CASL2SPASS.map_symbol"

---------------------------- Signature -----------------------------

transFuncMap :: IdType_SPId_Map ->
                Map.Map Id (Set.Set CSign.OpType) -> 
                (Map.Map SPIdentifier ([SPIdentifier],SPIdentifier),
                 IdType_SPId_Map)
transFuncMap idMap = Map.foldWithKey toSPOpType (Map.empty,idMap)
    where toSPOpType iden typeSet (fm,im) 
              | Set.null typeSet = 
                  error "CASL2SPASS: empty sets are not allowed in OpMaps"
              | Set.size typeSet == 1 =
                  let oType = head (Set.toList typeSet)
                      sid' = sid fm oType
                  in (Map.insert sid' (transOpType oType) fm,
                      insertSPId iden (COp oType) sid' im)
              | otherwise = Set.fold insOId (fm,im) typeSet
              where insOId typ (fm',im') =
                        let sid' = sid fm' typ
                        in (Map.insert sid' (transOpType typ) fm',
                         insertSPId iden (COp typ) sid' im')              
                    sid fma t = disSPOId (COp t) (transId iden) 
                                       (uType (transOpType t))
                                       (Set.union (Map.keysSet fma)
                                           (elemsSPId_Set idMap))
                    uType t = fst t ++ [snd t]

transPredMap :: IdType_SPId_Map -> 
                Map.Map Id (Set.Set CSign.PredType) -> 
                (Map.Map SPIdentifier [SPIdentifier],
                 IdType_SPId_Map)
transPredMap idMap = 
    Map.foldWithKey toSPPredType (Map.empty,idMap)
    where toSPPredType iden typeSet (fm,im) 
              | Set.null typeSet = 
                  error "CASL2SPASS: empty sets are not allowed in PredMaps"
              | Set.size typeSet == 1 =
                  let pType = head (Set.toList typeSet)
                      sid' = sid fm pType
                  in (Map.insert sid' (transPredType pType) fm,
                      insertSPId iden (CPred pType) sid' im)
              | otherwise = Set.fold insOId (fm,im) typeSet
              where insOId pType (fm',im') = 
                        let sid' = sid fm' pType 
                            predType = transPredType pType
                        in (Map.insert sid' predType fm',
                            insertSPId iden (CPred pType) sid' im')
                    sid fma t = disSPOId (CPred t) (transId iden) 
                                       (transPredType t)
                                       (Set.union (Map.keysSet fma)
                                           (elemsSPId_Set idMap))

disSPOId :: CType -> SPIdentifier -> [SPIdentifier] -> 
            Set.Set SPIdentifier -> SPIdentifier
disSPOId cType sid ty idSet
    | checkIdentifier sid && not (lkup sid) = sid
    | not (lkup asid) = asid
    | otherwise = addType asid 1
    where asid = sid ++ case cType of
                        CSort  -> ""
                        CVar _ -> ""
                        x -> '_':show (length ty - (case x of 
                                                    COp _ -> 1 
                                                    _     -> 0))
          lkup x = Set.member x idSet
          addType res n = 
              let nres = asid ++ '_':fc n
              in if nres == res 
                 then error ("CASL2SPASS: cannot calculate unambigous id for "++sid)
                 else if not (lkup nres) 
                      then nres
                      else addType nres (n+1)
          fc n = concatMap (take n) ty

transOpType :: CSign.OpType -> ([SPIdentifier],SPIdentifier)
transOpType ot = (map transId (CSign.opArgs ot), transId (CSign.opRes ot))

transPredType :: CSign.PredType -> [SPIdentifier]
transPredType pt = map transId (CSign.predArgs pt)

integrateGenerated :: IdType_SPId_Map -> [Named (FORMULA f)] -> 
                      Map.Map SPIdentifier (Maybe Generated) -> 
                      Map.Map SPIdentifier (Maybe Generated)
integrateGenerated idMap genSens spSortMap 
    | null genSens = spSortMap
    | otherwise = trace "Generated axioms are not implemented yet" spSortMap
{-        -- makeGens must not invent new sorts
        assert (Map.size spSortMap' == Map.size spSortMap) spSortMap'
    where spSortMap' = Map.union spSortMap (makeGens idMap genSens)

makeGens :: IdType_SPId_Map -> [Named (FORMULA f)] 
           -> Map.Map SPIdentifier (Maybe Generated)
makeGens idMap = 
    foldr ins Map.empty (concat (makeGen idMap))
  where
  ins (s,mGen) = Map.insert s mGen
  delDoubles xs = delDouble xs []
  delDouble [] _  = []
  delDouble (x:xs) sortList = let (Type s _a _b) = fst (head x) in
      if (length sortList) == 
         (length (addSortList s sortList)) then
        delDouble xs sortList
      else
        (x:(delDouble xs (s:sortList)))
  addSortList x xs = (List.nub (x :xs))


makeGen :: IdType_SPId_Map -> Named (FORMULA f) -> 
           [(SPIdentifier,Maybe Generated)]
makeGen sign nf = case sentence nf of 
  Sort_gen_ax constrs free -> (map makeGenP srts) where 
    (srts,ops,_maps) = recover_Sort_gen_ax constrs
    makeGenP s = (transSort s, 
                  mkGen (map makeOp (List.filter (hasTheSort s) ops)))
    makeOp opSym = (transOP_SYMB sign opSym, transArgs opSym)
    hasTheSort s (Qual_op_name _ ot _) = s == res_OP_TYPE ot 
    hasTheSort _ _ = error "CASL2SPASS.hasTheSort"
    transArgs (Qual_op_name _ sot _) = map transSort $ args_OP_TYPE ot
    transArgs _ = error "CASL2SPASS.transArgs"
  _ -> []
-}

transSign :: CSign.Sign f e -> 
             (SPSign.Sign,IdType_SPId_Map)
transSign sign = (SPSign.emptySign { sortRel = 
                                 Rel.map transId (CSign.sortRel sign) 
                           , sortMap = spSortMap
                           , funcMap = fMap
                           , predMap = pMap
                           },idMap'')
    where (spSortMap,idMap) = 
            Set.fold (\ i (sm,im) -> 
                          let sid = disSPOId CSort (transId i) 
                                       [take 20 (cycle "So")]
                                       (Map.keysSet sm)
                          in (Map.insert sid Nothing sm,
                              insertSPId i CSort sid im)) 
                                        (Map.empty,Map.empty) 
                                        (CSign.sortSet sign)
          (fMap,idMap') =  transFuncMap idMap  (CSign.opMap sign)
          (pMap,idMap'') = transPredMap idMap' (CSign.predMap sign) 

transTheory :: (Eq f) => SignTranslator f e 
            -> FormulaTranslator f e 
            -> (CSign.Sign f e, [Named (FORMULA f)])
            -> Result SPASSTheory 
transTheory trSig trForm (sign,sens) = 
  fmap (trSig sign (CSign.extendedInfo sign)) $
  return  (tSign {sortMap = integrateGenerated idMap 
                            genSens (sortMap tSign)},
          map (mapNamed (transFORM sign idMap trForm)) realSens)
  where (tSign,idMap) = transSign sign
        (genSens,realSens) = 
            partition (\ s -> case (sentence s) of
                              Sort_gen_ax _ _ -> True
                              _               -> False) sens


------------------------------ Formulas ------------------------------

transOP_SYMB :: IdType_SPId_Map -> OP_SYMB -> SPIdentifier
transOP_SYMB idMap (Qual_op_name op ot _) = 
    maybe (error ("CASL2SPASS unknown op: " ++ show op))
          id (lookupSPId op (COp (CSign.toOpType ot)) idMap)

transOP_SYMB _ (Op_name _) = error "CASL2SPASS: unqualified operation"

transPRED_SYMB :: IdType_SPId_Map -> PRED_SYMB -> SPIdentifier
transPRED_SYMB idMap (Qual_pred_name p pt _) =
    maybe (error ("CASL2SPASS unknown pred: " ++ show p))
          id (lookupSPId p (CPred (CSign.toPredType pt)) idMap)
transPRED_SYMB _ (Pred_name _) = error "CASL2SPASS: unqualified predicate"

-- | 
-- Translate the quantifier
quantify :: QUANTIFIER -> SPQuantSym
quantify q = 
    case q of
    Universal -> SPForall
    Existential -> SPExists
    Unique_existential -> 
        error "CASL2SPASS: no translation for existential quantification."

transVarTup :: (Set.Set SPIdentifier,IdType_SPId_Map) -> 
               (VAR,SORT) -> 
               ((Set.Set SPIdentifier,IdType_SPId_Map),
                (SPIdentifier,SPIdentifier)) -- ^ ((new set of used Ids,new map of Ids to original Ids),(var as sp_Id,sort as sp_Id))
transVarTup (usedIds,idMap) (v,s) = 
    ((Set.insert sid usedIds,insertSPId vi (CVar s) sid idMap)
    , (sid,spSort)) 
    where spSort = maybe (error ("CASL2SPASS: translation of sort \""++
                                showPretty s "\" not found"))
                         id (lookupSPId s CSort idMap) 
          vi = simpleIdToId v
          sid = disSPOId (CVar s) (transId vi) 
                    ["_Va_"++ showPretty s "_Va"]
                    usedIds

typedVarTerm :: SPIdentifier -> SPIdentifier -> SPTerm
typedVarTerm spVar spSort = compTerm (spSym spSort) [simpTerm (spSym spVar)]

spSym :: SPIdentifier -> SPSymbol
spSym = SPCustomSymbol 

compTerm :: SPSymbol -> [SPTerm] -> SPTerm
compTerm = SPComplexTerm

simpTerm :: SPSymbol -> SPTerm
simpTerm = SPSimpleTerm

mkConj :: SPTerm -> SPTerm -> SPTerm
mkConj t1 t2 = compTerm SPAnd [t1,t2]

mkDisj :: SPTerm -> SPTerm -> SPTerm
mkDisj t1 t2 = compTerm SPOr [t1,t2]

mkEq :: SPTerm -> SPTerm -> SPTerm
mkEq t1 t2 = compTerm SPEqual [t1,t2]

mapSen :: (Eq f) => FormulaTranslator f e 
       -> CSign.Sign f e -> FORMULA f -> SPTerm
mapSen trForm sign phi = transFORM sign (snd (transSign sign)) trForm phi

transFORM :: (Eq f) => CSign.Sign f e 
          -> IdType_SPId_Map -> FormulaTranslator f e 
          -> FORMULA f -> SPTerm
transFORM sign i tr phi = transFORMULA sign i tr phi'
    where phi' = codeOutConditionalF id 
                        (codeOutUniqueExtF id (\ _  -> id) phi)

transFORMULA :: CSign.Sign f e -> 
                IdType_SPId_Map -> FormulaTranslator f e 
                -> FORMULA f -> SPTerm
transFORMULA sign idMap tr (Quantification qu vdecl phi _) =
    SPQuantTerm (quantify qu) 
                    vList
                    (transFORMULA sign idMap' tr phi)
    where ((_,idMap'),vList) = 
              mapAccumL (\ acc e -> let (acc',e') = transVarTup acc e
                                    in (acc', (uncurry typedVarTerm) e')) 
                        (sidSet,idMap) (flatVAR_DECLs vdecl)
          sidSet = elemsSPId_Set idMap
transFORMULA sign idMap tr (Conjunction phis _) =
  if null phis then SPSimpleTerm SPTrue
  else foldl1 mkConj (map (transFORMULA sign idMap tr) phis)
transFORMULA sign idMap tr (Disjunction phis _) =
  if null phis then SPSimpleTerm SPFalse
  else foldl1 mkDisj (map (transFORMULA sign idMap tr) phis)
transFORMULA sign idMap tr (Implication phi1 phi2 _ _) =
  compTerm SPImplies [transFORMULA sign idMap tr phi1,
                      transFORMULA sign idMap tr phi2]
transFORMULA sign idMap tr (Equivalence phi1 phi2 _) =
  compTerm SPEquiv [transFORMULA sign idMap tr phi1,
                    transFORMULA sign idMap tr phi2]
transFORMULA sign idMap tr (Negation phi _) =
  compTerm SPNot [transFORMULA sign idMap tr phi]
transFORMULA _sign _idMap _tr (True_atom _)  = SPSimpleTerm SPTrue
transFORMULA _sign _idMap _tr (False_atom _) = SPSimpleTerm SPFalse
transFORMULA sign idMap tr (Predication psymb args _) =
  compTerm (spSym (transPRED_SYMB idMap psymb))
           (map (transTERM sign idMap tr) args)
transFORMULA sign idMap tr (Existl_equation t1 t2 _) 
    | term_sort t1 == term_sort t2 =
        mkEq (transTERM sign idMap tr t1) (transTERM sign idMap tr t2)
transFORMULA sign idMap tr (Strong_equation t1 t2 _) 
    | term_sort t1 == term_sort t2 =
        mkEq (transTERM sign idMap tr t1) (transTERM sign idMap tr t2)
transFORMULA sign idMap tr (ExtFORMULA phi) = tr sign idMap phi
transFORMULA _ _ _ (Definedness _ _) = SPSimpleTerm SPTrue -- totality assumed
transFORMULA sign idMap tr (Membership t s _) = 
    maybe (error ("CASL2SPASS.tF: no SPASS Id found for \""++
                  showPretty s "\""))
          (\si -> compTerm (spSym si) [transTERM sign idMap tr t])
          (lookupSPId s CSort idMap)
transFORMULA _ _ _ _ = 
  error "CASL2SPASS.transFORMULA: unknown FORMULA"


transTERM :: CSign.Sign f e -> 
             IdType_SPId_Map -> FormulaTranslator f e
          -> TERM f -> SPTerm
transTERM _sign idMap _tr (Qual_var v s _) =
  maybe (error ("CASL2SPASS.tT: no SPASS Id found for \""++showPretty v "\""))
        (simpTerm . spSym) (lookupSPId (simpleIdToId v) (CVar s) idMap)
transTERM sign idMap tr (Application opsymb args _) =
    compTerm (spSym (transOP_SYMB idMap opsymb))
             (map (transTERM sign idMap tr) args)

transTERM _sign _idMap _tr (Conditional _t1 _phi _t2 _) =
    error "CASL2SPASS.transTERM: Conditional terms must be coded out."
transTERM sign idMap tr (Sorted_term t s _) 
    | term_sort t == s = transTERM sign idMap tr t
transTERM sign idMap tr (Cast t s _) 
    | term_sort t == s = transTERM sign idMap tr t
transTERM _sign _idMap _tr _ =
  error "CASL2SPASS.transTERM: unknown TERM" 


