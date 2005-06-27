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

   - are all free type definitions a source of partial functions /
     partiallity

-}

module Comorphisms.CASL2SPASS where

-- Debuging and Warning
import Debug.Trace
import Control.Exception

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
import Data.Char
-- CASL
import CASL.Logic_CASL 
import CASL.AS_Basic_CASL
import CASL.Sublogic
import qualified CASL.Sign as CSign
import CASL.Morphism
import CASL.Quantification 
import CASL.Overload

-- SPASS
import SPASS.Sign as SPSign
import SPASS.Logic_SPASS

-- Isabelle
import Isabelle.Translate

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

------------------------------ Ids ---------------------------------

-- | collect all keywords of SPASS
reservedWords :: Set.Set SPIdentifier 
reservedWords = Set.fromList (map ((flip showPretty) "") [SPEqual
                                          , SPTrue 
                                          , SPFalse 
                                          , SPOr 
                                          , SPAnd
                                          , SPNot
                                          , SPImplies
                                          , SPImplied
                                          ,SPEquiv])


transId :: Id -> SPIdentifier
transId iden 
    | checkIdentifier str = if Set.member str reservedWords 
                            then "X_"++str
                            else str
    | otherwise = concatMap transToSPChar str
    where str = show iden

transToSPChar :: Char -> SPIdentifier
transToSPChar c
    | checkSPChar c = [c]
    | otherwise = Map.findWithDefault def c charMap
    where def = "Slash_"++ show (ord c)

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

transTheory :: SignTranslator f e ->
               FormulaTranslator f e ->
               (CSign.Sign f e, [Named (FORMULA f)])
                   -> Result SPASSTheory 
transTheory trSig trForm (sign,sens) = 
  fmap (trSig sign (CSign.extendedInfo sign)) $
  return  (tSign {sortMap = integrateGenerated idMap 
                            genSens (sortMap tSign)},
          map (mapNamed (transFORMULA sign idMap trForm)) realSens)
  where (tSign,idMap) = transSign sign
        (genSens,realSens) = 
            partition (\ s -> case (sentence s) of
                              Sort_gen_ax _ _ -> True
                              _               -> False) sens


--     baseSig = baseSign,
--     tsig = emptyTypeSig {arities = 
--                Set.fold (\s -> let s1 = (showIsaT s baseSign) in
--                                 if s1 `elem` dtTypes then id
--                                  else Map.insert s1 [(isaTerm, [])]) 
--                                Map.empty (sortSet sign)},
--     constTab = Map.foldWithKey insertPreds
--                 (Map.filterWithKey (isNotIn dtDefs) 
--                 $ Map.foldWithKey insertOps Map.empty 
--                 $ opMap sign) $ predMap sign,
--     dataTypeTab = dtDefs},      
--      map (mapNamed (mapSen trForm sign)) real_sens)  
--      -- for now, no new sentences
--   where 
--     (real_sens, sort_gen_axs) = List.partition 
--         (\ s -> case sentence s of
--                 Sort_gen_ax _ _ -> False
--                 _ -> True) sens
--     dtDefs = topoSort (makeDtDefs sign sort_gen_axs)
--     dtTypes = map ((\(Type s _ _) -> s).fst) $ concat dtDefs
--     insertOps op ts m = 
--      if Set.size ts == 1 
--       then Map.insert (showIsaT op baseSign) (transOpType (Set.findMin ts)) m
--       else 
--       foldl (\m1 (t,i) -> Map.insert (showIsaIT op i baseSign) 
--                           (transOpType t) m1) m 
--             (zip (Set.toList ts) [1..(Set.size ts)])
--     insertPreds pre ts m =
--      if Set.size ts == 1 
--       then Map.insert (showIsaT pre baseSign) 
--                (transPredType (Set.findMin ts)) m
--       else
--       foldl (\m1 (t,i) -> Map.insert (showIsaIT pre i baseSign) 
--                           (transPredType t) m1) m 
--             (zip (Set.toList ts) [1..Set.size ts])


-- topoSort 
-- A(i) = [[j]] with definition of datatype i needs j
-- inI(i) = [n] i is needed by n other definions
-- (1) L<-[]
-- (2) for i=1 to n do inI(i)<-0 od;
-- (3) for i=1 to n do 
-- (4)   for (j elem A(i)) do inI(j)<-inI(j) + 1 od
-- (5) od;
-- (6) for i=1 to n do 
-- (7)   if inI(i) = 0  then i:L fi 
-- (8) od; 
-- (9) while L != [] do
--(10)   v <- head(L)
--(11)   L <- tail(L)
--(12)   sortedList <- sortedList ++ v
--(13)   for (w elem A(v)) do
--(14)       inI(w) <- inI(w) - 1
--(15)       if inI(w)=0 then L<- L++w fi
--(16)   od;
--(17) od;
{-

topoSort :: [[(Typ, [(a, [Typ])])]] -> [[(Typ, [(a, [Typ])])]]
topoSort [] = []
topoSort dts = whileL (collectL inI_ 1) inI_ adI_ dts
    where 
    (inI_, adI_) =  makeLists [] dts 1 (map (const 0) dts) 
                    $ map (const [0]) dts
    -- generate both A- and inI-list
    makeLists :: [[(Typ, [(a, [Typ])])]] -> [[(Typ, [(a, [Typ])])]] -> 
                 Int -> [Int] -> [[Int]] -> ([Int], [[Int]])
    makeLists _ [] _ inI ad = (inI, ad)
    makeLists as1 (a:as2) n inI ad = 
        if (snd (findIn as1 a n [])) == True then
           makeLists (concat [as1, [a]]) as2 (n+1)  updateIn1 updateAdj1
        else 
           if (snd (findIn as2 a n [])) == True then
              makeLists (concat [as1,[a]]) as2 (n+1) updateIn2 updateAdj2
           else makeLists (concat [as1, [a]]) as2 (n+1) inI ad
        where 
        updateAdj1 = updateAdj ad (fst (findIn as1 a n [])) 0
        updateAdj2 = updateAdj ad (fst (findIn as2 a n [])) n
        updateIn1  = updateIn inI (count (fst (findIn as1 a n []))) n 
        updateIn2  = updateIn inI (count (fst (findIn as1 a n [])) + 
                                   count (fst (findIn as2 a n []))) n
    -- is Type a in the list (b:bs)
    findIn :: [[(Typ, [(a, [Typ])])]] -> [(Typ, [(a, [Typ])])] 
           -> Int -> [Int]-> ([Int], Bool) 
    findIn [] _ _ l = (if (sum l) > 0 then (l, True) else ([], False))
    findIn (b:bs) a n l = findIn bs a n (concat [l, list])
        where
        list = map (compareTypes n (getType (head b))) 
               $ concat (getUsedTypes (snd (head a)))
    compareTypes n t1 t2 = if t1 == t2 then n else 0
    -- returns the typename of a
    getType a = let (Type d _ _) = fst a in d
    -- returns all used types
    getUsedTypes [] = []
    getUsedTypes (b:bs) = (getUsedType (snd b)) :(getUsedTypes bs)
    getUsedType  [] = []
    getUsedType  (c:cs) = let (Type d _ _) = c in d :(getUsedType cs) 
    updateAdj :: [[a]] -> [a] -> Int -> [[a]]
    updateAdj (ad:ads) (c:cs) 0 = (c:ad):(updateAdj ads cs 0)   
    updateAdj (ad:ads) cs n = ad:(updateAdj ads cs (n-1))
    updateAdj ad _ _ = ad
    count as = length (List.filter (> 0) as)
    updateIn [] _ _ = error "topoSort.updateIn"
    updateIn (_ : inIs) c 1 = c:inIs           
    updateIn (inI:inIs) c n = inI:(updateIn inIs c (n-1)) 
    -- Lines 6-8                      
    collectL [] _ = []
    collectL (inI:inIs) i = if inI == 0 then i:(collectL inIs (i+1)) 
                            else (collectL inIs (i+1))

    -- Lines 9-16
    whileL [] _ _ _ = []
    whileL (l:ls) inI adI dtDefs = selElemAt l dtDefs 
                                   : whileL newLs newInIs adI dtDefs
        where 
        newLs = concat [ls, snd(updateInI2 (selElemAt l adI) inI 1 [] [])]
        newInIs = fst(updateInI2 (selElemAt l adI) inI 1 [] [])
        updateInI2 _  []  _ newL ins = (reverse ins, reverse newL)
        updateInI2 [] inI' _ _ _   = (inI', [])
        updateInI2 listOfInd (inI':inIs) n newL ins =
                 let dInI = inI' - 1 in 
                 if n `elem` listOfInd then 
                    if dInI == 0 then
                       updateInI2 listOfInd inIs (n+1) (n:newL) (dInI:ins)
                    else 
                       updateInI2 listOfInd inIs (n+1) newL (dInI:ins)
                 else updateInI2 listOfInd inIs (n+1) newL (inI':ins)
    -- get the l-th value from the list 
    selElemAt :: Int -> [a] -> a
    selElemAt l xs = xs !! (l - 1)                                  

transSort :: SORT -> Typ
transSort s = Type (showIsaT s baseSign) [] []

transOpType :: OpType -> Typ
transOpType ot = mkCurryFunType (map transSort $ opArgs ot) 
                 $ transSort (opRes ot)

transPredType :: PredType -> Typ
transPredType pt = mkCurryFunType (map transSort $ predArgs pt) boolType

-}
------------------------------ Formulas ------------------------------
{-
var :: String -> Term
--(c) var v = IsaSign.Free v noType isaTerm
var v = IsaSign.Free v noType

transVar :: VAR -> String
transVar v = showIsaT (simpleIdToId v) baseSign

xvar :: Int -> String
xvar i = if i<=26 then [chr (i+ord('a'))] else "x"++show i

rvar :: Int -> String
rvar i = if i<=9 then [chr (i+ord('R'))] else "R"++show i

quantifyIsa :: String -> (String, Typ) -> Term -> Term
quantifyIsa q (v,t) phi =
  App (Const q noType) (Abs (Free v noType) t phi NotCont) NotCont
--(c) App (Const q noType isaTerm) (Abs (Cont v noType isaTerm) t phi NotCont) 
--(c) NotCont
--quantifyIsa :: String -> (String, Typ) -> Term -> Term
--quantifyIsa q (v,t) phi =
-- App (Const q) (Abs [(Free v, t)] phi NotCont) NotCont

quantify :: QUANTIFIER -> (VAR, SORT) -> Term -> Term
quantify q (v,t) phi  = 
  quantifyIsa (qname q) (transVar v, transSort t) phi
  where
  qname Universal = allS
  qname Existential = exS
  qname Unique_existential = ex1S

-}


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

quantify :: QUANTIFIER -> SPQuantSym
quantify q = 
    case q of
    Universal -> SPForall
    Existential -> SPExists
    Unique_existential -> 
        error "CASL2SPASS: no translation for existential quantification yet."

transVarTup :: (Set.Set SPIdentifier,IdType_SPId_Map) -> 
               (VAR,SORT) -> 
               ((Set.Set SPIdentifier,IdType_SPId_Map),SPTerm)
transVarTup (usedIds,idMap) (v,s) = 
    ((Set.insert sid usedIds,insertSPId vi (CVar s) sid idMap)
    , spTerm) 
    where spSort = maybe (error ("CASL2SPASS: translation of sort \""++
                                showPretty s "\" not found"))
                         id (lookupSPId s CSort idMap) 
          vi = simpleIdToId v
          sid = disSPOId (CVar s) (transId vi) 
                    ["_Va_"++ showPretty s "_Va"]
                    usedIds
          spTerm = compTerm (spSym spSort) [simpTerm (spSym sid)]

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

mapSen :: FormulaTranslator f e -> CSign.Sign f e -> FORMULA f -> SPTerm
mapSen trForm sign phi = 
    transFORMULA sign (snd (transSign sign)) trForm phi

transFORMULA :: CSign.Sign f e -> 
                IdType_SPId_Map -> FormulaTranslator f e 
                -> FORMULA f -> SPTerm
transFORMULA sign idMap tr (Quantification qu vdecl phi _) =
    SPQuantTerm (quantify qu) 
                    vList
                    (transFORMULA sign idMap' tr phi) 
    where ((_,idMap'),vList) = 
              mapAccumL transVarTup (sidSet,idMap) (flatVAR_DECLs vdecl)
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
{-
transFORMULA _ _ (Definedness _ _) = true -- totality assumed
transFORMULA _ _ (Membership t s _) | term_sort t == s = true
-}
transFORMULA _ _ _ _ = 
  error "CASL2SPASS.transFORMULA: unknown FORMULA"


transTERM :: CSign.Sign f e -> 
             IdType_SPId_Map -> FormulaTranslator f e
          -> TERM f -> SPTerm
transTERM _sign idMap _tr (Qual_var v s _) =
  maybe (error ("CASL2SPASS: no SPASS Id found for \""++showPretty v "\""))
        (simpTerm . spSym) (lookupSPId (simpleIdToId v) (CVar s) idMap)
transTERM sign idMap tr (Application opsymb args _) =
    compTerm (spSym (transOP_SYMB idMap opsymb))
             (map (transTERM sign idMap tr) args)
{-
transTERM sign idMap tr (Conditional t1 phi t2 _) 
    | term_sort t1 == term_sort t2 =
  foldl termAppl (con "If") [transFORMULA sign idMap tr phi,
       transTERM sign idMap tr t1, transTERM sign idMap tr t2]
-}
transTERM sign idMap tr (Sorted_term t s _) 
    | term_sort t == s = transTERM sign idMap tr t
transTERM sign idMap tr (Cast t s _) 
    | term_sort t == s = transTERM sign idMap tr t
transTERM _sign _idMap _tr _ =
  error "CASL2SPASS.transTERM: unknown TERM" 


