
{- |
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, Christian Maeder and Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  non-portable (imports Morphsim)
    
The symbol map analysis for the HasCASL logic
(adapted from CASL version r1.8 of 24.1.2004)

-}
module HasCASL.SymbolMapAnalysis
    ( inducedFromMorphism
    , inducedFromToMorphism
    , cogeneratedSign
    , generatedSign
    )  where

import HasCASL.As
import HasCASL.Le
import HasCASL.AsToLe
import HasCASL.Symbol
import HasCASL.Morphism
import HasCASL.ClassAna
import HasCASL.VarDecl
import Common.Id
import Common.Result
import Common.Lib.State
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import Common.PrettyPrint
import Common.Lib.Pretty
import Control.Monad
import Data.Maybe

type RawSymbolMap = Map.Map RawSymbol RawSymbol
type SymbolSet = Set.Set Symbol 

inducedFromMorphism :: RawSymbolMap -> Env -> Result Morphism
inducedFromMorphism rmap sigma = do
  -- first check: do all source raw symbols match with source signature?
  let syms = symOf sigma
      srcTypeMap = typeMap sigma
      incorrectRsyms = Map.foldWithKey
        (\rsy _ -> if Set.any (matchesND rsy) syms
                    then id
                    else Set.insert rsy)
        Set.empty
        rmap
      matchesND rsy sy = 
        sy `matchSymb` rsy && 
        case rsy of
          ASymbol _ -> True
          -- unqualified raw symbols need some matching symbol
          -- that is not directly mapped
          _ -> Map.lookup (ASymbol sy) rmap == Nothing
  -- ... if not, generate an error
  when (not (Set.isEmpty incorrectRsyms))
    (pplain_error ()
       (ptext "the following symbols:"
        <+> printText incorrectRsyms 
        $$ ptext "are already mapped directly or do not match with signature"
        $$ printText sigma) 
       nullPos)
  -- compute the sort map (as a Map)
  myTypeIdMap <- foldr
              (\ (s, ti) m -> 
	       do s' <- typeFun s (typeKind ti)
                  m1 <- m
                  return $ Map.insert s s' m1) 
              (return Map.empty) $ Map.toList srcTypeMap
  -- compute the op map (as a Map)
  op_Map <- Map.foldWithKey (opFun myTypeIdMap)
              (return Map.empty) (assumps sigma)
  -- compute target signature
  let tarTypeMap = Map.foldWithKey ( \ i k m -> 
			       Map.insert (Map.findWithDefault i i myTypeIdMap)
					  k m)
	                    Map.empty srcTypeMap
      sigma' = sigma 
            { typeMap = tarTypeMap
            , assumps =  Map.foldWithKey (mapOps myTypeIdMap op_Map)
                              Map.empty (assumps sigma) }
  -- return assembled morphism
  return $ (mkMorphism sigma sigma') 
	     { typeIdMap = myTypeIdMap
	     , funMap = op_Map }
  where
  typeFun :: Id -> Kind -> Result Id
  typeFun s k = 
    -- rsys contains the raw symbols to which s is mapped to
    case Set.size rsys of
          0 -> return s  -- use default = identity mapping
          1 -> return $ rawSymName $ Set.findMin rsys -- take the unique rsy
          _ -> pplain_error s  -- ambiguity! generate an error 
                 (ptext "Sort" <+> printText s 
                  <+> ptext "mapped ambiguously:" <+> printText rsys)
                 nullPos
    where
    -- get all raw symbols to which s is mapped to
    rsys = Set.unions $ map (Set.maybeToSet . (\x -> Map.lookup x rmap))
               [ASymbol $ idToTypeSymbol s k, AnID s, AKindedId SK_type s]

 -- to a Fun_map, add evering resulting from mapping (id,ots) according to rmap
  opFun :: IdMap -> Id -> OpInfos -> Result FunMap -> Result FunMap
  opFun type_Map i ots m = 
    -- first consider all directly mapped profiles
    let (ots1,m1) = foldr (directOpMap type_Map i) (Set.empty,m) $ opInfos ots
    -- now try the remaining ones with (un)kinded raw symbol
    in case (Map.lookup (AKindedId SK_op i) rmap,Map.lookup (AnID i) rmap) of
       (Just rsy1, Just rsy2) -> 
          do m' <- m
             pplain_error m'
               (ptext "Operation" <+> printText i
                <+> ptext "is mapped twice:"
                <+> printText rsy1 <+> ptext "," <+> printText rsy2
               )
               nullPos
       (Just rsy, Nothing) -> 
          Set.fold (insertmapOpSym type_Map i rsy) m1 ots1
       (Nothing, Just rsy) -> 
          Set.fold (insertmapOpSym type_Map i rsy) m1 ots1
       -- Anything not mapped explicitly is left unchanged
       (Nothing,Nothing) -> Set.fold (unchangedOpSym type_Map i) m1 ots1
    -- try to map an operation symbol directly
    -- collect all opTypes that cannot be mapped directly
  directOpMap :: IdMap -> Id -> OpInfo -> (Set.Set TySc, Result FunMap)
                     -> (Set.Set TySc, Result FunMap)
  directOpMap type_Map i oi (ots,m) = let ot = TySc $ opType oi in
      case Map.lookup (ASymbol (idToOpSymbol i ot)) rmap of
        Just rsy -> 
          (ots,insertmapOpSym type_Map i rsy ot m)
        Nothing -> (Set.insert ot ots,m)
    -- map op symbol (id,ot) to raw symbol rsy
  mapOpSym :: IdMap -> Id -> TySc -> RawSymbol 
	     -> Result (Id, TySc)
  mapOpSym type_Map i ot rsy = let sc1@(TySc sc) = mapTySc type_Map ot in 
      case rsy of
      ASymbol (Symbol id' (OpAsItemType sc2@(TySc ot'))) ->
        if compatibleOpTypes sc ot'
           then return (id', sc2)
           else pplain_error (i, sc1)
             (ptext "Operation symbol " <+> printText (idToOpSymbol i sc1) 
              <+> ptext "is mapped to type" <+>  printText ot'
              <+> ptext "but should be mapped to type" <+>  
              printText sc 
             )
             nullPos
      AnID id' -> return (id', sc1)
      AKindedId SK_op id' -> return (id', sc1)
      _ -> pplain_error (i, sc1)
               (ptext "Operation symbol " <+> printText (idToOpSymbol i sc1)
                <+> ptext" is mapped to symbol of wrong kind:" 
                <+> printText rsy) 
               nullPos
    -- insert mapping of op symbol (id,ot) to raw symbol rsy into m
  insertmapOpSym type_Map i rsy ot m = do  
      m1 <- m        
      (id',kind') <- mapOpSym type_Map i ot rsy
      return (Map.insert (i, ot) (id',kind') m1)
    -- insert mapping of op symbol (id,ot) to itself into m
  unchangedOpSym type_Map i ot m = do
      m1 <- m
      return (Map.insert (i, ot) (i, mapTySc type_Map ot) m1)
  -- map the ops in the source signature
  mapOps type_Map op_Map i ots m = 
    foldr mapOp m (opInfos ots) 
    where
    mapOp ot m1 = 
	let sc = TySc $ opType ot
	    (id', TySc sc') = Map.findWithDefault (i, mapTySc type_Map sc)
			 (i, sc) op_Map
	    e = initialEnv {assumps = m1}
	    in assumps (execState (addOpId id' sc' [] (NoOpDefn Op)) e)

-- Some auxiliary functions for inducedFromToMorphism
testMatch :: RawSymbolMap -> Symbol -> Symbol -> Bool
testMatch rmap sym1 sym2 =
  Map.foldWithKey match1 True rmap
  where
  match1 rsy1 rsy2 b = b && ((sym1 `matchSymb` rsy1) <= (sym2 `matchSymb`rsy2))

canBeMapped :: RawSymbolMap -> Symbol -> Symbol -> Bool
canBeMapped rmap sym1@(Symbol {symbType = TypeAsItemType _k1}) 
                 sym2@(Symbol {symbType = TypeAsItemType _k2}) = 
   testMatch rmap sym1 sym2
canBeMapped rmap sym1@(Symbol {symbType = OpAsItemType _ot1}) 
                 sym2@(Symbol {symbType = OpAsItemType _ot2}) = 
   testMatch rmap sym1 sym2
canBeMapped _ _ _ = False

preservesName :: Symbol -> Symbol -> Bool
preservesName sym1 sym2 = symName sym1 == symName sym2


-- try to extend a symbol map with a yet unmapped symbol
extendSymbMap :: SymbolMap -> Symbol -> Symbol -> Maybe SymbolMap
extendSymbMap akmap sym1 sym2 =
  if case symbType sym1 of 
    TypeAsItemType k1 -> case symbType sym2 of 
       TypeAsItemType k2 -> rawKind k1 == rawKind k2
       _ -> False 
    OpAsItemType sc1@(TySc _) -> case symbType sym2 of
      OpAsItemType (TySc ot2) -> 
	  let TySc sc2 = 
		  mapTySc (Map.foldWithKey ( \ s1 s2 m ->
				Map.insert (symName s1) (symName s2) m)
			        Map.empty akmap) sc1 
	      in compatibleOpTypes ot2 sc2
      _ -> False
    _ -> False
  then Just $ Map.insert sym1 sym2 akmap
  else Nothing

-- Type for posmap
-- Each symbol is mapped to the set symbols it possibly can be mapped to
-- Additionally, we store a flag meaning "no default map" and the 
-- cardinality of the symobl set
-- For efficiency reasons, we also carry around an indexing of posmap
-- according to the pairs (flag,cardinality). Since several symbols
-- may lead to the same pair, we have to associate a list of symbols
-- (and corresponding symbol sets) with each pair.
-- Hence, PosMap really is a pair to two maps. 
type PosMap = (Map.Map Symbol (SymbolSet,(Bool,Int)), 
               Map.Map (Bool,Int) [(Symbol,SymbolSet)])

-- Some basic operations on PosMap

-- postpone entries with no default mapping and size > 1
postponeEntry :: Symbol -> SymbolSet -> Bool
postponeEntry sym symset = 
  not $ Set.any (preservesName sym) symset && Set.size symset > 1

removeFromPosmap :: Symbol -> (Bool,Int) -> PosMap -> PosMap
removeFromPosmap sym card (posmap1,posmap2) =
  (Map.delete sym posmap1,
   Map.update removeSym1 card posmap2)
  where
  removeSym [] = []
  removeSym ((x,y):l) = if x==sym then l else (x,y):removeSym l
  removeSym1 l = case removeSym l of
    [] -> Nothing
    l1 -> Just l1

addToPosmap :: Symbol -> SymbolSet -> PosMap -> PosMap
addToPosmap sym symset (posmap1,posmap2) =
  (Map.insert sym (symset,card) posmap1,
   Map.listInsert card (sym,symset) posmap2)
  where card = (postponeEntry sym symset,Set.size symset)

-- restrict posmap such that each symbol from symset1 is only mapped
-- to symbols from symset2
restrictPosMap :: SymbolSet -> SymbolSet -> PosMap -> PosMap
restrictPosMap symset1 symset2 posmap =
  Set.fold restrictPosMap1 posmap symset1
  where
  restrictPosMap1 sym1 pm@(posmap1,_)  =
    case Map.lookup sym1 posmap1 of
      Nothing -> pm
      Just (symset,card) ->
         addToPosmap sym1 (symset `Set.intersection` symset2)
          $ removeFromPosmap sym1 card posmap

-- the main function
inducedFromToMorphism :: RawSymbolMap -> Env -> Env -> Result Morphism
inducedFromToMorphism rmap sigma1 sigma2 = do
  --debug 3 ("rmap",rmap)
  -- 1. use rmap to get a renaming...
  mor1 <- inducedFromMorphism rmap sigma1
  -- 1.1 ... is the renamed source signature contained in the target signature?
  --debug 3 ("mtarget mor1",mtarget mor1)
  --debug 3 ("sigma2",sigma2)
  if isSubEnv (mtarget mor1) sigma2 
   -- yes => we are done
   then return (mor1 {mtarget = sigma2})
   -- no => OK, we've to take the hard way
   else do  -- 2. Compute initial posmap, using all possible mappings of symbols
     let symset1 = symOf sigma1
         symset2 = symOf sigma2
         addCard sym s = (s,(postponeEntry sym s,Set.size s))
         ins1 sym = Map.insert sym
                       (addCard sym $ Set.filter (canBeMapped rmap sym) symset2)
         posmap1 = Set.fold ins1 Map.empty symset1
         ins2 sym1 (symset,card) = Map.listInsert card (sym1,symset)
         posmap2 = Map.foldWithKey ins2 Map.empty posmap1
         posmap = (posmap1,posmap2)
     case Map.lookup (True,0) posmap2 of
       Nothing -> return ()
       Just syms -> pfatal_error
         (ptext "No symbol mapping for "
           <+> printText (Set.fromList $ map fst syms)) nullPos
     -- 3. call recursive function with empty akmap and initial posmap
     smap <- tryToInduce sigma1 sigma2 Map.empty posmap
     smap1 <- case smap of
                 Nothing -> fail "No signature morphism for symbol map"
                 Just x -> return x
     -- 9./10. compute and return the resulting morphism
     symbMapToMorphism sigma1 sigma2 smap1

     -- 4. recursive depth first function
     -- ambiguous map leads to fatal error (similar to exception)
tryToInduce sigma1 sigma2 akmap (posmap1, posmap2) = do
       --debug 5 ("akmap",akmap)
       --debug 6 ("posmap",(posmap1,posmap2))
       if Map.isEmpty posmap2 then return $ Just akmap -- 4a.
        else do
          --debug 7 ("posmap'",posmap')
          --debug 8 ("sym1",sym1)
          akmap1 <- tryToInduce1 sigma1 sigma2 akmap posmap' sym1 symset1
          if isNothing akmap1 
            -- 6. no map for symset1, hence try symset2
            then tryToInduce1 sigma1 sigma2 akmap posmap' sym1 symset2
            else return akmap1 -- otherwise, use symset1 only
       where
       -- 4b. take symbol with minimal remaining values (MRV)
       (card,(sym1,symset):symsets) = Map.findMin posmap2
       (symset1,symset2) = Set.partition (preservesName sym1) symset
       posmap' = removeFromPosmap sym1 card (posmap1,posmap2)
     -- 5. to 7.
tryToInduce1 sigma1 sigma2 akmap posmap sym1 symset =
       Set.fold (tryToInduce2 sigma1 sigma2 akmap posmap sym1) 
                (return Nothing) symset
tryToInduce2 sigma1 sigma2 akmap posmap sym1 sym2 akmapSoFar = do
       -- 5.1. to 5.3. consistency check
       akmapSoFar1 <- akmapSoFar
       akmap' <- case extendSymbMap akmap sym1 sym2 of
         Nothing -> return Nothing
         -- constraint propagation
         Just akmap1 -> tryToInduce sigma1 sigma2 akmap1 posmap
       -- 6./7. uniqueness check
       case (akmap',akmapSoFar1) of
         (Nothing,Nothing) -> return Nothing
         (Just smap,Nothing) -> return (Just smap)
         (Nothing,Just smap) -> return (Just smap)
         (Just smap1,Just smap2) -> 
            fail $ shows 
             (ptext "Ambiguous symbol map" $$ 
              ptext "Map1" <+> printText smap1 $$
              ptext "Map2" <+> printText smap2) 
            ""

generatedSign :: SymbolSet -> Env -> Result Morphism
generatedSign sys sigma = do
  if not (sys `Set.subset` symset)   -- 2.
   then pfatal_error 
         (ptext "Revealing: The following symbols" 
          <+> printText(sys Set.\\ symset)
          <+> ptext "are not in the signature") nullPos
   else return $ embedMorphism sigma2 sigma    -- 7.
  where
  symset = symOf sigma   -- 1. 
  sigma2 = Set.fold revealSym initialEnv sys  -- 4. 
  revealSym sy sigma1 = case symbType sy of  -- 4.1.
    TypeAsItemType k ->      -- 4.1.1.
      sigma1 {typeMap = Map.insert (symName sy) (TypeInfo k [] [] 
						NoTypeDefn) $ typeMap sigma1}
    OpAsItemType (TySc ot) ->     -- 4.1.2./4.1.3.
      execState (addOpId (symName sy) ot [] (NoOpDefn Op)) sigma1
    _ -> sigma1 

cogeneratedSign :: SymbolSet -> Env -> Result Morphism
cogeneratedSign symset sigma = do
  if not (symset `Set.subset` symset0)   -- 2.
   then pfatal_error 
         (ptext "Hiding: The following symbols" 
          <+> printText(symset Set.\\ symset0)
          <+> ptext "are not in the signature") nullPos
   else generatedSign symset1 sigma -- 4./5.
  where
  symset0 = symOf sigma   -- 1. 
  symset1 = Set.fold revealSym symset0 symset  -- 3. 
  revealSym sy symset2 = Set.delete sy symset2
