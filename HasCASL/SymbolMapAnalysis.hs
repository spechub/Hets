
{- |
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, Christian Maeder and Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable
    
The symbol map analysis for the HasCASL logic
(adapted from CASL version r1.8 of 24.1.2004)

-}
module HasCASL.SymbolMapAnalysis where

import HasCASL.AsToLe
import HasCASL.As
import HasCASL.Le
import HasCASL.Symbol
import HasCASL.Morphism
import HasCASL.ClassAna
import HasCASL.VarDecl
import Common.Id
import Common.Result
import Common.Lib.State
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Rel as Rel
import Common.PrettyPrint
import Common.Lib.Pretty
import Control.Monad
import Data.Maybe

type RawSymbolMap = Map.Map RawSymbol RawSymbol
type SymbolSet = Set.Set Symbol 

inducedFromMorphism :: RawSymbolMap -> Env -> Result Morphism
inducedFromMorphism rmap sigma = do
  -- ??? Missing: check preservation of overloading relation
  -- first check: do all source raw symbols match with source signature?
  let syms = symOf sigma
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
  type_Map <- Set.fold
              (\s v m -> do s' <- typeFun s
                            m1 <- m
                            return $ Map.insert s s' m1) 
              (return Map.empty) $ Map.keys $ typeMap sigma
  -- compute the op map (as a Map)
  op_Map <- Map.foldWithKey (opFun type_Map)
              (return Map.empty) (assumps sigma)
  -- compute target signature
  let sigma' = sigma 
            { typeMap = Map.foldWithKey (mapType type_Map) 
	                    Map.empty $ typeMap sigma
            , assumps =  Map.foldWithKey (mapOps type_Map op_Map) 
                              Map.empty (funMap sigma) }
  -- return assembled morphism
  return $ (mkMorphism sigma sigma') 
	     { typeIdMap = type_Map
	     , funMap = op_Map }
  where
  typeFun s = 
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
               [AnID s, AKindedId SK_type s]

  -- to a Fun_map, add evering resulting from mapping (id,ots) according to rmap
  opFun :: IdMap -> Id -> Set.Set TypeScheme -> Result FunMap -> Result FunMap
  opFun type_Map id ots m = 
    -- first consider all directly mapped profiles
    let (ots1,m1) = Set.fold (directOpMap id) (Set.empty,m) ots
    -- now try the remaining ones with (un)kinded raw symbol
    in case (Map.lookup (AKindedId SK_op id) rmap,Map.lookup (AnID id) rmap) of
       (Just rsy1, Just rsy2) -> 
          do m' <- m
             pplain_error m'
               (ptext "Operation" <+> printText id
                <+> ptext "is mapped twice:"
                <+> printText rsy1 <+> ptext "," <+> printText rsy2
               )
               nullPos
       (Just rsy, Nothing) -> 
          Set.fold (insertmapOpSym id rsy) m1 ots1
       (Nothing, Just rsy) -> 
          Set.fold (insertmapOpSym id rsy) m1 ots1
       -- Anything not mapped explicitly is left unchanged
       (Nothing,Nothing) -> Set.fold (unchangedOpSym id) m1 ots1
    where
    -- try to map an operation symbol directly
    -- collect all opTypes that cannot be mapped directly
    directOpMap :: Id -> TypeScheme -> (Set.Set TypeScheme, Result FunMap)
                     -> (Set.Set TypeScheme, Result FunMap)
    directOpMap id ot (ots,m) =
      case Map.lookup (ASymbol (idToOpSymbol id ot)) rmap of
        Just rsy -> 
          (ots,insertmapOpSym id rsy ot m)
        Nothing -> (Set.insert ot ots,m)
    -- map op symbol (id,ot) to raw symbol rsy
    mapOpSym :: Id -> TypeScheme -> RawSymbol -> Result (Id, TypeScheme)
    mapOpSym id ot rsy = case rsy of
      ASymbol (Symbol id' (OpAsItemType ot')) ->
        if compatibleOpTypes (mapTypeScheme type_Map ot) ot'
           then return (id', ot')
           else pplain_error (id, ot)
             (ptext "Operation symbol " <+> printText (idToOpSymbol id ot) 
              <+> ptext "is mapped to type" <+>  printText ot'
              <+> ptext "but should be mapped to type" <+>  
              printText (mapTypeScheme type_Map ot) 
             )
             nullPos
      AnID id' -> return (id', ot)
      AKindedId FunKind id' -> return (id', ot)
      rsy -> pplain_error (id, ot)
               (ptext "Operation symbol " <+> printText (idToOpSymbol id ot)
                <+> ptext" is mapped to symbol of wrong kind:" 
                <+> printText rsy) 
               nullPos
    -- insert mapping of op symbol (id,ot) to raw symbol rsy into m
    insertmapOpSym id rsy ot m = do  
      m1 <- m        
      (id',kind') <- mapOpSym id ot rsy
      return (Map.insert (id,ot) (id',kind') m1)
    -- insert mapping of op symbol (id,ot) to itself into m
    unchangedOpSym id ot m = do
      m1 <- m
      return (Map.insert (id, ot) (id, ot) m1)
  -- map the ops in the source signature
  mapOps type_Map op_Map id ots m = 
    Set.fold mapOp m ots 
    where
    mapOp ot m1 = 
      let (id',ot') = fromMaybe (id,ot) $ mapFunSym type_Map op_Map (id,ot)
      in Map.setInsert id' ot' m1

-- Some auxiliary functions for inducedFromToMorphism
testMatch :: RawSymbolMap -> Symbol -> Symbol -> Bool
testMatch rmap sym1 sym2 =
  Map.foldWithKey match1 True rmap
  where
  match1 rsy1 rsy2 b = b && ((sym1 `matchSymb` rsy1) <= (sym2 `matchSymb`rsy2))

canBeMapped :: RawSymbolMap -> Symbol -> Symbol -> Bool
canBeMapped rmap sym1@(Symbol {symbType = TypeAsItemType k1}) 
                 sym2@(Symbol {symbType = TypeAsItemType k2}) = 
   testMatch rmap sym1 sym2
canBeMapped rmap sym1@(Symbol {symbType = OpAsItemType ot1}) 
                 sym2@(Symbol {symbType = OpAsItemType ot2}) = 
   testMatch rmap sym1 sym2
canBeMapped _ _ _ = False

preservesName :: Symbol -> Symbol -> Bool
preservesName sym1 sym2 = symName sym1 == symName sym2


-- try to extend a symbol map with a yet unmapped symbol
-- (this can fail if sym1 and sym2 are operations/predicates,
--  and mapping on their profiles clashes with what is already
--  known in akmap)
extendSymbMap :: SymbolMap -> Symbol -> Symbol -> Maybe SymbolMap
extendSymbMap akmap sym1 sym2 =
  if case symbType sym1 of 
    TypeAsItemType k1 -> case symbType of 
       TypeAsItemType k2 -> rawKind k1 == rawKind k2
       _ -> False 
    OpAsItemType ot1 -> case symbType sym2 of
      OpAsItemType ot2 -> compatibleOpTypes ot2
			  $ mapTypeScheme (Map.foldWithKey ( \ s1 s2 m ->
				Map.insert (symName s1) (symName s2) m)
			        Map.empty akmap) ot1
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
  restrictPosMap1 sym1 posmap@(posmap1,posmap2)  =
    case Map.lookup sym1 posmap1 of
      Nothing -> posmap
      Just (symset1,card) ->
         addToPosmap sym1 (symset1 `Set.intersection` symset2)
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
  if isSubSig (mtarget mor1) sigma2 
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
     -- Are there symbols that cannot be mapped at all?
     -- Then generate an error immediately
     --debug 9 ("symdiff1",symset1 `Set.difference` symset2)
     --debug 10 ("symdiff2",symset2 `Set.difference` symset1)
     --debug 1 ("sigma1",sigma1)
     --debug 2 ("sigma2",sigma2)
     --debug 4 ("posmap",posmap)
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
     where
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
         Just akmap1 ->
           case posmap of
             Nothing -> return Nothing
             Just posmap2 -> tryToInduce sigma1 sigma2 akmap1 posmap2
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

{-
Computing signature generated by a symbol set.

Algorithm adapted from Bartek Klin's algorithm for CATS.

Input:  symbol set "Syms"
        signature "Sigma"
Output: signature "Sigma1"<=Sigma.

1. get a set "Sigma_symbols" of symbols in Sigma.
2. if Syms is not a subset of Sigma_symbols, return error.
3. let Sigma1 be an empty signature.
4. for each symbol "Sym" in Syms do:
        4.1. if Sym is a:
                4.1.1. sort "S": add sort S to Sigma1.
                4.1.2. total function "F" with profile "Fargs,Fres":
                        4.1.2.1. add all sorts from Fargs to Sigma1.
                        4.1.2.2. add sort Fres to Sigma1.
                        4.1.2.3. add F with the needed profile to Sigma1.
                4.1.3. partial function: as in 4.1.2.
                4.1.4. predicate: as in 4.1.2., except that Fres is omitted.
5. get a list "Sig_sub" of subsort relations in Sigma.
6. for each pair "S1,S2" in Sig_sub do:
        6.1. if S1,S2 are sorts in Sigma1, add "S1,S2" to sort relations in
                Sigma1.
7. return the inclusion of sigma1 into sigma.
-}

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
    OpAsItemType ot ->     -- 4.1.2./4.1.3.
      execState (addOpId (symName sy) ot [] NoOpDefn) sigma1
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
  revealSym sy symset1 = Set.delete sy symset1

finalUnion :: Env -> Env -> Result Env
finalUnion sigma1 sigma2 = return $ addSig sigma1 sigma2 
  -- ???  Finality check not yet implemented
