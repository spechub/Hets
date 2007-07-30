{- |
Module      :  $Header$
Description :  analysis of symbol mappings
Copyright   :  (c) Till Mossakowski, Christian Maeder and Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

symbol map analysis for the HasCASL logic

-}
module HasCASL.SymbolMapAnalysis
    ( inducedFromMorphism
    , inducedFromToMorphism
    , cogeneratedSign
    , generatedSign
    )  where

import HasCASL.As
import HasCASL.Le
import HasCASL.PrintLe
import HasCASL.Builtin
import HasCASL.AsToLe
import HasCASL.Symbol
import HasCASL.RawSym
import HasCASL.Merge
import HasCASL.Morphism
import HasCASL.VarDecl
import HasCASL.TypeAna

import Common.DocUtils
import Common.Id
import Common.Result
import Common.Lib.State
import qualified Data.Map as Map
import qualified Data.Set as Set

inducedFromMorphism :: RawSymbolMap -> Env -> Result Morphism
inducedFromMorphism rmap1 sigma = do
  -- first check: do all source raw symbols match with source signature?
  rmap <- anaRawMap sigma sigma rmap1
  let syms = symOf sigma
      srcTypeMap = typeMap sigma
      wrongRsyms = Map.foldWithKey
        (\rsy _ -> if any (matchesND rsy) $ Set.toList syms
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
  if Set.null wrongRsyms then do
  -- compute the sort map (as a Map)
      myTypeIdMap <- foldr
              (\ (s, ti) m ->
               do s' <- typeFun sigma rmap s (typeKind ti)
                  m1 <- m
                  return $ if s == s' then m1 else Map.insert s s' m1)
              (return Map.empty) $ Map.toList srcTypeMap
  -- compute the op map (as a Map)
      let tarTypeMap = addUnit (classMap sigma) $ Map.foldWithKey
                       ( \ i k m -> Map.insert
                         (Map.findWithDefault i i myTypeIdMap)
                         (mapTypeInfo myTypeIdMap k) m)
                       Map.empty srcTypeMap
          tarAliases = filterAliases tarTypeMap
      op_Map <- Map.foldWithKey (opFun rmap sigma tarAliases myTypeIdMap)
                (return Map.empty) (assumps sigma)
  -- compute target signature
      let tarTypeMap2 = Map.map (mapRestTypeInfo tarAliases myTypeIdMap op_Map)
                        tarTypeMap
          sigma' = Map.foldWithKey (mapOps tarAliases myTypeIdMap op_Map) sigma
                   { typeMap = tarTypeMap2, assumps = Map.empty }
                   $ assumps sigma
  -- return assembled morphism
      Result (envDiags sigma') $ Just ()
      return $ (mkMorphism sigma (diffEnv sigma' preEnv))
                 { typeIdMap = myTypeIdMap
                 , funMap = op_Map }
    else Result [mkDiag Error "unknown (or already directly mapped) symbol(s)"
                 wrongRsyms] Nothing

mapRestTypeInfo :: TypeMap -> IdMap -> FunMap -> TypeInfo -> TypeInfo
mapRestTypeInfo tm im fm ti = ti
    { typeDefn = mapRestTypeDefn tm im fm $ typeDefn ti }

mapRestTypeDefn :: TypeMap -> IdMap -> FunMap -> TypeDefn -> TypeDefn
mapRestTypeDefn tm im fm td = case td of
    DatatypeDefn de -> DatatypeDefn $ mapDataEntry tm im fm de
    _ -> td

mapTypeInfo :: IdMap -> TypeInfo -> TypeInfo
mapTypeInfo im ti =
    ti { superTypes = Set.map ( \ i -> Map.findWithDefault i i im)
                      $ superTypes ti
       , typeDefn = mapTypeDefn im $ typeDefn ti }

mapTypeDefn :: IdMap -> TypeDefn -> TypeDefn
mapTypeDefn im td = case td of
    DatatypeDefn (DataEntry tm i k args rk alts) ->
        DatatypeDefn (DataEntry (compIdMap tm im) i k args rk alts)
    AliasTypeDefn sc -> AliasTypeDefn $ mapType im sc
    _ -> td

-- | compute type mapping
typeFun :: Env -> RawSymbolMap -> Id -> RawKind -> Result Id
typeFun e rmap s k = do
    let rsys = Set.unions $ map ( \ x -> case Map.lookup x rmap of
                 Nothing -> Set.empty
                 Just r -> Set.singleton r)
               [ASymbol $ idToTypeSymbol e s k, AnID s, AKindedId SK_type s]
    -- rsys contains the raw symbols to which s is mapped to
    if Set.null rsys then return s -- use default = identity mapping
       else if Set.null $ Set.deleteMin rsys then
            return $ rawSymName $ Set.findMin rsys
            else Result [mkDiag Error ("type: " ++ showDoc s
                       " mapped ambiguously") rsys] Nothing

-- | compute mapping of functions
opFun :: RawSymbolMap -> Env -> TypeMap -> IdMap -> Id -> Set.Set OpInfo
      -> Result FunMap -> Result FunMap
opFun rmap e tm im i ots m =
    -- first consider all directly mapped profiles
    let (ots1,m1) = Set.fold (directOpMap rmap e tm im i)
                    (Set.empty, m) ots
    -- now try the remaining ones with (un)kinded raw symbol
    in case (Map.lookup (AKindedId SK_op i) rmap,Map.lookup (AnID i) rmap) of
       (Just rsy1, Just rsy2) ->
             Result [mkDiag Error ("Operation " ++ showId i " is mapped twice")
                     (rsy1, rsy2)] Nothing
       (Just rsy, Nothing) ->
          Set.fold (insertmapOpSym e tm im i rsy) m1 ots1
       (Nothing, Just rsy) ->
          Set.fold (insertmapOpSym e tm im i rsy) m1 ots1
       -- Anything not mapped explicitly is left unchanged
       (Nothing,Nothing) -> m1

    -- try to map an operation symbol directly
    -- collect all opTypes that cannot be mapped directly
directOpMap :: RawSymbolMap -> Env -> TypeMap -> IdMap -> Id -> OpInfo
            -> (Set.Set TypeScheme, Result FunMap)
            -> (Set.Set TypeScheme, Result FunMap)
directOpMap rmap e tm im i oi (ots,m) = let ot = opType oi in
    case Map.lookup (ASymbol $ idToOpSymbol e i ot) rmap of
        Just rsy ->
          (ots, insertmapOpSym e tm im i rsy ot m)
        Nothing -> (Set.insert ot ots, m)

    -- map op symbol (id,ot) to raw symbol rsy
mapOpSym :: Env -> TypeMap -> IdMap -> Id -> TypeScheme -> RawSymbol
             -> Result (Id, TypeScheme)
mapOpSym e tm im i ot rsy =
    let sc = mapTypeScheme tm im ot
        err d = Result [mkDiag Error ("Operation symbol " ++
                             showDoc (idToOpSymbol e i sc)
                             "\nis mapped to " ++ d) rsy] Nothing in
      case rsy of
      AnID id' -> return (id', sc)
      AKindedId k id' -> case k of
          SK_op -> return (id', sc)
          _ -> err "wrongly kinded raw symbol"
      ASymbol sy -> case symType sy of
          OpAsItemType ot2 -> if ot2 == expand (typeMap $ symEnv sy) sc
                              then return (symName sy, ot2)
              else err "wrongly typed symbol"
          _ ->  err "wrongly kinded symbol"
      _ -> error "mapOpSym"

    -- insert mapping of op symbol (id, ot) to raw symbol rsy into m
insertmapOpSym :: Env -> TypeMap -> IdMap -> Id -> RawSymbol -> TypeScheme
               -> Result FunMap -> Result FunMap
insertmapOpSym e tm im i rsy ot m = do
      m1 <- m
      q <- mapOpSym e tm im i ot rsy
      let p = (i, mapTypeScheme tm im ot)
      return $ if p == q then m1 else Map.insert p q m1
    -- insert mapping of op symbol (i, ot) into m

  -- map the ops in the source signature
mapOps :: TypeMap -> IdMap -> FunMap -> Id -> Set.Set OpInfo -> Env -> Env
mapOps tm im fm i ots e =
    Set.fold ( \ ot e' ->
        let sc = mapTypeScheme tm im $ opType ot
            (id', sc') = Map.findWithDefault (i, sc)
                         (i, sc) fm
            in execState (addOpId id' sc' (Set.map (mapOpAttr tm im fm)
                                          $ opAttrs ot)
                          (mapOpDefn tm im fm $ opDefn ot)) e')
    e ots

mapOpAttr :: TypeMap -> IdMap -> FunMap -> OpAttr -> OpAttr
mapOpAttr tm im fm oa = case oa of
    UnitOpAttr t ps -> UnitOpAttr (mapSen tm im fm t) ps
    _ -> oa

mapOpDefn :: TypeMap -> IdMap -> FunMap -> OpDefn -> OpDefn
mapOpDefn tm im fm d = case d of
   ConstructData i -> ConstructData $ Map.findWithDefault i i im
   SelectData cs i -> SelectData (Set.map (mapConstrInfo tm im fm) cs)
                      $ Map.findWithDefault i i im
   Definition b t -> Definition b $ mapSen tm im fm t
   _ -> d

mapConstrInfo :: TypeMap -> IdMap -> FunMap -> ConstrInfo -> ConstrInfo
mapConstrInfo tm im fm (ConstrInfo i sc) =
    let (j, nSc) = mapFunSym tm im fm (i, sc) in ConstrInfo j nSc

-- | basically test if the renamed source signature is in the target signature
inducedFromToMorphism :: RawSymbolMap -> Env -> Env -> Result Morphism
inducedFromToMorphism rmap1 sigma1 sigma2 = do
  mor1 <- inducedFromMorphism rmap1 sigma1
  if isSubEnv (mtarget mor1) sigma2
    -- yes => we are done
    then return mor1 { mtarget = sigma2 }
    -- no => OK, we've to take a harder way
    else do
        let ft = Set.filter ( \ (Symbol _ t _) -> case t of
                        TypeAsItemType _ -> True
                        _ -> False)
            s1 = ft $ symOf sigma1
            s2 = ft $ symOf sigma2
            err = Result [Diag Error ("No symbol mapping found for:\n"
                 ++ shows (printMap1 rmap1) "\nOrignal Signature 1:\n"
                 ++ showDoc sigma1 "\nInduced "
                 ++ showEnvDiff (mtarget mor1) sigma2) nullRange] Nothing
        if Set.size s1 == 1 && Set.size s2 == 1 then do
          let Symbol n1 _ _ = Set.findMin s1
              Symbol n2 _ _ = Set.findMin s2
          mor2 <- inducedFromMorphism (Map.insert (AKindedId SK_type n1)
                                       (AKindedId SK_type n2) rmap1) sigma1
          if isSubEnv (mtarget mor2) sigma2
            then return mor2 { mtarget = sigma2 }
            else err
          else err

-- | reveal the symbols in the set
generatedSign :: SymbolSet -> Env -> Result Morphism
generatedSign syms sigma =
    let signSyms = symOf sigma
        closedSyms = closeSymbSet syms
        subSigma = plainHide (signSyms Set.\\ closedSyms) sigma
    in checkSymbols closedSyms signSyms $
       return $ embedMorphism subSigma sigma

-- | hide the symbols in the set
cogeneratedSign :: SymbolSet -> Env -> Result Morphism
cogeneratedSign syms sigma =
    let signSyms = symOf sigma
        subSigma = Set.fold hideRelSymbol sigma syms
        in checkSymbols syms signSyms $
           return $ embedMorphism subSigma sigma
