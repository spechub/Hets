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
import Common.ExtSign
import Common.Result
import Common.Utils (composeMap)
import Common.Lib.Rel (setToMap)
import Common.Lib.State
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad

inducedFromMorphism :: RawSymbolMap -> Env -> Result Morphism
inducedFromMorphism rmap1 sigma = do
    -- first check: do all source raw symbols match with source signature?
    rmap <- anaRawMap sigma sigma rmap1
    let srcTypeMap = typeMap sigma
        srcClassMap = classMap sigma
        assMap = assumps sigma
    myClassIdMap <- foldr
              (\ (s, ti) m ->
               do s' <- classFun sigma rmap s (rawKind ti)
                  m1 <- m
                  return $ if s == s' then m1 else Map.insert s s' m1)
              (return Map.empty) $ Map.toList srcClassMap
    tarClassMap0 <- foldM (\ m (i, k) ->
       let ni = Map.findWithDefault i i myClassIdMap
           nk = mapClassInfo myClassIdMap k
       in case Map.lookup ni m of
         Nothing -> return $ Map.insert ni nk m
         Just ok -> do
           mk <- mergeClassInfo ok nk
           return $ Map.insert ni mk m)
       Map.empty $ Map.toList srcClassMap
    let tarClassMap = minimizeClassMap tarClassMap0
  -- compute the type map (as a Map)
    myTypeIdMap <- foldr
              (\ (s, ti) m ->
               do s' <- typeFun sigma rmap s (typeKind ti)
                  m1 <- m
                  return $ if s == s' then m1 else Map.insert s s' m1)
              (return Map.empty) $ Map.toList srcTypeMap
    tarTypeMap0 <- foldM (\ m (i, k) ->
       let ni = Map.findWithDefault i i myTypeIdMap
           nk = mapTypeInfo srcTypeMap myClassIdMap myTypeIdMap k
       in case Map.lookup ni m of
         Nothing -> return $ Map.insert ni nk m
         Just ok -> do
           mk <- mergeTypeInfo tarClassMap ok nk
           return $ Map.insert ni mk m)
       Map.empty $ Map.toList srcTypeMap
    let tarTypeMap = addUnit (classMap sigma) tarTypeMap0
        tarAliases = filterAliases tarTypeMap
  -- compute the op map (as a Map)
    op_Map <- Map.foldWithKey
      (opFun rmap sigma myClassIdMap tarAliases myTypeIdMap)
      (return Map.empty) assMap
  -- compute target signature
    let tarTypeMap2 = Map.map
          (mapRestTypeInfo myClassIdMap tarAliases myTypeIdMap op_Map)
                        tarTypeMap
        sigma' = Map.foldWithKey
          (mapOps myClassIdMap tarAliases myTypeIdMap op_Map) sigma
                   { typeMap = tarTypeMap2
                   , classMap = tarClassMap
                   , assumps = Map.empty }
                   assMap
    disjointKeys tarTypeMap2 tarClassMap
  -- return assembled morphism
    Result (envDiags sigma') $ Just ()
    return $ (mkMorphism sigma $ diffEnv sigma' preEnv)
                 { typeIdMap = myTypeIdMap
                 , classIdMap = myClassIdMap
                 , funMap = op_Map }

mapRestTypeInfo :: IdMap -> TypeMap -> IdMap -> FunMap -> TypeInfo -> TypeInfo
mapRestTypeInfo jm tm im fm ti = ti
    { typeDefn = mapRestTypeDefn jm tm im fm $ typeDefn ti }

mapRestTypeDefn :: IdMap -> TypeMap -> IdMap -> FunMap -> TypeDefn -> TypeDefn
mapRestTypeDefn jm tm im fm td = case td of
    DatatypeDefn de -> DatatypeDefn $ mapDataEntry jm tm im fm de
    AliasTypeDefn t -> AliasTypeDefn $ mapTypeE jm tm im t
    _ -> td

mapClassInfo :: IdMap -> ClassInfo -> ClassInfo
mapClassInfo im ti =
    ti { classKinds = Set.map (mapKindI im) $ classKinds ti }

mapTypeInfo :: TypeMap -> IdMap -> IdMap -> TypeInfo -> TypeInfo
mapTypeInfo tm jm im ti =
    ti { superTypes = Set.map ( \ i -> Map.findWithDefault i i im)
                      $ superTypes ti
       , otherTypeKinds = Set.map (mapKindI jm) $ otherTypeKinds ti
       , typeDefn = mapTypeDefn tm im $ typeDefn ti }

mapTypeDefn :: TypeMap -> IdMap -> TypeDefn -> TypeDefn
mapTypeDefn tmAll im td = case td of
    DatatypeDefn de@(DataEntry tm i k args rk alts) ->
        DatatypeDefn (DataEntry
           (Map.intersection (composeMap tmAll tm im)
            $ setToMap $ getDatatypeIds de) i k args rk alts)
    AliasTypeDefn sc -> AliasTypeDefn $ mapType im sc
    _ -> td

-- | compute class mapping
classFun :: Env -> RawSymbolMap -> Id -> RawKind -> Result Id
classFun e rmap s k = do
    let rsys = Set.unions $ map ( \ x -> case Map.lookup x rmap of
                 Nothing -> Set.empty
                 Just r -> Set.singleton r)
               [ASymbol $ idToClassSymbol e s k, AnID s, AKindedId SyKclass s]
    -- rsys contains the raw symbols to which s is mapped to
    if Set.null rsys then return s -- use default = identity mapping
       else if Set.null $ Set.deleteMin rsys then
            return $ rawSymName $ Set.findMin rsys
            else Result [mkDiag Error ("class: " ++ showDoc s
                       " mapped ambiguously") rsys] Nothing

-- | compute type mapping
typeFun :: Env -> RawSymbolMap -> Id -> RawKind -> Result Id
typeFun e rmap s k = do
    let rsys = Set.unions $ map ( \ x -> case Map.lookup x rmap of
                 Nothing -> Set.empty
                 Just r -> Set.singleton r)
               [ASymbol $ idToTypeSymbol e s k, AnID s, AKindedId SyKtype s]
    -- rsys contains the raw symbols to which s is mapped to
    if Set.null rsys then return s -- use default = identity mapping
       else if Set.null $ Set.deleteMin rsys then
            return $ rawSymName $ Set.findMin rsys
            else Result [mkDiag Error ("type: " ++ showDoc s
                       " mapped ambiguously") rsys] Nothing

-- | compute mapping of functions
opFun :: RawSymbolMap -> Env -> IdMap -> TypeMap -> IdMap -> Id
      -> Set.Set OpInfo -> Result FunMap -> Result FunMap
opFun rmap e jm tm im i ots m =
    -- first consider all directly mapped profiles
    let (ots1, m1) = Set.fold (directOpMap rmap e jm tm im i)
                    (Set.empty, m) ots
    -- now try the remaining ones with (un)kinded raw symbol
    in case (Map.lookup (AKindedId SyKop i) rmap,Map.lookup (AnID i) rmap) of
       (Just rsy1, Just rsy2) ->
             Result [mkDiag Error ("Operation " ++ showId i " is mapped twice")
                     (rsy1, rsy2)] Nothing
       (Just rsy, Nothing) ->
          Set.fold (insertmapOpSym e jm tm im i rsy) m1 ots1
       (Nothing, Just rsy) ->
          Set.fold (insertmapOpSym e jm tm im i rsy) m1 ots1
       -- Anything not mapped explicitly is left unchanged
       (Nothing, Nothing) -> m1

    -- try to map an operation symbol directly
    -- collect all opTypes that cannot be mapped directly
directOpMap :: RawSymbolMap -> Env -> IdMap -> TypeMap -> IdMap -> Id -> OpInfo
            -> (Set.Set TypeScheme, Result FunMap)
            -> (Set.Set TypeScheme, Result FunMap)
directOpMap rmap e jm tm im i oi (ots,m) = let ot = opType oi in
    case Map.lookup (ASymbol $ idToOpSymbol e i ot) rmap of
        Just rsy ->
          (ots, insertmapOpSym e jm tm im i rsy ot m)
        Nothing -> (Set.insert ot ots, m)

    -- map op symbol (id,ot) to raw symbol rsy
mapOpSym :: Env -> IdMap -> TypeMap -> IdMap -> Id -> TypeScheme -> RawSymbol
         -> Result (Id, TypeScheme)
mapOpSym e jm tm im i ot rsy =
    let sc = mapTypeScheme jm tm im ot
        err d = Result [mkDiag Error ("Operation symbol " ++
                             showDoc (idToOpSymbol e i sc)
                             "\nis mapped to " ++ d) rsy] Nothing in
      case rsy of
      AnID id' -> return (id', sc)
      AKindedId k id' -> case k of
          SyKop -> return (id', sc)
          _ -> err "wrongly kinded raw symbol"
      ASymbol sy -> case symType sy of
          OpAsItemType ot2 -> if ot2 == expand (typeMap $ symEnv sy) sc
                              then return (symName sy, ot2)
              else err "wrongly typed symbol"
          _ ->  err "wrongly kinded symbol"
      _ -> error "mapOpSym"

    -- insert mapping of op symbol (id, ot) to raw symbol rsy into m
insertmapOpSym :: Env -> IdMap -> TypeMap -> IdMap -> Id -> RawSymbol
               -> TypeScheme -> Result FunMap -> Result FunMap
insertmapOpSym e jm tm im i rsy ot m = do
      m1 <- m
      q <- mapOpSym e jm tm im i ot rsy
      let p = (i, mapTypeScheme jm tm im ot)
      return $ if p == q then m1 else Map.insert p q m1
    -- insert mapping of op symbol (i, ot) into m

  -- map the ops in the source signature
mapOps :: IdMap -> TypeMap -> IdMap -> FunMap -> Id -> Set.Set OpInfo -> Env
       -> Env
mapOps jm tm im fm i ots e =
    Set.fold ( \ ot e' ->
        let sc = mapTypeScheme jm tm im $ opType ot
            (id', sc') = Map.findWithDefault (i, sc)
                         (i, sc) fm
            in execState (addOpId id' sc' (Set.map (mapOpAttr jm tm im fm)
                                          $ opAttrs ot)
                          (mapOpDefn jm tm im fm $ opDefn ot)) e')
    e ots

mapOpAttr :: IdMap -> TypeMap -> IdMap -> FunMap -> OpAttr -> OpAttr
mapOpAttr jm tm im fm oa = case oa of
    UnitOpAttr t ps -> UnitOpAttr (mapSen jm tm im fm t) ps
    _ -> oa

mapOpDefn :: IdMap -> TypeMap -> IdMap -> FunMap -> OpDefn -> OpDefn
mapOpDefn jm tm im fm d = case d of
   ConstructData i -> ConstructData $ Map.findWithDefault i i im
   SelectData cs i -> SelectData (Set.map (mapConstrInfo jm tm im fm) cs)
                      $ Map.findWithDefault i i im
   Definition b t -> Definition b $ mapSen jm tm im fm t
   _ -> d

mapConstrInfo :: IdMap -> TypeMap -> IdMap -> FunMap -> ConstrInfo
              -> ConstrInfo
mapConstrInfo jm tm im fm (ConstrInfo i sc) =
    let (j, nSc) = mapFunSym jm tm im fm (i, sc) in ConstrInfo j nSc

-- | basically test if the renamed source signature is in the target signature
inducedFromToMorphism :: RawSymbolMap -> ExtSign Env Symbol
                      -> ExtSign Env Symbol -> Result Morphism
inducedFromToMorphism rmap1 e1@(ExtSign sigma1 sy1) (ExtSign sigma2 sy2) = do
  mor1 <- inducedFromMorphism rmap1 sigma1
  if isSubEnv (mtarget mor1) sigma2
    -- yes => we are done
    then return mor1 { mtarget = sigma2 }
    -- no => OK, we've to take a harder way
    else do
        let ft = Set.filter ( \ (Symbol _ t _) -> case t of
                        TypeAsItemType _ -> True
                        _ -> False)
            s1 = ft sy1
            s2 = ft sy2
            err mor = Result [Diag Error ("No symbol mapping found for:\n"
                 ++ shows (printMap1 rmap1) "\nOriginal Signature 1:\n"
                 ++ showDoc e1 "\nInduced "
                 ++ showEnvDiff (mtarget mor) sigma2
                 ++ "\ndeclared Symbols of Signature 2:\n"
                 ++ showDoc sy2 "") nullRange] Nothing
        if Set.size s1 == 1 && Set.size s2 == 1 then do
          let Symbol n1 _ _ = Set.findMin s1
              Symbol n2 _ _ = Set.findMin s2
          mor2 <- inducedFromMorphism (Map.insert (AKindedId SyKtype n1)
                                       (AKindedId SyKtype n2) rmap1) sigma1
          if isSubEnv (mtarget mor2) sigma2
            then return mor2 { mtarget = sigma2 }
            else err mor2
          else err mor1

-- | reveal the symbols in the set
generatedSign :: SymbolSet -> Env -> Result Morphism
generatedSign syms sigma =
    let signSyms = symOf sigma
        closedSyms = closeSymbSet syms
        subSigma = plainHide (signSyms Set.\\ closedSyms) sigma
    in checkSymbols closedSyms signSyms $
       return $ mkMorphism subSigma sigma

-- | hide the symbols in the set
cogeneratedSign :: SymbolSet -> Env -> Result Morphism
cogeneratedSign syms sigma =
    let signSyms = symOf sigma
        subSigma = Set.fold hideRelSymbol sigma syms
        in checkSymbols syms signSyms $
           return $ mkMorphism subSigma sigma
