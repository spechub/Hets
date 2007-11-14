{- |
Module      :  $Header$
Description :  morphisms implementation
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

mapping entities of morphisms

-}

module HasCASL.Morphism where

import HasCASL.Le
import HasCASL.As
import HasCASL.TypeAna
import HasCASL.AsUtils
import HasCASL.AsToLe
import HasCASL.MapTerm
import HasCASL.Merge

import Common.DocUtils
import Common.Id
import Common.Result
import qualified Data.Set as Set
import qualified Data.Map as Map

instance Eq Morphism where
  m1 == m2 = (msource m1, mtarget m1, typeIdMap m1, classIdMap m1, funMap m1)
     == (msource m2, mtarget m2, typeIdMap m2, classIdMap m2, funMap m2)

-- | map type and expand it
mapTypeE :: TypeMap -> IdMap -> Type -> Type
mapTypeE tm im = expandAliases tm . mapType im

mapTypeScheme :: TypeMap -> IdMap -> TypeScheme -> TypeScheme
mapTypeScheme tm im = mapTypeOfScheme $ mapTypeE tm im

mapSen :: TypeMap -> IdMap -> FunMap -> Term -> Term
mapSen tm im fm = mapTerm (mapFunSym tm im fm, mapTypeE tm im)

setToMap :: Ord a => Set.Set a -> Map.Map a a
setToMap = Map.fromAscList . map ( \ a -> (a, a)) . Set.toList

getDatatypeIds :: DataEntry -> Set.Set Id
getDatatypeIds (DataEntry _ i _ _ _ alts) =
    let getAltIds (Construct _ tys _ sels) = Set.union
            (Set.unions $ map getTypeIds tys)
            $ Set.unions $ concatMap (map getSelIds) sels
        getSelIds (Select _ ty _) = getTypeIds ty
        getTypeIds = idsOf (== 0)
    in Set.insert i $ Set.unions $ map getAltIds $ Set.toList alts

mapDataEntry :: TypeMap -> IdMap -> FunMap -> DataEntry -> DataEntry
mapDataEntry tm im fm de@(DataEntry dm i k args rk alts) =
    let tim = Map.intersection (compIdMap dm im) $ setToMap $ getDatatypeIds de
    in DataEntry tim i k args rk $ Set.map
           (mapAlt tm tim fm args $ patToType (Map.findWithDefault i i tim)
                   args rk) alts

mapAlt :: TypeMap -> IdMap -> FunMap -> [TypeArg] -> Type -> AltDefn
       -> AltDefn
mapAlt tm im fm args dt c@(Construct mi ts p sels) =
    case mi of
    Just i ->
      let sc = TypeScheme args
             (getFunType dt p $ map (mapTypeE tm im) ts) nullRange
          (j, TypeScheme _ ty _) = mapFunSym tm im fm (i, sc)
          in Construct (Just j) ts (getPartiality ts ty) $
             map (map (mapSel tm im fm args dt)) sels
    Nothing -> c

mapSel :: TypeMap -> IdMap -> FunMap -> [TypeArg] -> Type -> Selector
       -> Selector
mapSel tm im fm args dt s@(Select mid t p) = case mid of
    Nothing -> s
    Just i -> let
        sc = TypeScheme args (getSelType dt p $ mapTypeE tm im t) nullRange
        (j, TypeScheme _ ty _) = mapFunSym tm im fm (i, sc)
        in Select (Just j) t $ getPartiality [dt] ty

-- | get the partiality from a constructor type
-- with a given number of curried arguments
getPartiality :: [a] -> Type -> Partiality
getPartiality args t = case getTypeAppl t of
   (TypeName i _ _, [_, res]) | isArrow i -> case args of
     [] -> Total
     [_] -> if isPartialArrow i then Partial else Total
     _ : rs -> getPartiality rs res
   (TypeName i _ _, [_]) | i == lazyTypeId ->
        if null args then Partial else error "getPartiality"
   _ -> Total

mapSentence :: Morphism -> Sentence -> Result Sentence
mapSentence m s = let
    tm = filterAliases $ typeMap $ mtarget m
    im = typeIdMap m
    fm = funMap m
    f = mapFunSym tm im fm
    in return $ case s of
      Formula t -> Formula $ mapSen tm im fm t
      DatatypeSen td -> DatatypeSen $ map (mapDataEntry tm im fm) td
      ProgEqSen i sc pe ->
        let (ni, nsc) = f (i, sc)
        in ProgEqSen ni nsc $ mapEq (f,  mapTypeE tm im) pe

mapFunSym :: TypeMap -> IdMap -> FunMap -> (Id, TypeScheme) -> (Id, TypeScheme)
mapFunSym tm im fm (i, sc) =
    let msc = mapTypeScheme tm im sc
    in Map.findWithDefault (i, msc) (i, msc) fm

embedMorphism :: Env -> Env -> Morphism
embedMorphism = mkMorphism

ideMor :: Env -> Morphism
ideMor e = embedMorphism e e

compIdMap :: IdMap -> IdMap -> IdMap
compIdMap im1 im2 = Map.foldWithKey ( \ i j ->
    let k = Map.findWithDefault j j im2 in
    if i == k then id else Map.insert i k) im2 im1

compMor :: Morphism -> Morphism -> Result Morphism
compMor m1 m2 =
  if mtarget m1 == msource m2 then
      let tm2 = typeIdMap m2
          im = compIdMap (typeIdMap m1) tm2
          cm2 = classIdMap m2
          cm = compIdMap (classIdMap m1) cm2
          fm2 = funMap m2
          tar = mtarget m2
          src = msource m1
          tm = filterAliases $ typeMap tar
      in return (mkMorphism src tar)
      { typeIdMap = Map.intersection im $ typeMap src
      , classIdMap = Map.intersection cm $ classMap src
      , funMap = Map.intersection (Map.foldWithKey ( \ p1 p2 ->
                       let p3 = mapFunSym tm tm2 fm2 p2 in
                       if p1 == p3 then id else Map.insert p1 p3)
                 fm2 $ funMap m1) $ Map.fromList $
                    concatMap ( \ (k, os) ->
                          map ( \ o -> ((k, mapTypeScheme tm im
                                        $ opType o), ())) $ Set.toList os)
                     $ Map.toList $ assumps src
      }
   else fail "intermediate signatures of morphisms do not match"

inclusionMor :: Env -> Env -> Result Morphism
inclusionMor e1 e2 =
  if isSubEnv e1 e2
     then return (embedMorphism e1 e2)
     else Result [Diag Error
          ("Attempt to construct inclusion between non-subsignatures:\n"
           ++ showEnvDiff e1 e2) nullRange] Nothing

showEnvDiff :: Env -> Env -> String
showEnvDiff e1 e2 =
    "Signature 1:\n" ++ showDoc e1 "\nSignature 2:\n"
           ++ showDoc e2 "\nDifference\n" ++ showDoc
              (diffEnv e1 e2) ""

legalEnv :: Env -> Bool
legalEnv _ = True -- maybe a closure test?

legalMor :: Morphism -> Bool
legalMor m = let
    s = msource m
    t = mtarget m
    ts = typeIdMap m
    cs = classIdMap m
    fs = funMap m in
       all (`elem` Map.keys (typeMap s)) (Map.keys ts)
    && all (`elem` Map.keys (typeMap t)) (Map.elems ts)
    && all (`elem` Map.keys (classMap s)) (Map.keys cs)
    && all (`elem` Map.keys (classMap t)) (Map.elems cs)
    && all ((`elem` Map.keys (assumps s)) . fst) (Map.keys fs)
    && all ((`elem` Map.keys (assumps t)) . fst) (Map.elems fs)

morphismUnion :: Morphism -> Morphism -> Result Morphism
morphismUnion m1 m2 = do
  let s1 = msource m1
      s2 = msource m2
  s <- merge s1 s2
  t <- merge (mtarget m1) $ mtarget m2
  let tm1 = typeMap s1
      tm2 = typeMap s2
      im1 = typeIdMap m1
      im2 = typeIdMap m2
      -- unchanged types
      ut1 = Map.keysSet tm1 Set.\\ Map.keysSet im1
      ut2 = Map.keysSet tm2 Set.\\ Map.keysSet im2
      ima1 = Map.union im1 $ setToMap ut1
      ima2 = Map.union im2 $ setToMap ut2
      sAs = filterAliases $ typeMap s
      tAs = filterAliases $ typeMap t
      expP = Map.fromList . map ( \ ((i, o), (j, p)) ->
                            ((i, expand tAs o), (j, expand tAs p)))
                  . Map.toList
      fm1 = expP $ funMap m1
      fm2 = expP $ funMap m2
      af im = Set.unions . map ( \ (i, os) ->
                   Set.map ( \ o -> (i, mapTypeScheme tAs im
                                    $ expand sAs $ opType o)) os)
                      . Map.toList
                 -- unchanged functions
      uf1 = af im1 (assumps s1) Set.\\ Map.keysSet fm1
      uf2 = af im2 (assumps s2) Set.\\ Map.keysSet fm2
      fma1 = Map.union fm1 $ setToMap uf1
      fma2 = Map.union fm2 $ setToMap uf2
      showFun (i, ty) = showId i . (" : " ++) . showDoc ty
  tma <- mergeMap ( \ t1 t2 -> if t1 == t2 then return t1 else
                      fail $ "incompatible type mapping to `"
                         ++ showId t1 "' and '" ++ showId t2 "'") ima1 ima2
  fma <- mergeMap ( \ o1 o2 -> if o1 == o2 then return o1 else
                      fail $ "incompatible mapping to '"
                         ++ showFun o1 "' and '" ++ showFun o2 "'") fma1 fma2
  return (mkMorphism s t)
    { typeIdMap = tma
    , funMap = fma }

morphismToSymbMap :: Morphism -> SymbolMap
morphismToSymbMap mor = let
    src = msource mor
    tar = mtarget mor
    im = typeIdMap mor
    tm = filterAliases $ typeMap tar
    typeSymMap = Map.foldWithKey ( \ i ti ->
       let j = Map.findWithDefault i i im
           k = typeKind ti
           in Map.insert (idToTypeSymbol src i k)
               $ idToTypeSymbol tar j k) Map.empty $ typeMap src
   in Map.foldWithKey
         ( \ i s m ->
             Set.fold ( \ oi ->
             let ty = opType oi
                 (j, t2) = mapFunSym tm im (funMap mor) (i, ty)
             in Map.insert (idToOpSymbol src i ty)
                        (idToOpSymbol tar j t2)) m s)
         typeSymMap $ assumps src

-- | map a kind along a signature morphism (variance is preserved)
mapKinds :: Morphism -> Kind -> Kind
mapKinds mor  = mapKind $ (\ a -> Map.findWithDefault a a $ classIdMap mor)
