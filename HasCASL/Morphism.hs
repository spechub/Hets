{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
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

import Common.Id
import Common.Result
import qualified Common.Lib.Map as Map
import Data.List as List

instance Eq Morphism where
    m1 == m2 = (msource m1, mtarget m1, typeIdMap m1, funMap m1) == 
               (msource m2, mtarget m2, typeIdMap m2, funMap m2)

mapTypeScheme :: IdMap -> TypeScheme -> TypeScheme
mapTypeScheme im = mapTypeOfScheme $ mapType im

mapSen :: Morphism -> Term -> Term
mapSen m = let im = typeIdMap m in 
       mapTerm (mapFunSym im (funMap m), mapType im)

mapDataEntry :: Morphism -> DataEntry -> DataEntry
mapDataEntry m (DataEntry tm i k args rk alts) = 
    let tim = compIdMap tm $ typeIdMap m
    in DataEntry tim i k args rk $ map 
           (mapAlt m tim args $ patToType (Map.findWithDefault i i tim) 
                   args rk) alts

mapAlt :: Morphism -> IdMap -> [TypeArg] -> Type -> AltDefn -> AltDefn
mapAlt m tm args dt c@(Construct mi ts p sels) = 
    case mi of
    Just i -> 
      let sc = TypeScheme args 
             (getFunType dt p (map (mapType tm) ts)) nullRange
          (j, TypeScheme _ ty _) = 
              mapFunSym (typeIdMap m) (funMap m) (i, sc)
          in Construct (Just j) ts (getPartiality ts ty) sels
                -- do not change (unused) selectors
    Nothing -> c

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
mapSentence m s = return $ case s of 
   Formula t -> Formula $ mapSen m t 
   DatatypeSen td -> DatatypeSen $ map (mapDataEntry m) td
   ProgEqSen i sc pe ->
       let tm = typeIdMap m 
           fm = funMap m 
           f = mapFunSym tm fm
           (ni, nsc) = f (i, sc) 
           in ProgEqSen ni nsc $ mapEq (f,  mapType tm) pe

mapFunSym :: IdMap -> FunMap -> (Id, TypeScheme) -> (Id, TypeScheme)
mapFunSym im fm (i, sc) = 
    let msc = mapTypeScheme im sc
        (j, sc2) = Map.findWithDefault (i, msc) 
                   (i, msc) fm in
        (j , sc2)

embedMorphism :: Env -> Env -> Morphism
embedMorphism = mkMorphism

ideMor :: Env -> Morphism
ideMor e = embedMorphism e e

compIdMap :: IdMap -> IdMap -> IdMap
compIdMap im1 im2 = Map.foldWithKey ( \ i j -> 
                       Map.insert i $ Map.findWithDefault j j im2)
                             im2 im1

compMor :: Morphism -> Morphism -> Result Morphism
compMor m1 m2 = 
  if isSubEnv (mtarget m1) (msource m2) && 
     isSubEnv (msource m2) (mtarget m1) then 
      let tm2 = typeIdMap m2 
          fm2 = funMap m2 in return
      (mkMorphism (msource m1) (mtarget m2))
      { typeIdMap = compIdMap (typeIdMap m1) tm2
      , funMap = Map.foldWithKey ( \ p1 p2 -> 
                       Map.insert p1
                       $ mapFunSym tm2 fm2 p2) fm2 $ funMap m1
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
    "Signature 1:\n" ++ showPretty e1 "\nSignature 2:\n" 
           ++ showPretty e2 "\nDifference\n" ++ showPretty 
              (diffEnv e1 e2) ""

legalEnv :: Env -> Bool
legalEnv _ = True -- maybe a closure test?
legalMor :: Morphism -> Bool
legalMor m = let s = msource m
                 t = mtarget m
                 ts = typeIdMap m
                 fs = funMap m
             in  
             all (`elem` (Map.keys $ typeMap s)) 
                  (Map.keys ts)
             && all (`elem` (Map.keys $ typeMap t))
                (Map.elems ts)
             && all ((`elem` (Map.keys $ assumps s)) . fst)
                (Map.keys fs)
             && all ((`elem` (Map.keys $ assumps t)) . fst)
                (Map.elems fs)

morphismUnion :: Morphism -> Morphism -> Result Morphism
morphismUnion m1 m2 = 
    do let s1 = msource m1
           s2 = msource m2
           tm1 = Map.toList $ typeIdMap m1
           tm2 = Map.toList $ typeIdMap m2
                 -- unchanged types
           ut1 = Map.keys (typeMap s1) List.\\ map fst tm1
           ut2 = Map.keys (typeMap s2) List.\\ map fst tm2
           mkP = map ( \ a -> (a, a))
           tml = tm1 ++ tm2 ++ mkP (ut1 ++ ut2)
           fm1 = Map.toList $ funMap m1
           fm2 = Map.toList $ funMap m2
                 -- all functions
           af = concatMap ( \ (i, os) ->  
                      map ( \ o -> (i, opType o)) $ opInfos os) . Map.toList
                 -- unchanged functions
           uf1 = af (assumps s1) List.\\ map fst fm1
           uf2 = af (assumps s2) List.\\ map fst fm2
           fml = fm1 ++ fm2 ++ mkP (uf1 ++ uf2)
       s <- merge s1 s2
       t <- merge (mtarget m1) $ mtarget m2
       tm <- foldr ( \ (i, j) rm -> 
                     do m <- rm
                        case Map.lookup i m of
                          Nothing -> return $ Map.insert i j m
                          Just k -> if j == k then return m
                            else fail ("incompatible mapping of type id: " ++ 
                                       showId i " to: " ++ showId j " and: " 
                                       ++ showId k ""))
             (return Map.empty) tml
       fm <- foldr ( \ (isc@(i, sc), jsc@(j, sc1)) rm -> do
                     let nsc = expand (typeMap t) sc1 
                         nisc = (i, expand (typeMap s) sc)
                     m <- rm
                     case Map.lookup nisc m of
                       Nothing -> return $ Map.insert nisc 
                          (j, nsc) m
                       Just ksc@(k, sc2) -> if j == k && 
                         nsc == sc2  
                         then return m
                            else fail ("incompatible mapping of op: " ++ 
                               showFun isc " to: " ++ showFun jsc " and: " 
                               ++ showFun ksc ""))
             (return Map.empty) fml
       return (mkMorphism s t) 
                  { typeIdMap = Map.filterWithKey (/=) tm
                  , funMap = Map.filterWithKey (/=) fm }

showFun :: (Id, TypeScheme) -> ShowS
showFun (i, ty) = showId i . (" : " ++) . showPretty ty

morphismToSymbMap :: Morphism -> SymbolMap
morphismToSymbMap mor = 
  let
    src = msource mor
    tar = mtarget mor
    tm = typeIdMap mor
    typeSymMap = Map.foldWithKey ( \ i ti -> 
       let j = Map.findWithDefault i i tm
           k = typeKind ti
           in Map.insert (idToTypeSymbol src i k)
               $ idToTypeSymbol tar j k) Map.empty $ typeMap src
   in Map.foldWithKey
         ( \ i (OpInfos l) m ->
             foldr ( \ oi -> 
             let ty = opType oi 
                 (j, t2) = mapFunSym
                     tm (funMap mor) (i, ty)
             in Map.insert (idToOpSymbol src i ty) 
                        (idToOpSymbol tar j t2)) m l) 
         typeSymMap $ assumps src
