{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2003
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable
    
Morphism on 'Env' (as for CASL)
-}

module HasCASL.Morphism where

import HasCASL.Le
import HasCASL.As
import HasCASL.AsToLe
import HasCASL.Unify
import HasCASL.MapTerm
import HasCASL.AsUtils
import HasCASL.Merge

import Common.Id
import Common.Keywords
import Common.Result
import Common.PrettyPrint
import Common.Lib.Pretty
import qualified Common.Lib.Map as Map

type FunMap = Map.Map (Id, TypeScheme) (Id, TypeScheme)

data Morphism = Morphism { msource :: Env
                         , mtarget :: Env
                         , classIdMap :: IdMap  -- ignore
                         , typeIdMap :: IdMap 
                         , funMap :: FunMap } 
                         deriving (Eq, Show)

instance PrettyPrint Morphism where
  printText0 ga m = 
      let tm = typeIdMap m 
          fm = funMap m
          ds = Map.foldWithKey ( \ (i, s) (j, t) l -> 
                (printText0 ga i <+> colon <+> printText0 ga s
                <+> text mapsTo <+>      
                printText0 ga j <+> colon <+> printText0 ga t) : l)
               [] fm 
      in (if Map.isEmpty tm then empty
         else text (typeS ++ sS) <+> printText0 ga tm)
         $$ (if Map.isEmpty fm then empty 
             else text (opS ++ sS) <+> fsep (punctuate comma ds))
         $$ nest 1 colon <+> braces (printText0 ga $ msource m) 
                    $$ nest 1 (text mapsTo)
                    <+> braces (printText0 ga $ mtarget m)
      
mapTypeScheme :: IdMap -> TypeScheme -> TypeScheme
mapTypeScheme im = mapTypeOfScheme $ mapType im

mapSen :: Morphism -> Term -> Term
mapSen m = let im = typeIdMap m in 
       mapTerm (mapFunSym im (funMap m), mapType im)

mapDataEntry :: Morphism -> DataEntry -> DataEntry
mapDataEntry m (DataEntry tm i k args alts) = 
    let tim = compIdMap tm $ typeIdMap m
    in DataEntry tim i k args $ map 
           (mapAlt m tim args (Map.findWithDefault i i tim, args, star)) alts

mapAlt :: Morphism -> IdMap -> [TypeArg] -> DataPat -> AltDefn -> AltDefn
mapAlt m tm args dt c@(Construct mi ts p sels) = 
    case mi of
    Just i -> 
      let sc = TypeScheme args 
             (getConstrType dt p (map (mapType tm) ts)) []
          (j, TypeScheme _ ty _) = 
              mapFunSym (typeIdMap m) (funMap m) (i, sc)
          in Construct (Just j) ts (getPartiality ts ty) sels
                -- do not change (unused) selectors
    Nothing -> c

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
    let (j, sc2) = Map.findWithDefault (i, mapTypeScheme im sc) 
                   (i, sc) fm in
        (j , sc2)

mkMorphism :: Env -> Env -> Morphism
mkMorphism e1 e2 = Morphism e1 e2 Map.empty Map.empty Map.empty

embedMorphism :: Env -> Env -> Morphism
embedMorphism = mkMorphism

ideMor :: Env -> Morphism
ideMor e = embedMorphism e e

compIdMap :: IdMap -> IdMap -> IdMap
compIdMap im1 im2 = Map.foldWithKey ( \ i j -> 
                       Map.insert i $ Map.findWithDefault j j im2)
                             im2 $ im1

compMor :: Morphism -> Morphism -> Result Morphism
compMor m1 m2 = 
  if isSubEnv (mtarget m1) (msource m2) && 
     isSubEnv (msource m2) (mtarget m1) then 
      let tm2 = typeIdMap m2 
          fm2 = funMap m2 in return
      (mkMorphism (msource m1) (mtarget m2))
      { classIdMap = compIdMap (classIdMap m1) $ classIdMap m2
      , typeIdMap = compIdMap (typeIdMap m1) tm2
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
           ++ showEnvDiff e1 e2) nullPos] Nothing

showEnvDiff :: Env -> Env -> String
showEnvDiff e1 e2 = 
    "Signature 1:\n" ++ showPretty e1 "\nSignature 2:\n" 
           ++ showPretty e2 "\nDifference\n" ++ showPretty 
              (diffEnv e1 e2) ""

symbMapToMorphism :: Env -> Env -> SymbolMap -> Result Morphism
-- consider partial symbol map
symbMapToMorphism sigma1 sigma2 smap = do
  type_map1 <- Map.foldWithKey myIdMap (return Map.empty) $ typeMap sigma1
  fun_map1 <- Map.foldWithKey myAsMap (return Map.empty) $ assumps sigma1
  return (mkMorphism sigma1 sigma2)
         { typeIdMap = type_map1
         , funMap = fun_map1}
  where
  myIdMap i k m = do
    m1 <- m 
    sym <- maybeToResult (posOfId i)
             ("symbMapToMorphism - Could not map type "++showId i "")
             $ Map.lookup (Symbol { symName = i
                                  , symType = TypeAsItemType 
                                               $ typeKind k
                                  , symEnv = sigma1 }) smap
    return (Map.insert i (symName sym) m1)
  myAsMap i (OpInfos ots) m = foldr (insFun i) m ots
  insFun i ot m = do
    let osc = opType ot
    m1 <- m
    sym <- maybeToResult (posOfId i)
             ("symbMapToMorphism - Could not map op "++showId i "")
             $ Map.lookup (Symbol { symName = i
                                  , symType = OpAsItemType osc
                                  , symEnv = sigma1 }) smap
    k <- case symType sym of
        OpAsItemType sc -> return sc
        _ -> Result [mkDiag Error
                     "symbMapToMorphism - Wrong result symbol type for op" i]
             Nothing
    return (Map.insert (i, osc) (symName sym, k) m1)

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
    do s <- merge (msource m1) $ msource m2
       t <- merge (mtarget m1) $ mtarget m2
       tm <- foldr ( \ (i, j) rm -> 
                     do m <- rm
                        case Map.lookup i m of
                          Nothing -> return $ Map.insert i j m
                          Just k -> if j == k then return m
                            else do 
                            Result [Diag Error 
                              ("incompatible mapping of type id: " ++ 
                               showId i " to: " ++ showId j " and: " 
                               ++ showId k "") $ posOfId i] $ Just ()
                            return m) 
             (return $ typeIdMap m1) $ Map.toList $ typeIdMap m2
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
                            else do 
                            Result [Diag Error 
                              ("incompatible mapping of op: " ++ 
                               showFun isc " to: " ++ showFun jsc " and: " 
                               ++ showFun ksc "") $ posOfId i] $ Just ()
                            return m) 
             (return Map.empty) (Map.toList (funMap m1) ++ 
                                 Map.toList (funMap m2))
       return (mkMorphism s t) 
                  { typeIdMap = tm
                  , funMap = fm }

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
