{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2003
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable
    
Morphism on 'Env' (as for CASL)
-}

module HasCASL.Morphism where

import HasCASL.Le
import HasCASL.As
import HasCASL.AsToLe
import HasCASL.PrintLe
import HasCASL.Unify
import HasCASL.Symbol
import Common.Id
import Common.Keywords
import Common.Result
import Common.PrettyPrint
import Common.Lib.Pretty
import qualified Common.Lib.Map as Map

type IdMap = Map.Map Id Id

type FunMap = Map.Map (Id, TySc) (Id, TySc)

data Morphism = Morphism { msource :: Env
			 , mtarget :: Env
			 , classIdMap :: IdMap  -- ignore
			 , typeIdMap :: IdMap 
                         , funMap :: FunMap } 
                         deriving (Eq, Show)

instance PrettyPrint Morphism where
  printText0 ga m = braces (printText0 ga (msource m)) 
		    $$ text mapsTo
		    <+> braces (printText0 ga (mtarget m))

mapType :: IdMap -> Type -> Type
-- include classIdMap later
mapType m t = case t of
	   TypeName i k n ->
	       if n == 0 then 
		  case Map.lookup i m of
		  Just j -> TypeName j k 0
		  _ -> t
	       else t
	   TypeAppl t1 t2 ->
	       TypeAppl (mapType m t1) (mapType m t2)
	   TypeToken _ -> t
	   BracketType b l ps ->
	       BracketType b (map (mapType m) l) ps
	   KindedType tk k ps -> 
	       KindedType (mapType m tk) k ps
	   MixfixType l -> MixfixType $ map (mapType m) l
	   LazyType tl ps -> LazyType (mapType m tl) ps
	   ProductType l ps -> ProductType (map (mapType m) l) ps
           FunType t1 a t2 ps -> FunType (mapType m t1) a (mapType m t2) ps


mapTypeScheme :: IdMap -> TypeScheme -> TypeScheme
-- rename clashing type arguments later
mapTypeScheme m (TypeScheme args (q :=> t) ps) =
    TypeScheme args (q :=> mapType m t) ps

mapTySc :: IdMap -> TySc -> TySc
mapTySc m (TySc s1) = TySc (mapTypeScheme m s1)


mapFunSym :: IdMap -> FunMap -> (Id, TySc) -> Maybe (Id, TySc)
mapFunSym tm fm (i, sc) = do
  (newI, _sc1) <- Map.lookup (i, sc) fm
  let sc2 = mapTySc tm sc
      -- unify sc2 with sc1 later
  return (newI, sc2)

mkMorphism :: Env -> Env -> Morphism
mkMorphism e1 e2 = Morphism e1 e2 Map.empty Map.empty Map.empty

embedMorphism :: Env -> Env -> Morphism
embedMorphism a b =
    (mkMorphism a b) 
    { typeIdMap = foldr (\x -> Map.insert x x) Map.empty 
                $ Map.keys $ typeMap a
    , funMap = Map.foldWithKey 
                 ( \ i (OpInfos ts) m -> foldr 
                      (\ oi -> let v = (i, TySc $ opType oi) in 
		           Map.insert v v) m ts)
                 Map.empty $ assumps a
    }

ideMor :: Env -> Morphism
ideMor e = embedMorphism e e

compMor :: Morphism -> Morphism -> Maybe Morphism
compMor m1 m2 = 
  if isSubEnv (mtarget m1) (msource m2) then Just 
      (mkMorphism (msource m1) (mtarget m2))
      { typeIdMap = Map.map ( \ i -> Map.findWithDefault i i $ typeIdMap m2)
			     $ typeIdMap m1 
      , funMap = Map.foldWithKey ( \ (i1, sc1) (i2, sc2) m -> 
		       Map.insert (i1, sc1) 
		       (Map.findWithDefault (i2, sc2) (i2, sc2) $ 
			funMap m2) m) Map.empty $ funMap m1
      }
   else Nothing

inclusionMor :: Env -> Env -> Result Morphism
inclusionMor e1 e2 =
  if isSubEnv e1 e2
     then return (embedMorphism e1 e2)
     else pplain_error (ideMor initialEnv)
          (ptext "Attempt to construct inclusion between non-subsignatures:"
           $$ ptext "Singature 1:" $$ printText e1
           $$ ptext "Singature 2:" $$ printText e2)
           nullPos

symbMapToMorphism :: Env -> Env -> SymbolMap -> Result Morphism
symbMapToMorphism sigma1 sigma2 smap = do
  type_map1 <- Map.foldWithKey myIdMap (return Map.empty) $ typeMap sigma1
  fun_map1 <- Map.foldWithKey myAsMap (return Map.empty) $ assumps sigma1
  return (mkMorphism sigma1 sigma2)
	 { typeIdMap = type_map1
	 , funMap = fun_map1}
  where
  myIdMap i k m = do
    m1 <- m 
    sym <- maybeToResult nullPos 
             ("symbMapToMorphism - Could not map sort "++showId i "")
             $ Map.lookup (Symbol { symName = i
				  , symType = TypeAsItemType 
				               $ typeKind k
				  , symEnv = sigma1 }) smap
    return (Map.insert i (symName sym) m1)
  myAsMap i (OpInfos ots) m = foldr (insFun i) m ots
  insFun i ot m = do
    let osc = opType ot
    m1 <- m
    sym <- maybeToResult nullPos 
             ("symbMapToMorphism - Could not map op "++showId i "")
             $ Map.lookup (Symbol { symName = i
				  , symType = OpAsItemType osc
				  , symEnv = sigma1 }) smap
    k <- case symType sym of
        OpAsItemType sc -> return $ TySc sc
        _ -> plain_error (TySc osc)
              ("symbMapToMorphism - Wrong result symbol type for op"
               ++showId i "") nullPos 
    return (Map.insert (i, TySc osc) (symName sym, k) m1)

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
       fm <- foldr ( \ (isc@(i, _), jsc@(j, TySc sc1)) rm -> do
		     m <- rm
		     case Map.lookup isc m of
		       Nothing -> return $ Map.insert isc jsc m
		       Just ksc@(k, TySc sc2) -> if j == k && 
		         isUnifiable (typeMap t) 0 sc1 sc2  
		         then return m
		            else do 
		            Result [Diag Error 
			      ("incompatible mapping of op: " ++ 
			       showFun isc " to: " ++ showFun jsc " and: " 
			       ++ showFun ksc "") $ posOfId i] $ Just ()
		            return m) 
	     (return $ funMap m1) $ Map.toList $ funMap m2
       return (mkMorphism s t) 
		  { typeIdMap = tm
		  , funMap = fm }

showFun :: (Id, TySc) -> ShowS
showFun (i, TySc ty) = showId i . (" : " ++) . showPretty ty

morphismToSymbMap :: Morphism -> SymbolMap
morphismToSymbMap mor = 
  let
    src = msource mor
    tar = mtarget mor
    tm = typeMap src
    typeSymMap = 
      Map.foldWithKey
         ( \ s1 s2 m -> let k = typeKind $ 
	                        Map.findWithDefault starTypeInfo s1 tm 
	   in Map.insert (idToTypeSymbol src s1 k) (idToTypeSymbol tar s2 k) m)
         Map.empty $ 
         typeIdMap mor
   in Map.foldWithKey
         ( \ (id1, TySc t1) (id2, TySc t2) m -> 
             Map.insert (idToOpSymbol src id1 t1) 
                        (idToOpSymbol tar id2 t2) m)
         typeSymMap $ funMap mor 
