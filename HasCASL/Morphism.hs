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
import HasCASL.PrintLe
import HasCASL.Unify
import HasCASL.Symbol
import HasCASL.MapTerm
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
mapType m = rename ( \ i k n ->
	       let t = TypeName i k n in
	       if n == 0 then 
		  case Map.lookup i m of
		  Just j -> TypeName j k 0
		  _ -> t
	       else t)

mapTypeScheme :: IdMap -> TypeScheme -> TypeScheme
-- rename clashing type arguments later
mapTypeScheme = mapTypeOfScheme . mapType

mapTySc :: IdMap -> TySc -> TySc
mapTySc m (TySc s1) = TySc $ mapTypeScheme m s1

mapSen :: Morphism -> Term -> Result Term
mapSen m = let tm = typeIdMap m in 
       return . mapTerm (mapFunSym tm (funMap m), mapType tm)

-- mapAlt :: Morphism -> AltDefn -> AltDefn
-- mapAlt m c@(Construct _i _ts _p _sels) = c -- missing
--      (Map.findWithDefault t t $ typeIdMap m) k args $ map (mapAlt m) alts

mapSentence :: Morphism -> Sentence -> Result Sentence
mapSentence m s = case s of 
   Formula t -> fmap Formula $ mapSen m t 
   DatatypeSen td -> return $ DatatypeSen td
   ProgEqSen i sc pe ->
       let tm = typeIdMap m 
	   fm = funMap m 
	   f = mapFunSym tm fm
	   (ni, nsc) = f (i, sc) 
	   in return $ ProgEqSen ni sc $ mapEq (f,  mapType tm) pe

mapFunSym :: IdMap -> FunMap -> (Id, TypeScheme) -> (Id, TypeScheme)
mapFunSym tm fm (i, sc) =  
    let (i2, TySc sc2) = Map.findWithDefault 
			 (i, TySc $ mapTypeScheme tm sc)
			 (i, TySc sc) fm
	in (i2, sc2)

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
