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
import HasCASL.Symbol
import HasCASL.MapTerm
import HasCASL.AsUtils

import Common.Id
import Common.Keywords
import Common.Result
import Common.PrettyPrint
import Common.Lib.Pretty
import qualified Common.Lib.Map as Map

type FunMap = Map.Map (Id, TySc) (Id, TySc)

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
	  ds = Map.foldWithKey ( \ (i, TySc s) (j, TySc t) l -> 
		(printText0 ga i <+> colon <+> printText0 ga s
		<+> text mapsTo	<+>	 
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
-- rename clashing type arguments later
mapTypeScheme = mapTypeOfScheme . mapType

mapTySc :: TypeMap -> IdMap -> TySc -> TySc
mapTySc tm im (TySc s1) = 
    TySc $ mapTypeOfScheme (expandAlias tm . mapType im) s1

mapSen :: Morphism -> Term -> Term
mapSen m = let im = typeIdMap m in 
       mapTerm (mapFunSym (typeMap $ mtarget m) im (funMap m), mapType im)

mapDataEntry :: Morphism -> DataEntry -> DataEntry
mapDataEntry m (DataEntry tm i k args alts) = 
    let tim = compIdMap tm $ typeIdMap m
    in DataEntry tim i k args $ map 
	   (mapAlt m tim args $ 
	    typeIdToType (Map.findWithDefault i i tim) 
	    args star) alts

mapAlt :: Morphism -> IdMap -> [TypeArg] -> Type -> AltDefn -> AltDefn
mapAlt m tm args dt c@(Construct mi ts p sels) = 
    case mi of
    Just i -> 
      let sc = TypeScheme args 
	     ([] :=> getConstrType dt p (map (mapType tm) ts)) []
	  (j, TypeScheme _ (_ :=> ty) _) = 
	      mapFunSym (typeMap $ mtarget m) (typeIdMap m) (funMap m) (i, sc)
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
	   f = mapFunSym (typeMap $ mtarget m) tm fm
	   (ni, nsc) = f (i, sc) 
	   in ProgEqSen ni nsc $ mapEq (f,  mapType tm) pe

mapFunSym :: TypeMap -> IdMap -> FunMap -> (Id, TypeScheme) -> (Id, TypeScheme)
mapFunSym tm im fm (i, sc) = 
    let (j, TySc s) = mapFunEntry tm im fm (i, TySc sc) in (j, s)

mapFunEntry :: TypeMap -> IdMap -> FunMap -> (Id, TySc) -> (Id, TySc)
mapFunEntry tm im fm p@(i, sc) = 
    if Map.isEmpty im && Map.isEmpty fm then p else 
    Map.findWithDefault (i, mapTySc tm im sc) (i, sc) fm

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

compMor :: Morphism -> Morphism -> Maybe Morphism
compMor m1 m2 = 
  if isSubEnv (mtarget m1) (msource m2) then 
      let tm2 = typeIdMap m2 
	  fm2 = funMap m2 in Just 
      (mkMorphism (msource m1) (mtarget m2))
      { classIdMap = compIdMap (classIdMap m1) $ classIdMap m2
      , typeIdMap = compIdMap (typeIdMap m1) tm2
      , funMap = Map.foldWithKey ( \ p1 p2 -> 
		       Map.insert p1
		       $ mapFunEntry (typeMap $ mtarget m2) 
				   tm2 fm2 p2) fm2 $ funMap m1
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
		         asSchemes 0 (equalSubs $ typeMap t) sc1 sc2  
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
                 (j, TySc t2) = mapFunEntry (typeMap tar) 
		     tm (funMap mor) (i, TySc ty)
             in	Map.insert (idToOpSymbol src i ty) 
                        (idToOpSymbol tar j t2)) m l) 
         typeSymMap $ assumps src
