{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  portable 

   auxiliary functions for raw kinds
-}

module HasCASL.ClassAna where

import HasCASL.As
import HasCASL.AsUtils
import Common.Id
import HasCASL.Le
import Data.List
import Data.Maybe
import Common.PrettyPrint
import qualified Common.Lib.Map as Map
import Common.Lib.State
import Common.Result

anaClassId :: ClassId -> State Env (Maybe Kind)
anaClassId ci = 
    do cMap <- gets classMap
       case Map.lookup ci cMap of
	    Nothing -> do addDiags [mkDiag Error "undeclared class" ci]
			  return Nothing
	    Just (ClassInfo l) ->  return $ Just $ ClassKind ci $ 
				   toIntersection l

toIntersection :: [Kind] -> Kind
toIntersection l = case mkIntersection l of
			  [] -> star
			  [h] -> h
			  is -> Intersection is []

mkIntersection :: [Kind] -> [Kind]
mkIntersection = delete star . nub .
		     concatMap ( \ k -> case k of
				 Intersection lk _ -> mkIntersection lk
			         _ -> [k]) 

rawKind :: Kind -> Kind
rawKind c = 
    case c of
    Universe _ -> c
    MissingKind -> error "rawKind1"
    ClassKind _ rk -> rawKind rk
    Downset _ _ rk _ -> rawKind rk
    Intersection l _ -> if null l then error "rawKind2"
					      else rawKind $ head l
    FunKind e k ps  -> FunKind (rawKind e) (rawKind k) ps
    ExtKind k InVar _ -> rawKind k
    ExtKind k v ps -> ExtKind (rawKind k) v ps 

checkIntersection :: Kind -> [Kind] -> [Diagnosis]
checkIntersection _ [] = []
checkIntersection k (f:r) = 
	case k == rawKind f of 
	False -> 
	      Diag Error ("incompatible kind of: " ++ showPretty f "" 
		++  "\n  for raw kind: " ++ showPretty k "")
	      (posOf [f]) : checkIntersection k r
	True -> checkIntersection k r

diffKindDiag :: (PosItem a, PrettyPrint a) => 
		 a -> Kind -> Kind -> [Diagnosis]
diffKindDiag a k1 k2 = 
           [ Diag Error
	      ("incompatible kind of: " ++ showPretty a "" ++ expected k1 k2)
	    $ posOf [a] ]

minKind :: Bool -> Kind -> Kind -> Maybe Kind
minKind b k1 k2 = 
    case k1 of 
	    FunKind ek1 k3 ps -> 
		case k2 of
			FunKind ek2 k4 qs ->
			    do ek <- minKind (not b) ek1 ek2
			       k <- minKind b k3 k4 
			       return $ FunKind ek k (ps++qs)
		        ExtKind _ _ _ -> minKind b (ExtKind k1 InVar []) k2
			_ -> Nothing
	    Universe ps -> case k2 of
			 Universe qs -> Just $ Universe (ps ++ qs)
		         ExtKind _ _ _ -> minKind b (ExtKind k1 InVar []) k2
			 _ -> Nothing
	    ExtKind k3 v1 ps -> case k2 of
	         ExtKind k4 v2 qs -> do 
		       k <- minKind b k3 k4
		       v <- (if b then minVar else maxVar) v1 v2
		       return $ ExtKind k v (ps ++ qs)
		 _ -> minKind b k1 (ExtKind k2 InVar [])
	    _ -> error "minKind"

maxVar, minVar :: Variance -> Variance -> Maybe Variance
maxVar v InVar = Just v
maxVar InVar v = Just v
maxVar v1 v2 = if v1 == v2 then Just v1 else Nothing

minVar v1 v2 = if v1 == v2 then Just v1 else Just InVar

checkKinds :: (PosItem a, PrettyPrint a) => 
              a -> Kind -> Kind -> State Env ()
checkKinds p k1 k2 =
    do let k3 = rawKind k1
           k4 = rawKind k2
       if k3 == k4 then return ()
	  else addDiags $ diffKindDiag p k1 k2

cyclicClassId :: ClassId -> Kind -> Bool
cyclicClassId ci k =
    case k of
	   FunKind k1 k2 _ -> cyclicClassId ci k1 || cyclicClassId ci k2
	   ExtKind ek _ _ -> cyclicClassId ci ek
	   ClassKind cj ck -> cj == ci || cyclicClassId ci ck
	   Downset _ _ dk _ -> cyclicClassId ci dk
	   Intersection l _ -> any (cyclicClassId ci) l
	   _ -> False
