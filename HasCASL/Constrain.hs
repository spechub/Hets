
{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003 
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  experimental
Portability :  portable 

constraint resolution

-}

module HasCASL.Constrain where

import HasCASL.Unify 
import HasCASL.As
import HasCASL.AsUtils
import HasCASL.Le
import HasCASL.TypeAna
import qualified Common.Lib.Set as Set
import Common.PrettyPrint
import Common.Lib.Pretty
import Common.Keywords
import Common.Id
import Common.Result

import Data.List
import Data.Maybe

data Constrain = Kinding Type Kind
               | Subtyping Type Type 
		 deriving (Eq, Ord, Show)

instance PrettyPrint Constrain where
    printText0 ga c = case c of 
       Kinding ty k -> printText0 ga ty <+> colon 
				      <+> printText0 ga k
       Subtyping t1 t2 -> printText0 ga t1 <+> text lessS
				      <+> printText0 ga t2

instance PosItem Constrain where
  get_pos c = Just $ case c of 
    Kinding ty _ -> posOfType ty
    Subtyping t1 t2 -> firstPos [t1, t2] []

type Constraints = Set.Set Constrain

noC :: Constraints
noC = Set.empty

joinC :: Constraints -> Constraints -> Constraints
joinC = Set.union

substC :: Subst -> Constraints -> Constraints
substC s = Set.image (\ c -> case c of
    Kinding ty k -> Kinding (subst s ty) k
    Subtyping t1 t2 -> Subtyping (subst s t1) $ subst s t2)

simplify :: TypeMap -> Constraints -> ([Diagnosis], Constraints)
simplify tm rs = 
    if Set.isEmpty rs then ([], Set.empty)
    else let (r, rt) = Set.deleteFindMin rs 
	     Result ds m = entail tm r
             (es, cs) = simplify tm rt
             in (ds ++ es, case m of
                                 Just _ -> cs
	                         Nothing -> Set.insert r cs)
   
entail :: Monad m => TypeMap -> Constrain -> m ()
entail tm p = 
    do is <- byInst tm p
       mapM_ (entail tm) $ Set.toList is

byInst :: Monad m => TypeMap -> Constrain -> m Constraints
byInst tm c = case c of 
    Kinding ty k -> case ty of 
      ExpandedType _ t -> byInst tm $ Kinding t k
      _ -> case k of
	   Intersection l _ -> if null l then return noC else
			  do pss <- mapM (\ ik -> byInst tm (Kinding ty ik)) l 
			     return $ Set.unions pss
	   ExtKind ek _ _ -> byInst tm (Kinding ty ek)
	   ClassKind _ _ -> let (topTy, args) = getTypeAppl tm ty in
	       case topTy of 
	       TypeName _ kind _ -> if null args then
		   if lesserKind tm kind k then return noC 
		         else fail $ expected k kind
		   else do 
		       let ks = getKindAppl kind args
		       newKs <- dom tm k ks 
		       return $ Set.fromList $ zipWith Kinding args newKs
	       _ -> error "byInst: unexpected Type" 
	   _ -> error "byInst: unexpected Kind" 
    Subtyping t1 t2 -> if lesserType tm t1 t2 then return noC
                       else fail ("unable to prove: " ++ showPretty t1 " < " 
                                  ++ showPretty t2 "")

maxKind :: TypeMap -> Kind -> Kind -> Maybe Kind
maxKind tm k1 k2 = if lesserKind tm k1 k2 then Just k1 else 
		if lesserKind tm k2 k1 then Just k2 else Nothing

maxKinds :: TypeMap -> [Kind] -> Maybe Kind
maxKinds tm l = case l of 
    [] -> Nothing
    [k] -> Just k
    [k1, k2] -> maxKind tm k1 k2
    k1 : k2 : ks -> case maxKind tm k1 k2 of 
          Just k -> maxKinds tm (k : ks)
	  Nothing -> do k <- maxKinds tm (k2 : ks)
			maxKind tm k1 k 

maxKindss :: TypeMap -> [[Kind]] -> Maybe [Kind]
maxKindss tm l = let margs = map (maxKinds tm) $ transpose l in
   if all isJust margs then Just $ map fromJust margs
      else Nothing

dom :: Monad m => TypeMap -> Kind -> [(Kind, [Kind])] -> m [Kind]
dom tm k ks = 
    let fks = filter ( \ (rk, _) -> lesserKind tm rk k ) ks 
	margs = maxKindss tm $ map snd fks
        in if null fks then fail ("class not found " ++ showPretty k "") 
           else case margs of 
	      Nothing -> fail "dom: maxKind"
	      Just args -> if any ((args ==) . snd) fks then return args
			   else fail "dom: not coregular"


