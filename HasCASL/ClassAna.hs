{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  portable 

   analyse given classes
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
import qualified Common.Lib.Set as Set
import Common.Lib.State
import Common.Result

-- ---------------------------------------------------------------------------
-- analyse class
-- ---------------------------------------------------------------------------

-- transitiv super classes 
-- PRE: all superclasses and defns must be defined in ClassEnv
-- and there must be no cycle!

-- | get all superclass ids 
allSuperClasses :: ClassMap -> ClassId -> Set.Set ClassId
allSuperClasses ce ci = 
    let recurse = Set.unions . map (allSuperClasses ce) in
    case Map.lookup ci ce of 
    Just info -> (case classDefn info of 
                        Just (Intersection cis _) -> recurse $ Set.toList cis
                        _ -> Set.single ci)
                 `Set.union` recurse (Set.toList $ superClasses info)
    Nothing -> error "allSuperClasses"

anaClassId :: ClassId -> State Env (Maybe Kind)
anaClassId ci = 
    do cMap <- gets classMap
       case Map.lookup ci cMap of
	    Nothing -> do addDiags [mkDiag Error "undeclared class" ci]
			  return Nothing
	    Just i -> return $ Just $ classKind i

expandKind :: Kind -> State Env Kind
expandKind (ExtClass c _ _) = 
    case c of
    Intersection s _ ->
	if Set.isEmpty s then return star else
	   do mk <- anaClassId $ Set.findMin s
	      case mk of
	           Just k -> return k
		   _ -> error "expandKind"
    _ -> return star

expandKind (KindAppl k1 k2 ps) = 
    do k3 <- expandKind k1
       k4 <- expandKind k2
       return $ KindAppl k3 k4 ps
    
anaClass :: Class -> State Env (Kind, Class)
anaClass ic@(Intersection s ps) =
    do l <- mapM ( \ ci -> do mki <- anaClassId ci
		              case mki of 
		                   Nothing -> return []
		                   Just ki -> return [(ki, ci)]
		 ) $ Set.toList s
       let (ks, restCs) = unzip (concat l)
	   k = if null ks then star else head ks
       mapM ( \ ki -> 
			 checkKinds ic k ki) ks
       return (k, Intersection (Set.fromList restCs) ps)

anaClass (Downset t) = 
    do addDiags [downsetWarning t] 
       return (star, Downset t)

downsetWarning :: Type -> Diagnosis
downsetWarning t = mkDiag Warning "unchecked type" t

-- ---------------------------------------------------------------------------
-- analyse kind
-- ---------------------------------------------------------------------------

anaKind :: Kind -> State Env Kind
anaKind (KindAppl k1 k2 p) = 
    do k1e <- anaKind k1 
       k2e <- anaKind k2
       return $ KindAppl k1e k2e p
anaKind (ExtClass k v p) = 
    do (_, c) <- anaClass k
       return $ ExtClass c v p

-- ---------------------------------------------------------------------
-- comparing kinds 
-- ---------------------------------------------------------------------

checkKinds :: (PosItem a, PrettyPrint a) => 
	      a -> Kind -> Kind -> State Env ()
checkKinds p k1 k2 =
    do k3 <- expandKind k1
       k4 <- expandKind k2
       addDiags (eqKindDiag p k3 k4)
       return ()

eqKindDiag :: (PosItem a, PrettyPrint a) => a -> Kind -> Kind -> [Diagnosis]
eqKindDiag a k1 k2 = 
    if eqKind k1 k2 then []
       else [ Diag Error
	      ("incompatible kind of: " ++ showPretty a "" ++ expected k1 k2)
	    $ posOf [a] ]

indent :: Int -> ShowS -> ShowS
indent i s = showString $ concat $ 
	     intersperse ('\n' : replicate i ' ') (lines $ s "")

eqKind :: Kind -> Kind -> Bool
eqKind (KindAppl p1 c1 _) (KindAppl p2 c2 _) =
    eqKind p1 p2 && eqKind c1 c2
eqKind (ExtClass _ _ _) (ExtClass _ _ _) = True
eqKind _ _ = False

-- ---------------------------------------------------------------------
