
{- HetCATS/HasCASL/ClassAna.hs
   $Id$
   Authors: Christian Maeder
   Year:    2003
   
   analyse given classes
-}

module HasCASL.ClassAna where

import HasCASL.As
import HasCASL.AsUtils()
import Common.Id
import HasCASL.Le
import Data.List
import Data.Maybe
import HasCASL.PrintAs()
import Common.PrettyPrint
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import Common.Result
import HasCASL.Reader

-- ---------------------------------------------------------------------------
-- analyse class
-- ---------------------------------------------------------------------------

-- transitiv super classes 
-- PRE: all superclasses and defns must be defined in ClassEnv
-- and there must be no cycle!
allSuperClasses :: ClassMap -> ClassId -> Set.Set ClassId
allSuperClasses ce ci = 
    let recurse = Set.unions . map (allSuperClasses ce) in
    case Map.lookup ci ce of 
    Just info -> (case classDefn info of 
                        Just (Intersection cis _) -> recurse $ Set.toList cis
                        _ -> Set.single ci)
                 `Set.union` recurse (Set.toList $ superClasses info)
    Nothing -> error "allSuperClasses"

anaClassId :: ClassId -> ReadR ClassMap Kind
anaClassId ci = 
    do cMap <- ask
       case Map.lookup ci cMap of
	    Nothing -> lift $ Result [mkDiag Error "undeclared class" ci]
		       Nothing
	    Just i -> return $ classKind i

expandKind :: Kind -> ReadR ClassMap Kind
expandKind (ExtClass c _ _) = 
    case c of
    Intersection s _ ->
	if Set.isEmpty s then return star else 
	   anaClassId $ Set.findMin s
    _ -> return star

expandKind (KindAppl k1 k2 ps) = 
    do k3 <- expandKind k1
       k4 <- expandKind k2
       return $ KindAppl k3 k4 ps
    
anaClass :: Class -> ReadR ClassMap (Kind, Class)
anaClass (Intersection s ps) =
    do l <- foldReadR ( \ ci -> fmap ( \ ki -> (ki, ci) ) 
			$ anaClassId ci) $ Set.toList s
       let (ks, restCs) = unzip l
	   k = if null ks then star else head ks
       foldReadR ( \ (ki, ci) -> 
			 checkKinds (posOfId ci) k ki) l
       return (k, Intersection (Set.fromList restCs) ps)

anaClass (Downset t) = 
    lift $ Result [downsetWarning t] $ Just (star, Downset t)

downsetWarning :: Type -> Diagnosis
downsetWarning t = mkDiag Warning "unchecked type" t

-- ----------------------------------------------------------------------------
-- analyse kind
-- ----------------------------------------------------------------------------

anaKind :: Kind -> ReadR ClassMap Kind
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

checkKinds :: Pos -> Kind -> Kind -> ReadR ClassMap ()
checkKinds p k1 k2 =
    do k3 <- expandKind k1
       k4 <- expandKind k2
       lift $ Result (eqKindDiag p k3 k4) $ Just ()

eqKindDiag :: Pos -> Kind -> Kind -> [Diagnosis]
eqKindDiag p k1 k2 = 
    if eqKind k1 k2 then []
       else [ Diag Error
	      (indent 2 (showString "incompatible kinds\n" .
			 showPretty k1 . 
			 showChar '\n' .  
			 showPretty k2) "")
	    $ p ]

indent :: Int -> ShowS -> ShowS
indent i s = showString $ concat $ 
	     intersperse ('\n' : replicate i ' ') (lines $ s "")

eqKind :: Kind -> Kind -> Bool
eqKind (KindAppl p1 c1 _) (KindAppl p2 c2 _) =
    eqKind p1 p2 && eqKind c1 c2
eqKind (ExtClass _ _ _) (ExtClass _ _ _) = True
eqKind _ _ = False

-- ---------------------------------------------------------------------


