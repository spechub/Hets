
{- HetCATS/HasCASL/ClassAna.hs
   $Id$
   Authors: Christian Maeder
   Year:    2003
   
   analyse given classes
-}

module ClassAna where

import As
import AsUtils
import Id
import Le
import List
import Maybe
import MonadState
import PrintAs(showPretty)
import FiniteMap
import Result

-- ---------------------------------------------------------------------------
-- analyse class
-- ---------------------------------------------------------------------------

-- transitiv super classes 
-- PRE: all superclasses and defns must be defined in ClassEnv
-- and there must be no cycle!
allSuperClasses :: ClassMap -> ClassId -> [ClassId]
allSuperClasses ce ci = 
    let recurse = nub . concatMap (allSuperClasses ce) in
    case lookupFM ce ci of 
    Just info -> nub $ (case classDefn info of 
			Nothing -> [ci]
			Just (Intersection cis _) -> recurse cis
			Just _ -> [ci])
		 ++ recurse (superClasses info)
    Nothing -> error "allSuperClasses"

anaClassId :: ClassMap -> ClassId -> [Diagnosis]
anaClassId cMap ci = 
       case lookupFM cMap ci of
       Nothing -> [Diag Error ("undeclared class '" ++ showId ci "'")
		  $ posOfId ci]
       _ -> []

anaClass :: Class -> State Env Class
anaClass (Intersection cs ps) =  
    do cMap <- getClassMap
       let l = zip (map (anaClassId cMap) cs) cs
	   restCs = map snd $ filter (\ (x, _) -> null x) l  
	   ds = concatMap fst l 
       appendDiags ds 
       return $ Intersection restCs ps 

anaClass (Downset t) = 
    do downsetWarning t
       return $ Downset t

downsetWarning :: Type -> State Env ()
downsetWarning t = 
    appendDiags [Diag Warning ("unchecked type: " ++ showPretty t "")
			       $ posOfType t]

-- ----------------------------------------------------------------------------
-- analyse kind
-- ----------------------------------------------------------------------------

anaKind :: Kind -> State Env Kind
anaKind (KindAppl k1 k2 p) = 
    do k3 <- anaKind k1
       k4 <- anaKind k2
       return $ KindAppl k3 k4 p
anaKind (ProdClass l p) =
    do cs <- mapM anaKind l
       return $ ProdClass cs p
anaKind (ExtClass k v p) = 
    do k1 <- anaKind k
       return $ ExtClass k1 v p
anaKind (PlainClass c) = 
    do c1 <- anaClass c
       return $ PlainClass c1

-- ---------------------------------------------------------------------------
-- analyse type
-- ---------------------------------------------------------------------------

eqKindDiag :: Kind -> Kind -> [Diagnosis]
eqKindDiag k1 k2 = 
    if eqKind Compatible k1 k2 then []
       else [ Diag Error
	      ("incompatible kinds\n" ++ 
	       indent 2 (showPretty k1 . 
			 showChar '\n' .  
			 showPretty k2) "")
	    $ posOfKind k1 ]

-- ---------------------------------------------------------------------
-- comparing kinds 
-- ---------------------------------------------------------------------

data EqMode = Compatible | SameSyntax

eqKind :: EqMode -> Kind -> Kind -> Bool
eqKind emod (KindAppl p1 c1 _) (KindAppl p2 c2 _) =
    eqKind emod p1 p2 && eqKind emod c1 c2
eqKind emod (ProdClass s1 _) (ProdClass s2 _) =
    eqListBy (eqKind emod) s1 s2
eqKind emod (ExtClass c1 v1 _) (ExtClass c2 v2 _) = 
    eqKind emod c1 c2 && 
	   case emod of Compatible -> True
			SameSyntax -> v1 == v2
eqKind emod (PlainClass c1) (PlainClass c2) = 
	   case emod of Compatible -> True
			SameSyntax -> eqClass c1 c2

eqKind _ _ _ = False

eqListBy :: (a -> a -> Bool) -> [a] -> [a] -> Bool
eqListBy _ [] [] = True
eqListBy f (h1:t1) (h2:t2) = f h1 h2 && eqListBy f t1 t2
eqListBy _ _ _ = False

eqClass :: Class -> Class -> Bool
eqClass(Intersection i1 _) (Intersection i2 _) = i1 == i2
eqClass (Downset t1) (Downset t2) = t1 == t2
eqClass _ _ = False

-- ---------------------------------------------------------------------


