
{- HetCATS/HasCASL/ClassAna.hs
   $Id$
   Authors: Christian Maeder
   Year:    2003
   
   analyse given classes
-}

module HasCASL.ClassAna where

import HasCASL.As
import HasCASL.AsUtils
import Common.Id
import HasCASL.Le
import Data.List
import Data.Maybe
import Control.Monad.State
import HasCASL.PrintAs(showPretty)
import Common.PrettyPrint
import qualified Common.Lib.Map as Map
import Common.Result

mkDiag :: (PosItem a, PrettyPrint a) => DiagKind -> String -> a -> Diagnosis
mkDiag k s a =
    Diag k (s ++ " '" ++ showPretty a "'") $
		 case get_pos a of 
		 Nothing -> nullPos
		 Just p -> p

-- ---------------------------------------------------------------------------
-- analyse class
-- ---------------------------------------------------------------------------

-- transitiv super classes 
-- PRE: all superclasses and defns must be defined in ClassEnv
-- and there must be no cycle!
allSuperClasses :: ClassMap -> ClassId -> [ClassId]
allSuperClasses ce ci = 
    let recurse = nub . concatMap (allSuperClasses ce) in
    case Map.lookup ci ce of 
    Just info -> nub $ (case classDefn info of 
			Nothing -> [ci]
			Just (Intersection cis _) -> recurse cis
			Just _ -> [ci])
		 ++ recurse (superClasses info)
    Nothing -> error "allSuperClasses"

anaClassId :: ClassMap -> ClassId -> Maybe Kind
anaClassId cMap ci = 
       case Map.lookup ci cMap of
       Nothing -> Nothing
       Just i -> Just $ classKind i

anaClass :: Class -> State Env (Kind, Class)
anaClass (Intersection cs ps) =  
    do cMap <- getClassMap
       let l = zip (map (anaClassId cMap) cs) cs
	   (js, ns) = partition (isJust . fst) l
	   ds = map (mkDiag Error "undeclared class" . snd) ns
	   restCs = map snd js
	   ks = map (fromJust. fst) js
	   k = if null ks then star else fromJust $ fst $ head js
	   es = filter (not . eqKind Compatible k . fromJust . fst) js
	   fs =	map (\ (Just wk, i) -> mkDiag Error 
		     ("wrong kind '" ++ showPretty wk "' of")
		     i) es
       appendDiags (ds ++ fs) 
       return (k, Intersection restCs ps) 

anaClass (Downset t) = 
    do downsetWarning t
       return $ (star, Downset t)

downsetWarning :: Type -> State Env ()
downsetWarning t = 
    addDiag $ mkDiag Warning "unchecked type" t

-- ----------------------------------------------------------------------------
-- analyse kind
-- ----------------------------------------------------------------------------

anaKind :: Kind -> State Env Kind
anaKind (KindAppl k1 k2 p) = 
    do k3 <- anaKind k1
       k4 <- anaKind k2
       return $ KindAppl k3 k4 p
anaKind (ExtClass k v p) = 
    do (k1, c) <- anaClass k
       return $ case k1 of 
			ExtClass _ _ _ -> ExtClass c v p
			_ -> k1

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
eqKind emod (ExtClass c1 v1 _) (ExtClass c2 v2 _) = 
    v1 == v2 && 
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


