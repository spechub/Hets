
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

anaClassId :: ClassMap -> ClassId -> Maybe Kind
anaClassId cMap ci = 
       case Map.lookup ci cMap of
       Nothing -> Nothing
       Just i -> Just $ classKind i

expandKind :: ClassMap -> Kind -> Kind
expandKind cMap (ExtClass c _ _) = 
    case c of
    Intersection s _ ->
	if Set.isEmpty s then star else 
	case anaClassId cMap $ Set.findMin s of
	    Just k -> expandKind cMap k
	    _ -> error "expandKind"
    _ -> star

expandKind cMap (KindAppl k1 k2 ps) = 
    KindAppl (expandKind cMap k1) (expandKind cMap k2) ps
    
anaClass :: Class -> ReadR ClassMap (Kind, Class)
anaClass (Intersection s ps) =
    do cMap <- ask
       let cs = Set.toList s
	   l = zip (map (anaClassId cMap) cs) cs
	   (js, ns) = partition (isJust . fst) l
	   ds = map (mkDiag Error "undeclared class" . snd) ns
	   restCs = Set.fromList $ map snd js
	   ks = map (fromJust. fst) js
	   k = if null ks then star else expandKind cMap $ 
	       fromJust $ fst $ head js
	   es = filter (not . eqKind k . expandKind cMap . 
			fromJust . fst) js
	   fs =	map (\ (Just wk, i) -> mkDiag Error 
		     ("wrong kind '" ++ showPretty wk "' of")
		     i) es
       lift $ Result (ds ++ fs) $ Just (k, Intersection restCs ps) 

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

checkKinds :: ClassMap -> Pos -> Kind -> Kind -> [Diagnosis]
checkKinds cMap p k1 k2 =
       eqKindDiag p (expandKind cMap k1) 
		   $ expandKind cMap k2

eqKindDiag :: Pos -> Kind -> Kind -> [Diagnosis]
eqKindDiag p k1 k2 = 
    if eqKind k1 k2 then []
       else [ Diag Error
	      ("incompatible kinds\n" ++ 
	       indent 2 (showPretty k1 . 
			 showChar '\n' .  
			 showPretty k2) "")
	    $ p ]


eqKind :: Kind -> Kind -> Bool
eqKind (KindAppl p1 c1 _) (KindAppl p2 c2 _) =
    eqKind p1 p2 && eqKind c1 c2
eqKind (ExtClass _ _ _) (ExtClass _ _ _) = True
eqKind _ _ = False

-- ---------------------------------------------------------------------


