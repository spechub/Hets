{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  portable 

   analyse classes and types
-}

module HasCASL.TypeAna where

import HasCASL.As
import HasCASL.AsUtils
import HasCASL.ClassAna
import HasCASL.Le
import HasCASL.Unify
import Data.List
import Data.Maybe
import qualified Common.Lib.Map as Map
import Common.Id
import Common.Result
import Common.Lib.State
import Common.PrettyPrint

-- --------------------------------------------------------------------------
-- kind analysis
-- --------------------------------------------------------------------------

toKind :: Maybe Kind -> Kind 
toKind mk = case mk of Nothing -> star
		       Just k -> k

anaKind :: Kind -> State Env Kind
anaKind k = fmap toKind (anaKindM k)

anaKindM :: Kind -> State Env (Maybe Kind)
anaKindM k = 
    case k of
    Universe _  -> return (Just k)
    MissingKind -> return Nothing
    Downset v t _ ps -> do (rk, mt) <- anaType (Nothing, t) 
			   case mt of
				  Nothing -> return Nothing
				  Just newT -> return $ Just $ 
					       Downset v newT rk ps
    ClassKind ci _ -> anaClassId ci
    Intersection ks ps -> do mks <- mapM anaKindM ks
			     let newKs = mkIntersection $ catMaybes mks 
                             if null newKs then return Nothing
			        else let ds = checkIntersection 
						 (rawKind $ head newKs)
						 $ tail newKs
				     in if null ds then 
					return $ Just $ if isSingle newKs 
					       then head newKs 
					       else Intersection newKs ps
					else do addDiags ds
						return Nothing
    FunKind k1 k2 ps -> do m1 <- anaKindM k1
			   m2 <- anaKindM k2 
			   return $ do k3 <- m1
				       k4 <- m2
				       return $ FunKind k3 k4 ps
    ExtKind ek v ps -> do m <- anaKindM ek
			  return $ do nk <- m
				      return $ ExtKind nk v ps

data ApplMode = OnlyArg | TopLevel 

mkTypeConstrAppls :: ApplMode -> Type -> State Env (Maybe Type)
mkTypeConstrAppls _ t@(TypeName _ _ _) = 
       return $ Just t 

mkTypeConstrAppls m (TypeAppl t1 t2) = 
    do mt3 <- mkTypeConstrAppls m t1
       mt4 <- mkTypeConstrAppls OnlyArg t2
       case (mt3, mt4) of
           (Just t3, Just t4) -> return $ Just $ TypeAppl t3 t4 
	   _ -> return Nothing

mkTypeConstrAppls _ (TypeToken t) = 
    do let i = simpleIdToId t
       tk <- gets typeMap
       let m = getKind tk i
	   c = if isTypeVar tk i then 1 else 0
       case m of 
	      Just k -> return $ Just $ TypeName i k c 
	      _ -> do addDiags [mkDiag Error "unknown type" t]
		      return Nothing

mkTypeConstrAppls m t@(BracketType b ts ps) =
    do mArgs <- mapM (mkTypeConstrAppls m) ts
       if all isJust mArgs then 
	  do let err = do addDiags [mkDiag Error "illegal type" t]
			  return Nothing 
	     case catMaybes mArgs of 
	          [x] -> case b of
		         Parens -> return $ Just x 		
			 _ -> do let [o,c] = mkBracketToken b ps 
				     i = Id [o, Token place $ posOfType 
					    $ head ts, c] [] []
				 tk <- gets typeMap
				 case getKind tk i of
				     Nothing -> err
				     Just k -> return $ Just $ TypeAppl 
					       (TypeName i k 0) x 
		  _ -> err
          else return Nothing

mkTypeConstrAppls _ (MixfixType []) = error "mkTypeConstrAppl (MixfixType [])"
mkTypeConstrAppls _ (MixfixType (f:a)) =
   do mF <- mkTypeConstrAppls TopLevel f 
      case mF of
          Nothing -> return Nothing
	  Just newF -> 
	      do mA <- mapM (mkTypeConstrAppls OnlyArg) a
		 if all isJust mA then
		    return $ Just $ foldl1 TypeAppl $ newF : catMaybes mA
		    else return Nothing

mkTypeConstrAppls m (KindedType t k p) =
    do mT <- mkTypeConstrAppls m t
       return $ fmap ( \ newT -> KindedType newT k p ) mT

mkTypeConstrAppls _ (LazyType t p) =
    do mT <- mkTypeConstrAppls TopLevel t
       return $ fmap ( \ newT -> LazyType newT p ) mT

mkTypeConstrAppls _ (ProductType ts ps) =
    do mTs <- mapM (mkTypeConstrAppls TopLevel) ts
       if all isJust mTs then
	  return $ Just $ mkProductType (catMaybes mTs) ps
	  else return Nothing

mkTypeConstrAppls _ (FunType t1 a t2 ps) =
    do mT1 <- mkTypeConstrAppls TopLevel t1
       mT2 <- mkTypeConstrAppls TopLevel t2
       case (mT1, mT2) of 
           (Just newT1, Just newT2) -> 
	       return $ Just $ FunType newT1 a newT2 ps
	   _ -> return Nothing

-- ---------------------------------------------------------------------------
-- compare kinds
-- ---------------------------------------------------------------------------

lesserKind :: Kind -> Kind -> Bool
lesserKind k1 k2 = 
    case (k1, k2) of 
    (MissingKind, _) -> error "lesserKind1"
    (_, MissingKind) -> error "lesserKind2"
    (_, Intersection l2 _) -> and $ map (lesserKind k1) l2
    (Intersection l1 _, _) -> or $ map ( \ k -> lesserKind k k2) l1
    (ExtKind ek1 v1 _, ExtKind ek2 v2 _) -> 
	(v1 == InVar || v1 == v2) && lesserKind ek1 ek2
    (_, ExtKind ek2 _ _) -> lesserKind k1 ek2
    (ExtKind ek1 v1 _, _) -> v1 == InVar && lesserKind ek1 k2
    (Universe _, Universe _) -> True
    (Universe _, _) -> False
    (Downset _ t1 k _,  Downset _ t2 _ _) -> t1 == t2 || lesserKind k k2
    (Downset _ _ k _, _) -> lesserKind k k2
    (ClassKind c1 k,  ClassKind c2 _) -> c1 == c2 || lesserKind k k2
    (ClassKind _ k, _) -> lesserKind k k2
    (FunKind ek rk _, FunKind ek2 rk2 _) -> 
	lesserKind rk rk2 && lesserKind ek2 ek
    (FunKind _ _ _, _) -> False

-- ---------------------------------------------------------------------------
-- infer raw kind
-- ---------------------------------------------------------------------------

inferRawKind :: Type -> State Env Kind
inferRawKind (TypeName i _ _) = getIdRawKind i

inferRawKind (TypeAppl t1 t2) = 
    do k1 <- inferRawKind t1 
       case k1 of
	       FunKind fk ak _ -> do checkTypeRawKind t2 fk
				     return ak
	       _ -> do addDiags [mkDiag Error 
				 "incompatible kind of type" t1] 
		       return k1

inferRawKind (FunType t1 _ t2 _) = 
    do checkTypeRawKind t1 star 
       checkTypeRawKind t2 star
       return star 
inferRawKind (ProductType ts _) = 
    do mapM_ ( \ t -> checkTypeRawKind t star) ts 
       return star 
inferRawKind (LazyType t _) = 
    do checkTypeRawKind t star
       return star 
inferRawKind (TypeToken t) = getIdRawKind $ simpleIdToId t
inferRawKind (KindedType t k _) =
    do checkTypeRawKind t k
       return k
inferRawKind t =
    do addDiags [mkDiag Error "unresolved type" t] 
       return star

checkTypeRawKind :: Type -> Kind -> State Env ()
checkTypeRawKind t j = 
    case j of 
    ExtKind ek _ _ -> checkTypeRawKind t ek
    _ -> do k <- inferRawKind t
	    if k == j then return () else addDiags $ diffKindDiag t j k

getIdRawKind :: Id -> State Env Kind
getIdRawKind i = 
    do tk <- gets typeMap
       let m = getRawKind tk i
       case m of
	    Nothing -> do addDiags [mkDiag Error "undeclared type" i]
			  return star
	    Just k -> return k

getRawKind :: TypeMap -> Id -> Maybe Kind
getRawKind tk i = 
       case Map.lookup i tk of
       Nothing -> Nothing
       Just (TypeInfo k _ _ _) -> Just k

-- ---------------------------------------------------------------------------
-- infer kind
-- ---------------------------------------------------------------------------

checkMaybeKinds :: (PosItem a, PrettyPrint a) => 
              a -> Maybe Kind -> Maybe Kind -> State Env (Maybe Kind)
checkMaybeKinds a mk1 mk2 =
    case mk1 of
           Nothing -> return mk2
	   Just k1 -> case mk2 of 
	       Nothing -> return mk1
	       Just k2 -> 
		   if lesserKind k1 k2 then return mk1
		      else if lesserKind k2 k1 then return mk2
		      else do addDiags $ diffKindDiag a k1 k2
			      return Nothing

checkFunKind :: Maybe Kind -> Type -> Type -> Kind -> State Env (Maybe Kind)
checkFunKind mk t1 t2 k1 = 
    case k1 of 
	FunKind fk ak _ -> do 
	    mk2 <- inferKind (Just fk) t2
	    case mk2 of 
		Nothing -> return mk
		Just _ -> checkMaybeKinds (TypeAppl t1 t2) mk (Just ak)
	Intersection l ps -> do
	    ml <- mapM (checkFunKind mk t1 t2) l
	    let ks = mkIntersection $ catMaybes ml
	    return $ if null ks then Nothing else if isSingle ks then
	       Just $ head ks else Just $ Intersection ks ps
	ClassKind _ k -> checkFunKind mk t1 t2 k
	Downset _ _ k _ -> checkFunKind mk t1 t2 k
	ExtKind k _ _ -> checkFunKind mk t1 t2 k
	_ -> do addDiags [mkDiag Error 
				 "unexpected type argument" t2]
	        return Nothing

inferKind :: Maybe Kind -> Type -> State Env (Maybe Kind)
inferKind mk (TypeName i _ _) = 
    do m <- getIdKind i 
       checkMaybeKinds i mk m

inferKind mk (TypeAppl t1 t2) = 
    do mk1 <- inferKind Nothing t1 
       case mk1 of 
	   Nothing -> return mk
	   Just k1 -> checkFunKind mk t1 t2 k1

inferKind mk (FunType t1 a t2 _) = 
    do let i = arrowId a
       mfk <- getIdKind i
       let fk = case mfk of Nothing -> funKind
			    Just k -> k
           tn = TypeName i fk 0
       inferKind mk (TypeAppl (TypeAppl tn t1) t2)

inferKind mk t@(ProductType ts _) = 
    if null ts then checkMaybeKinds t mk (Just star)
    else do mpk <- getIdKind productId
	    let pk = case mpk of Nothing -> prodKind
				 Just k -> k
		tn = TypeName productId pk 0
		mkAppl [t1] = t1
		mkAppl (t1:tr) = TypeAppl (TypeAppl tn t1) $ mkAppl tr
		mkAppl [] = error "inferKind: mkAppl"
            inferKind mk $ mkAppl ts
inferKind mk (LazyType t _) = 
    do inferKind mk t
inferKind mk (KindedType t k _) =
    do mk2 <- inferKind (Just k) t
       checkMaybeKinds t mk mk2
inferKind _ t =
    do addDiags [mkDiag Error "unresolved type" t] 
       return Nothing

getIdKind :: Id -> State Env (Maybe Kind)
getIdKind i = 
    do tk <- gets typeMap
       let m = getKind tk i 
       case m of
	    Nothing -> do addDiags [mkDiag Error "undeclared type" i]
	    Just _ -> return ()
       return m

getKind :: TypeMap -> Id -> Maybe Kind
getKind tk i = 
       case Map.lookup i tk of
       Nothing -> Nothing
       Just (TypeInfo _ l _ _) -> Just $  
	   if null l then Universe [] else 
	      if isSingle l then head l else Intersection l []

-- ---------------------------------------------------------------------------
isTypeVar :: TypeMap -> Id -> Bool
isTypeVar tk i = 
       case Map.lookup i tk of
       Just (TypeInfo _ _ _ TypeVarDefn) -> True
       _ -> False

anaType :: (Maybe Kind, Type) -> State Env (Kind, Maybe Type)
anaType (mk, t) = 
    do mT <- mkTypeConstrAppls TopLevel t
       tm <- gets typeMap
       case mT of 
            Nothing -> return (star, mT)
	    Just nt -> do let (newT,_) = expandAlias tm nt
			  newMk <- inferKind mk newT 
			  return (case newMk of 
				 Nothing -> star
				 Just aK -> aK, Just newT)

anaStarType :: Type -> State Env (Maybe Type)
anaStarType t = fmap snd $ anaType (Just star, t)

mkBracketToken :: BracketKind -> [Pos] -> [Token]
mkBracketToken k ps = 
    if null ps then mkBracketToken k [nullPos]
       else zipWith Token ((\ (o,c) -> [o,c]) $ getBrackets k) 
		[head ps, last ps] 


