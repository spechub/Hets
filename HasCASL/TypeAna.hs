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
import Common.PrettyPrint

-- --------------------------------------------------------------------------
-- kind analysis
-- --------------------------------------------------------------------------

anaKindM :: Kind -> Env -> Result Kind
anaKindM k env = 
    case k of
    MissingKind -> mkError "missing kind" k
    Downset v t _ ps -> do (rk, newT) <- anaType (Nothing, t) (typeMap env)
			   return $ Downset v newT rk ps
    ClassKind ci _ -> anaClassId ci (classMap env)
    Intersection ks ps -> do newKs <- mapM ( \ ek -> anaKindM ek env) ks
                             if null newKs then return k
			        else let ds = checkIntersection 
						 (rawKind $ head newKs)
						 $ tail newKs
				     in if null ds then 
					return $ if isSingle newKs 
					       then head newKs 
					       else Intersection newKs ps
					else Result ds Nothing
    FunKind k1 k2 ps -> do k3 <- anaKindM k1 env
			   k4 <- anaKindM k2 env
			   return $ FunKind k3 k4 ps
    ExtKind ek v ps -> do nk <- anaKindM ek env
			  return $ ExtKind nk v ps

data ApplMode = OnlyArg | TopLevel 

getIdType :: Id -> TypeMap -> Result Type
getIdType i tm = do 
       k <- getIdKind tm i 
       return $ TypeName i k $ case Map.lookup i tm of
		 Just (TypeInfo _ _ _ (TypeVarDefn c)) -> c
		 _ -> 0

mkTypeConstrAppls :: ApplMode -> Type -> TypeMap -> Result Type
mkTypeConstrAppls m ty tm = case ty of
    TypeName _ _ _ -> return ty
    TypeAppl t1 t2 -> do 
       t3 <- mkTypeConstrAppls m t1 tm 
       t4 <- mkTypeConstrAppls OnlyArg t2 tm
       return $ TypeAppl t3 t4
    TypeToken tt -> getIdType (simpleIdToId tt) tm
    BracketType b ts ps -> do
       args <- mapM (\ trm -> mkTypeConstrAppls m trm tm) ts
       case args of
	          [] -> case b of
			Parens -> return logicalType
			_ -> let i = Id (mkBracketToken b ps) [] []
			     in getIdType i tm
	          [x] -> case b of
		         Parens -> return x
			 _ -> do let [o,c] = mkBracketToken b ps 
				     i = Id [o, Token place $ posOfType 
					    $ head ts, c] [] []
				 t <- getIdType i tm
				 return $ TypeAppl t x 
		  _ -> mkError "illegal type" ty
    MixfixType [] -> error "mkTypeConstrAppl (MixfixType [])"
    MixfixType (f:a) -> case (f, a) of 
      (TypeToken t, [BracketType Squares as@(_:_) ps]) -> do 
         mis <- mapM mkTypeCompId as 
         getIdType (Id [t] mis ps) tm
      _ -> do newF <- mkTypeConstrAppls TopLevel f tm 
	      nA <- mapM ( \ t -> mkTypeConstrAppls OnlyArg t tm) a
	      return $ foldl1 TypeAppl $ newF : nA
    KindedType t k p -> do 
       newT <- mkTypeConstrAppls m t tm
       return $ KindedType newT k p
    LazyType t p -> do
       newT <- mkTypeConstrAppls TopLevel t tm
       return $ LazyType newT p 
    ProductType ts ps -> do
       mTs <- mapM (\ t -> mkTypeConstrAppls TopLevel t tm) ts
       return $ mkProductType mTs ps
    FunType t1 a t2 ps -> do
       newT1 <- mkTypeConstrAppls TopLevel t1 tm
       newT2 <- mkTypeConstrAppls TopLevel t2 tm
       return $ FunType newT1 a newT2 ps
    ExpandedType _ t2 -> mkTypeConstrAppls m t2 tm

mkTypeCompId :: Type -> Result Id
mkTypeCompId ty = case ty of 
    TypeToken t -> if isPlace t then mkError "unexpected place" t
		   else return $ Id [t] [] []
    MixfixType [] -> error "mkTypeCompId: MixfixType []"
    MixfixType (hd:tps) ->
         if null tps then mkTypeCompId hd
	 else do 
	 let (toks, comps) = break ( \ p -> 
			case p of BracketType Squares (_:_) _ -> True
			          _ -> False) tps
	 mts <- mapM mkTypeCompToks (hd:toks)
	 (mis, ps) <- if null comps then return ([], [])
		     else mkTypeCompIds $ head comps
	 pls <- if null comps then return [] 
		else mapM mkTypeIdPlace $ tail comps
	 return $ Id (concat mts ++ pls) mis ps 
    _ -> do ts <- mkTypeCompToks ty
	    return $ Id ts [] []

mkTypeCompIds :: Type -> Result ([Id], [Pos])
mkTypeCompIds ty = case ty of
    BracketType Squares tps@(_:_) ps -> do
        mis <- mapM mkTypeCompId tps  
        return (mis, ps)
    _ -> mkError "no compound list for type id" ty

mkTypeCompToks :: Type -> Result [Token]
mkTypeCompToks ty = case ty of 
    TypeToken t -> return [t]
    BracketType bk [tp] ps -> case bk of 
        Parens -> mkError "no type id" ty
        _ -> do let [o,c] = mkBracketToken bk ps
	        mts <- mkTypeCompToks tp
	        return (o : mts ++ [c])
    MixfixType tps -> do
        mts <- mapM mkTypeCompToks tps
        return $ concat mts
    _ -> mkError "no type tokens" ty

mkTypeIdPlace :: Type -> Result Token
mkTypeIdPlace ty =  case ty of 
    TypeToken t -> if isPlace t then return t
		   else mkError "no place" t
    _ -> mkError "no place" ty

-- ---------------------------------------------------------------------------
-- compare kinds
-- ---------------------------------------------------------------------------

lesserKind :: Kind -> Kind -> Bool
lesserKind k1 k2 = 
    case (k1, k2) of 
    (MissingKind, _) -> error "lesserKind1"
    (_, MissingKind) -> error "lesserKind2"
    (_, Intersection l2@(_:_) _) -> and $ map (lesserKind k1) l2
    (Intersection l1@(_:_) _, _) -> or $ map (flip lesserKind k2) l1
    (ExtKind ek1 v1 _, ExtKind ek2 v2 _) -> 
	(v1 == v2) && lesserKind ek1 ek2
    (_, ExtKind ek2 _ _) -> lesserKind k1 ek2
    (ExtKind _ _ _, _) -> False
    (Intersection [] _, Intersection [] _) -> True
    (Intersection [] _, _) -> False
    (Downset _ t1 k _,  Downset _ t2 _ _) -> t1 == t2 || lesserKind k k2
    (Downset _ _ k _, _) -> lesserKind k k2
    (ClassKind c1 k,  ClassKind c2 _) -> c1 == c2 || lesserKind k k2
    (ClassKind _ k, _) -> lesserKind k k2
    (FunKind ek rk _, FunKind ek2 rk2 _) -> 
	lesserKind rk rk2 && lesserKind ek2 ek
    (FunKind _ _ _, _) -> False


-- ---------------------------------------------------------------------------
-- infer kind
-- ---------------------------------------------------------------------------

checkMaybeKinds :: (PosItem a, PrettyPrint a) => 
              a -> Maybe Kind -> Kind -> Result Kind
checkMaybeKinds a mk1 k2 =
    case mk1 of
           Nothing -> return k2
	   Just k1 -> if lesserKind k1 k2 then return k1
		      else if lesserKind k2 k1 then return k2
		      else Result (diffKindDiag a k1 k2) Nothing

checkFunKind :: Maybe Kind -> Type -> Type -> Kind -> TypeMap -> Result Kind
checkFunKind mk t1 t2 k1 tm = 
    case k1 of 
	FunKind fk ak _ -> do 
	    inferKind (Just fk) t2 tm
	    checkMaybeKinds (TypeAppl t1 t2) mk ak 
	Intersection l@(_:_) ps -> do
	    ml <- mapM ( \ k -> checkFunKind mk t1 t2 k tm) l
	    return $ toIntersection ml ps
	ClassKind _ k -> checkFunKind mk t1 t2 k tm
	Downset _ _ k _ -> checkFunKind mk t1 t2 k tm
	ExtKind k _ _ -> checkFunKind mk t1 t2 k tm
	_ -> mkError "unexpected type argument" t2

inferKind :: Maybe Kind -> Type -> TypeMap -> Result Kind
inferKind mk ty tm = case ty of 
    TypeName i _ _ -> do 
       m <- getIdKind tm i
       checkMaybeKinds i mk m
    TypeAppl t1 t2 -> do 
       k1 <- inferKind Nothing t1 tm
       checkFunKind mk t1 t2 k1 tm
    ExpandedType _ t1 -> inferKind mk t1 tm
    FunType t1 a t2 _ -> do
       let i = arrowId a
       fk <- getIdKind tm i
       let tn = TypeName i fk 0
       inferKind mk (TypeAppl (TypeAppl tn t1) t2) tm
    ProductType ts _ -> if null ts then checkMaybeKinds ty mk star else
         do pk <- getIdKind tm productId
	    let tn = TypeName productId pk 0
		mkAppl [t1] = t1
		mkAppl (t1:tr) = TypeAppl (TypeAppl tn t1) $ mkAppl tr
		mkAppl [] = error "inferKind: mkAppl"
            inferKind mk (mkAppl ts) tm
    LazyType t _ -> inferKind mk t tm
    KindedType t k _ -> do
       mk2 <- inferKind (Just k) t tm
       checkMaybeKinds t mk mk2
    _ -> mkError "unresolved type" ty

getIdKind :: TypeMap -> Id -> Result Kind
getIdKind tm i = case Map.lookup i tm of
       Nothing -> mkError "unknown type" i
       Just (TypeInfo rk l _ _) -> return $  
	   if null l then rk else 
	      if isSingle l then head l else Intersection l []

-- ---------------------------------------------------------------------------
anaType :: (Maybe Kind, Type) -> TypeMap -> Result (Kind, Type)
anaType (mk, t) tm = 
    do nt <- mkTypeConstrAppls TopLevel t tm
       let newTy = expandAlias tm nt
       newk <- inferKind mk newTy tm
       return (newk, newTy)

mkGenVars :: [TypeArg] -> Type -> Type
mkGenVars fvs newTy = 
    let ts = zipWith ( \ (TypeArg i k _ _) n -> 
				  TypeName i k n) fvs [-1, -2..]
	m = Map.fromList $ zip fvs ts
    in  repl m newTy

generalize :: TypeScheme -> Result TypeScheme
generalize (TypeScheme newArgs (q :=> newTy) p) = do
 	       let fvs = varsOf newTy
		   qTy = q :=> mkGenVars fvs newTy
                   ds = unboundTypevars newArgs newTy
	       if null ds then
	          return $ TypeScheme newArgs qTy p
	          else if null newArgs then 
		       return $ TypeScheme fvs qTy p
		  else Result ds Nothing

mkBracketToken :: BracketKind -> [Pos] -> [Token]
mkBracketToken k ps = 
    if null ps then mkBracketToken k [nullPos]
       else zipWith Token ((\ (o,c) -> [o,c]) $ getBrackets k) 
		[head ps, last ps]
