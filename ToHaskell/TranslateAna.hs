{- |
Module      :  $Header$
Copyright   :  (c) Uni Bremen 2003
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  portable 

   Translation of the abstract syntax of HasCASL after the static analysis
   to the abstract syntax of Haskell.

-}

module ToHaskell.TranslateAna (
       -- * Translation of an environment
         translateSig
       -- * Translation of sentences
       , translateSentence
       -- * remove dummy decls that are better given by sentences
       , cleanSig
       ) where

import Common.Id
import qualified Common.Lib.Map as Map
import Common.AS_Annotation

import HasCASL.As
import HasCASL.Le
import HasCASL.Unify
import HasCASL.AsUtils
import HasCASL.ProgEq

import Haskell.Hatchet.HsSyn

import ToHaskell.TranslateId
import ToHaskell.UniqueId

-------------------------------------------------------------------------
-- Translation of an HasCASL-Environement
-------------------------------------------------------------------------

-- | Converts an abstract syntax of HasCASL (after the static analysis) 
-- to the top datatype of the abstract syntax of haskell.
translateSig :: Env -> [HsDecl]
translateSig env = 
    (concat $ map (translateTypeInfo env) $ Map.toList $ typeMap env)
    ++ (concatMap translateAssump $ distinctOpIds 2 $ Map.toList $ assumps env)

-------------------------------------------------------------------------
-- Translation of types
-------------------------------------------------------------------------

-- | Converts one type to a data or type declaration in Haskell.
-- Uses 'translateIdWithType'.
translateTypeInfo :: Env -> (TypeId, TypeInfo) -> [HsDecl]
translateTypeInfo env (tid,info) = 
  let hsname = mkHsIdent UpperId tid
      ddecl = HsDataDecl nullLoc
	               [] -- empty HsContext
	               hsname
		       (kindToTypeArgs 1 $ typeKind info)
		       [(HsConDecl nullLoc hsname [])]
		       derives
  in case typeDefn info of
       NoTypeDefn -> case superTypes info of
         [] -> [ddecl]
	 [si] -> if isSameId tid si then [ddecl] else 
		 [typeSynonym hsname si]
         si : _ -> [typeSynonym hsname si]
       Supertype _ ts _ ->
	   [HsTypeDecl nullLoc hsname (getAliasArgs ts) $ getAliasType ts]
       AliasTypeDefn ts -> 
	   [HsTypeDecl nullLoc hsname (getAliasArgs ts) $ getAliasType ts]
       DatatypeDefn de -> [sentence $ translateDt env de] 
       TypeVarDefn _-> [] -- ignore others
       PreDatatype -> [] -- ignore others


isSameId :: TypeId -> Type -> Bool
isSameId tid (TypeName tid2 _ _) = tid == tid2
isSameId _tid _ty = False

typeSynonym :: HsName -> Type -> HsDecl
typeSynonym hsname ty = 
  HsTypeDecl nullLoc hsname [] (translateType ty)

kindToTypeArgs :: Int -> Kind -> [HsName]
kindToTypeArgs i k = case k of
    MissingKind -> []
    ClassKind _ rk -> kindToTypeArgs i rk
    Downset _ _ rk _ -> kindToTypeArgs i rk
    FunKind _ kr _ -> HsIdent ("a" ++ show i) : kindToTypeArgs (i+1) kr
    Intersection l _ -> if null l then []
			 else kindToTypeArgs i $ head l
    ExtKind ek _ _ -> kindToTypeArgs i ek

getAliasArgs :: TypeScheme -> [HsName]
getAliasArgs (TypeScheme arglist (_plist :=> _t) _poslist) = 
    map getArg arglist

getArg :: TypeArg -> HsName
getArg (TypeArg tid _ _ _) = mkHsIdent LowerId tid
-- ist UpperId oder LowerId hier richtig?

getAliasType :: TypeScheme -> HsType
getAliasType (TypeScheme _arglist (_plist :=> t) _poslist) = translateType t

-- | Translation of an alternative constructor for a datatype definition.
translateAltDefn :: Env -> Type -> [TypeArg] -> IdMap -> AltDefn -> [HsConDecl]
translateAltDefn env dt args im (Construct muid origTs p _) = 
    let ts = map (mapType im) origTs in
    case muid of
    Just uid -> let sc = TypeScheme args ([] :=> getConstrType dt p ts) []
                    (UpperId, UnQual ui) = translateId env uid sc
		in [HsConDecl nullLoc ui $ map (HsBangedTy . translateType) ts]
    Nothing -> []

translateDt :: Env -> DataEntry -> Named HsDecl
translateDt env (DataEntry im i _ args alts) = 
   	 let j = Map.findWithDefault i i im
	     dt = typeIdToType j args star
	     hsname = mkHsIdent UpperId j in
         NamedSen ("ga_" ++ showId j "") $
         HsDataDecl nullLoc
	               [] -- empty HsContext
	               hsname
		       (map getArg args) -- type arguments
		       (concatMap (translateAltDefn env dt args im) alts)
		       derives


-------------------------------------------------------------------------
-- Translation of functions
-------------------------------------------------------------------------

-- | Converts one distinct named function in HasCASL to the corresponding
-- haskell declaration.
-- Generates a definition (Prelude.undefined) for functions that are not 
-- defined in HasCASL.
translateAssump :: (Id, OpInfo) -> [HsDecl]
translateAssump (i, opinf) = 
  let fname = mkHsIdent LowerId i
      res = HsTypeSig nullLoc
                       [fname]
                       $ translateTypeScheme $ opType opinf
  in case opDefn opinf of
    VarDefn -> []
    ConstructData _ -> [] -- wrong case!
    _ -> [res, (functionUndef fname)]

-- | Translation of the result type of a typescheme to a haskell type.
--   Uses 'translateType'.
translateTypeScheme :: TypeScheme -> HsQualType
translateTypeScheme (TypeScheme _arglist (_plist :=> t) _poslist) = 
  HsUnQualType (translateType t)
-- The context (in the _plist) is not yet used in HasCASL
-- arglist ??

-- | Translation of types (e.g. product type, type application ...).
translateType :: Type -> HsType
translateType t = 
  case t of
  FunType t1 _arr t2 _poslist -> HsTyFun (translateType t1) (translateType t2)
  ProductType tlist _poslist -> if null tlist 
               then HsTyCon (UnQual (HsIdent "Bool"))
	       else HsTyTuple (map translateType tlist)
  LazyType lt _poslist -> translateType lt
  KindedType kt _kind _poslist -> translateType kt
  TypeAppl t1 t2 -> HsTyApp (translateType t1) (translateType t2)
  TypeName tid _kind n -> 
      if n == 0 then
	 HsTyCon $ snd $ mkUnQual UpperId tid
      else HsTyVar $ mkHsIdent LowerId tid
  _ -> error ("translateType: unexpected type: " ++ show t)

mkHsIdent :: IdCase -> Id -> HsName
mkHsIdent c i = HsIdent $ translateIdWithType c i

mkUnQual :: IdCase -> Id -> (IdCase, HsQName)
mkUnQual c j = (c, UnQual $ mkHsIdent c j)

translateId :: Env -> Id -> TypeScheme -> (IdCase, HsQName)
translateId env uid sc = 
      let oid = findUniqueId env uid sc
      in case oid of
        Just (i, oi) -> if isConstructor oi then mkUnQual UpperId i
			else mkUnQual LowerId i
	_ -> mkUnQual LowerId uid -- variable
 
-- | Converts a term in HasCASL to an expression in haskell
translateTerm :: Env -> Term -> HsExp
translateTerm env t = 
  let undef = HsVar $ UnQual $ HsIdent "undefined" in
  case t of
    QualVar (VarDecl v ty _ _) -> 
	let (LowerId, i) = translateId env v $ simpleTypeScheme ty in HsVar i
    QualOp _ (InstOpId uid _types _) sc _pos -> 
    -- The identifier 'uid' may have been renamed. To find its new name,
    -- the typescheme 'ts' is tested for unifiability with the 
    -- typeschemes of the assumps. If an identifier is found, it is used
    -- as HsVar or HsCon.
      let (c, ui) = translateId env uid sc
      in case c of
        UpperId -> HsCon ui
	LowerId -> HsVar ui
    ApplTerm t1 t2 _pos -> let at = translateTerm env t2 in
       HsApp (translateTerm env t1) $ (case at of 
       HsTuple _ -> id
       HsCon _ -> id
       HsVar _ -> id
       _ -> HsParen) at
    TupleTerm ts _pos -> HsTuple (map (translateTerm env) ts)
    TypedTerm t1 tqual _ty _pos -> -- check for global types later
      let res = translateTerm env t1
      in case tqual of 
        InType -> undef
        _ -> res
    QuantifiedTerm _quant _vars _t1 _pos -> undef
    LambdaTerm pats _part t1 _pos -> 
        HsLambda nullLoc
                 (map (translatePattern env) pats)
	         (translateTerm env t1)
    CaseTerm t1 progeqs _pos -> 
        HsCase (translateTerm env t1)
	       (map (translateCaseProgEq env) progeqs)

    LetTerm _ progeqs t1 _pos -> 
        HsLet (map (translateLetProgEq env) progeqs)
	      (translateTerm env t1)
    _ -> error ("translateTerm: unexpected term: " ++ show t)

-- | Conversion of patterns form HasCASL to haskell.
translatePattern :: Env -> Pattern -> HsPat
translatePattern env pat = case pat of
      QualVar (VarDecl v ty _ _) -> 
	  if show v == "_" then HsPWildCard else
	  let (LowerId, UnQual i) = translateId env v $ simpleTypeScheme ty
	      in HsPVar i
      QualOp _ (InstOpId uid _t _p) sc _pos -> 
        let (_, ui) = translateId env uid sc
	in HsPApp ui []
      ApplTerm p1 p2 _pos -> 
	  let tp = translatePattern env p1
	      a = translatePattern env p2
	      in case tp of
                 HsPApp u os -> HsPParen $ HsPApp u (os ++ [a])
		 HsPParen (HsPApp u os) -> HsPParen $ HsPApp u (os ++ [a])
		 _ -> error ("problematic application pattern " ++ show pat)
      TupleTerm pats _pos -> 
	  HsPTuple $ map (translatePattern env) pats
      TypedTerm p OfType _ty _pos -> translatePattern env p 
                                 --the type is implicit
      --AsPattern pattern pattern pos -> HsPAsPat name pattern ??
      AsPattern (VarDecl v ty _ _) p _ -> 
	    let (LowerId, UnQual i) = translateId env v $ simpleTypeScheme ty
		hp = translatePattern env p
	    in HsPAsPat i hp
      _ -> error ("translatePattern: unexpected pattern: " ++ show pat)


-- | Translation of a program equation of a case term in HasCASL
translateCaseProgEq :: Env -> ProgEq -> HsAlt
translateCaseProgEq env (ProgEq pat t _pos) = 
  HsAlt nullLoc
	(translatePattern env pat)
	(HsUnGuardedAlt (translateTerm env t))
	[]

-- | Translation of a program equation of a let term in HasCASL
translateLetProgEq :: Env -> ProgEq -> HsDecl
translateLetProgEq env (ProgEq pat t _pos) = 
  HsPatBind nullLoc
	    (translatePattern env pat)
	    (HsUnGuardedRhs (translateTerm env t))
	    []

-- | Translation of a toplevel program equation
translateProgEq :: Env -> ProgEq -> HsDecl
translateProgEq env (ProgEq pat t _) = 
    case getAppl pat of
    Just (uid, sc, args) -> 
        let (_, ui) = translateId env uid sc
	in HsFunBind [HsMatch nullLoc ui
	             (map (translatePattern env) args) -- [HsPat]
	             (HsUnGuardedRhs $ translateTerm env t) -- HsRhs
	             []]
    Nothing -> error ("translateLetProgEq: no toplevel id: " ++ show pat)

translateSentence ::  Env -> Named Sentence -> [Named HsDecl] 
translateSentence env sen = case sentence sen of
    DatatypeSen dt -> map (translateDt env) dt
    ProgEqSen _ _ pe -> [NamedSen (senName sen) 
			$ translateProgEq env pe]
    _ -> []

-------------------------------------------------------------------------
-- some stuff
-------------------------------------------------------------------------
-- The positions in the source code are not necessary during the translation,
-- therefore the same SrcLoc is used everywhere.
nullLoc :: SrcLoc
nullLoc = SrcLoc 1 0

-- For the definition of an undefined function.
-- Takes the name of the function as argument.
functionUndef :: HsName -> HsDecl
functionUndef s = 
    HsPatBind nullLoc
	      (HsPVar s)
	      (HsUnGuardedRhs (HsVar (UnQual (HsIdent "undefined"))))
	      []

-- | remove dummy decls given by sentences
cleanSig :: [HsDecl] -> [Named HsDecl] -> [HsDecl]
cleanSig ds sens = 
    let dds = foldr ( \ nd l -> case sentence nd of
		      HsDataDecl _ _ n _ _ _ -> n : l
		      _ -> l) [] sens
	funs = foldr ( \ nd l -> case sentence nd of
		      HsFunBind (HsMatch _ n _ _ _ : _) -> n : l
		      _ -> l) [] sens
    in filter ( \ hs -> case hs of 
        HsDataDecl _ _ n _ _ _ -> n `notElem` dds
        HsTypeDecl _ n _ _ -> n `notElem` dds
        HsPatBind _ (HsPVar n) _ _ -> UnQual n `notElem` funs
	_ -> True)
       ds 
derives :: [HsQName]
derives = [(UnQual $ HsIdent "Show"), (UnQual $ HsIdent "Eq"),
	   (UnQual $ HsIdent "Ord")] 
