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
import HasCASL.Morphism
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
  let hsname = (HsIdent (translateIdWithType UpperId tid))
      ddecl = HsDataDecl nullLoc
	               [] -- empty HsContext
	               hsname
		       (kindToTypeArgs 1 $ typeKind info)
		       [(HsConDecl nullLoc hsname [])]
		       derives
  in case (typeDefn info) of
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
       TypeVarDefn -> [] -- ignore others
       PreDatatype -> [] -- ignore others


isSameId :: TypeId -> Type -> Bool
isSameId tid (TypeName tid2 _ _) = tid == tid2
isSameId _tid _ty = False

typeSynonym :: HsName -> Type -> HsDecl
typeSynonym hsname ty = 
  HsTypeDecl nullLoc hsname [] (translateType ty)

kindToTypeArgs :: Int -> Kind -> [HsName]
kindToTypeArgs i k = case k of
    Universe _ -> []
    MissingKind -> []
    ClassKind _ rk -> kindToTypeArgs i rk
    Downset _ _ rk _ -> kindToTypeArgs i rk
    FunKind _ kr _ -> HsIdent ("a" ++ show i) : kindToTypeArgs (i+1) kr
    Intersection l _ -> if null l then error "kindToTypeArgs"
			 else kindToTypeArgs i $ head l
    ExtKind ek _ _ -> kindToTypeArgs i ek

getAliasArgs :: TypeScheme -> [HsName]
getAliasArgs (TypeScheme arglist (_plist :=> _t) _poslist) = 
    map getArg arglist

getArg :: TypeArg -> HsName
getArg (TypeArg tid _ _ _) = (HsIdent (translateIdWithType LowerId tid))
-- ist UpperId oder LowerId hier richtig?

getAliasType :: TypeScheme -> HsType
getAliasType (TypeScheme _arglist (_plist :=> t) _poslist) = translateType t

-- | Translation of an alternative constructor for a datatype definition.
translateAltDefn :: Env -> Type -> [TypeArg] -> IdMap -> AltDefn -> [HsConDecl]
translateAltDefn env dt args im (Construct muid origTs p _) = 
    let ts = map (mapType im) origTs in
    case muid of
    Just uid -> let sc = TypeScheme args ([] :=> getConstrType dt p ts) []
                    (UpperId, UnQual ui) = translateId (assumps env)
				(typeMap env) uid sc
		in [HsConDecl nullLoc ui $ map (HsBangedTy . translateType) ts]
    Nothing -> []

translateDt :: Env -> DataEntry -> Named HsDecl
translateDt env (DataEntry im i _ args alts) = 
   	 let j = Map.findWithDefault i i im
	     dt = typeIdToType j args star
	     hsname = HsIdent $ translateIdWithType UpperId j in
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
  let fname = translateIdWithType LowerId i
      res = HsTypeSig nullLoc
                       [(HsIdent fname)]
                       (translateTypeScheme (opType opinf))
  in case (opDefn opinf) of
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
      if n > 0 then
	 HsTyVar (HsIdent (translateIdWithType LowerId tid))
      else
         HsTyCon (UnQual (HsIdent (translateIdWithType UpperId tid)))
  _ -> error ("translateType: unexpected type: " ++ show t)

-- | Generates a type signature and a definition of a function in haskell 
--   from the corresponding information in HasCASL.
translateFunDef :: Assumps -> TypeMap -> Id -> TypeScheme -> Term -> [HsDecl]
translateFunDef as tm i ts term = 
  let fname = translateIdWithType LowerId i
  in [HsTypeSig nullLoc 
             [(HsIdent fname)] 
              (translateTypeScheme ts)] ++
     [HsFunBind [HsMatch nullLoc
	             (UnQual (HsIdent fname)) --HsName
	             (getPattern term) -- [HsPat]
	             (getRhs as tm term) -- HsRhs
	             [] -- {-where-} [HsDecl]
	       ]
     ]

getPattern :: Term -> [HsPat]
getPattern _t = []

getRhs :: Assumps -> TypeMap -> Term -> HsRhs
getRhs as tm t = HsUnGuardedRhs (translateTerm as tm t) 

translateId :: Assumps -> TypeMap -> Id -> TypeScheme -> (IdCase, HsQName)
translateId as tm uid sc = 
      let oid = findUniqueId uid sc tm as 
	  mkUnQual c j = (c, UnQual $ HsIdent $ translateIdWithType c j)
      in case oid of
        Just (i, oi) -> if isConstructor oi then mkUnQual UpperId i
			else mkUnQual LowerId i
	_ -> mkUnQual LowerId uid -- variable
 
-- | Converts a term in HasCASL to an expression in haskell
translateTerm :: Assumps -> TypeMap -> Term -> HsExp
translateTerm as tm t = 
  let undef = HsVar $ UnQual $ HsIdent "undefined" in
  case t of
    QualVar v ty _pos -> 
	let (LowerId, i) = translateId as tm v $ simpleTypeScheme ty in HsVar i
    QualOp _ (InstOpId uid _types _) sc _pos -> 
    -- The identifier 'uid' may have been renamed. To find its new name,
    -- the typescheme 'ts' is tested for unifiability with the 
    -- typeschemes of the assumps. If an identifier is found, it is used
    -- as HsVar or HsCon.
      let (c, ui) = translateId as tm uid sc
      in case c of
        UpperId -> HsCon ui
	LowerId -> HsVar ui
    ApplTerm t1 t2 _pos -> let at = translateTerm as tm t2 in
       HsApp (translateTerm as tm t1) $ (case at of 
       HsTuple _ -> id
       HsCon _ -> id
       HsVar _ -> id
       _ -> HsParen) at
    TupleTerm ts _pos -> HsTuple (map (translateTerm as tm) ts)
    TypedTerm t1 tqual _ty _pos -> -- check for global types later
      let res = translateTerm as tm t1
      in case tqual of 
        InType -> undef
        _ -> res
    QuantifiedTerm _quant _vars _t1 _pos -> undef
    LambdaTerm pats _part t1 _pos -> 
        HsLambda nullLoc
                 (map (translatePattern as tm) pats)
	         (translateTerm as tm t1)
    CaseTerm t1 progeqs _pos -> 
        HsCase (translateTerm as tm t1)
	       (map(translateCaseProgEq as tm)progeqs)

    LetTerm _ progeqs t1 _pos -> 
        HsLet (map (translateLetProgEq as tm) progeqs)
	      (translateTerm as tm t1)
    _ -> error ("translateTerm: unexpected term: " ++ show t)

-- | Conversion of patterns form HasCASL to haskell.
translatePattern :: Assumps -> TypeMap -> Pattern -> HsPat
translatePattern as tm pat = case pat of
      QualVar v ty _pos -> 
	  let (LowerId, UnQual i) = translateId as tm v $ simpleTypeScheme ty
	      in HsPVar i
      QualOp _ (InstOpId uid _t _p) sc _pos -> 
        let (_, ui) = translateId as tm uid sc
	in HsPApp ui []
      ApplTerm p1 p2 _pos -> 
	  let tp = translatePattern as tm p1
	      a = translatePattern as tm p2
	      in case tp of
                 HsPApp u os -> HsPParen $ HsPApp u (os ++ [a])
		 HsPParen (HsPApp u os) -> HsPParen $ HsPApp u (os ++ [a])
		 _ -> error ("problematic application pattern " ++ show pat)
      TupleTerm pats _pos -> 
	  HsPTuple $ map (translatePattern as tm) pats
      TypedTerm p OfType _ty _pos -> translatePattern as tm p 
                                 --the type is implicit
      --AsPattern pattern pattern pos -> HsPAsPat name pattern ??
      AsPattern _p1 _p2 _pos -> error "AsPattern nyi"
      _ -> error ("translatePattern: unexpected pattern: " ++ show pat)


-- | Translation of a program equation of a case term in HasCASL
translateCaseProgEq :: Assumps -> TypeMap -> ProgEq -> HsAlt
translateCaseProgEq as tm (ProgEq pat t _pos) = 
  HsAlt nullLoc
	(translatePattern as tm pat)
	(HsUnGuardedAlt (translateTerm as tm t))
	[]

-- | Translation of a program equation of a let term in HasCASL
translateLetProgEq ::Assumps ->  TypeMap -> ProgEq -> HsDecl
translateLetProgEq as tm (ProgEq pat t _pos) = 
  HsPatBind nullLoc
	    (translatePattern as tm pat)
	    (HsUnGuardedRhs (translateTerm as tm t))
	    []

-- | Translation of a toplevel program equation
translateProgEq ::Assumps ->  TypeMap -> ProgEq -> HsDecl
translateProgEq as tm (ProgEq pat t _) = 
    case getAppl pat of
    Just (uid, sc, args) -> 
        let (_, ui) = translateId as tm uid sc
	in HsFunBind [HsMatch nullLoc ui
	             (map (translatePattern as tm) args) -- [HsPat]
	             (HsUnGuardedRhs $ translateTerm as tm t) -- HsRhs
	             []]
    Nothing -> error ("translateLetProgEq: no toplevel id: " ++ show pat)

translateSentence ::  Env -> Named Sentence -> [Named HsDecl] 
translateSentence env sen = 
    let as = assumps env
	tm = typeMap env
    in case sentence sen of
    DatatypeSen dt -> map (translateDt env) dt
    ProgEqSen _ _ pe -> [NamedSen (senName sen) 
			$ translateProgEq as tm pe]
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
functionUndef :: String -> HsDecl
functionUndef s = 
    HsPatBind nullLoc
	      (HsPVar (HsIdent s))
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
