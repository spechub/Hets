{- |
Module      :  $Header$
Copyright   :  (c) Uni Bremen 2003
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  portable 

   Translation of the abstract syntax of HasCASL after the static analysis
   to the abstract syntax of haskell.

   todo: rename also vars when overloaded
-}

module ToHaskell.TranslateAna (
       -- * Translation of an environment
         translateSig
       -- * Translation of a map of assumptions
       , translateAssumps
       , distinctOpIds
       , translateTypeScheme
       , translateType
       , translateFunDef
       -- ** Translation of terms
       , translateTerm
       -- ** Translation of pattern
       , translatePattern
       -- ** Translation of toplevel program equation
       , translateProgEq
       -- * Translation of a map of types
       , translateTypeMap
       , translateTypeInfo
       , translateAltDefn
       , translateDt
       , translateSentence
       ) where

import Common.Id
import qualified Common.Lib.Map as Map
import Common.AS_Annotation

import HasCASL.As
import HasCASL.Le
import HasCASL.OpDecl
import Haskell.Hatchet.HsSyn

import ToHaskell.TranslateId
import ToHaskell.UniqueId

-------------------------------------------------------------------------
-- Translation of an HasCASL-Environement
-------------------------------------------------------------------------


-- | Converts an abstract syntax of HasCASL (after the static analysis) 
-- to the top datatype of the abstract syntax of haskell.
-- Calls 'translateTypeMap' and 'translateAssumps'. 
-- A True argument includes dummy types for data types.
translateSig :: Bool -> Env -> [HsDecl]
translateSig b env = translateTypeMap b (typeMap env) ++ 
		    translateAssumps (assumps env)

-------------------------------------------------------------------------
-- Translation of types
-------------------------------------------------------------------------

-- | Converts all HasCASL types to data or type declarations in haskell.
-- Uses 'translateData'. 
translateTypeMap :: Bool -> TypeMap -> [HsDecl]
translateTypeMap b m = concat $ map (translateTypeInfo b) (Map.assocs m)

-- | Converts one type to a data or type declaration in haskell.
-- Uses 'translateIdWithType'. True includes a dummy type for data types.
translateTypeInfo :: Bool -> (TypeId, TypeInfo) -> [HsDecl]
translateTypeInfo b (tid,info) = 
  let hsname = (HsIdent (translateIdWithType UpperId tid))
      len = length $ superTypes info
      ddecl = HsDataDecl nullLoc
	               [] -- empty HsContext
	               hsname
		       (kindToTypeArgs 1 $ typeKind info)
		       [(HsConDecl nullLoc hsname [])]
		       []
  in case (typeDefn info) of
       NoTypeDefn ->
         if len == 0 || (len == 1 && isSameId tid (head $ superTypes info))then
           [ddecl]
	 else (map (typeSynonym hsname)(superTypes info))
       AliasTypeDefn ts -> 
	  [(HsTypeDecl nullLoc
	               hsname
	               (getAliasArgs ts)
	               (getAliasType ts)
	   )]
       DatatypeDefn _ _ _ -> if b then [ddecl] else []
       _ -> [] -- ignore others


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


-- | Translation of an alternative constructor for a datatype definition.
--   Uses 'translateRecord'.
translateAltDefn :: AltDefn -> HsConDecl
translateAltDefn (Construct uid ts _ _) = 
    HsConDecl nullLoc
	      (HsIdent (translateIdWithType UpperId uid))
	      (map getType ts)

getType :: Type -> HsBangType
getType t = HsBangedTy (translateType t)
    
getAliasArgs :: TypeScheme -> [HsName]
getAliasArgs (TypeScheme arglist (_plist :=> _t) _poslist) = 
    map getArg arglist

getArg :: TypeArg -> HsName
getArg (TypeArg tid _ _ _) = (HsIdent (translateIdWithType LowerId tid))
-- ist UpperId oder LowerId hier richtig?

getAliasType :: TypeScheme -> HsType
getAliasType (TypeScheme _arglist (_plist :=> t) _poslist) = translateType t


-------------------------------------------------------------------------
-- Translation of functions
-------------------------------------------------------------------------

-- | Converts functions in HasCASL to the coresponding haskell declarations.
translateAssumps :: Assumps -> [HsDecl]
translateAssumps as =
  let distList =  distinctOpIds $ Map.toList as
  in  concat $ map translateAssump distList

-- | Converts one distinct named function in HasCASL to the corresponding
-- haskell declaration.
-- Generates a definition (Prelude.undefined) for functions that are not 
-- defined in HasCASL.
translateAssump :: (Id,OpInfos) -> [HsDecl]
translateAssump (i, opinf) = 
  let fname = translateIdWithType LowerId i
      res = HsTypeSig nullLoc
                       [(HsIdent fname)]
                       (translateTypeScheme (opType $ head $ opInfos opinf))
  in case (opDefn $ head $ opInfos opinf) of
    NoOpDefn _ -> [res, (functionUndef fname)]
    _ -> []

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
  ProductType tlist _poslist -> HsTyTuple (map translateType tlist)
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

isConstructId :: Id -> [(Id,OpInfos)] -> Bool
isConstructId _ [] = False
isConstructId i ((i1,info1):idInfoList) = 
  if i == i1 then
    or $ map isConstructor $ opInfos info1
  else isConstructId i idInfoList

isConstructor :: OpInfo -> Bool
isConstructor o = case opDefn o of
		    ConstructData _ -> True
		    _ -> False

-- | Converts a term in HasCASL to an expression in haskell
translateTerm :: Assumps -> TypeMap -> Term -> HsExp
translateTerm as tm t = 
  let undef = HsVar $ UnQual $ HsIdent "undefined" in
  case t of
    QualVar v _ty _pos -> HsVar $ UnQual $ HsIdent $ 
			  translateIdWithType LowerId v
    QualOp _ (InstOpId uid _types _) ts _pos -> 
    -- The identifier 'uid' may have been renamed. To find its new name,
    -- the typescheme 'ts' is tested for "Unifizierbarkeit" with the 
    -- typeschemes of the assumps. If an identifier is found, it is used
    -- as HsVar or HsCon.
      let oid = findUniqueId uid ts tm as 
      in case oid of
        Just i ->
	    if isConstructId i $ Map.toList as then
	      (HsCon (UnQual (HsIdent (translateIdWithType UpperId i))))
	    else (HsVar (UnQual (HsIdent (translateIdWithType LowerId i))))
        _ -> error("translateTerm: non-unique id: " ++ show t)
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
      QualVar v _ty _pos
	  -> HsPVar $ HsIdent $ translateIdWithType LowerId v
      QualOp _ (InstOpId uid _t _p) ts _pos -> 
        let oid = findUniqueId uid ts tm as
	in case oid of
	  Just i ->
	        HsPApp (UnQual $ HsIdent $ translateIdWithType UpperId i) []
	  _ -> error ("translatePattern: non-unique id: " ++ show pat)
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
    let (topPat, args) = getApplConstr pat in
	case topPat of
      QualOp _ (InstOpId uid _t _p) ts _ -> 
        let oid = findUniqueId uid ts tm as
	in case oid of
	  Just i -> HsFunBind [HsMatch nullLoc
	             (UnQual $ HsIdent $ translateIdWithType LowerId i)
	             (map (translatePattern as tm) $ reverse args) -- [HsPat]
	             (HsUnGuardedRhs $ translateTerm as tm t) -- HsRhs
	             []]
	  _ -> error ("translateLetProgEq: non-unique id: " ++ show pat)
      _ -> error ("translateLetProgEq: no toplevel id: " ++ show pat)

translateDt :: DatatypeDefn -> Named HsDecl
translateDt (DatatypeConstr i _ _ args alts) = 
   	 let hsname = HsIdent $ translateIdWithType UpperId i in
         NamedSen ("ga_" ++ showId i "") $
         HsDataDecl nullLoc
	               [] -- empty HsContext
	               hsname
		       (map getArg args) -- type arguments
		       (map translateAltDefn alts) -- [HsConDecl] 
		       []

translateSentence ::  Env -> Named Sentence -> [Named HsDecl] 
translateSentence env sen = case sentence sen of
    DatatypeSen dt -> map translateDt dt
    ProgEqSen _ _ pe -> [NamedSen (senName sen) 
			$ translateProgEq 
			 (assumps env) (typeMap env) pe]
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
