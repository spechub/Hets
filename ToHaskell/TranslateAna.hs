{- |
Module      :  $Header$
Copyright   :  (c) Uni Bremen 2003
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  portable 

   Translation of the abstract syntax of HasCASL after the static analysis
   to the abstract syntax of haskell.
-}

module ToHaskell.TranslateAna (
       -- * Translation of an environment
         translateAna
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
       -- * Translation of a map of types
       , translateTypeMap
       , translateData
       , translateAltDefn
       , translateRecord
       ) where

import HasCASL.As
import HasCASL.Le
import Haskell.Hatchet.HsSyn
import Common.Id
import qualified Common.Lib.Map as Map
import ToHaskell.TranslateId
import ToHaskell.UniqueId

-------------------------------------------------------------------------
-- Translation of an HasCASL-Environement
-------------------------------------------------------------------------

-- | Converts an abstract syntax of HasCASL (after the static analysis) 
-- to the top datatype of the abstract syntax of haskell.
-- Calls 'translateTypeMap' and 'translateAssumps'.
translateAna :: Env -> [HsDecl]
--translateAna env = error (show env)
translateAna env = 
             ((translateTypeMap (typeMap env)) ++ 
             (translateAssumps (assumps env) (typeMap env)))   -- [HsDecl]

-------------------------------------------------------------------------
-- Translation of types
-------------------------------------------------------------------------

-- | Converts all HasCASL types to data or type declarations in haskell.
-- Uses 'translateData'.
translateTypeMap :: TypeMap -> [HsDecl]
translateTypeMap m = concat $ map translateData (Map.assocs m)

-- | Converts one type to a data or type declaration in haskell.
-- Uses 'translateIdWithType'.
translateData :: (TypeId, TypeInfo) -> [HsDecl]
translateData (tid,info) = 
  let hsname = (HsIdent (translateIdWithType UpperId tid))
      len = length $ superTypes info
  in case (typeDefn info) of
       NoTypeDefn ->
         if len == 0 || (len == 1 && isSameId tid (head $ superTypes info))then
           [(HsDataDecl nullLoc
	               [] -- empty HsContext
	               hsname
		       [] -- [HsName] no type arguments
		       [(HsConDecl nullLoc hsname [])]
		       [(UnQual $ HsIdent "Show")] -- [HsQName]  (deriving ...)
	    )]
	 else (map (typeSynonym hsname)(superTypes info))
       Supertype _vars _ty _form ->[]
       DatatypeDefn _ typeargs altDefns -> 
 	  [(HsDataDecl nullLoc
	               [] -- empty HsContext
	               hsname
		       (map getArg typeargs) -- type arguments
		       (map translateAltDefn altDefns) -- [HsConDecl] 
		       [(UnQual $ HsIdent "Show")] -- [HsQName]  (deriving ...)
	   )]
       AliasTypeDefn ts -> 
	  [(HsTypeDecl nullLoc
	               hsname
	               (getAliasArgs ts)
	               (getAliasType ts)
	   )]
       TypeVarDefn -> [] -- are ignored in haskell
       PreDatatype -> error "translateData: unexpected PreDatatype"

isSameId :: TypeId -> Type -> Bool
isSameId tid (TypeName tid2 _ _) = tid == tid2
isSameId _tid _ty = False

typeSynonym :: HsName -> Type -> HsDecl
typeSynonym hsname ty = 
  HsTypeDecl nullLoc hsname [] (translateType ty)

-- | Translation of an alternative constructor for a datatype definition.
--   Uses 'translateRecord'.
translateAltDefn :: AltDefn -> HsConDecl
translateAltDefn (Construct uid ts _ []) = 
    HsConDecl nullLoc
	      (HsIdent (translateIdWithType UpperId uid))
	      (map getType ts)
translateAltDefn (Construct uid _ts _ sel) =
    HsRecDecl nullLoc
	      (HsIdent (translateIdWithType UpperId uid))
	      (map translateRecord sel)

-- | Translation one field label.
translateRecord :: Selector -> ([HsName], HsBangType)
translateRecord (Select opid t _) = 
    ([(HsIdent (translateIdWithType LowerId opid))],
     getType t)

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
translateAssumps :: Assumps -> TypeMap -> [HsDecl]
translateAssumps as tm =
  let distList =  distinctOpIds $ Map.toList as
      distAs = Map.fromList distList
  in  concat $ map (translateAssump distAs tm) $ distList

-- | Converts one distinct named function in HasCASL to the corresponding
-- haskell declaration.
-- Generates a definition (Prelude.undefined) for functions that are not 
-- defined in HasCASL.
translateAssump :: Assumps -> TypeMap -> (Id,OpInfos) -> [HsDecl]
translateAssump as tm (i, opinf) = 
  let fname = translateIdWithType LowerId i
      res = HsTypeSig nullLoc
                       [(HsIdent fname)]
                       (translateTypeScheme (opType $ head $ opInfos opinf))
  in case (opDefn $ head $ opInfos opinf) of
    NoOpDefn _ -> [res, (functionUndef fname)]
    ConstructData _ -> []  -- Implicitly introduced by the datatype definition.
    SelectData _ _ -> []   -- Implicitly introduced by the datatype definition.
    Definition _ term -> 
      (translateFunDef as tm i (opType $ head $ opInfos opinf) term)
    VarDefn -> []

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
 let err = error ("unexpected type: " ++ show t) in 
  case t of
  FunType t1 _arr t2 _poslist -> HsTyFun (translateType t1) (translateType t2)
  ProductType tlist _poslist -> HsTyTuple (map translateType tlist)
  LazyType lt _poslist -> translateType lt
  MixfixType _ -> err
  KindedType kt _kind _poslist -> translateType kt
  BracketType _ _ _ -> err
  TypeToken _ -> err
  TypeAppl t1 t2 -> HsTyApp (translateType t1) (translateType t2)
  TypeName tid _kind n -> 
      if n > 0 then
	 HsTyVar (HsIdent (translateIdWithType LowerId tid))
      else
         HsTyCon (UnQual (HsIdent (translateIdWithType UpperId tid)))   

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
  let err = error ("Unexpected term: " ++ show t) in
  case t of
    QualVar v ty _pos ->
        HsParen (HsExpTypeSig 
		 nullLoc 
		 (HsVar (UnQual (HsIdent (translateIdWithType LowerId v))))
		 (HsUnQualType $ translateType ty))      
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
        _ -> error("Problem with finding of unique id: " ++ show t)

    ApplTerm t1 t2 _pos ->
      HsApp(translateTerm as tm t1)(HsParen $ translateTerm as tm t2)
    TupleTerm ts _pos -> HsTuple (map (translateTerm as tm) ts)
    TypedTerm t1 tqual ty _pos ->
      let res = (HsExpTypeSig nullLoc 
	                    (translateTerm as tm t1)
                            (HsUnQualType $ translateType ty)) in
      case tqual of 
        OfType -> HsParen res
        AsType -> HsParen res
	-- Here a HsExpTypeSig (t1::ty) is sufficient because supertypes
        -- in HasCASL are converted to typesynonymes in haskell.
        InType -> error ("Translation of \"InType\" not possible: " ++ show t)

    QuantifiedTerm _quant _vars _t1 _pos -> -- forall ...
        error ("Translation of \"QuantifiedTerm\" not possible" ++ show t)
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
    _ -> err -- ResolvedMixTerm, TermToken, MixfixTerm, BracketTerm 


-- | Conversion of patterns form HasCASL to haskell.
translatePattern :: Assumps -> TypeMap -> Pattern -> HsPat
translatePattern as tm pat = 
  let err = error ("unexpected pattern: " ++ show pat) in
    case pat of
      PatternVar (VarDecl v _ty _sepki _pos) 
	  -> HsPVar $ HsIdent $ translateIdWithType LowerId v
      PatternConstr (InstOpId uid _t _p) ts _pos -> 
        let oid = findUniqueId uid ts tm as
	in case oid of
	  Just i ->
	      if isConstructId i $ Map.toList as then
	        HsPApp (UnQual $ HsIdent $ translateIdWithType UpperId i) []
	      else HsPApp (UnQual $ HsIdent $ translateIdWithType LowerId i) []
	  _ -> error ("Proplem with finding of unique id: " ++ show pat)
      ApplPattern p1 p2 _pos -> 
	  let tp = translatePattern as tm p1
	      a = translatePattern as tm p2
	      in case tp of
                 HsPApp u os -> HsPApp u (os ++ [a])
		 _ -> error ("problematic application pattern " ++ show pat)
      TuplePattern pats _pos -> 
	  HsPTuple $ map (translatePattern as tm) pats
      TypedPattern p _ty _pos -> translatePattern as tm p 
                                 --the type is implicit
      --AsPattern pattern pattern pos -> HsPAsPat name pattern ??
      AsPattern _p1 _p2 _pos -> error "AsPattern nyi"
      _ -> err


-- | Translation of a programm equation of a case term in HasCASL
translateCaseProgEq :: Assumps -> TypeMap -> ProgEq -> HsAlt
translateCaseProgEq as tm (ProgEq pat t _pos) = 
  HsAlt nullLoc
	(translatePattern as tm pat)
	(HsUnGuardedAlt (translateTerm as tm t))
	[]

-- | Translation of a programm equation of a let term in HasCASL
translateLetProgEq ::Assumps ->  TypeMap -> ProgEq -> HsDecl
translateLetProgEq as tm (ProgEq pat t _pos) = 
  HsPatBind nullLoc
	    (translatePattern as tm pat)
	    (HsUnGuardedRhs (translateTerm as tm t))
	    []

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
