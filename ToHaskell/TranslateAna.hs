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
import HasCASL.AsUtils
import HasCASL.Le

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
getAliasArgs (TypeScheme arglist _ _) = 
    map getArg arglist

getArg :: TypeArg -> HsName
getArg (TypeArg tid _ _ _) = mkHsIdent LowerId tid

getAliasType :: TypeScheme -> HsType
getAliasType (TypeScheme _ t _) = translateType t

-- | Translation of an alternative constructor for a datatype definition.
translateAltDefn :: Env -> DataPat -> [TypeArg] -> IdMap -> AltDefn 
                 -> [HsConDecl]
translateAltDefn env dt args im (Construct muid origTs p _) = 
    let ts = map (mapType im) origTs in
    case muid of
    Just uid -> let sc = TypeScheme args (getConstrType dt p ts) []
                    (UpperId, UnQual ui) = translateId env uid sc
                in [HsConDecl nullLoc ui $ map (HsBangedTy . translateType) ts]
    Nothing -> []

translateDt :: Env -> DataEntry -> Named HsDecl
translateDt env (DataEntry im i _ args alts) = 
         let j = Map.findWithDefault i i im in
         NamedSen ("ga_" ++ showId j "") $
         HsDataDecl nullLoc
                       [] -- empty HsContext
                       (mkHsIdent UpperId j)
                       (map getArg args) -- type arguments
                       (concatMap (translateAltDefn env (j, args, star)
                                   args im) alts)
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
translateTypeScheme (TypeScheme _ t _) = 
  HsUnQualType (translateType t)

-- | Translation of types (e.g. product type, type application ...).
translateType :: Type -> HsType
translateType t = 
  case t of
  FunType t1 _arr t2 _ -> HsTyFun (translateType t1) (translateType t2)
  ProductType tlist _ -> if null tlist 
               then HsTyCon (UnQual (HsIdent "Bool"))
               else HsTyTuple (map translateType tlist)
  LazyType lt _ -> translateType lt
  KindedType kt _kind _ -> translateType kt
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
    QualOp _ (InstOpId uid _ _) sc _ -> 
    -- The identifier 'uid' may have been renamed. To find its new name,
    -- the typescheme 'ts' is tested for unifiability with the 
    -- typeschemes of the assumps. If an identifier is found, it is used
    -- as HsVar or HsCon.
      let (c, ui) = translateId env uid sc
      in case c of
        UpperId -> HsCon ui
        LowerId -> HsVar ui
    ApplTerm t1 t2 _ -> let at = translateTerm env t2 in
       HsApp (translateTerm env t1) $ (case at of 
       HsTuple _ -> id
       HsCon _ -> id
       HsVar _ -> id
       _ -> HsParen) at
    TupleTerm ts _ -> HsTuple (map (translateTerm env) ts)
    TypedTerm t1 tqual _ty _ -> -- check for global types later
      let res = translateTerm env t1
      in case tqual of 
        InType -> undef
        _ -> res
    QuantifiedTerm _quant _vars _t1 _ -> undef
    LambdaTerm pats _part t1 _ -> 
        HsLambda nullLoc
                 (map (translatePattern env) pats)
                 (translateTerm env t1)
    CaseTerm t1 progeqs _ -> 
        HsCase (translateTerm env t1)
               (map (translateCaseProgEq env) progeqs)

    LetTerm _ progeqs t1 _ -> 
        HsLet (map (translateLetProgEq env) progeqs)
              (translateTerm env t1)
    _ -> error ("translateTerm: unexpected term: " ++ show t)

-- | Conversion of patterns form HasCASL to haskell.
translatePattern :: Env -> Pattern -> HsPat
translatePattern env pat = case pat of
      QualVar (VarDecl v ty _ _) -> 
          if show v == "_" then HsPWildCard else
          let (c, UnQual i) = translateId env v $ simpleTypeScheme ty
              in case c of 
                 LowerId -> HsPVar i
                 _ -> error ("unexpected constructor as variable: " ++ show v) 
      QualOp _ (InstOpId uid _t _p) sc _ -> 
        let (_, ui) = translateId env uid sc
        in HsPApp ui []
      ApplTerm p1 p2 _ -> 
          let tp = translatePattern env p1
              a = translatePattern env p2
              in case tp of
                 HsPApp u os -> HsPParen $ HsPApp u (os ++ [a])
                 HsPParen (HsPApp u os) -> HsPParen $ HsPApp u (os ++ [a])
                 _ -> error ("problematic application pattern " ++ show pat)
      TupleTerm pats _ -> 
          HsPTuple $ map (translatePattern env) pats
      TypedTerm _ InType _ _ -> error "translatePattern InType"
      TypedTerm p _ _ty _ -> translatePattern env p 
                                 --the type is implicit
      --AsPattern pattern pattern pos -> HsPAsPat name pattern ??
      AsPattern (VarDecl v ty _ _) p _ -> 
            let (c, UnQual i) = translateId env v $ simpleTypeScheme ty
                hp = translatePattern env p
            in case c of 
               LowerId -> HsPAsPat i hp
               _ -> error ("unexpected constructor as @-variable: " ++ show v)
      _ -> error ("translatePattern: unexpected pattern: " ++ show pat)

-- | Translation of a program equation of a case term in HasCASL
translateCaseProgEq :: Env -> ProgEq -> HsAlt
translateCaseProgEq env (ProgEq pat t _) = 
  HsAlt nullLoc
        (translatePattern env pat)
        (HsUnGuardedAlt (translateTerm env t))
        []

-- | Translation of a program equation of a let term in HasCASL
translateLetProgEq :: Env -> ProgEq -> HsDecl
translateLetProgEq env (ProgEq pat t _) = 
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
