{- |
Module      :  $Header$
Copyright   :  (c) Uni Bremen 2003
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  non-portable 

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

import SourceNames
import HsName hiding (Id)
import HsDeclStruct
import PropPosSyntax hiding (Id, HsName)
import qualified NewPrettyPrint as HatPretty

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
translateTypeInfo :: Env -> (TypeId, TypeInfo) -> [HsDecl]
translateTypeInfo env (tid,info) = 
  let hsname = mkHsIdent UpperId tid
      hsTyName = hsTyCon hsname
      mkTp l = foldl hsTyApp hsTyName l
      loc = toProgPos $ posOfId tid
      ddecl = hsDataDecl loc
                       [] -- empty HsContext
                       (mkTp $ kindToTypeArgs 1 $ typeKind info)
                       [HsConDecl loc [] [] hsname []]
                       derives
  in case typeDefn info of
       NoTypeDefn -> case superTypes info of
         [] -> [ddecl]
         [si] -> if isSameId tid si then [ddecl] else 
                 [typeSynonym loc hsTyName si]
         si : _ -> [typeSynonym loc hsTyName si]
       Supertype _ ts _ ->
           [hsTypeDecl loc (mkTp $ getAliasArgs ts) $ getAliasType ts]
       AliasTypeDefn ts -> 
           [hsTypeDecl loc (mkTp $ getAliasArgs ts) $ getAliasType ts]
       DatatypeDefn de -> [sentence $ translateDt env de] 
       _ -> []  -- ignore others

isSameId :: TypeId -> Type -> Bool
isSameId tid (TypeName tid2 _ _) = tid == tid2
isSameId _tid _ty = False

typeSynonym :: SrcLoc -> HsType -> Type -> HsDecl
typeSynonym loc hsname ty = 
  hsTypeDecl loc hsname (translateType ty)

kindToTypeArgs :: Int -> Kind -> [HsType]
kindToTypeArgs i k = case k of
    MissingKind -> []
    ClassKind _ rk -> kindToTypeArgs i rk
    Downset _ _ rk _ -> kindToTypeArgs i rk
    FunKind _ kr _ -> (hsTyVar $ fakeSN $ UnQual ("a" ++ show i)) 
                      : kindToTypeArgs (i+1) kr
    Intersection l _ -> if null l then []
                         else kindToTypeArgs i $ head l
    ExtKind ek _ _ -> kindToTypeArgs i ek

getAliasArgs :: TypeScheme -> [HsType]
getAliasArgs (TypeScheme arglist _ _) = 
    map getArg arglist

getArg :: TypeArg -> HsType
getArg (TypeArg tid _ _ _) = hsTyVar $ mkHsIdent LowerId tid

getAliasType :: TypeScheme -> HsType
getAliasType (TypeScheme _ t _) = translateType t

-- | Translation of an alternative constructor for a datatype definition.
translateAltDefn :: Env -> DataPat -> [TypeArg] -> IdMap -> AltDefn 
                 -> [HsConDecl HsType [HsType]]
translateAltDefn env dt args im (Construct muid origTs p _) = 
    let ts = map (mapType im) origTs in
    case muid of
    Just uid -> let loc = toProgPos $ posOfId uid
                    sc = TypeScheme args (getConstrType dt p ts) []
                    -- resolve overloading
                    (c, ui) = translateId env uid sc
                in case c of 
                   UpperId -> -- no existentials, no context
                       [HsConDecl loc [] [] ui $ 
                                  map (HsBangedType . translateType) ts]
                   _ -> error "ToHaskell.TranslateAna.translateAltDefn"
    Nothing -> []

translateDt :: Env -> DataEntry -> Named HsDecl
translateDt env (DataEntry im i _ args alts) = 
         let j = Map.findWithDefault i i im 
             loc = toProgPos $ posOfId i 
             hsname = mkHsIdent UpperId j
             hsTyName = hsTyCon hsname
             tp = foldl hsTyApp hsTyName $ map getArg args
         in
         NamedSen ("ga_" ++ showId j "") $
         hsDataDecl loc
                       [] -- empty HsContext
                       tp
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
      loc = toProgPos $ posOfId i
      res = hsTypeSig loc
                       [fname] []
                       $ translateTypeScheme $ opType opinf
  in case opDefn opinf of
    VarDefn -> []
    ConstructData _ -> [] -- wrong case!
    _ -> [res, functionUndef loc fname]

-- | Translation of the result type of a typescheme to a haskell type.
--   Uses 'translateType'.
translateTypeScheme :: TypeScheme -> HsType
translateTypeScheme (TypeScheme _ t _) = 
  translateType t


-- | Translation of types (e.g. product type, type application ...).
translateType :: Type -> HsType
translateType t = 
  case t of
  FunType t1 _arr t2 _ -> hsTyFun (translateType t1) (translateType t2)
  ProductType tlist ps -> hsTyTuple (toProgPos $ headPos ps) 
                        $ map translateType tlist
  LazyType lt _ -> translateType lt
  KindedType kt _kind _ -> translateType kt
  TypeAppl t1 t2 -> hsTyApp (translateType t1) (translateType t2)
  TypeName tid _kind n -> 
      if n == 0 then
         hsTyCon $ mkHsIdent UpperId tid
      else hsTyVar $ mkHsIdent LowerId tid
  _ -> error ("translateType: unexpected type: " ++ show t)


toProgPos :: Pos -> SrcLoc
toProgPos p = if isNullPos p then loc0 else let SourcePos n l c = p
              in SrcLoc n (1000 + (l-1) * 80 + c) l c 

mkHsIdent :: IdCase -> Id -> SN HsName
mkHsIdent c i = SN (UnQual $ translateIdWithType c i)
                $ toProgPos $  posOfId i

translateId :: Env -> Id -> TypeScheme -> (IdCase, SN HsName)
translateId env uid sc = 
      let oid = findUniqueId env uid sc
          mkUnQual :: IdCase -> Id -> (IdCase, SN HsName)
          mkUnQual c j = (c, mkHsIdent c j)
      in case oid of
        Just (i, oi) -> if isConstructor oi then mkUnQual UpperId i
                        else mkUnQual LowerId i
        _ -> mkUnQual LowerId uid -- variable


-- | Converts a term in HasCASL to an expression in haskell
translateTerm :: Env -> Term -> HsExp
translateTerm env t = 
  let loc = toProgPos $ getMyPos t in
  case t of
    QualVar (VarDecl v ty _ _) -> 
        let (c, i) = translateId env v $ simpleTypeScheme ty in 
            case c of 
            LowerId -> rec $ HsId $ HsVar i
            _ -> error "translateTerm: variable with UpperId" 
    QualOp _ (InstOpId uid _ _) sc _ -> 
    -- The identifier 'uid' may have been renamed. To find its new name,
    -- the typescheme 'ts' is tested for unifiability with the 
    -- typeschemes of the assumps. If an identifier is found, it is used
    -- as HsVar or HsCon.
      let (c, ui) = translateId env uid sc
      in rec $ HsId $ case c of
        UpperId -> HsCon ui
        LowerId -> HsVar ui
    ApplTerm t1 t2 _ ->
       rec $ HsApp (translateTerm env t1) $ translateTerm env t2
    TupleTerm ts _ -> rec $ HsTuple (map (translateTerm env) ts)
    TypedTerm t1 tqual _ty _ -> -- check for global types later
      case tqual of 
        InType -> expUndef loc $ show tqual
        _ -> translateTerm env t1
    QuantifiedTerm qu _vars _t1 _ -> expUndef loc $ show qu
    LambdaTerm pats _part t1 _ -> 
        rec $ HsLambda
                 (map (translatePattern env) pats)
                 (translateTerm env t1)
    CaseTerm t1 progeqs _ -> 
        rec $ HsCase (translateTerm env t1)
               (map (translateCaseProgEq env) progeqs)

    LetTerm _ progeqs t1 _ -> 
        rec $ HsLet (map (translateLetProgEq env) progeqs)
              (translateTerm env t1)
    _ -> error ("translateTerm: unexpected term: " ++ show t)

-- | Conversion of patterns form HasCASL to haskell.
translatePattern :: Env -> Pattern -> HsPat
translatePattern env pat = case pat of
      QualVar (VarDecl v ty _ _) -> 
          if show v == "_" then rec HsPWildCard else
          let (c, i) = translateId env v $ simpleTypeScheme ty
              in case c of 
                 LowerId -> rec $ HsPId $ HsVar i
                 _ -> error ("unexpected constructor as variable: " ++ show v) 
      QualOp _ (InstOpId uid _t _p) sc _ -> 
        let (_, ui) = translateId env uid sc
        in rec $ HsPApp ui []
      ApplTerm p1 p2 _ -> 
          let tp = translatePattern env p1
              a = translatePattern env p2
              in case struct tp of
                 HsPApp u os -> rec $ HsPParen $ rec $ HsPApp u (os ++ [a])
                 HsPParen (Pat (HsPApp u os)) -> 
                     rec $ HsPParen $ rec $ HsPApp u (os ++ [a])
                 _ -> error ("problematic application pattern " ++ show pat)
      TupleTerm pats _ -> 
          rec $ HsPTuple $ map (translatePattern env) pats
      TypedTerm _ InType _ _ -> error "translatePattern InType"
      TypedTerm p _ _ty _ -> translatePattern env p 
                                 --the type is implicit
      AsPattern (VarDecl v ty _ _) p _ -> 
            let (c, i) = translateId env v $ simpleTypeScheme ty
                hp = translatePattern env p
            in case c of 
               LowerId -> rec $ HsPAsPat i hp
               _ -> error ("unexpected constructor as @-variable: " ++ show v)
      _ -> error ("translatePattern: unexpected pattern: " ++ show pat)

-- | Translation of a program equation of a case term in HasCASL
translateCaseProgEq :: Env -> ProgEq -> HsAlt HsExp HsPat [HsDecl]
translateCaseProgEq env (ProgEq pat t ps) = 
  HsAlt (toProgPos ps)
        (translatePattern env pat)
        (HsBody (translateTerm env t))
        []

-- | Translation of a program equation of a let term in HasCASL
translateLetProgEq :: Env -> ProgEq -> HsDecl
translateLetProgEq env (ProgEq pat t ps) = 
  hsPatBind (toProgPos ps)
            (translatePattern env pat)
            (HsBody (translateTerm env t))
            []

-- | Translation of a toplevel program equation
translateProgEq :: Env -> ProgEq -> HsDecl
translateProgEq env (ProgEq pat t _) =
    let loc = toProgPos $ posOfTerm pat in case getAppl pat of
    Just (uid, sc, args) -> 
        let (_, ui) = translateId env uid sc
        in hsFunBind loc [HsMatch loc ui
                     (map (translatePattern env) args) -- [HsPat]
                     (HsBody $ translateTerm env t) -- HsRhs
                     []]
    Nothing -> error ("translateLetProgEq: no toplevel id: " ++ show pat)

-- | remove dummy decls given by sentences
cleanSig :: [HsDecl] -> [Named HsDecl] -> [HsDecl]
cleanSig ds sens = 
    let dds = foldr ( \ nd l -> case basestruct $ sentence nd of
                      Just (HsDataDecl _ _ n _ _) -> n : l
                      _ -> l) [] sens
        funs = foldr ( \ nd l -> case basestruct $ sentence nd of
                      Just (HsFunBind _ (HsMatch _ n _ _ _ : _)) -> n : l
                      _ -> l) [] sens
    in filter ( \ hs -> case basestruct hs of 
        Just (HsDataDecl _ _ n _ _) -> n `notElem` dds
        Just (HsTypeDecl _ n _) -> n `notElem` dds
        Just (HsFunBind _ (HsMatch _ n _ _ _ : _)) -> n `notElem` funs
        _ -> True)
       ds 


expUndef :: SrcLoc -> String -> HsExp
expUndef loc s = rec $ HsApp (rec $ HsId $ HsVar $ fakeSN $ UnQual "error")
                       $ rec $ HsLit loc $ HsString s

-- For the definition of an undefined function.
-- Takes the name of the function as argument.
functionUndef :: SrcLoc -> SN HsName -> HsDecl
functionUndef loc s = 
    hsFunBind loc [HsMatch loc s []  -- hsPatBind loc (rec $ HsPId $ HsVar s)
              (HsBody $ expUndef loc $ HatPretty.pp s)
              []]

translateSentence ::  Env -> Named Sentence -> [Named HsDecl] 
translateSentence env sen = case sentence sen of
    DatatypeSen dt -> map (translateDt env) dt
    ProgEqSen _ _ pe -> [NamedSen (senName sen) 
                        $ translateProgEq env pe]
    _ -> []

derives :: [SN HsName]
derives = [] -- map (fakeSN . UnQual) ["Show", "Eq", "Ord"] 
