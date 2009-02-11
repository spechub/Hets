{- |
Module      :  $Header$
Description :  translating program equations to Haskell
Copyright   :  (c) Christian Maeder, Uni Bremen 2004-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable

The embedding comorphism from HasCASL to Haskell.
-}

module Comorphisms.HasCASL2Haskell where

import Logic.Logic
import Logic.Comorphism

import Data.List((\\))

import Common.Id
import Common.Result
import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.ExtSign
import qualified Data.Map as Map
import qualified Data.Set as Set

import HasCASL.As
import HasCASL.AsUtils
import HasCASL.Builtin
import HasCASL.DataAna
import HasCASL.Le as HC
import HasCASL.Logic_HasCASL
import HasCASL.Sublogic

import Haskell.Logic_Haskell as HS
import Haskell.HatParser hiding(TypeInfo, Kind)
import Haskell.HatAna
import Haskell.TranslateId

-- | The identity of the comorphism
data HasCASL2Haskell = HasCASL2Haskell deriving Show

instance Language HasCASL2Haskell -- default definition is okay

instance Comorphism HasCASL2Haskell
               HasCASL Sublogic
               BasicSpec Sentence SymbItems SymbMapItems
               Env
               Morphism
               HC.Symbol HC.RawSymbol ()
               Haskell ()
               HsDecls (TiDecl PNT) () ()
               Sign
               HaskellMorphism
               HS.Symbol HS.RawSymbol () where
    sourceLogic HasCASL2Haskell = HasCASL
    sourceSublogic HasCASL2Haskell = noSubtypes
    targetLogic HasCASL2Haskell = Haskell
    mapSublogic HasCASL2Haskell _ = Just ()
    map_morphism = mapDefaultMorphism
    map_sentence HasCASL2Haskell = mapSingleSentence
    map_theory HasCASL2Haskell = mapTheory
    isInclusionComorphism HasCASL2Haskell = True

mapSingleSentence :: Env -> Sentence -> Result (TiDecl PNT)
mapSingleSentence sign sen = do
    (_, l) <- mapTheory (sign, [makeNamed "" sen])
    case l of
      [] -> fail "sentence was not translated"
      [s] -> return $ sentence s
      _ -> do (_, o) <- mapTheory (sign, [])
              case l \\ o of
                [] -> fail "not a new sentence"
                [s] -> return $ sentence s
                _ -> fail "several sentences resulted"

mapTheory :: (Env, [Named Sentence]) -> Result (Sign, [Named (TiDecl PNT)])
mapTheory (sig, csens) = do
    let hs = translateSig sig
        ps = concatMap (translateSentence sig) csens
        cs = cleanSig hs ps
    (_, ExtSign hsig _, sens) <-
            hatAna (HsDecls (cs ++ map sentence ps),
                            emptySign, emptyGlobalAnnos)
    return (diffSign hsig preludeSign,
            filter  (not . preludeEntity . getHsDecl . sentence) sens)

-- former file UniqueId

-- | Generates distinct names for overloaded function identifiers.
distinctOpIds :: Int -> [(Id, [OpInfo])] -> [(Id, OpInfo)]
distinctOpIds n l = case l of
  [] -> []
  (i, info) : idInfoList ->
    case info of
    [] -> distinctOpIds 2 idInfoList
    [hd] -> (i, hd) : distinctOpIds 2 idInfoList
    hd : tl -> (newName i n, hd) :
             distinctOpIds (n + 1) ((i, tl) : idInfoList)

-- | Adds a number to the name of an identifier.
newName :: Id -> Int -> Id
newName (Id tlist idlist poslist) n =
  Id (tlist ++ [mkSimpleId $ '0' : show n]) idlist poslist

-- | Searches for the real name of an overloaded identifier.
findUniqueId :: Env -> Id -> TypeScheme -> Maybe (Id, OpInfo)
findUniqueId env uid ts =
    let l = Set.toList $ Map.findWithDefault Set.empty uid $ assumps env
        fit :: Int -> [OpInfo] -> Maybe (Id, OpInfo)
        fit n tl =
            case tl of
                   [] -> Nothing
                   oi:rt -> if ts == opType oi then
                            Just (if null rt then uid else newName uid n, oi)
                            else fit (n + 1) rt
    in fit 2 l

-- former TranslateAna file

-------------------------------------------------------------------------
-- Translation of an HasCASL-Environement
-------------------------------------------------------------------------

-- | Converts an abstract syntax of HasCASL (after the static analysis)
-- to the top datatype of the abstract syntax of haskell.
translateSig :: Env -> [HsDecl]
translateSig env =
    concatMap (translateTypeInfo env) (Map.toList $ typeMap env)
    ++ concatMap translateAssump (distinctOpIds 2 $ Map.toList
                      $ Map.map Set.toList $ assumps env)

-------------------------------------------------------------------------
-- Translation of types
-------------------------------------------------------------------------

-- | Converts one type to a data or type declaration in Haskell.
translateTypeInfo :: Env -> (Id, TypeInfo) -> [HsDecl]
translateTypeInfo env (tid,info) =
  let hsname = mkHsIdent UpperId tid
      hsTyName = hsTyCon hsname
      mkTp = foldl hsTyApp hsTyName
      k = typeKind info
      loc = toProgPos $ posOfId tid
      ddecl = hsDataDecl loc
                       [] -- empty HsContext
                       (mkTp $ kindToTypeArgs 1 k)
                       [HsConDecl loc [] [] hsname []]
                       derives
  in case typeDefn info of
       NoTypeDefn -> case Set.toList $ superTypes info of
         [] -> [ddecl]
         j : _ -> [typeSynonym loc hsTyName $ TypeName j k 0]
       AliasTypeDefn ts ->
           [hsTypeDecl loc (mkTp $ getAliasArgs ts) $ getAliasType ts]
       DatatypeDefn de -> [sentence $ translateDt env de]
       _ -> []  -- ignore others

isSameId :: Id -> Type -> Bool
isSameId tid (TypeName tid2 _ _) = tid == tid2
isSameId _tid _ty = False

typeSynonym :: SrcLoc -> HsType -> Type -> HsDecl
typeSynonym loc hsname = hsTypeDecl loc hsname . translateType

kindToTypeArgs :: Int -> RawKind -> [HsType]
kindToTypeArgs i k = case k of
    ClassKind _ -> []
    FunKind _ _ kr ps -> (hsTyVar $ mkSName ('a' : show i)
                                   $ toProgPos ps)
                      : kindToTypeArgs (i + 1) kr

getAliasArgs :: Type -> [HsType]
getAliasArgs ty = case ty of
    TypeAbs v t _ -> getArg v : getAliasArgs t
    ExpandedType _ t -> getAliasArgs t
    KindedType t _ _ -> getAliasArgs t
    _ -> []

getArg :: TypeArg -> HsType
getArg = hsTyVar . mkHsIdent LowerId . getTypeVar

getAliasType :: Type -> HsType
getAliasType ty = case ty of
    TypeAbs _ t _ -> getAliasType t
    ExpandedType _ t -> getAliasType t
    KindedType t _ _ -> getAliasType t
    _ -> translateType ty

-- | Translation of an alternative constructor for a datatype definition.
translateAltDefn :: Env -> DataPat-> AltDefn
                 -> [HsConDecl HsType [HsType]]
translateAltDefn env dp (Construct muid ts p _) = case muid of
    Just uid -> let loc = toProgPos $ posOfId uid
                    sc = getConstrScheme dp p ts
                    -- resolve overloading
                    (c, ui) = translateId env uid sc
                in case c of
                   UpperId -> -- no existentials, no context
                       [HsConDecl loc [] [] ui $
                                  map (HsBangedType . translateType) ts]
                   _ -> error "HasCASL2Haskell.translateAltDefn"
    Nothing -> []

translateDt :: Env -> DataEntry -> Named HsDecl
translateDt env de@(DataEntry _ i _ args _ alts) =
         let dp@(DataPat j _ _ _) = toDataPat de
             loc = toProgPos $ posOfId i
             hsname = mkHsIdent UpperId j
             hsTyName = hsTyCon hsname
             tp = foldl hsTyApp hsTyName $ map getArg args
         in
         (makeNamed ("ga_" ++ showId j "") $ hsDataDecl loc
                       [] -- empty HsContext
                       tp (concatMap (translateAltDefn env dp)
                           $ Set.toList alts)
                       derives) { isDef = True }

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
    ConstructData _ -> [] -- wrong case!
    _ -> [res, functionUndef loc fname]

-- | Translation of the result type of a typescheme to a haskell type.
--   Uses 'translateType'.
translateTypeScheme :: TypeScheme -> HsType
translateTypeScheme (TypeScheme _ t _) =
  translateType t


-- | Translation of types (e.g. product type, type application ...).
translateType :: Type -> HsType
translateType t = case getTypeAppl t of
   (TypeName tid _ n, tyArgs) -> let num = length tyArgs in
      if n == 0 then
          if tid == unitTypeId && null tyArgs then
             hsTyCon $ mkSName "Bool" $ toProgPos $ getRange t
          else if tid == lazyTypeId && num == 1 then
             translateType $ head tyArgs
          else if isArrow tid && num == 2 then
             let [t1, t2] = tyArgs in
             hsTyFun (translateType t1) (translateType t2)
          else if isProductId tid && num > 1 then
             hsTyTuple loc0 $ map translateType tyArgs
          else foldl hsTyApp (hsTyCon $ mkHsIdent UpperId tid)
               $ map translateType tyArgs
       else foldl hsTyApp (hsTyVar $ mkHsIdent LowerId tid)
            $ map translateType tyArgs
   _ -> error "translateType"

toProgPos :: Range -> SrcLoc
toProgPos p = if isNullRange p then loc0
               else let Range (SourcePos n l c:_) = p
                     in SrcLoc n (1000 + (l-1) * 80 + c) l c

mkSName :: String -> SrcLoc -> SN HsName
mkSName = SN . UnQual

mkHsIdent :: IdCase -> Id -> SN HsName
mkHsIdent c i = mkSName (translateIdWithType c i) $ toProgPos $ posOfId i

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
  let loc = toProgPos $ getRange t
  in case t of
    QualVar (VarDecl v ty _ _) ->
        let (c, i) = translateId env v $ simpleTypeScheme ty in
            case c of
            LowerId -> rec $ HsId $ HsVar i
            _ -> error "translateTerm: variable with UpperId"
    QualOp _ (PolyId uid _ _) sc _ _ _ -> let
    -- The identifier 'uid' may have been renamed. To find its new name,
    -- the typescheme 'ts' is tested for unifiability with the
    -- typeschemes of the assumps. If an identifier is found, it is used
    -- as HsVar or HsCon.
      mkPHsVar s = rec $ HsPId $ HsVar $ mkSName s loc
      mkHsVar s = rec $ HsId $ HsVar $ mkSName s loc
      mkHsCon s = rec $ HsId $ HsCon $ mkSName s loc
      mkUncurry s = rec $ HsApp (mkHsVar "uncurry") (mkHsVar s)
      mkErr s = expUndef loc $ s ++ pp loc
      hTrue = mkHsCon "True"
      a = mkHsVar "a"
      b = mkHsVar "b"
      c = mkHsVar "c"
      vs2 = [mkPHsVar "a", mkPHsVar "b"]
      vs3 = vs2 ++ [mkPHsVar "c"]
      pat2 = [rec $ HsPTuple loc vs2]
      pat3 = [rec $ HsPTuple loc vs3]
      mkLam2 x y = rec $ HsParen $ rec $ HsLambda pat2 $ rec $ HsIf x y hTrue
      mkLam3 x y = rec $ HsParen $ rec $ HsLambda pat3 $ rec $ HsIf x y c
      in if uid == botId then mkErr "bottom at "
      else if uid == trueId then hTrue
      else if uid == falseId then mkHsCon "False"
      else if uid == notId || uid == negId then mkHsVar "not"
      else if uid == defId then rec $ HsRightSection
               (HsVar $ mkSName "seq" loc) hTrue
      else if uid == orId then mkUncurry "||"
      else if uid == andId then mkUncurry "&&"
      else if uid == eqId || uid == eqvId || uid == exEq then
           mkErr "equality at "
      else if uid == implId then mkLam2 a b
      else if uid == infixIf then mkLam2 b a
      else if uid == whenElse then mkLam3 b a
      else if uid == ifThenElse then mkLam3 a b
      else let (cs, ui) = translateId env uid sc
      in rec $ HsId $ case cs of
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
translatePattern :: Env -> Term -> HsPat
translatePattern env pat = case pat of
      QualVar (VarDecl v ty _ _) ->
          if show v == "_" then rec HsPWildCard else
          let (c, i) = translateId env v $ simpleTypeScheme ty
              in case c of
                 LowerId -> rec $ HsPId $ HsVar i
                 _ -> error ("unexpected constructor as variable: " ++ show v)
      QualOp _ (PolyId uid _ _) sc _ _ _ ->
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
          rec $ HsPTuple (toProgPos $ getRange pat)
                  $ map (translatePattern env) pats
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
    let loc = toProgPos $ getRange pat in case getAppl pat of
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
expUndef loc = rec . HsApp (rec $ HsId $ HsVar $ mkSName "error" loc)
                   . rec . HsLit loc . HsString

-- For the definition of an undefined function.
-- Takes the name of the function as argument.
functionUndef :: SrcLoc -> SN HsName -> HsDecl
functionUndef loc s =
    hsFunBind loc [HsMatch loc s []  -- hsPatBind loc (rec $ HsPId $ HsVar s)
              (HsBody $ expUndef loc $ pp s)
              []]

translateSentence :: Env -> Named Sentence -> [Named HsDecl]
translateSentence env sen = case sentence sen of
    DatatypeSen dt -> map (translateDt env) dt
    ProgEqSen _ _ pe -> [sen { sentence = translateProgEq env pe }]
    _ -> []

derives :: [SN HsName]
derives = [] -- map (fakeSN . UnQual) ["Show", "Eq", "Ord"]
