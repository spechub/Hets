{- |
Module      :  $Header$
Copyright   :  (c) C. Maeder, DFKI 2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

The embedding comorphism from HasCASL to Isabelle-HOL.
-}

module Comorphisms.PCoClTyConsHOL2IsabelleHOL
    (PCoClTyConsHOL2IsabelleHOL(..)) where

import Logic.Logic as Logic
import Logic.Comorphism

import HasCASL.Logic_HasCASL
import HasCASL.Sublogic
import HasCASL.Le as Le
import HasCASL.As as As
import HasCASL.AsUtils
import HasCASL.Builtin
import HasCASL.Unify

import Isabelle.IsaSign as Isa
import Isabelle.IsaConsts
import Isabelle.Logic_Isabelle
import Isabelle.Translate

import Common.DocUtils
import Common.Id
import Common.Result
import qualified Common.Lib.Map as Map
import Common.AS_Annotation
import Common.GlobalAnnotations

import Data.List (elemIndex)
import Control.Monad (foldM)

-- | The identity of the comorphism
data PCoClTyConsHOL2IsabelleHOL = PCoClTyConsHOL2IsabelleHOL deriving Show

instance Language PCoClTyConsHOL2IsabelleHOL -- default definition is okay

instance Comorphism PCoClTyConsHOL2IsabelleHOL
               HasCASL Sublogic
               BasicSpec Le.Sentence SymbItems SymbMapItems
               Env Morphism
               Symbol RawSymbol ()
               Isabelle () () Isa.Sentence () ()
               Isa.Sign
               IsabelleMorphism () () ()  where
    sourceLogic PCoClTyConsHOL2IsabelleHOL = HasCASL
    sourceSublogic PCoClTyConsHOL2IsabelleHOL = noSubtypes
    targetLogic PCoClTyConsHOL2IsabelleHOL = Isabelle
    mapSublogic PCoClTyConsHOL2IsabelleHOL _ = ()
    map_theory PCoClTyConsHOL2IsabelleHOL (env, sens) = do
      sign <- transSignature env
      isens <- mapM (mapNamedM $ transSentence env) sens
      dt <- mapM (transDataEntry env) $ concatMap
            ( \ ns -> case sentence ns of
              DatatypeSen ds -> ds
              _ -> []) sens
      return (sign { domainTab = dt },
                   filter ( \ ns -> sentence ns /= mkSen true) isens)
    map_morphism = mapDefaultMorphism
    map_sentence PCoClTyConsHOL2IsabelleHOL sign phi =
       transSentence sign phi
    map_symbol = errMapSymbol

-- * Signature
baseSign :: BaseSig
baseSign = MainHC_thy

transAssumps :: GlobalAnnos -> Assumps -> Result ConstTab
transAssumps ga = foldM insertOps Map.empty . Map.toList where
  insertOps m (name, ops) =
      let b = isMixfix name
          chk t = let pf = isPlainFunType t in if b || pf < 2 then pf else -1
          trns = if b then transPlainFunType else transFunType
      in case opInfos ops of
          [info] -> case transOpInfo info of
                 Nothing -> return m
                 Just r -> do
                    ty <- r
                    return $ Map.insert
                           (mkIsaConstT False ga (chk ty)
                            name baseSign) (trns ty) m
          infos -> foldM ( \ m' (i, info) ->
                      case transOpInfo info of
                        Nothing -> return m'
                        Just r -> do
                          ty <- r
                          return $ Map.insert
                             (mkIsaConstIT False ga (chk ty)
                              name i baseSign) (trns ty) m'
                         ) m $ zip [1..] infos

transSignature :: Env -> Result Isa.Sign
transSignature env = do
    ct <- transAssumps (globAnnos env) $ assumps env
    let extractTypeName tyId typeInfo m =
            let getTypeArgs n k = case k of
                        ClassKind _ -> []
                        FunKind _ _ r _ ->
                            (TFree ("'a" ++ show n) [], [isaTerm])
                                           : getTypeArgs (n + 1) r
            in Map.insert (showIsaTypeT tyId baseSign)
                  [(isaTerm, getTypeArgs (1 :: Int) $ typeKind typeInfo)] m
    return $ Isa.emptySign
        { baseSig = baseSign
    -- translation of typeconstructors
        , tsig = emptyTypeSig
             { arities = Map.foldWithKey extractTypeName
                                        Map.empty
                                        (typeMap env) }
        , constTab = ct }

-- * translation of a type in an operation declaration

-- extract type from OpInfo
-- omit datatype constructors
transOpInfo :: OpInfo -> Maybe (Result FunType)
transOpInfo (OpInfo (TypeScheme _ op _) _ opDef) =  case opDef of
    ConstructData _ -> Nothing
    _  -> Just $ funType op

unitTyp :: Typ
unitTyp = Type "unit" holType []
-- types
transType :: Type -> Result Typ
transType = fmap transPlainFunType . funType

transFunType :: FunType -> Typ
transFunType fty = case fty of
    UnitType -> unitTyp
    BoolType -> boolType
    FunType f a -> mkFunType (transFunType f) $ transFunType a
    PartialVal a -> mkOptionType $ transFunType a
    PairType a b -> prodType (transFunType a) $ transFunType b
    TupleType l -> transFunType $ foldr1 PairType l
    ApplType tid args -> Type (showIsaTypeT tid baseSign) []
                       $ map transFunType args
    TypeVar tid -> TFree (showIsaTypeT tid baseSign) []

-- compute number of arguments for plain CASL functions
isPlainFunType :: FunType -> Int
isPlainFunType fty = case fty of
    FunType f a -> case a of
                     FunType _ _ -> -1
                     _ -> case f of
                            TupleType l -> if length l == 2 then 2 else -1
                            _ -> 1
    _ -> 0

transPlainFunType :: FunType -> Typ
transPlainFunType fty = if isPlainFunType fty == 2 then
    case fty of
    FunType (TupleType l) a -> foldr mkFunType (transFunType a)
                               $ map transFunType l
    _ -> transFunType fty
    else transFunType fty

data FunType = UnitType | BoolType | FunType FunType FunType
             | PartialVal FunType | PairType FunType FunType
             | TupleType [FunType]
             | ApplType Id [FunType] | TypeVar Id
               deriving Eq

isPartialVal :: FunType -> Bool
isPartialVal t = case t of
    PartialVal _ -> True
    BoolType -> True
    _ -> False

makePartialVal :: FunType -> FunType
makePartialVal t = if isPartialVal t then t else case t of
    UnitType -> BoolType
    _ -> PartialVal t

funType :: Type -> Result FunType
funType t = case getTypeAppl t of
   (TypeName tid _ n, tys) ->
       if n == 0 then do
           ftys <- mapM funType tys
           return $ case ftys of
             [] | tid == unitTypeId -> UnitType
             [ty] | tid == lazyTypeId -> makePartialVal ty
             [t1, t2] | isArrow tid -> FunType t1 $
                  if isPartialArrow tid then makePartialVal t2 else t2
             (_ : _ : _) | isProductId tid -> TupleType ftys
             _ -> ApplType tid ftys
       else if null tys then return $ TypeVar tid
            else fatal_error "funType: no higher kinds" $ posOfId tid
   _ -> fatal_error "funType: no type appl" $ getRange t

-- * translation of a datatype declaration

-- datatype with name (tyId) + args (tyArgs) and alternatives
transDataEntry :: Env -> DataEntry -> Result [DomainEntry]
transDataEntry env (DataEntry tm tyId gk tyArgs rk alts) =
    let i = Map.findWithDefault tyId tyId tm
        dt = patToType i tyArgs rk
    in case gk of
    Le.Free -> do
      nalts <- mapM (transAltDefn env tm tyArgs dt i) alts
      let transDName ti ta = Type (showIsaTypeT ti baseSign) []
                             $ map transTypeArg ta
      return [(transDName i tyArgs, nalts)]
    _ -> fatal_error ("only free types are allowed: "  ++ show i)
         $ posOfId i

-- arguments of a datatype's typeconstructor
transTypeArg :: TypeArg -> Typ
transTypeArg ta = TFree (showIsaTypeT (getTypeVar ta) baseSign) []

-- datatype alternatives/constructors
transAltDefn :: Env -> IdMap -> [TypeArg] -> Type -> Id -> AltDefn
             -> Result (VName, [Typ])
transAltDefn env tm args dt tyId alt = case alt of
    Construct (Just opId) ts Total _ -> do
        let mTs = map (mapType tm) ts
            sc = TypeScheme args (getFunType dt Total mTs) nullRange
        nts <- mapM funType mTs
        -- extract overloaded opId number
        return (transOpId env opId sc, case nts of
                [TupleType l] | isMixfix opId -> map transFunType l
                _ -> map transFunType nts)
    _ -> fatal_error ("missing total constructor for: " ++ show tyId)
         $ posOfId tyId

-- * Formulas

-- simple variables
transVar :: Var -> VName
transVar v = mkVName $ showIsaConstT v baseSign

transSentence :: Env -> Le.Sentence -> Result Isa.Sentence
transSentence sign s = case s of
    Le.Formula trm -> do
      (ty, t) <- transTerm sign trm
      case ty of
        BoolType -> return $ mkSen t
        PartialVal _ -> return $ mkSen $ mkTermAppl option2bool t
        FunType _ _ -> error "transSentence: FunType"
        PairType _ _ -> error "transSentence: PairType"
        TupleType _ -> error "transSentence: TupleType"
        ApplType _ _ -> error "transSentence: ApplType"
        _ -> return $ mkSen true
    DatatypeSen _ -> return $ mkSen true
    ProgEqSen _ _ (ProgEq _ _ r) -> warning (mkSen true)
                           "translation of sentence not implemented"
                           r

-- disambiguate operation names
transOpId :: Env -> UninstOpId -> TypeScheme -> VName
transOpId sign op ts@(TypeScheme _ ty _) =
    let ga = globAnnos sign
        Result _ mty = funType ty
    in case mty of
         Nothing -> error "transOpId"
         Just fty ->
           let pf = isPlainFunType fty
               args = if pf < 2 || isMixfix op then pf else -1
           in case (do
           ops <- Map.lookup op (assumps sign)
           if isSingle (opInfos ops) then return $
              mkIsaConstT False ga args op baseSign
             else do i <- elemIndex ts (map opType (opInfos ops))
                     return $ mkIsaConstIT False ga args op (i+1) baseSign) of
          Just str -> str
          Nothing  -> error $ "transOpId " ++ showIsaConstT op baseSign

transProgEq :: Env -> ProgEq -> Result (Isa.Term, Isa.Term)
transProgEq sign (ProgEq pat trm r) = do
    op <- transPattern sign pat
    (ty, ot) <- transTerm sign trm
    if isPartialVal ty then fatal_error
           ("rhs must not be partial currently: " ++ showDoc trm "") r
       else return (op, ot)

ifImplOp :: Isa.Term
ifImplOp = conDouble "ifImplOp"

unitOp :: Isa.Term
unitOp = Tuplex [] NotCont

noneOp :: Isa.Term
noneOp = conDouble "None"

exEqualOp :: Isa.Term
exEqualOp = conDouble "exEqualOp"

whenElseOp :: Isa.Term
whenElseOp = conDouble "whenElseOp"

uncurryOpS :: String
uncurryOpS = "uncurryOp"

uncurryOp :: Isa.Term
uncurryOp = conDouble uncurryOpS

-- terms
transTerm :: Env -> As.Term -> Result (FunType, Isa.Term)
transTerm sign trm = case trm of
    QualVar (VarDecl var t _ _) -> do
        fTy <- funType t
        return (fTy, Isa.Free (transVar var) $ transFunType fTy)
    QualOp _ (InstOpId opId is _) ts@(TypeScheme targs ty _) _ -> do
        fTy <- funType ty
        instfTy <- funType $ subst (if null is then Map.empty else
                    Map.fromList $ zipWith (\ (TypeArg _ _ _ _ i _ _) t
                                                -> (i, t)) targs is) ty
        let cf = mkTermAppl (convFun $ instType fTy instfTy)
            unCurry f = (fTy, termAppl uncurryOp $ con f)
        return $ case () of
          ()
              | opId == trueId -> (fTy, true)
              | opId == falseId -> (fTy, false)
              | opId == botId -> (fTy, noneOp)
              | opId == andId -> unCurry conjV
              | opId == orId -> unCurry disjV
              | opId == implId -> unCurry implV
              | opId == infixIf -> (fTy, ifImplOp)
              | opId == eqvId -> unCurry eqV
              | opId == exEq -> (fTy, exEqualOp)
              | opId == eqId -> (instfTy, cf $ termAppl uncurryOp $ con eqV)
              | opId == notId -> (fTy, notOp)
              | opId == defId -> (instfTy, cf $ defOp)
              | opId == whenElse -> (fTy, whenElseOp)
              | otherwise -> (instfTy,
                            cf $ (if isPlainFunType fTy == 2 && isMixfix opId
                                  then termAppl uncurryOp
                                  else id) $ con $ transOpId sign opId ts)
    QuantifiedTerm quan varDecls phi _ -> do
        let qname = case quan of
                      Universal -> allS
                      Existential -> exS
                      Unique -> ex1S
            quantify phi' gvd = case gvd of
                GenVarDecl (VarDecl var typ _ _) -> do
                    ty <- transType typ
                    return $ termAppl (conDouble $ qname)
                               $ Abs (con $ transVar var)
                                 ty phi' NotCont
                GenTypeVarDecl _ ->  return phi'
        (ty, psi) <- transTerm sign phi
        psiR <- foldM quantify psi $ reverse varDecls
        return (ty, psiR)
    TypedTerm t _q _ty _ -> transTerm sign t
    LambdaTerm pats q body r -> do
        p@(ty, _) <- transTerm sign body
        pt <- case q of
            Partial -> return p
            Total -> if isPartialVal ty
                     then fatal_error
                         ("partial lambda body in total abstraction: "
                          ++ showDoc body "") r
                     else return p
        foldM (abstraction sign) pt $ reverse pats
    LetTerm As.Let peqs body _ -> do
        (bTy, bTrm) <- transTerm sign body
        nEqs <- mapM (transProgEq sign) peqs
        return (bTy, Isa.Let nEqs bTrm)
    TupleTerm ts@(_ : _) _ -> do
        nTs <- mapM (transTerm sign) ts
        return $ foldr1 ( \ (s, p) (t, e) ->
                          (PairType s t, Tuplex [p, e] NotCont)) nTs
    TupleTerm [] _ -> return (UnitType, unitOp)
    ApplTerm t1 t2 _ -> mkApp sign t1 t2 -- transAppl sign Nothing t1 t2
    _ -> fatal_error ("cannot translate term: " ++ showDoc trm "")
         $ getRange trm

instType :: FunType -> FunType -> ConvFun
instType f1 f2 = case (f1, f2) of
    (TupleType l1, _) -> instType (foldr1 PairType l1) f2
    (_, TupleType l2) -> instType f1 $ foldr1 PairType l2
    (PartialVal (TypeVar _), BoolType) -> Option2bool
    (PairType a c, PairType b d) ->
        let c2 = instType c d
            c1 = instType a b
        in mkCompFun (mkMapFun MapSnd c2) $ mkMapFun MapFst c1
    (FunType a c, FunType b d) ->
         let c2 = instType c d
             c1 = instType a b
        in  mkCompFun (mkResFun c2) $ mkArgFun $ invertConv c1
    _ -> IdOp

invertConv :: ConvFun -> ConvFun
invertConv c = case c of
    Option2bool -> Bool2option
    MapFun mv cf -> MapFun mv $ invertConv cf
    ResFun cf -> ResFun $ invertConv cf
    ArgFun cf -> ArgFun $ invertConv cf
    CompFun c1 c2 -> CompFun (invertConv c2) (invertConv c1)
    _ -> IdOp

data MapFun = MapFst | MapSnd | MapSome

data LiftFun = LiftFst | LiftSnd

data ConvFun = IdOp | CompFun ConvFun ConvFun | ConstNil | ConstTrue | SomeOp
             | MapFun MapFun ConvFun | LiftFun LiftFun ConvFun
             | LiftUnit FunType
             | LiftSome FunType
             | ResFun ConvFun | ArgFun ConvFun | Bool2option | Option2bool

isNotIdOp :: ConvFun -> Bool
isNotIdOp f = case f of
    IdOp -> False
    _ -> True

mkCompFun :: ConvFun -> ConvFun -> ConvFun
mkCompFun f1 f2 = case f1 of
    IdOp -> f2
    _ -> case f2 of
           IdOp -> f1
           _ -> CompFun f1 f2

mkMapFun :: MapFun -> ConvFun -> ConvFun
mkMapFun m f = case f of
    IdOp -> IdOp
    _ -> MapFun m f

mkLiftFun :: LiftFun -> ConvFun -> ConvFun
mkLiftFun lv c = case c of
    IdOp -> IdOp
    _ -> LiftFun lv c

liftFun :: LiftFun -> Isa.Term
liftFun lf = case lf of
    LiftFst -> liftFst
    LiftSnd -> liftSnd

mapFun :: MapFun -> Isa.Term
mapFun mf = case mf of
    MapFst -> mapFst
    MapSnd -> mapSnd
    MapSome -> mapSome

convFun :: ConvFun -> Isa.Term
convFun cvf = case cvf of
    IdOp -> idOp
    Bool2option -> bool2option
    Option2bool -> option2bool
    LiftUnit rTy -> case rTy of
       UnitType -> liftUnit2unit
       BoolType -> liftUnit2bool
       PartialVal _ -> liftUnit2option
       _ -> liftUnit
    LiftSome rTy ->
        case rTy of
            UnitType -> lift2unit
            BoolType -> lift2bool
            PartialVal _ -> lift2option
            _ -> lift
    CompFun f1 f2 ->
        mkTermAppl (mkTermAppl (con compV) $ convFun f1) $ convFun f2
    ConstNil -> constNil
    ConstTrue -> constTrue
    SomeOp -> conSome
    MapFun mf cv -> mkTermAppl (mapFun mf) $ convFun cv
    LiftFun lf cv -> mkTermAppl (liftFun lf) $ convFun cv
    ArgFun cv -> mkTermAppl argFunOp $ convFun cv
    ResFun cv -> mkTermAppl (con compV) $ convFun cv

liftFst, liftSnd, mapFst, mapSnd, mapSome, idOp, bool2option,
    option2bool, constNil, constTrue, argFunOp,
    liftUnit2unit, liftUnit2bool, liftUnit2option, liftUnit, lift2unit,
    lift2bool, lift2option, lift :: Isa.Term

liftFst = conDouble "liftFst"
liftSnd = conDouble "liftSnd"
mapFst = conDouble "mapFst"
mapSnd = conDouble "mapSnd"
mapSome = conDouble "mapSome"
idOp = conDouble "id"
bool2option = conDouble "bool2option"
option2bool = conDouble "option2bool"
constNil = conDouble "constNil"
constTrue = conDouble "constTrue"
argFunOp = conDouble "flipComp"
liftUnit2unit = conDouble "liftUnit2unit"
liftUnit2bool = conDouble "liftUnit2bool"
liftUnit2option = conDouble "liftUnit2option"
liftUnit = conDouble "liftUnit"
lift2unit = conDouble "lift2unit"
lift2bool = conDouble "lift2bool"
lift2option = conDouble "lift2option"
lift = conDouble "mapSome"

unpackOp :: FunType -> Isa.Term
unpackOp ft = case ft of
    UnitType -> conDouble "unpack2bool"
    BoolType -> conDouble "unpackBool"
    PartialVal _ -> conDouble "unpackOption"
    _ ->  conDouble "unpack2option"

-- True means require result type to be partial
adjustTypes :: FunType -> FunType -> FunType
            -> Result ((Bool, ConvFun), (FunType, ConvFun))
adjustTypes aTy rTy ty = case (aTy, ty) of
    (TupleType l, _) -> adjustTypes (foldr1 PairType l) rTy ty
    (_, TupleType l) -> adjustTypes aTy rTy $ foldr1 PairType l
    (BoolType, BoolType) -> return ((False, IdOp), (ty, IdOp))
    (UnitType, UnitType) -> return ((False, IdOp), (ty, IdOp))
    (PartialVal _, BoolType) -> return ((False, IdOp), (aTy, Bool2option))
    (BoolType, PartialVal _) -> return ((False, IdOp), (aTy, Option2bool))
    (_, BoolType) -> return ((True, LiftUnit rTy), (ty, IdOp))
    (BoolType, _) -> return ((False, IdOp), (aTy, ConstTrue))
    (PartialVal a, PartialVal b) -> do
        q@(fp, (argTy, aTrm)) <- adjustTypes a rTy b
        return $ case argTy of
            PartialVal _ -> q
            _ -> (fp, (PartialVal argTy, mkMapFun MapSome aTrm))
    (a, PartialVal b) -> do
        q@(_, ap@(argTy, _)) <- adjustTypes a rTy b
        return $ case argTy of
            PartialVal _ -> q
            _ -> ((True, LiftSome rTy), ap)
    (PartialVal a, b) -> do
        q@(fp, (argTy, aTrm)) <- adjustTypes a rTy b
        return $ case argTy of
            PartialVal _ -> q
            _ -> (fp, (PartialVal argTy, mkCompFun SomeOp aTrm))
    (PairType a c, PairType b d) -> do
        ((res2Ty, f2), (arg2Ty, a2)) <- adjustTypes c rTy d
        ((res1Ty, f1), (arg1Ty, a1)) <- adjustTypes a
                (if res2Ty then makePartialVal rTy else rTy) b
        return $ ((res1Ty || res2Ty,
             mkCompFun (mkLiftFun LiftFst f1) $ mkLiftFun LiftSnd f2),
                  (PairType arg1Ty arg2Ty,
                   mkCompFun (mkMapFun MapSnd a2) $ mkMapFun MapFst a1))
    (FunType a c, FunType b d) -> do
        ((_, aF), (aT, aC)) <- adjustTypes b c a
        ((cB, cF), (dT, dC)) <- adjustTypes c rTy d
        if cB || isNotIdOp cF
          then fail "cannot adjust result types of function type"
          else return ((False, IdOp),
                       (FunType aT dT,
                        mkCompFun aF $ mkCompFun (mkResFun dC) $ mkArgFun aC))
    (TypeVar _, _) -> return ((False, IdOp), (ty, IdOp))
    (_, TypeVar _) -> return ((False, IdOp), (aTy, IdOp))
    (ApplType i1 l1, ApplType i2 l2) | i1 == i2 && length l1 == length l2
        -> do l <- mapM (\ (a, b) -> adjustTypes a rTy b) $ zip l1 l2
              if or (map (fst . fst) l) || or
                 (map (isNotIdOp . snd . snd) l)
                then fail "cannot adjust type application"
                else return ((False, IdOp),
                             (ApplType i1 $ map (fst . snd) l, IdOp))
    _ -> fail "cannot adjust types"

applConv :: ConvFun -> Isa.Term -> Isa.Term
applConv cnv t = case cnv of
    IdOp -> t
    _ -> mkTermAppl (convFun cnv) t

mkArgFun :: ConvFun -> ConvFun
mkArgFun c = case c of
    IdOp -> c
    _ -> ArgFun c

mkResFun :: ConvFun -> ConvFun
mkResFun c = case c of
    IdOp -> c
    _ -> ResFun c

isEquallyLifted :: Isa.Term -> Isa.Term -> Maybe (Isa.Term, Isa.Term, Isa.Term)
isEquallyLifted l r = case (l, r) of
    (MixfixApp ft@(Const f _) [la] _,
     MixfixApp (Const g _) [ra] _)
        | f == g && elem (new f) [someS, "option2bool", "bool2option"]
            -> Just (ft, la, ra)
    _ -> Nothing

mkTermAppl :: Isa.Term -> Isa.Term -> Isa.Term
mkTermAppl fun arg = case (fun, arg) of
      (MixfixApp (Const uc _) [b@(Const bin _)] c, Tuplex a@[l, r] _)
          | new uc == uncurryOpS -- && elem (new bin) [eq, conj, disj, impl]
              -> case isEquallyLifted l r of
                   Just (_, la, ra) | new bin == eq -> MixfixApp b [la, ra] c
                   _ -> MixfixApp b a c
      (MixfixApp (Const mp _) [f] _, Tuplex [a, b] c)
          | new mp == "mapFst" -> Tuplex [mkTermAppl f a, b] c
          | new mp == "mapSnd" -> Tuplex [a, mkTermAppl f b] c
      (Const mp _, Tuplex [a, b] _)
          | new mp == "ifImplOp" -> binImpl b a
      (Const mp _, Tuplex [a, Tuplex [b, c] _] d)
          | new mp == "whenElseOp" -> case isEquallyLifted a c of
              Just (f, na, nc) -> mkTermAppl f $ If b na nc d
              Nothing -> If b a c d
      (MixfixApp (Const mp _) [f] c, _)
          | new mp == "liftUnit2bool" -> let af = mkTermAppl f unitOp in
             case arg of
               Const ma _ | new ma == "True" -> af
                          | new ma == "False" -> false
               _ -> If arg af false c
          | new mp == "liftUnit2option" -> let af = mkTermAppl f unitOp in
             case arg of
               Const ma _ | new ma == "True" -> af
                          | new ma == "False" -> noneOp
               _ -> If arg af noneOp c
      (MixfixApp (Const mp _) [_] _, _)
          | new mp == "liftUnit2unit" -> arg
          | new mp == "lift2unit" -> mkTermAppl (conDouble "option2bool") arg
      (MixfixApp (MixfixApp (Const cmp _) [f] _) [g] c, _)
          | new cmp == compS -> mkTermAppl f $ mkTermAppl g arg
          | new cmp == "flipComp" -> mkTermAppl g $ mkTermAppl f arg
          | new cmp == "flipCurryOp" -> mkTermAppl f $ Tuplex [arg, g] c
          | new cmp == "curryOp" -> mkTermAppl f $ Tuplex [g, arg] c
      (MixfixApp (MixfixApp (Const cmp _) [f] _) [g] _,
       Tuplex [a, b] _)
          | new cmp == "liftFst" -> mkTermAppl (mkTermAppl f
                (mkTermAppl (mkTermAppl (conDouble "flipCurryOp") g) b)) a
          | new cmp == "liftSnd" -> mkTermAppl (mkTermAppl f
                (mkTermAppl (mkTermAppl (conDouble "curryOp") g) a)) b
      (Const d _, MixfixApp (Const sm _) [a] _)
          | new d == "defOp" && new sm == someS -> true
          | new d == "option2bool" && new sm == someS -> true
          | new d == "option2bool" && new sm == "bool2option"
            || new d == "bool2option" && new sm == "option2bool" -> a
      (Const i _, _)
          | new i == "bool2option" ->
              let tc = mkTermAppl conSome $ unitOp
              in case arg of
                    Const j _ | new j == "True" -> tc
                              | new j == "False" -> noneOp
                    _ -> termAppl fun arg -- If arg tc noneOp NotCont
          | new i == "id" -> arg
          | new i == "constTrue" -> true
          | new i == "constNil" -> unitOp
      (Const i _, Tuplex [] _)
          | new i == "option2bool" -> false
      _ -> termAppl fun arg

mkApp :: Env -> As.Term -> As.Term -> Result (FunType, Isa.Term)
mkApp sg f arg = do
    (fTy, fTrm) <- transTerm sg f
    (aTy, aTrm) <- transTerm sg arg
    case fTy of
         FunType a r -> do
             ((rTy, fConv), (_, aConv)) <- adjustTypes a r aTy
             return $ (if rTy then makePartialVal r else r,
                mkTermAppl (applConv fConv fTrm)
                             $ applConv aConv aTrm)
         PartialVal (FunType a r) -> do
             ((_, fConv), (_, aConv)) <- adjustTypes a r aTy
             let resTy = makePartialVal r
             return (resTy, mkTermAppl (mkTermAppl (mkTermAppl
                              (unpackOp r) $ convFun fConv) fTrm)
                            $ applConv aConv aTrm)
         _ -> fail "not a function type"

-- * translation of lambda abstractions

getPatternType :: As.Term -> Result FunType
getPatternType t =
      case t of
        QualVar (VarDecl _ typ _ _) -> funType typ
        TypedTerm _ _ typ _ -> funType typ
        TupleTerm ts _ -> do
            ptys <- mapM getPatternType ts
            return $ foldr1 PairType ptys
        _ -> fatal_error ("not a pattern for Isabelle: " ++ showDoc t "")
             $ getRange t

transPattern :: Env -> As.Term -> Result Isa.Term
transPattern sign pat = do
    (ty, trm) <- transTerm sign pat
    if isPartialVal ty then
        fatal_error ("pattern must not be partial: " ++ showDoc pat "")
             $ getRange pat
       else return trm

-- form Abs(pattern term)
abstraction :: Env -> (FunType, Isa.Term) -> As.Term
            -> Result (FunType, Isa.Term)
abstraction sign (ty, body) pat = do
    pTy <- getPatternType pat
    nPat <- transPattern sign pat
    return (FunType pTy ty, Abs nPat (transFunType pTy) body NotCont)
