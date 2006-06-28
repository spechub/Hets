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
import Common.Id
import Common.Result
import qualified Common.Lib.Map as Map
import Common.AS_Annotation (Named(..))

import Data.List
import Data.Maybe

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
    map_theory PCoClTyConsHOL2IsabelleHOL = mkTheoryMapping transSignature
                   (map_sentence PCoClTyConsHOL2IsabelleHOL)
    map_morphism = mapDefaultMorphism
    map_sentence PCoClTyConsHOL2IsabelleHOL sign phi =
       case transSentence sign phi of
         Nothing   -> warning (mkSen true)
                           "translation of sentence not implemented" nullRange
         Just (ts) -> return $ mkSen ts
    map_symbol = errMapSymbol

-- * Signature
baseSign :: BaseSig
baseSign = MainHC_thy

transSignature :: Env -> Result (Isa.Sign,[Named Isa.Sentence])
transSignature sign =
  return (Isa.emptySign {
    baseSig = baseSign,
    -- translation of typeconstructors
    tsig = emptyTypeSig
             { arities = Map.foldWithKey extractTypeName
                                        Map.empty
                                        (typeMap sign) },
    -- translation of operation declarations
    constTab = Map.foldWithKey insertOps
                               Map.empty
                               (assumps sign),
    -- translation of datatype declarations
    domainTab = transDatatype (typeMap sign),
    showLemmas = True },
    [] )
   where
    extractTypeName tyId typeInfo m =
        if isDatatypeDefn typeInfo then m
           else let getTypeArgs n k = case k of
                        ClassKind _ -> []
                        FunKind _ _ r _ ->
                            (TFree ("'a" ++ show n) [], [isaTerm])
                                           : getTypeArgs (n + 1) r
                in Map.insert (showIsaTypeT tyId baseSign)
                  [(isaTerm, getTypeArgs (1 :: Int) $ typeKind typeInfo)] m
    isDatatypeDefn t = case typeDefn t of
                         DatatypeDefn _ -> True
                         _              -> False
    insertOps name ops m =
     let infos = opInfos ops
     in if isSingle infos then
            let transOp = transOpInfo (head infos)
            in case transOp of
                 Just op ->
                     Map.insert (mkVName $ showIsaConstT name baseSign) op m
                 Nothing -> m
          else
            let transOps = map transOpInfo infos
            in  foldl (\ m' (transOp,i) ->
                           case transOp of
                             Just typ -> Map.insert
                                 (mkVName $ showIsaConstIT name i baseSign)
                                 typ m'
                             Nothing   -> m')
                      m (zip transOps [1::Int ..])

-- * translation of a type in an operation declaration

-- extract type from OpInfo
-- omit datatype constructors
transOpInfo :: OpInfo -> Maybe Typ
transOpInfo (OpInfo t _ opDef) =  case opDef of
    ConstructData _ -> Nothing
    _  -> Just (transOpType t)

-- operation type
transOpType :: TypeScheme -> Typ
transOpType (TypeScheme _ op _) = transType op

unitTyp :: Typ
unitTyp = Type "unit" holType []
-- types
transType :: Type -> Typ
transType = transFunType . funType

transFunType :: FunType -> Typ
transFunType fty = case fty of
    UnitType -> unitTyp
    BoolType -> boolType
    FunType f a -> mkFunType (transFunType f) $ transFunType a
    PartialVal a -> mkOptionType $ transFunType a
    PairType a b -> prodType (transFunType a) $ transFunType b
    ApplType tid args -> Type (showIsaTypeT tid baseSign) []
                       $ map transFunType args
    TypeVar tid -> TFree (showIsaTypeT tid baseSign) []

data FunType = UnitType | BoolType | FunType FunType FunType
             | PartialVal FunType | PairType FunType FunType
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

funType :: Type -> FunType
funType t = case getTypeAppl t of
   (TypeName tid _ n, tys) ->
       if n == 0 then
           case map funType tys of
           [] | tid == unitTypeId -> UnitType
           [ty] | tid == lazyTypeId -> makePartialVal ty
           [t1, t2] | isArrow tid -> FunType t1 $ if isPartialArrow tid then
                                               makePartialVal t2 else t2
           ftys@(_ : _ : _) | isProductId tid -> foldl1 PairType ftys
           ftys -> ApplType tid ftys
       else if null tys then TypeVar tid
            else error "funType: no higher kinds"
   _ -> error "funType: no type appl"

-- * translation of a datatype declaration

transDatatype :: TypeMap -> DomainTab
transDatatype tm = map transDataEntry (Map.fold extractDataypes [] tm)
  where extractDataypes ti des = case typeDefn ti of
                                   DatatypeDefn de -> des++[de]
                                   _               -> des

-- datatype with name (tyId) + args (tyArgs) and alternatives
transDataEntry :: DataEntry -> [DomainEntry]
transDataEntry (DataEntry _ tyId _ tyArgs _ alts) =
    -- only free types are allowed
    [(transDName tyId tyArgs, map transAltDefn alts)]
  where transDName ti ta = Type (showIsaTypeT ti baseSign) []
                           $ map transTypeArg ta

-- arguments of datatype's typeconstructor
transTypeArg :: TypeArg -> Typ
transTypeArg ta = TFree (showIsaTypeT (getTypeVar ta) baseSign) []

-- datatype alternatives/constructors
transAltDefn :: AltDefn -> (VName, [Typ])
transAltDefn (Construct opId ts Total _) =
   let ts' = map transType ts
   in case opId of
        Just opId' -> (mkVName $ showIsaConstT opId' baseSign, ts')
        Nothing  -> (mkVName "", ts')
transAltDefn _ = error "PCoClTyConsHOL2IsabelleHOL.transAltDefn"

-- * Formulas

-- simple variables
transVar :: Var -> VName
transVar v = mkVName $ showIsaConstT v baseSign

transSentence :: Env -> Le.Sentence -> Maybe Isa.Term
transSentence sign s = case s of
    Le.Formula trm -> Just $ case transTerm sign trm of
        (BoolType, t) -> t
        (PartialVal _, t) -> mkTermAppl option2bool t
        (FunType _ _, _) -> error "transSentence: FunType"
        (PairType _ _, _) -> error "transSentence: PairType"
        (ApplType _ _, _) -> error "transSentence: ApplType"
        _ -> true
    DatatypeSen _ -> Nothing
    ProgEqSen _ _ _ -> Nothing

-- disambiguate operation names
transOpId :: Env -> UninstOpId -> TypeScheme -> String
transOpId sign op ts =
  case (do ops <- Map.lookup op (assumps sign)
           if isSingle (opInfos ops) then return $ showIsaConstT op baseSign
             else do i <- elemIndex ts (map opType (opInfos ops))
                     return $ showIsaConstIT op (i+1) baseSign) of
    Just str -> str
    Nothing  -> error $ "transOpId " ++ showIsaConstT op baseSign

transProgEq :: Env -> ProgEq -> (Isa.Term, Isa.Term)
transProgEq sign (ProgEq pat trm _) =
    let op = transPattern sign pat
        (ty, ot) = transTerm sign trm
    in if isPartialVal ty then error "transProgEq"
       else (op, ot)

ifImplOp :: Isa.Term
ifImplOp = conDouble "ifImplOp"

unitOp :: Isa.Term
unitOp = Tuplex [] NotCont

noneOp :: Isa.Term
noneOp = conDouble "None"

exEqualOp :: Isa.Term
exEqualOp = conDouble "exEqualOp"

ifThenElseOp :: Isa.Term
ifThenElseOp = conDouble "ifThenElseOp"

uncurryOpS :: String
uncurryOpS = "uncurryOp"

uncurryOp :: Isa.Term
uncurryOp = conDouble uncurryOpS

-- terms
transTerm :: Env -> As.Term -> (FunType, Isa.Term)
transTerm sign trm = case trm of
    QualVar (VarDecl var t _ _) -> (funType t,
        Isa.Free (transVar var) $ transType t)
    QualOp _ (InstOpId opId is _) ts@(TypeScheme targs ty _) _
      | opId == trueId -> (fTy, true)
      | opId == falseId -> (fTy, false)
      | opId == botId -> (fTy, noneOp)
      | opId == andId -> unCurry conjV
      | opId == orId -> unCurry disjV
      | opId == implId -> unCurry implV
      | opId == infixIf -> (fTy, ifImplOp)
      | opId == eqvId -> unCurry eqV
      | opId == exEq -> (fTy, exEqualOp)
      | opId == eqId -> (instfTy, cf $ mkTermAppl uncurryOp $ con eqV)
      | opId == notId -> (fTy, notOp)
      | opId == defId -> (instfTy, cf $ defOp)
      | opId == whenElse -> (fTy, ifThenElseOp)
      | otherwise -> (instfTy, cf $ conDouble $ transOpId sign opId ts)
       where instfTy = funType $ subst (if null is then Map.empty else
                    Map.fromList $ zipWith (\ (TypeArg _ _ _ _ i _ _) t
                          -> (i, t)) targs is) ty
             fTy = funType ty
             cf = mkTermAppl (convFun $ instType fTy instfTy)
             unCurry f = (fTy, mkTermAppl uncurryOp $ con f)
    QuantifiedTerm quan varDecls phi _ ->
        let quantify q gvd phi' = case gvd of
                GenVarDecl (VarDecl var typ _ _) ->
                    termAppl (conDouble $ qname q)
                    $ Abs (con $ transVar var)
                          (transType typ) phi' NotCont
                GenTypeVarDecl _ ->  phi'
            qname Universal   = allS
            qname Existential = exS
            qname Unique      = ex1S
            (ty, psi) = transTerm sign phi
        in (ty, foldr (quantify quan) psi varDecls)
    TypedTerm t _q _ty _ -> transTerm sign t
    LambdaTerm pats q body _ ->
        let (ty, t) = transTerm sign body in
        foldr (abstraction sign) (case q of
            Partial -> -- if isPartialVal ty then
                           (ty, t)
                       -- else (makePartialVal ty, termAppl conSome t)
            Total -> if isPartialVal ty
                     then error "PCoClTyConsHOL2IsabelleHOL.totalLambda"
                     else (ty, t)) pats
    LetTerm As.Let peqs body _ ->
        let (bTy, bTrm) = transTerm sign body
        in (bTy, Isa.Let (map (transProgEq sign) peqs) bTrm)
    TupleTerm ts@(_ : _) _ ->
        foldl1 ( \ (s, p) (t, e) -> (PairType s t, Tuplex [p, e] NotCont))
                   $ map (transTerm sign) ts
    TupleTerm [] _ -> (UnitType, unitOp)
    ApplTerm t1 t2 _ -> mkApp sign t1 t2 -- transAppl sign Nothing t1 t2
    _ -> error $ "PCoClTyConsHOL2IsabelleHOL.transTerm " ++ showPretty trm "\n"
                ++ show trm

instType :: FunType -> FunType -> ConvFun
instType f1 f2 = case (f1, f2) of
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
    CompFun f1 f2 -> mkTermAppl (mkTermAppl compFun $ convFun f1) $ convFun f2
    ConstNil -> constNil
    ConstTrue -> constTrue
    SomeOp -> conSome
    MapFun mf cv -> mkTermAppl (mapFun mf) $ convFun cv
    LiftFun lf cv -> mkTermAppl (liftFun lf) $ convFun cv
    ArgFun cv -> mkTermAppl argFunOp $ convFun cv
    ResFun cv -> mkTermAppl compFun $ convFun cv

liftFst, liftSnd, mapFst, mapSnd, mapSome, idOp, bool2option,
    option2bool, compFun, constNil, constTrue, argFunOp,
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
compFun = conDouble "comp"
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
            -> ((Bool, ConvFun), (FunType, ConvFun))
adjustTypes aTy rTy ty = case (aTy, ty) of
    (BoolType, BoolType) -> ((False, IdOp), (ty, IdOp))
    (UnitType, UnitType) -> ((False, IdOp), (ty, IdOp))
    (PartialVal _, BoolType) -> ((False, IdOp), (aTy, Bool2option))
    (BoolType, PartialVal _) -> ((False, IdOp), (aTy, Option2bool))
    (_, BoolType) -> ((True, LiftUnit rTy), (ty, IdOp))
    (BoolType, _) -> ((False, IdOp), (aTy, ConstTrue))
    (PartialVal a, PartialVal b) -> case adjustTypes a rTy b of
        q@(fp, (argTy, aTrm)) -> case argTy of
            PartialVal _ -> q
            _ -> (fp, (PartialVal argTy, mkMapFun MapSome aTrm))
    (a, PartialVal b) -> case adjustTypes a rTy b of
        q@(_, ap@(argTy, _)) -> case argTy of
            PartialVal _ -> q
            _ -> ((True, LiftSome rTy), ap)
    (PartialVal a, b) -> case adjustTypes a rTy b of
        q@(fp, (argTy, aTrm)) -> case argTy of
            PartialVal _ -> q
            _ -> (fp, (PartialVal argTy, mkCompFun SomeOp aTrm))
    (PairType a c, PairType b d) ->
        let ((res2Ty, f2), (arg2Ty, a2)) = adjustTypes c rTy d
            ((res1Ty, f1), (arg1Ty, a1)) = adjustTypes a
                (if res2Ty then makePartialVal rTy else rTy) b
        in ((res1Ty || res2Ty,
             mkCompFun (mkLiftFun LiftFst f1) $ mkLiftFun LiftSnd f2),
           (PairType arg1Ty arg2Ty,
           mkCompFun (mkMapFun MapSnd a2) $ mkMapFun MapFst a1))
    (FunType a c, FunType b d) ->
       let ((_, aF), (aT, aC)) = adjustTypes b c a
           ((cB, cF), (dT, dC)) = adjustTypes c rTy d
       in if cB || isNotIdOp cF
          then error "adjustTypes.FunTypes" else ((False, IdOp),
           (FunType aT dT,
                    mkCompFun aF $ mkCompFun (mkResFun dC) $ mkArgFun aC))
    (TypeVar _, _) -> ((False, IdOp), (ty, IdOp))
    (_, TypeVar _) -> ((False, IdOp), (aTy, IdOp))
    (ApplType i1 l1, ApplType i2 l2) | i1 == i2 && length l1 == length l2
        -> let l = zipWith (\ a b -> adjustTypes a rTy b) l1 l2
           in if or (map (fst . fst) l) || or
                 (map (isNotIdOp . snd . snd) l)
              then error "adjustTypes.ApplType"
              else ((False, IdOp), (ApplType i1 $ map (fst . snd) l, IdOp))
    _ -> error "adjustTypes"

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

mkTermAppl :: Isa.Term -> Isa.Term -> Isa.Term
mkTermAppl fun arg = case (fun, arg) of
      (MixfixApp (Const uc _) [b@(Const bin _)] c, Tuplex a@[_, _] _)
          | new uc == uncurryOpS && elem (new bin) [eq, conj, disj, impl]
              -> MixfixApp b a c
      (MixfixApp (Const mp _) [f] _, Tuplex [a, b] c)
          | new mp == "mapFst" -> Tuplex [mkTermAppl f a, b] c
          | new mp == "mapSnd" -> Tuplex [a, mkTermAppl f b] c
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
          | new cmp == "comp" -> mkTermAppl f $ mkTermAppl g arg
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
                    _ -> If arg tc noneOp NotCont
          | new i == "id" -> arg
          | new i == "constTrue" -> true
          | new i == "constNil" -> unitOp
      (Const i _, Tuplex [] _)
          | new i == "option2bool" -> false
      _ -> termAppl fun arg

mkApp :: Env -> As.Term -> As.Term -> (FunType, Isa.Term)
mkApp sg f arg =
    let (fTy, fTrm) = transTerm sg f
        (aTy, aTrm) = transTerm sg arg
    in case fTy of
         FunType a r -> let ((rTy, fConv), (_, aConv)) = adjustTypes a r aTy
            in (if rTy then makePartialVal r else r,
                mkTermAppl (applConv fConv fTrm)
                             $ applConv aConv aTrm)
         PartialVal (FunType a r) ->
             let ((_, fConv), (_, aConv)) = adjustTypes a r aTy
                 resTy = makePartialVal r
             in (resTy,
                mkTermAppl (mkTermAppl (mkTermAppl
                              (unpackOp r) $ convFun fConv) fTrm)
                  $ applConv aConv aTrm)
         _ -> error "not a function type"

-- * translation of lambda abstractions

getPatternType :: As.Term -> FunType
getPatternType t =
      case t of
        QualVar (VarDecl _ typ _ _) -> funType typ
        TypedTerm _ _ typ _         -> funType typ
        TupleTerm ts _           -> foldr1 PairType $ map getPatternType ts
        _ -> error "PCoClTyConsHOL2IsabelleHOL.getPatternType"

transPattern :: Env -> As.Term -> Isa.Term
transPattern sign pat =
    let (ty, trm) = transTerm sign pat
    in if isPartialVal ty then error "transPattern"
       else trm

-- form Abs(pattern term)
abstraction :: Env -> As.Term -> (FunType, Isa.Term) -> (FunType, Isa.Term)
abstraction sign pat (ty, body) = let pTy = getPatternType pat in
    (FunType pTy ty,
     Abs (transPattern sign pat) (transFunType pTy) body NotCont)
