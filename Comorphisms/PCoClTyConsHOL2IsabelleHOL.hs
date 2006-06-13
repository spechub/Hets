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
                                 (mkVName $ showIsaConstIT name i baseSign)                                 typ m'
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
transType = transFunType . funType False False

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
makePartialVal t = if isPartialVal t then t else 
                       case t of 
                         UnitType -> BoolType 
                         _ -> PartialVal t

funType :: Bool -> Bool -> Type -> FunType
funType makeResPartial makeArgTotal t = case getTypeAppl t of
   (TypeName tid _ n, tys) -> 
       if n == 0 then 
           case tys of 
           [] | tid == unitTypeId -> UnitType
           [ty] | tid == lazyTypeId -> if makeArgTotal then
               funType True True ty else makePartialVal 
                       $ funType makeResPartial makeArgTotal ty
           [t1, t2] | isArrow tid -> 
                FunType (funType True makeArgTotal t1) $
              (if isPartialArrow tid || makeResPartial 
               then makePartialVal else id)
                 $ funType makeResPartial makeArgTotal t2
           ftys@(_ : _ : _) | isProductId tid -> foldl1 PairType 
                $ map (funType makeResPartial makeArgTotal) ftys
           ftys -> ApplType tid $ map (funType True True) ftys
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
        (PartialVal _, t) -> termAppl option2bool t
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
    let op = transTerm sign pat
        ot = transTerm sign trm
    in {- if isPartial op || isPartial ot then
           (someTerm op, someTerm ot)
       else -} (snd op, snd ot)

ifImplOp :: Isa.Term
ifImplOp = conDouble "ifImplOp"

unitOp :: Isa.Term
unitOp = Tuplex [] NotCont

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
    QualVar (VarDecl var t _ _) -> (funType False False t,  
        Isa.Free (transVar var) $ transType t)
    QualOp _ (InstOpId opId _ _) ts@(TypeScheme _ ty _) _ 
      | opId == trueId -> (fTy, true)
      | opId == falseId -> (fTy, false)
      | opId == botId -> (fTy, conDouble "None")
      | opId == andId -> unCurry conjV
      | opId == orId -> unCurry disjV
      | opId == implId -> unCurry implV
      | opId == infixIf -> (fTy, ifImplOp)
      | opId == eqvId -> unCurry eqV
      | opId == exEq -> (fTy, exEqualOp) 
      | opId == eqId -> unCurry eqV
      | opId == notId -> (fTy, notOp)
      | opId == defId -> (fTy, defOp)
      | opId == whenElse -> (fTy, ifThenElseOp)
      | otherwise -> (fTy, conDouble $ transOpId sign opId ts)
       where fTy = funType False False ty
             unCurry f = (fTy, termAppl uncurryOp $ con f) 
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
            (_, psi) = transTerm sign phi
        in (BoolType, foldr (quantify quan) psi varDecls)
    TypedTerm t _ _ _ -> transTerm sign t
    LambdaTerm pats _ body _ ->
        let tPats = map (fst . transTerm sign) pats 
            (bodyTy, bodyTrm) = transTerm sign body
        in ( foldr FunType bodyTy tPats
           , foldr (abstraction sign) bodyTrm pats )
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
    CompFun f1 f2 -> termAppl (termAppl compFun $ convFun f1) $ convFun f2
    ConstNil -> constNil
    ConstTrue -> constTrue
    SomeOp -> conSome
    MapFun mf cv -> mkTermAppl (mapFun mf) $ convFun cv
    LiftFun lf cv -> termAppl (liftFun lf) $ convFun cv
    ArgFun cv -> termAppl argFunOp $ convFun cv
    ResFun cv -> termAppl compFun $ convFun cv

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
argFunOp = conDouble "argFunOp"
liftUnit2unit = conDouble "liftUnit2unit"
liftUnit2bool = conDouble "liftUnit2bool"
liftUnit2option = conDouble "liftUnit2option"
liftUnit = conDouble "liftUnit"
lift2unit = conDouble "lift2unit"
lift2bool = conDouble "lift2bool"
lift2option = conDouble "lift2option"
lift = conDouble "mapSome"

unpackOp :: FunType -> Isa.Term
unpackOp _ = conDouble "unpackOp"

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
       let ((aB, aF), (aT, aC)) = adjustTypes b c a 
           ((cB, cF), (dT, dC)) = adjustTypes c rTy d
       in if aB || cB || isNotIdOp aF || isNotIdOp cF 
          then error "adjustTypes.FunTypes" else ((False, IdOp), 
           (FunType aT dT, mkCompFun (mkResFun dC) (mkArgFun aC)))
    (TypeVar _, FunType b d) -> 
       let r = makePartialVal d
           (_, (dT, dC)) = adjustTypes r rTy d
       in ((False, IdOp), 
           (FunType b dT, mkResFun dC))
    (TypeVar _, _) -> ((False, IdOp), (ty, IdOp))
    (_,  TypeVar _) -> ((False, IdOp), (aTy, IdOp))
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
      (MixfixApp (Const uc _) [b@(Const bin _)] c, 
       Tuplex a@[_, _] _) | new uc == uncurryOpS && 
                                     elem (new bin) [eq, conj, disj, impl]
                                     -> MixfixApp b a c
      (MixfixApp (Const mp _) [f] _,
       Tuplex [a, b] c) 
          | new mp == "mapFst" -> Tuplex [mkTermAppl f a, b] c
          | new mp == "mapSnd" -> Tuplex [a, mkTermAppl f b] c
      (MixfixApp (MixfixApp (Const cmp _) [f] _) [g] _, _)
          | new cmp == "comp" -> mkTermAppl f $ mkTermAppl g arg
      (Const d _, MixfixApp (Const sm _) [_] _) 
          | new d == "defOp" && new sm == someS -> true 
          | new d == "option2bool" && new sm == someS -> true
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
             let ((rTy, fConv), (_, aConv)) = adjustTypes a r aTy
                 resTy = makePartialVal r
             in (resTy, 
                mkTermAppl (termAppl (termAppl 
                              (unpackOp resTy) $ convFun fConv) fTrm)
                  $ applConv aConv aTrm)
         _ -> error "not a function type"

-- * translation of lambda abstractions

-- form Abs(pattern term)
abstraction :: Env -> As.Term -> Isa.Term -> Isa.Term
abstraction sign pat body =
    Abs (snd $ transTerm sign pat) (getType pat) body NotCont
    where
    getType t =
      case t of
        QualVar (VarDecl _ typ _ _) -> transType typ
        TypedTerm _ _ typ _         -> transType typ
        TupleTerm terms _           -> evalTupleType terms
        _                           ->
          error "PCoClTyConsHOL2IsabelleHOL.abstraction"
    evalTupleType t = foldr1 prodType (map getType t)
