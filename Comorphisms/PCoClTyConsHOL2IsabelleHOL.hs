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

{-
mkPairType :: FunType -> FunType -> FunType 
mkPairType a b = case (a, b) of 
    (PartialVal c, PartialVal d) -> PartialVal $ PairType c d
    (PartialVal c, _) -> PartialVal $ PairType c b
    (_, PartialVal d) -> PartialVal $ PairType a d
    _ -> PairType a b

makeFunType :: FunType -> FunType -> FunType 
makeFunType a b = case a of 
    PartialVal e@(FunType _ (PartialVal _)) -> FunType e b
    PartialVal (FunType c d) -> FunType (FunType c (PartialVal d)) b
    FunType _ (PartialVal _) -> FunType a b
    FunType c d -> FunType (FunType c (PartialVal d)) b
    _ -> FunType a b
-}

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

funType :: Type -> FunType
funType t = case getTypeAppl t of
   (TypeName tid _ n, tys) -> 
       if n == 0 then 
           case map funType tys of 
           [] | tid == unitTypeId -> UnitType
           [ty] | tid == lazyTypeId -> makePartialVal ty
           [t1, t2] | isArrow tid -> FunType (case t1 of 
                 FunType t3 t4 -> FunType t3 $ makePartialVal t4
                 PartialVal (FunType t3 t4) -> FunType t3 $ makePartialVal t4
                 _ -> t1) $
              (if isPartialArrow tid then makePartialVal else id) t2
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

option2bool :: Isa.Term
option2bool = conDouble "option2bool"

-- simple variables
transVar :: Var -> VName
transVar v = mkVName $ showIsaConstT v baseSign

transSentence :: Env -> Le.Sentence -> Maybe Isa.Term
transSentence sign s = case s of
    Le.Formula t      -> Just $ case transTerm sign t of 
                                 (UnitType, _) -> true
                                 (BoolType, t) -> t
                                 _ -> error "transSentence"
    DatatypeSen _     -> Nothing
    ProgEqSen _ _ _pe -> Nothing

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

uncurryOp :: Isa.Term
uncurryOp = conDouble "uncurryOp"

wrapLogOp :: Isa.Term
wrapLogOp = conDouble "wrapLogOp"

defOp1 :: Isa.Term
defOp1 = conDouble "defOp1"

notOp1 :: Isa.Term
notOp1 = conDouble "notOp1"

-- terms
transTerm :: Env -> As.Term -> (FunType, Isa.Term)
transTerm sign trm = case trm of
    QualVar (VarDecl var t _ _) -> (funType t,  
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
       where fTy = funType ty
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
        foldl1 ( \ (s, p) (t, e) -> (PairType s t, {- case (s, t) of
                  (PartialVal _, PartialVal _) -> binConst pairC p e
                  (PartialVal _, _) -> binConst "pairL" p e
                  (_, PartialVal _) -> binConst "pairR" p e
                  _ -> -} Tuplex [p, e] NotCont)) $ map (transTerm sign) ts
    TupleTerm [] _ -> (UnitType, unitOp)
    ApplTerm t1 t2 _ -> mkApp sign t1 t2 -- transAppl sign Nothing t1 t2
    _ -> error $ "PCoClTyConsHOL2IsabelleHOL.transTerm " ++ showPretty trm "\n"
                ++ show trm

data MapFun = MapFst | MapSnd | MapSome

data LiftFun = Lift | LiftFst | LiftSnd 

data ConvFun = IdOp | CompFun ConvFun ConvFun | ConstNil | ConstTrue | SomeOp 
             | MapFun MapFun ConvFun | LiftFun LiftFun ConvFun | LiftUnit
             | ResFun ConvFun | ArgFun ConvFun | Bool2Option | Option2Bool

liftFun :: LiftFun -> Isa.Term
liftFun lf = case lf of
    Lift -> liftToSome
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
    Bool2Option -> bool2option
    Option2Bool -> option2bool
    LiftUnit -> liftUnit
    CompFun IdOp f2 -> convFun f2
    CompFun f1 IdOp -> convFun f1
    CompFun f1 f2 -> termAppl (termAppl compFun $ convFun f1) $ convFun f2
    ConstNil -> constNil
    ConstTrue -> constTrue
    SomeOp -> conSome
    MapFun mf IdOp -> idOp
    MapFun mf cv -> termAppl (mapFun mf) $ convFun cv
    LiftFun lf cv -> termAppl (liftFun lf) $ convFun cv
    ArgFun cv -> termAppl argFunOp $ convFun cv
    ResFun cv -> termAppl resFunOp $ convFun cv

liftToSome = conDouble "liftToSome"
liftFst = conDouble "liftFst"
liftSnd = conDouble "liftSnd"
mapFst = conDouble "mapFst"
mapSnd = conDouble "mapSnd"
mapSome = conDouble "mapSome"
idOp = conDouble "idOp"
bool2option = conDouble "bool2option"
liftUnit = conDouble "liftUnit"
compFun = conDouble "compFun"
constNil = conDouble "constNil"
constTrue = conDouble "constTrue"
argFunOp = conDouble "argFunOp"
resFunOp = conDouble "resFunOp"

adjustTypes :: FunType -> FunType -> (ConvFun, ConvFun)
adjustTypes aTy ty = case (aTy, ty) of 
   (BoolType, BoolType) -> (IdOp, IdOp)
   (UnitType, UnitType) -> (IdOp, IdOp)
   (PartialVal _, BoolType) -> (IdOp, Bool2Option)
   (BoolType, PartialVal _) -> (IdOp, Option2Bool)
   (UnitType, BoolType) -> (LiftUnit, IdOp)
   (BoolType, UnitType) -> (IdOp, ConstTrue)
   (PartialVal a, PartialVal b) -> case adjustTypes a b of
       (fTrm, aTrm) -> (fTrm, MapFun MapSome aTrm)
   (PartialVal a, b) -> case adjustTypes a b of
       (fTrm, aTrm) -> (fTrm, CompFun SomeOp aTrm)
   (a, PartialVal b) -> case adjustTypes a b of
       (fTrm, aTrm) -> (LiftFun Lift fTrm, aTrm)
   (PairType a c, PairType b d) -> 
       let (aC, bC) = adjustTypes a b 
           (cC, dC) = adjustTypes c d
       in (case (aC, cC) of
             (IdOp, IdOp) -> IdOp
             (IdOp, _) -> LiftFun LiftSnd cC
             (_, IdOp) -> LiftFun LiftFst aC
             _ -> CompFun (LiftFun LiftSnd cC) $ LiftFun LiftFst aC,
           CompFun (MapFun MapSnd dC) $ MapFun MapFst bC)
   (FunType a c, FunType b d) -> 
       let (_, aC) = adjustTypes b a 
           (_, dC) = adjustTypes c d
       in (IdOp, CompFun (ResFun dC) (ArgFun aC))
   _ -> (IdOp, IdOp)

mkApp :: Env -> As.Term -> As.Term -> (FunType, Isa.Term)
mkApp sg f arg = 
    let (fTy, fTrm) = transTerm sg f
        (aTy, aTrm) = transTerm sg arg
    in case fTy of 
         FunType a r -> let (fConv, aConv) = adjustTypes a aTy
            in (case fConv of 
                  IdOp -> r
                  _ -> makePartialVal r, 
                termAppl (termAppl (convFun fConv) fTrm)
                  $ termAppl (convFun aConv) aTrm)
         PartialVal (FunType a r) -> let (fConv, aConv) = adjustTypes a aTy
            in (makePartialVal r, 
                termAppl (termAppl (termAppl unpackOp $ convFun fConv) fTrm)
                  $ termAppl (convFun aConv) aTrm)
         _ -> error "not a function type"

unpackOp = conDouble "unpackOp"

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
