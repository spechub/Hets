{- |
Module      :  $Header$
Description :  translating a HasCASL subset to Isabelle
Copyright   :  (c) C. Maeder, DFKI 2008
License     :  GPLv2 or higher

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

utility function for translation from HasCASL to Isabelle leaving open how
partial values are interpreted
-}

module Comorphisms.PPolyTyConsHOL2IsaUtils
  ( mapTheory
  , simpForPairs
  , simpForOption
  , typeToks
  , transSentence
  , SimpKind(..)
  , OldSimpKind(..)
  ) where

import HasCASL.As as As
import HasCASL.AsUtils
import HasCASL.Builtin
import HasCASL.DataAna
import HasCASL.Le as Le
import HasCASL.Unify (substGen)

import Isabelle.IsaSign as Isa
import Isabelle.IsaConsts
import Isabelle.IsaPrint
import Isabelle.Translate

import Common.DocUtils
import Common.Id
import Common.Result
import Common.Utils (isSingleton, number)
import Common.Lib.State
import Common.AS_Annotation
import Common.GlobalAnnotations

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List
import Data.Maybe (catMaybes, isNothing)
import Control.Monad (foldM)

mapTheory :: SimpKind -> Simplifier -> (Env, [Named Le.Sentence])
          -> Result (Isa.Sign, [Named Isa.Sentence])
mapTheory simK simpF (env, sens) = do
      let tyToks = typeToks env
      sign <- transSignature env tyToks
      isens <- mapM (mapNamedM $ transSentence env tyToks simK simpF) sens
      (dt, _, _) <- foldM (transDataEntries env tyToks)
         ([], Set.empty, Set.empty) $ filter (not . null) $ map
           (\ ns -> case sentence ns of
             DatatypeSen ds -> ds
             _ -> []) sens
      return ( sign { domainTab = reverse dt }
             , filter ((/= mkSen true) . sentence) isens)

-- * Signature
baseSign :: BaseSig
baseSign = MainHC_thy

transAssumps :: GlobalAnnos -> Set.Set String -> Assumps -> Result ConstTab
transAssumps ga toks = foldM insertOps Map.empty . Map.toList where
  insertOps m (name, ops) =
      let chk = isPlainFunType
      in case map opType $ Set.toList ops of
          [TypeScheme _ op _ ] -> do
              ty <- funType op
              return $ Map.insert
                         (mkIsaConstT (isPredType op) ga (chk ty)
                          name baseSign toks) (transPlainFunType ty) m
          infos -> foldM ( \ m' (TypeScheme _ op _, i) -> do
                        ty <- funType op
                        return $ Map.insert
                             (mkIsaConstIT (isPredType op) ga (chk ty)
                              name i baseSign toks) (transPlainFunType ty) m'
                         ) m $ number infos

-- all possible tokens of mixfix identifiers that must not be used as variables
getAssumpsToks :: Assumps -> Set.Set String
getAssumpsToks = Map.foldWithKey (\ i ops s ->
    Set.union s $ Set.unions
        $ map (\ (_, o) -> getConstIsaToks i o baseSign)
                     $ number $ Set.toList ops) Set.empty

typeToks :: Env -> Set.Set String
typeToks =
    Set.map (\ tyId -> showIsaTypeT tyId baseSign) . Map.keysSet . typeMap

transSignature :: Env -> Set.Set String -> Result Isa.Sign
transSignature env toks = do
    let extractTypeName tyId typeInfo m =
            let getTypeArgs n k = case k of
                        ClassKind _ -> []
                        FunKind _ _ r _ ->
                            (TFree ("'a" ++ show n) [], [isaTerm])
                                           : getTypeArgs (n + 1) r
            in Map.insert (showIsaTypeT tyId baseSign)
                  [(isaTerm, getTypeArgs (1 :: Int) $ typeKind typeInfo)] m
    ct <- transAssumps (globAnnos env) toks $ assumps env
    return $ Isa.emptySign
        { baseSig = baseSign
    -- translation of typeconstructors
        , tsig = emptyTypeSig
             { arities = Map.foldWithKey extractTypeName Map.empty
               $ typeMap env }
        , constTab = ct }

-- * translation of a type in an operation declaration

unitTyp :: Typ
unitTyp = Type "unit" holType []

mkPartialType :: Typ -> Typ
mkPartialType arg = Type "partial" [] [arg]

transFunType :: FunType -> Typ
transFunType fty = case fty of
    UnitType -> unitTyp
    BoolType -> boolType
    FunType f a -> mkFunType (transFunType f) $ transFunType a
    PartialVal a -> mkPartialType $ transFunType a
    PairType a b -> prodType (transFunType a) $ transFunType b
    TupleType l -> case l of
      [] -> error "transFunType"
      _ -> transFunType $ foldl1 PairType l
    ApplType tid args -> Type (showIsaTypeT tid baseSign) []
                       $ map transFunType args
    TypeVar tid -> TFree (showIsaTypeT tid baseSign) []

-- compute number of arguments for plain CASL functions
isPlainFunType :: FunType -> Int
isPlainFunType fty = case fty of
    FunType f a -> case a of
                     FunType _ _ -> -1
                     _ -> case f of
                            TupleType l -> length l
                            _ -> 1
    _ -> 0

transPlainFunType :: FunType -> Typ
transPlainFunType fty =
    case fty of
    FunType (TupleType l) a -> case a of
        FunType _ _ -> transFunType fty
        _ -> foldr mkFunType (transFunType a) $ map transFunType l
    _ -> transFunType fty

data FunType = UnitType | BoolType
  | FunType FunType FunType
  | PartialVal FunType
  | PairType FunType FunType -- only used to represent tuples as nested pairs
  | TupleType [FunType]
  | ApplType Id [FunType]
  | TypeVar Id
    deriving (Eq, Show)

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

transDataEntries :: Env -> Set.Set String
                 -> (DomainTab, Set.Set TName, Set.Set VName) -> [DataEntry]
                 -> Result (DomainTab, Set.Set TName, Set.Set VName)
transDataEntries env tyToks t@(dt, tys, cs) l = do
    let rs = map (transDataEntry env tyToks) l
        ms = map maybeResult rs
        toWarning = map ( \ d -> d { diagKind = Warning })
    appendDiags $ toWarning $ concatMap diags rs
    if any isNothing ms then return t
        else do
        let des = catMaybes ms
            ntys = map (Isa.typeId . fst) des
            ncs = concatMap (map fst . snd) des
            foldF str cnv = foldM ( \ s i ->
                   if Set.member i s then
                       fail $ "duplicate " ++ str ++ cnv i
                   else return $ Set.insert i s)
            Result d1 mrtys = foldF "datatype " id tys ntys
            Result d2 mrcs = foldF "constructor " new cs ncs
        appendDiags $ toWarning $ d1 ++ d2
        case (mrtys, mrcs) of
          (Just rtys, Just rcs) -> return (des : dt, rtys, rcs)
          _ -> return t

-- datatype with name (tyId) + args (tyArgs) and alternatives
transDataEntry :: Env -> Set.Set String -> DataEntry -> Result DomainEntry
transDataEntry env tyToks de@(DataEntry _ _ gk _ _ alts) =
    let dp@(DataPat _ i tyArgs _ _) = toDataPat de
    in case gk of
    Le.Free -> do
      nalts <- mapM (transAltDefn env tyToks dp) $ Set.toList alts
      let transDName ti = Type (showIsaTypeT ti baseSign) []
                             . map transTypeArg
      return (transDName i tyArgs, nalts)
    _ -> fatal_error ("not a free type: "  ++ show i)
         $ posOfId i

-- arguments of a datatype's typeconstructor
transTypeArg :: TypeArg -> Typ
transTypeArg ta = TFree (showIsaTypeT (getTypeVar ta) baseSign) []

-- datatype alternatives/constructors
transAltDefn :: Env -> Set.Set String -> DataPat -> AltDefn
             -> Result (VName, [Typ])
transAltDefn env tyToks dp alt = case alt of
  Construct mi ts p _ -> case mi of
    Just opId -> case p of
      Total -> do
        let sc = getConstrScheme dp p ts
        nts <- mapM funType ts
        -- extract overloaded opId number
        return (transOpId env tyToks opId sc, case nts of
                [TupleType l] -> map transFunType l
                _ -> map transFunType nts)
      Partial -> mkError "not a total constructor" opId
    Nothing -> mkError "no support for data subtypes" ts

-- * Formulas

-- variables
transVar :: Set.Set String -> Id -> VName
transVar toks v = let
    s = showIsaConstT v baseSign
    renVar t = if Set.member t toks then renVar $ "X_" ++ t else t
    in mkVName $ renVar s

mkTypedConst :: VName -> FunType -> Isa.Term
mkTypedConst v fTy = Isa.Const v $ Disp (transFunType fTy) NA Nothing

transTypedVar :: Set.Set String -> VarDecl -> Result Isa.Term
transTypedVar toks (VarDecl var ty _ _) = do
    fTy <- funType ty
    return $ mkTypedConst (transVar toks var) fTy

mkSimplifiedSen :: OldSimpKind -> Simplifier -> Isa.Term -> Isa.Sentence
mkSimplifiedSen simK simpF t = mkSen $ evalState (simplify simK simpF t) 0

isTrue :: Isa.Term -> Bool
isTrue t = case t of
  Const n _ -> new n == cTrue
  _ -> False

mkBinConj :: Isa.Term -> Isa.Term -> Isa.Term
mkBinConj t1 t2 = case isTrue of
  isT | isT t1 -> t2
      | isT t2 -> t1
  _ -> binConj t1 t2

data OldSimpKind = NoSimpLift | Lift2Restrict | Lift2Case deriving Eq

data SimpKind = New | Old OldSimpKind deriving Eq

transSentence :: Env -> Set.Set String -> SimpKind -> Simplifier -> Le.Sentence
              -> Result Isa.Sentence
transSentence sign tyToks simK simpF s = case s of
    Le.Formula trm -> do
      ITC ty t cs <- transTerm sign tyToks (simK == New)
        (getAssumpsToks $ assumps sign) Set.empty trm
      let et = case ty of
                 PartialVal UnitType -> mkTermAppl defOp t
                 _ -> t
          bt = if isTrue et then cond2bool cs else
                   mkTermAppl (integrateCondInBool cs) et
          st = mkSimplifiedSen (case simK of
                Old osim -> osim
                New -> NoSimpLift) simpF bt
      case ty of
        BoolType -> return st
        PartialVal _ -> return st
        FunType _ _ -> error "transSentence: FunType"
        PairType _ _ -> error "transSentence: PairType"
        TupleType _ -> error "transSentence: TupleType"
        ApplType _ _ -> error "transSentence: ApplType"
        _ -> return $ mkSen true
    DatatypeSen ls -> if all (\ (DataEntry _ _ gk _ _ _) -> gk == Generated) ls
      then transSentence sign tyToks simK simpF . Le.Formula
               $ inductionScheme ls
      else return $ mkSen true
    ProgEqSen _ _ (ProgEq _ _ r) -> warning (mkSen true)
        "translation of sentence not implemented" r

-- disambiguate operation names
transOpId :: Env -> Set.Set String -> Id -> TypeScheme -> VName
transOpId sign tyToks op ts@(TypeScheme _ ty _) =
    let ga = globAnnos sign
        Result _ mty = funType ty
    in case mty of
         Nothing -> error "transOpId"
         Just fty ->
           let args = isPlainFunType fty
           in case (do
           ops <- Map.lookup op (assumps sign)
           if isSingleton ops then return $
              mkIsaConstT (isPredType ty) ga args op baseSign tyToks
             else do
                 i <- elemIndex ts $ map opType $ Set.toList ops
                 return $ mkIsaConstIT (isPredType ty)
                        ga args op (i+1) baseSign tyToks) of
          Just str -> str
          Nothing  -> error $ "transOpId " ++ show op

transLetEq :: Env -> Set.Set String -> Bool -> Set.Set String
    -> Set.Set VarDecl -> ProgEq -> Result ((As.Term, Isa.Term), IsaTermCond)
transLetEq sign tyToks collectConds toks pVars (ProgEq pat trm r) = do
    (_, op) <- transPattern sign tyToks toks pat
    p@(ITC ty _ _) <- transTerm sign tyToks collectConds toks pVars trm
    if isPartialVal ty && not (isQualVar pat) then fatal_error
           ("rhs must not be partial for a tuple currently: "
            ++ showDoc trm "") r
       else return ((pat, op), p)

transLetEqs :: Env -> Set.Set String -> Bool -> Set.Set String
            -> Set.Set VarDecl -> [ProgEq]
            -> Result (Set.Set VarDecl, [(Isa.Term, IsaTermCond)])
transLetEqs sign tyToks collectConds toks pVars es = case es of
    [] -> return (pVars, [])
    e : r -> do
      ((pat, op), pt@(ITC ty _ _)) <-
        transLetEq sign tyToks collectConds toks pVars e
      (newPVars, newEs) <- transLetEqs sign tyToks collectConds toks
        (if isPartialVal ty then Set.insert (getQualVar pat) pVars else pVars) r
      return (newPVars, (op, pt) : newEs)

isQualVar :: As.Term -> Bool
isQualVar trm = case trm of
    QualVar (VarDecl _ _ _ _) -> True
    TypedTerm t _ _ _ -> isQualVar t
    _ -> False

getQualVar :: As.Term -> VarDecl
getQualVar trm = case trm of
    QualVar vd -> vd
    TypedTerm t _ _ _ -> getQualVar t
    _ -> error "getQualVar"

ifImplOp :: Isa.Term
ifImplOp = conDouble "ifImplOp"

unitOp :: Isa.Term
unitOp = Tuplex [] NotCont

noneOp :: Isa.Term
noneOp = conDouble "undefinedOp"

whenElseOp :: Isa.Term
whenElseOp = conDouble "whenElseOp"

resOp :: Isa.Term
resOp = conDouble "resOp"

makeTotal :: Isa.Term
makeTotal = conDouble "makeTotal"

uncurryOpS :: String
uncurryOpS = "uncurryOp"

curryOpS :: String
curryOpS = "curryOp"

uncurryOp :: Isa.Term
uncurryOp = conDouble uncurryOpS

curryOp :: Isa.Term
curryOp = conDouble curryOpS

for :: Int -> (a -> a) -> a -> a
for n f a = if n <= 0 then a else for (n - 1) f $ f a

data IsaTermCond = ITC FunType Isa.Term Cond

data Cond = None
  | Cond Isa.Term
  | CondList [Cond]
  | PairCond Cond Cond

instance Show Cond where
  show c = case c of
    None -> "none"
    Cond t -> show $ printTerm t
    CondList l -> intercalate " & " $ map show l
    PairCond p1 p2 -> '(' : shows p1 ", " ++ shows p2 ")"

joinCond :: Cond -> Cond -> Cond
joinCond c1 c2 = let
  toCs c = case c of
          CondList cs -> cs
          None -> []
          _ -> [c]
  in case toCs c1 ++ toCs c2 of
       [] -> None
       [s] -> s
       cs -> CondList cs

pairCond :: Cond -> Cond -> Cond
pairCond c1 c2 = case (c1, c2) of
  (None, None) -> None
  _ -> PairCond c1 c2

condToList :: Cond -> [Isa.Term]
condToList c = case c of
  None -> []
  Cond t -> [t]
  CondList cs -> concatMap condToList cs
  PairCond c1 c2 -> condToList c1 ++ condToList c2

{- pass tokens that must not be used as variable names and pass those
variables that are partial because they have been computed in a
let-term. -}
transTerm :: Env -> Set.Set String -> Bool -> Set.Set String
          -> Set.Set VarDecl -> As.Term -> Result IsaTermCond
transTerm sign tyToks collectConds toks pVars trm = case trm of
    QualVar vd@(VarDecl v t _ _) -> do
        fTy <- funType t
        let vt = con $ transVar toks v
        return $ if Set.member vd pVars then ITC (makePartialVal fTy) vt None
          else ITC fTy vt None
    QualOp _ (PolyId opId _ _) ts@(TypeScheme targs ty _) insts _ _ -> do
        fTy <- funType ty
        instfTy <- funType $ substGen (if null insts then Map.empty else
                    Map.fromList $ zipWith (\ (TypeArg _ _ _ _ i _ _) t
                                                -> (i, t)) targs insts) ty
        let cf = mkTermAppl (convFun None $ instType fTy instfTy)
            unCurry f = let rf = termAppl uncurryOp $ con f in
              ITC fTy rf None
        return $ case (opId ==) of
          is  | is trueId -> ITC fTy true None
              | is falseId -> ITC fTy false None
              | is botId -> case instfTy of
                  PartialVal t -> ITC t (termAppl makeTotal noneOp) $ Cond false
                  _ -> ITC instfTy (cf noneOp) None
              | is andId -> unCurry conjV
              | is orId -> unCurry disjV
              | is implId -> unCurry implV
              | is infixIf -> ITC fTy ifImplOp None
              | is eqvId -> unCurry eqV
              | is exEq -> let
                  ef = cf $ termAppl uncurryOp existEqualOp
                  in ITC instfTy ef None
              | is eqId -> let
                  ef = cf $ termAppl uncurryOp $ con eqV
                  in ITC instfTy ef None
              | is notId -> ITC fTy notOp None
              | is defId -> ITC instfTy (cf defOp) None
              | is whenElse -> ITC instfTy (cf whenElseOp) None
              | is resId -> ITC instfTy (cf resOp) None
          _ -> let
                  isaId = transOpId sign tyToks opId ts
                  ef = cf $ for (isPlainFunType fTy - 1) (termAppl uncurryOp)
                             $ if elem opId [injName, projName] then
                                   mkTypedConst isaId instfTy
                               else con isaId
                  in ITC instfTy ef None
    QuantifiedTerm quan varDecls phi _ -> do
        let qname = case quan of
                      Universal -> allS
                      Existential -> exS
                      Unique -> ex1S
            quantify phi' gvd = case gvd of
                GenVarDecl vd -> do
                    vt <- transTypedVar toks vd
                    return $ termAppl (conDouble qname) $ Abs vt phi' NotCont
                GenTypeVarDecl _ -> return phi'
        ITC ty psi cs <- fmap integrateCond
          $ transTerm sign tyToks collectConds toks pVars phi
        psiR <- foldM quantify psi $ reverse varDecls
        return $ ITC ty psiR cs
    TypedTerm t _q _ty _ -> transTerm sign tyToks collectConds toks pVars t
    LambdaTerm pats q body r -> do
        p@(ITC ty _ ncs) <- transTerm sign tyToks collectConds toks pVars body
        appendDiags $ case q of
            Partial -> []
            Total -> [Diag Warning
              ("partial lambda body in total abstraction: "
               ++ showDoc body "") r
                  | isPartialVal ty || not (isTrue $ cond2bool ncs) ]
        foldM (abstraction sign tyToks toks) (integrateCond p)
          $ reverse pats
    LetTerm As.Let peqs body _ -> do
        (nPVars, nEqs) <-
            transLetEqs sign tyToks collectConds toks pVars peqs
        ITC bTy bTrm defCs <-
          transTerm sign tyToks collectConds toks nPVars body
        let pEs = map (\ (p, ITC _ t _) -> (p, t)) nEqs
            cs = foldl joinCond None $ map (\ (_, ITC _ _ c) -> c) nEqs
        return $ ITC bTy (mkLetAppl pEs bTrm) $ joinCond cs defCs
    TupleTerm ts@(_ : _) _ -> do
        nTs <- mapM (transTerm sign tyToks collectConds toks pVars) ts
        return $ foldl1 ( \ (ITC s p cs) (ITC t e cr) ->
          ITC (PairType s t) (Tuplex [p, e] NotCont) $ pairCond cs cr) nTs
    TupleTerm [] _ -> return $ ITC UnitType unitOp None
    ApplTerm t1 t2 _ -> mkApp sign tyToks collectConds toks pVars t1 t2
    _ -> fatal_error ("cannot translate term: " ++ showDoc trm "")
         $ getRange trm

integrateCond :: IsaTermCond -> IsaTermCond
integrateCond (ITC ty trm cs) = if isTrue $ cond2bool cs then
  ITC ty trm None
  else case ty of
    PartialVal _ -> ITC ty (mkTermAppl (integrateCondInPartial cs) trm) None
    BoolType -> ITC ty (mkTermAppl (integrateCondInBool cs) trm) None
    UnitType -> ITC BoolType (cond2bool cs) None
    _ -> ITC (makePartialVal ty)
         (mkTermAppl (integrateCondInTotal cs) trm) None
    -- return partial result type

instType :: FunType -> FunType -> ConvFun
instType f1 f2 = case (f1, f2) of
    (TupleType l1, _) -> instType (foldl1 PairType l1) f2
    (_, TupleType l2) -> instType f1 $ foldl1 PairType l2
    (PartialVal (TypeVar _), BoolType) -> Partial2bool True
    (PairType a c, PairType b d) ->
        let c2 = instType c d
            c1 = instType a b
        in mkCompFun (mkMapFun MapSnd c2) $ mkMapFun MapFst c1
    (FunType a c, FunType b d) ->
         let c2 = instType c d
             c1 = instType a b
        in mkCompFun (mkResFun c2) $ mkArgFun $ invertConv c1
    _ -> IdOp

invertConv :: ConvFun -> ConvFun
invertConv c = case c of
    Partial2bool _ -> Bool2partial False
    Bool2partial _ -> Partial2bool False
    Unit2bool _ -> Bool2unit
    Bool2unit -> Unit2bool False
    MkPartial _ -> MkTotal
    MkTotal -> MkPartial False
    MapFun mv cf -> mkMapFun mv $ invertConv cf
    ResFun cf -> mkResFun $ invertConv cf
    ArgFun cf -> mkArgFun $ invertConv cf
    CompFun c1 c2 -> mkCompFun (invertConv c2) (invertConv c1)
    _ -> IdOp

data MapFun = MapFst | MapSnd | MapPartial deriving Show

data LiftFun = LiftFst | LiftSnd deriving Show

{- the additional Bool indicates condition integration
   Bool2bool and Partial2partial must be mapped to IdOp
   if the conditions should be ignored.
   Bool2Unit and MkTotal can propagate out conditions -}
data ConvFun =
    IdOp
  | Bool2partial Bool
  | Partial2bool Bool
  | Bool2bool
  | Unit2bool Bool
  | Bool2unit
  | Partial2partial
  | MkPartial Bool
  | MkTotal
  | CompFun ConvFun ConvFun
  | MapFun MapFun ConvFun
  | LiftFun LiftFun ConvFun
  | LiftUnit FunType
  | LiftPartial FunType
  | ResFun ConvFun
  | ArgFun ConvFun
    deriving Show

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

mapFun :: MapFun -> Isa.Term
mapFun mf = case mf of
    MapFst -> mapFst
    MapSnd -> mapSnd
    MapPartial -> mapPartial

compOp :: Isa.Term
compOp = con compV

convFun :: Cond -> ConvFun -> Isa.Term
convFun cnd cvf = case cvf of
    IdOp -> idOp
    Bool2partial b -> if b
      then metaComp bool2partial $ integrateCondInBool cnd
      else bool2partial
    Partial2bool b -> if b
      then metaComp (integrateCondInBool cnd) defOp
      else defOp
    Bool2bool -> integrateCondInBool cnd
    Unit2bool b -> if b
      then metaComp (integrateCondInBool cnd) constTrue else constTrue
    Bool2unit -> constNil
    Partial2partial -> integrateCondInPartial cnd
    MkPartial b -> if b
      then integrateCondInTotal cnd
      else mkPartial
    MkTotal -> makeTotal
    LiftUnit rTy -> case rTy of
       UnitType -> liftUnit2unit
       BoolType -> liftUnit2bool
       PartialVal _ -> liftUnit2partial
       _ -> liftUnit
    LiftPartial rTy ->
        case rTy of
            UnitType -> lift2unit
            BoolType -> lift2bool
            PartialVal _ -> lift2partial
            _ -> mapPartial
    CompFun f1 f2 -> metaComp (convFun cnd f1) $ convFun cnd f2
    MapFun mf cv -> mkTermAppl (mapFun mf) $ convFun cnd cv
    LiftFun lf cv -> let ccv = convFun cnd cv in case lf of
        LiftFst -> metaComp (metaComp uncurryOp flipOp)
                   $ metaComp (metaComp (mkTermAppl compOp ccv) flipOp)
                   curryOp
        LiftSnd -> metaComp uncurryOp $ metaComp (mkTermAppl compOp ccv)
                   curryOp
    ArgFun cv -> mkTermAppl (termAppl flipOp compOp) $ convFun cnd cv
    ResFun cv -> mkTermAppl compOp $ convFun cnd cv

mapFst, mapSnd, mapPartial, idOp, bool2partial, constNil, constTrue,
    liftUnit2unit, liftUnit2bool, liftUnit2partial, liftUnit, lift2unit,
    lift2bool, lift2partial, mkPartial, restrict :: Isa.Term

mapFst = conDouble "mapFst"
mapSnd = conDouble "mapSnd"
mapPartial = conDouble "mapPartial"
idOp = conDouble "id"
bool2partial = conDouble "bool2partial"
constNil = conDouble "constNil"
constTrue = conDouble "constTrue"
liftUnit2unit = conDouble "liftUnit2unit"
liftUnit2bool = conDouble "liftUnit2bool"
liftUnit2partial = conDouble "liftUnit2partial"
liftUnit = conDouble "liftUnit"
lift2unit = conDouble "lift2unit"
lift2bool = conDouble "lift2bool"
lift2partial = conDouble "lift2partial"
mkPartial = conDouble "makePartial"
restrict = conDouble "restrictOp"

existEqualOp :: Isa.Term
existEqualOp =
  con $ VName "existEqualOp" $ Just $ AltSyntax "(_ =e=/ _)"  [50, 51] 50

integrateCondInBool :: Cond -> Isa.Term
integrateCondInBool c = let b = cond2bool c in
  if isTrue b then idOp else mkTermAppl (con conjV) b

integrateCondInPartial :: Cond -> Isa.Term
integrateCondInPartial c = let b = cond2bool c in
  if isTrue b then idOp else
  mkTermAppl (mkTermAppl flipOp restrict) b

metaComp :: Isa.Term -> Isa.Term -> Isa.Term
metaComp = mkTermAppl . mkTermAppl compOp

integrateCondInTotal :: Cond -> Isa.Term
integrateCondInTotal c = metaComp (integrateCondInPartial c) mkPartial

addCond :: Isa.Term -> Cond -> Cond
addCond = joinCond . Cond

cond2bool :: Cond -> Isa.Term
cond2bool c = case nub $ condToList c of
  [] -> true
  ncs -> foldr1 mkBinConj ncs

-- adjust actual argument to expected argument type of function
-- considering a definedness conditions
adjustArgType :: FunType -> FunType -> Result ConvFun
adjustArgType aTy ty = case (aTy, ty) of
    (TupleType l, _) -> adjustArgType (foldl1 PairType l) ty
    (_, TupleType l) -> adjustArgType aTy $ foldl1 PairType l
    (BoolType, BoolType) -> return Bool2bool
    (UnitType, UnitType) -> return IdOp
    (PartialVal UnitType, BoolType) -> return $ Bool2partial True
    (BoolType, PartialVal UnitType) -> return $ Partial2bool True
    (UnitType, BoolType) -> return Bool2unit
    (BoolType, UnitType) -> return $ Unit2bool True
    (PartialVal a, PartialVal b) -> do
        c <- adjustArgType a b
        return $ mkCompFun Partial2partial c
    (a, PartialVal b) -> do
        c <- adjustArgType a b
        return $ mkCompFun MkTotal c
    (PartialVal a, b) -> do
        c <- adjustArgType a b
        return $ mkCompFun (MkPartial True) c
    (PairType e1 e2, PairType a1 a2) -> do
        c1 <- adjustArgType e1 a1
        c2 <- adjustArgType e2 a2
        return . mkCompFun (mkMapFun MapSnd c2) $ mkMapFun MapFst c1
    (FunType a b, FunType c d) -> do
        aC <- adjustArgType a c -- function a -> c (a fixed)
        dC <- adjustArgType b d -- function d -> b (b fixed)
        -- (d -> b) o (c -> d) o (a -> c) :: a -> b
        -- not not integrate cond treatment via invertConv . invertConv
        return . mkCompFun (mkResFun . invertConv $ invertConv dC)
          . mkArgFun $ invertConv aC
    (TypeVar _, _) -> return IdOp
    (_, TypeVar _) -> return IdOp
    (ApplType i1 l1, ApplType i2 l2) | i1 == i2 && length l1 == length l2
        -> do l <- mapM (uncurry adjustArgType) $ zip l1 l2
              if any (isNotIdOp . invertConv) l
                then fail "cannot adjust type application"
                else return IdOp
    _ -> fail $ "cannot adjust argument type\n" ++ show (aTy, ty)

unpackOp :: Isa.Term -> Bool -> Bool -> FunType -> ConvFun -> Isa.Term
unpackOp fTrm isPf pfTy ft fConv = let isaF = convFun None fConv in
  if isPf then mkTermAppl
  (mkTermAppl (conDouble $ case if pfTy then makePartialVal ft else ft of
    UnitType -> "unpack2bool"
    BoolType -> "unpackBool"
    PartialVal _ -> "unpackPartial"
    _ -> "unpack2partial") isaF) fTrm
  else mkTermAppl isaF fTrm

-- True means function type result was partial
adjustMkApplOrig :: Isa.Term -> Cond -> Bool -> FunType -> FunType
                 -> IsaTermCond -> Result IsaTermCond
adjustMkApplOrig fTrm fCs isPf aTy rTy (ITC ty aTrm aCs) = do
  ((pfTy, fConv), (_, aConv)) <- adjustTypes aTy rTy ty
  return . ITC (if isPf || pfTy then makePartialVal rTy else rTy)
    (mkTermAppl (unpackOp fTrm isPf pfTy rTy fConv)
    $ mkTermAppl (convFun None aConv) aTrm) $ joinCond fCs aCs

-- True means require result type to be partial
adjustTypes :: FunType -> FunType -> FunType
            -> Result ((Bool, ConvFun), (FunType, ConvFun))
adjustTypes aTy rTy ty = case (aTy, ty) of
    (TupleType l, _) -> adjustTypes (foldl1 PairType l) rTy ty
    (_, TupleType l) -> adjustTypes aTy rTy $ foldl1 PairType l
    (BoolType, BoolType) -> return ((False, IdOp), (ty, IdOp))
    (UnitType, UnitType) -> return ((False, IdOp), (ty, IdOp))
    (PartialVal _, BoolType) ->
        return ((False, IdOp), (aTy, Bool2partial False))
    (BoolType, PartialVal _) ->
        return ((False, IdOp), (aTy, Partial2bool False))
    (_, BoolType) -> return ((True, LiftUnit rTy), (ty, IdOp))
    (BoolType, _) -> return ((False, IdOp), (aTy, Unit2bool False))
    (PartialVal a, PartialVal b) -> do
        q@(fp, (argTy, aTrm)) <- adjustTypes a rTy b
        return $ case argTy of
            PartialVal _ -> q
            _ -> (fp, (PartialVal argTy, mkMapFun MapPartial aTrm))
    (a, PartialVal b) -> do
        q@(_, ap@(argTy, _)) <- adjustTypes a rTy b
        return $ case argTy of
            PartialVal _ -> q
            _ -> ((True, LiftPartial rTy), ap)
    (PartialVal a, b) -> do
        q@(fp, (argTy, aTrm)) <- adjustTypes a rTy b
        return $ case argTy of
            PartialVal _ -> q
            _ -> (fp, (PartialVal argTy, mkCompFun (MkPartial False) aTrm))
    (PairType a c, PairType b d) -> do
        ((res2Ty, f2), (arg2Ty, a2)) <- adjustTypes c rTy d
        ((res1Ty, f1), (arg1Ty, a1)) <- adjustTypes a
                (if res2Ty then makePartialVal rTy else rTy) b
        return ((res1Ty || res2Ty,
             mkCompFun (mkLiftFun LiftFst f1) $ mkLiftFun LiftSnd f2),
                  (PairType arg1Ty arg2Ty,
                   mkCompFun (mkMapFun MapSnd a2) $ mkMapFun MapFst a1))
    (FunType a c, FunType b d) -> do
        ((_, aF), (aT, aC)) <- adjustTypes b c a
        ((cB, cF), (dT, dC)) <- adjustTypes c rTy d
        if cB || isNotIdOp cF
          then fail "cannot adjust result types of function type"
          else return ((False, IdOp), (FunType aT dT,
                 mkCompFun aF $ mkCompFun (mkResFun dC) $ mkArgFun aC))
    (TypeVar _, _) -> return ((False, IdOp), (ty, IdOp))
    (_, TypeVar _) -> return ((False, IdOp), (aTy, IdOp))
    (ApplType i1 l1, ApplType i2 l2) | i1 == i2 && length l1 == length l2
        -> do l <- mapM (\ (a, b) -> adjustTypes a rTy b) $ zip l1 l2
              if any (fst . fst) l || any (isNotIdOp . snd . snd) l
                then fail "cannot adjust type application"
                else return ((False, IdOp),
                             (ApplType i1 $ map (fst . snd) l, IdOp))
    _ -> fail $ "cannot adjust types\n" ++ show (aTy, ty)

adjustMkAppl :: Isa.Term -> Cond -> Bool -> FunType -> FunType
             -> IsaTermCond -> Result IsaTermCond
adjustMkAppl fTrm fCs isPf aTy rTy (ITC ty aTrm aCs) = do
    aConv <- adjustArgType aTy ty
    let (natrm, nacs) = applConv aConv (aTrm, aCs)
        (nftrm, nfcs) = if isPf
          then (mkTermAppl makeTotal fTrm, addCond (mkTermAppl defOp fTrm) fCs)
          else (fTrm, fCs)
    return $ ITC rTy (mkTermAppl nftrm natrm) $ joinCond nfcs nacs

applConv :: ConvFun -> (Isa.Term, Cond) -> (Isa.Term, Cond)
applConv cnv (t, c) = let
  rt = mkTermAppl (convFun c cnv) t
  r = (rt, c)
  rb = (rt, None)
  in case cnv of
    IdOp -> (t, c)
    Bool2partial b -> if b then rb else r
    Partial2bool b -> if b then rb else r
    Bool2bool -> rb
    Unit2bool b -> if b then rb else r
    Bool2unit -> (rt, addCond t c)
    Partial2partial -> rb
    MkPartial b -> if b then rb else r
    MkTotal -> (rt, addCond (mkTermAppl defOp t) c)
    CompFun f1 f2 -> applConv f1 $ applConv f2 (t, c)
    MapFun mf cv -> case t of
      Tuplex [t1, t2] _ -> let
        (c1, c2) = case c of
          PairCond p1 p2 -> (p1, p2)
          _ -> (c, c)
        in case mf of
        MapFst -> let
          (nt1, nc1) = applConv cv (t1, c1)
          in (Tuplex [nt1, t2] NotCont, PairCond nc1 c2)
        MapSnd -> let
          (nt2, nc2) = applConv cv (t2, c2)
          in (Tuplex [t1, nt2] NotCont, PairCond c1 nc2)
        MapPartial -> r
      _ -> r
    _ -> r

mkArgFun :: ConvFun -> ConvFun
mkArgFun c = case c of
    IdOp -> c
    Bool2bool -> c
    Partial2partial -> c
    _ -> ArgFun c

mkResFun :: ConvFun -> ConvFun
mkResFun c = case c of
    IdOp -> c
    Bool2bool -> c
    Partial2partial -> c
    _ -> ResFun c

isEquallyLifted :: Isa.Term -> Isa.Term -> Maybe (Isa.Term, Isa.Term, Isa.Term)
isEquallyLifted l r = case (l, r) of
    (App ft@(Const f _) la _,
     App (Const g _) ra _)
        | f == g && elem (new f) ["makePartial", "bool2partial"]
            -> Just (ft, la, ra)
    _ -> Nothing

isLifted :: Isa.Term -> Bool
isLifted t = case t of
    App (Const f _) _ _ | new f == "makePartial" -> True
    _ -> False

splitArg :: Isa.Term -> (Isa.Term, Isa.Term)
splitArg arg = case arg of
  App (App (Const n _) p _) b _ | new n == "restrictOp" ->
      case p of
        App (Const pp _) t _ | new pp == "makePartial"
            -> (b, t)
        _ -> (mkBinConj b $ mkTermAppl defOp p, mkTermAppl makeTotal p)
  _ -> (mkTermAppl defOp arg, mkTermAppl makeTotal arg)

flipS :: String
flipS = "flip"

flipOp :: Isa.Term
flipOp = conDouble flipS

mkTermAppl :: Isa.Term -> Isa.Term -> Isa.Term
mkTermAppl fun arg = case (fun, arg) of
      (App (Const uc _) b _, Tuplex [l, r] _) | new uc == uncurryOpS ->
        let res = mkTermAppl (mkTermAppl b l) r in case b of
          Const bin _ | elem (new bin) [eq, "existEqualOp"] ->
            case isEquallyLifted l r of
              Just (_, la, ra) -> mkTermAppl (mkTermAppl (con eqV) la) ra
              _ -> if isLifted l || isLifted r
                   then mkTermAppl (mkTermAppl (con eqV) l) r
                   else let
                     (lb, lt) = splitArg l
                     (rb, rt) = splitArg r
                   in if new bin == "existEqualOp" then
                      mkBinConj lb $ mkBinConj rb
                      $ mkTermAppl (mkTermAppl (con eqV) lt) rt
                      else res
          _ -> res
      (App (Const mp _) f _, Tuplex [a, b] c)
          | new mp == "mapFst" -> Tuplex [mkTermAppl f a, b] c
          | new mp == "mapSnd" -> Tuplex [a, mkTermAppl f b] c
      (Const mp _, Tuplex [a, b] _)
          | new mp == "ifImplOp" -> binImpl b a
      (Const mp _, Tuplex [Tuplex [a, b] _, c] d)
          | new mp == "whenElseOp" -> case isEquallyLifted a c of
              Just (f, na, nc) -> mkTermAppl f $ If b na nc d
              Nothing -> If b a c d
      (App (Const mp _) f _, App (Const mp2 _) arg2 _)
          | new mp == "mapPartial" && new mp2 == "makePartial" ->
             mkTermAppl mkPartial $ mkTermAppl f arg2
      (App (Const mp _) f c, _)
          | new mp == "liftUnit2bool" -> let af = mkTermAppl f unitOp in
             case arg of
               Const ma _ | isTrue arg -> af
                          | new ma == cFalse -> false
               _ -> If arg af false c
          | new mp == "liftUnit2partial" -> let af = mkTermAppl f unitOp in
             case arg of
               Const ma _ | isTrue arg -> af
                          | new ma == cFalse -> noneOp
               _ -> If arg af noneOp c
      (App (Const mp _) _ _, _)
          | new mp == "liftUnit2unit" -> arg
          | new mp == "lift2unit" -> mkTermAppl defOp arg
      (App (App (Const cmp _) f _) g c, _)
          | new cmp == compS -> mkTermAppl f $ mkTermAppl g arg
          | new cmp == curryOpS -> mkTermAppl f $ Tuplex [g, arg] c
          | new cmp == flipS -> mkTermAppl (mkTermAppl f arg) g
      (Const d _, App (Const sm _) a _)
          | new d == defOpS && new sm == "makePartial" -> true
          | new d == defOpS && new sm == "bool2partial"
            || new d == "bool2partial" && new sm == defOpS -> a
          | new d == curryOpS && new sm == uncurryOpS -> a
      (Const i _, _)
          | new i == "bool2partial" ->
              let tc = mkTermAppl mkPartial unitOp
              in case arg of
                    Const j _ | isTrue arg -> tc
                              | new j == cFalse -> noneOp
                    _ -> termAppl fun arg -- If arg tc noneOp NotCont
          | new i == "id" -> arg
          | new i == "constTrue" -> true
          | new i == "constNil" -> unitOp
      (Const i _, Tuplex [] _)
          | new i == defOpS -> false
      _ -> termAppl fun arg

freshIndex :: State Int Int
freshIndex = do
  i <- get
  put $ i + 1
  return i

type Simplifier = VName
  -> Isa.Term -- variable
  -> Isa.Term -- simplified application to variable
  -> Isa.Term -- simplified argument
  -> State Int Isa.Term

simpForOption :: Simplifier
simpForOption l v nF nArg =
  return $ Case nArg
   [ (conDouble "None", if new l == "lift2bool" then false else noneOp)
   , (termAppl conSome v,
      if new l == "mapPartial" then mkTermAppl mkPartial nF else nF)]

mkLetAppl :: [(Isa.Term, Isa.Term)] -> Isa.Term -> Isa.Term
mkLetAppl eqs inTrm = case inTrm of
  App (Const mp _) arg _ | new mp == "makePartial" ->
    mkTermAppl mkPartial $ Isa.Let eqs arg
  _ -> Isa.Let eqs inTrm

simpForPairs :: Simplifier
simpForPairs l v2 nF nArg = do
  n <- freshIndex
  let v1 = mkFree $ "Xb" ++ show n
  return $ mkLetAppl [(Tuplex [v1, v2] NotCont, nArg)] $
     If v1 (if new l == "mapPartial" then mkTermAppl mkPartial nF else nF)
            (if new l == "lift2bool" then false else noneOp) NotCont

simplify :: OldSimpKind -> Simplifier -> Isa.Term -> State Int Isa.Term
simplify simK simpF trm = case trm of
    App (App (Const l _) f _) arg _
      | simK /= NoSimpLift && elem (new l)
        ["lift2bool", "lift2partial", "mapPartial"] -> do
     nArg <- simplify simK simpF arg
     let lf = new l
         res = simK == Lift2Restrict
     if res && lf == "lift2partial" then return . mkTermAppl
         (mkTermAppl restrict . mkTermAppl f $ mkTermAppl makeTotal nArg)
         $ mkTermAppl defOp nArg
         else if res && lf == "mapPartial" then return . mkTermAppl
          (mkTermAppl restrict . mkTermAppl mkPartial
                   . mkTermAppl f $ mkTermAppl makeTotal nArg)
          $ mkTermAppl defOp nArg
         else do
      n <- freshIndex
      let pvar = mkFree $ "Xc" ++ show n
      nF <- simplify simK simpF $ mkTermAppl f pvar
      simpF l pvar nF nArg
    App f arg c -> do
        nF <- simplify simK simpF f
        nArg <- simplify simK simpF arg
        return $ App nF nArg c
    Abs v t c -> do
        nT <- simplify simK simpF t
        return $ Abs v nT c
    _ -> return trm

mkApp :: Env -> Set.Set String -> Bool -> Set.Set String
      -> Set.Set VarDecl -> As.Term -> As.Term -> Result IsaTermCond
mkApp sign tyToks collectConds toks pVars f arg = do
    fTr@(ITC fTy fTrm fCs) <-
        transTerm sign tyToks collectConds toks pVars f
    aTr <- transTerm sign tyToks collectConds toks pVars arg
    let pv = case arg of -- dummy application of a unit argument
          TupleTerm [] _ -> return fTr
          _ -> mkError "wrong function type"  f
        adjstAppl = if collectConds then adjustMkAppl else adjustMkApplOrig
    adjustPos (getRange [f, arg]) $ case fTy of
         FunType a r -> adjstAppl fTrm fCs False a r aTr
         PartialVal (FunType a r) -> adjstAppl fTrm fCs True a r aTr
         PartialVal _ -> pv
         BoolType -> pv
         _ -> mkError "not a function type" f

-- * translation of lambda abstractions

isPatternType :: As.Term -> Bool
isPatternType trm = case trm of
    QualVar (VarDecl _ _ _ _) -> True
    TypedTerm t _ _ _ -> isPatternType t
    TupleTerm ts _ -> all isPatternType ts
    _ -> False

transPattern :: Env -> Set.Set String -> Set.Set String -> As.Term
             -> Result (FunType, Isa.Term)
transPattern sign tyToks toks pat = do
    ITC ty trm cs <- transTerm sign tyToks False toks Set.empty pat
    case pat of
      TupleTerm [] _ -> return (ty, mkFree "_")
      _ -> if not (isPatternType pat) || isPartialVal ty
              || case cs of
                   None -> False
                   _ -> True then
        fatal_error ("illegal pattern for Isabelle: " ++ showDoc pat "")
             $ getRange pat
       else return (ty, trm)

-- form Abs(pattern term)
abstraction :: Env -> Set.Set String -> Set.Set String
            -> IsaTermCond -> As.Term -> Result IsaTermCond
abstraction sign tyToks toks (ITC ty body cs) pat = do
    (pTy, nPat) <- transPattern sign tyToks toks pat
    return $ ITC (FunType pTy ty) (Abs nPat body NotCont) cs
