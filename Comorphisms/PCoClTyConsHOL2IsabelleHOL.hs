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
           else Map.insert (showIsaTypeT tyId baseSign) [(isaTerm, [])] m
                -- translate the kind here!
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
transOpInfo (OpInfo t _ opDef) =
  case opDef of
    ConstructData _ -> Nothing
    _  -> Just (transOpType t)

-- operation type
transOpType :: TypeScheme -> Typ
transOpType (TypeScheme _ op _) = transType op

-- types
transType :: Type -> Typ
transType t = case getTypeAppl t of
   (TypeName tid _ n, tyArgs) -> let num = length tyArgs in
      if n == 0 then
          if tid == unitTypeId && null tyArgs then boolType
          else if tid == lazyTypeId && num == 1 then
             transType $ head tyArgs
          else if isArrow tid && num == 2 then
             let [t1, t2] = tyArgs
                 p = isPartialArrow tid
             in mkFunType (transType t1) $
                    if isPredType t then boolType
                       else (if p
                             then mkOptionType
                             else id) $ transType t2
          else if isProductId tid && num > 1 then
             foldl1 prodType $ map transType tyArgs
          else Type (showIsaTypeT tid baseSign) [] 
                   $ map transType tyArgs
       else TFree (showIsaTypeT tid baseSign) []
            -- type arguments are not allowed here!
   _ -> error $ "transType " ++ showPretty t "\n" ++ show t

data FunType = NoFun | BoolVal | FunType FunType FunType | PartialVal FunType
             deriving Eq

isPartialVal :: FunType -> Bool
isPartialVal t = case t of 
    PartialVal _ -> True
    _ -> False

funType :: Type -> FunType
funType t = case getTypeAppl t of
   (TypeName tid _ n, tyArgs) | n == 0 ->
       if tid == unitTypeId && null tyArgs then BoolVal
       else case tyArgs of 
              [arg, res] | isArrow tid ->
                let tArg = funType arg
                    tRes = funType res
                in FunType tArg $ 
                   (if tRes /= BoolVal && isPartialArrow tid then PartialVal
                    else id) tRes
              _ -> NoFun 
   _ -> NoFun

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
    Le.Formula t      -> Just (snd $ transTerm sign t)
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

exEqualOp :: Isa.Term
exEqualOp = conDouble "exEqualOp"

ifThenElseOp :: Isa.Term
ifThenElseOp = conDouble "ifThenElseOp"

uncurryOp :: Isa.Term
uncurryOp = conDouble "uncurryOp"

-- terms
transTerm :: Env -> As.Term -> (FunType, Isa.Term)
transTerm sign trm = case trm of
    QualVar (VarDecl var t _ _) -> (funType t,  
        Isa.Free (transVar var) $ transType t)
    QualOp _ (InstOpId opId _ _) ts@(TypeScheme _ ty _) _ 
      | opId == trueId -> (fTy, true)
      | opId == falseId -> (fTy, false)
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
        in (BoolVal, foldr (quantify quan) psi varDecls)
    TypedTerm t _ _ _ -> transTerm sign t
    LambdaTerm pats _ body _ ->
        let tPats = map (fst . transTerm sign) pats 
            (bodyTy, bodyTrm) = transTerm sign body
        in ( foldr FunType bodyTy tPats
           , foldr (abstraction sign) bodyTrm pats )
    LetTerm As.Let peqs body _ -> 
        let (bTy, bTrm) = transTerm sign body
        in (bTy, Isa.Let (map (transProgEq sign) peqs) bTrm)
    TupleTerm ts@(_ : _)  _ -> 
        let (tys, tts) = unzip $ map (transTerm sign) ts
        in (if any isPartialVal tys then PartialVal NoFun else NoFun,
            foldl1 (binConst pairC) tts)
    ApplTerm t1 t2 _ -> mkApp sign t1 t2 -- transAppl sign Nothing t1 t2
    _ -> error $ "PCoClTyConsHOL2IsabelleHOL.transTerm " ++ showPretty trm "\n"
                ++ show trm

mkApp :: Env -> As.Term -> As.Term -> (FunType, Isa.Term)
mkApp sg tt tt' = 
    let (fTy, fTrm) = transTerm sg tt
        (aTy, aTrm) = transTerm sg tt'
    in case fTy of
         FunType _ r@(PartialVal _) ->
            (r, termAppl (termAppl (conDouble 
                (if isPartialVal aTy then "appl1" else "appl2")) fTrm) aTrm)
         FunType _ r -> if isPartialVal aTy then
            (PartialVal r, termAppl (termAppl (conDouble "appl3") fTrm) aTrm)
             else (r, termAppl fTrm aTrm)
         PartialVal (FunType _ r@(PartialVal _)) ->
            (r, termAppl (termAppl (conDouble 
                (if isPartialVal aTy then "appl4" else "appl5")) fTrm) aTrm)
         PartialVal (FunType _ r) ->
            (PartialVal r, termAppl (termAppl (conDouble 
                (if isPartialVal aTy then "appl6" else "appl7")) fTrm) aTrm)
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
