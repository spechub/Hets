{- |
Module      :  ./CASL/OMDocImport.hs
Description :  OMDoc-to-CASL conversion
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2009
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  ewaryst.schulz@dfki.de
Stability   :  provisional
Portability :  portable

CASL implementation of the interface functions omdocToSym, omdocToSen
, addOMadtToTheory, addOmdocToTheory from class Logic. The actual
instantiation can be found in module "CASL.Logic_CASL".
-}

module CASL.OMDocImport
    ( omdocToSym
    , omdocToSen
    , addOMadtToTheory
    , addOmdocToTheory
    ) where

import OMDoc.DataTypes

import Common.Id
import Common.Result
import Common.AS_Annotation
import qualified Common.Lib.Rel as Rel

import CASL.AS_Basic_CASL
import CASL.Sign
import CASL.OMDoc

import Control.Monad
import qualified Control.Monad.Fail as Fail

import qualified Data.Map as Map
import Data.List
import Data.Function (on)

-- * Environment Interface

type Env = SigMapI Symbol

symbolToSort :: Symbol -> SORT
symbolToSort (Symbol n SortAsItemType) = n
symbolToSort s = error $ "symbolToSort: Nonsort encountered: " ++ show s

symbolToOp :: Symbol -> (Id, OpType)
symbolToOp (Symbol n (OpAsItemType ot)) = (n, ot)
symbolToOp s = error $ "symbolToOp: Nonop encountered: " ++ show s

symbolToPred :: Symbol -> (Id, PredType)
symbolToPred (Symbol n (PredAsItemType pt)) = (n, pt)
symbolToPred s = error $ "symbolToPred: Nonpred encountered: " ++ show s

lookupSymbol :: Env -> OMName -> Symbol
lookupSymbol e omn =
    Map.findWithDefault
           (error $ concat [ "lookupSymbol failed for: "
                           , show omn, "\nmap: ", show $ sigMapISymbs e])
       omn $ sigMapISymbs e

lookupSort :: Env -> OMName -> SORT
lookupSort e = symbolToSort . lookupSymbol e

lookupSortOMS :: String -> Env -> OMElement -> SORT
lookupSortOMS msg = lookupOMS lookupSort $ msg ++ "(SORT)"

lookupPred :: Env -> OMName -> (Id, PredType)
lookupPred e = symbolToPred . lookupSymbol e

lookupPredOMS :: String -> Env -> OMElement -> (Id, PredType)
lookupPredOMS msg = lookupOMS lookupPred $ msg ++ "(PRED)"

lookupOp :: Env -> OMName -> (Id, OpType)
lookupOp e = symbolToOp . lookupSymbol e

lookupOpOMS :: String -> Env -> OMElement -> (Id, OpType)
lookupOpOMS msg = lookupOMS lookupOp $ msg ++ "(Op)"

lookupOMS :: (Env -> OMName -> a) -> String -> Env -> OMElement -> a
lookupOMS f msg e oms@(OMS (cd, omn)) =
    if cdIsEmpty cd then f e omn
    else error $ concat [ msg, ": lookupOMS: Nonempty cd in const: "
                        , show oms]
lookupOMS _ msg _ ome =
    error $ concat [msg, ": lookupOMS: Nonsymbol: ", show ome]

toOpSymb :: (Id, OpType) -> OP_SYMB
toOpSymb (i, t) = Qual_op_name i (toOP_TYPE t) nullRange

toPredSymb :: (Id, PredType) -> PRED_SYMB
toPredSymb (i, t) = Qual_pred_name i (toPRED_TYPE t) nullRange

-- * TOPLEVEL Interface

-- | A TCSymbols is transformed to a CASL symbol with given name.
omdocToSym :: Env -> TCElement -> String -> Result Symbol
omdocToSym e sym@(TCSymbol _ ctp srole _) n =
    case srole of
      Typ | ctp == const_sort -> return $ idToSortSymbol $ nameToId n
          | otherwise -> Fail.fail $ "omdocToSym: No sorttype for " ++ show sym
      Obj -> return $
             case omdocToType e ctp of
               Left ot -> idToOpSymbol (nameToId n) ot
               Right pt -> idToPredSymbol (nameToId n) pt
      _ -> Fail.fail $ concat [ "omdocToSym: only type or object are allowed as"
                         , " symbol roles, but found: ", show srole ]

omdocToSym _ sym _ = Fail.fail $ concat [ "omdocToSym: only TCSymbol is allowed,"
                                   , " but found: ", show sym ]


omdocToSen :: Env -> TCElement -> String
           -> Result (Maybe (Named (FORMULA f)))
omdocToSen e (TCSymbol _ t sr _) n =
    case nameDecode n of
      Just _ ->
          return Nothing -- don't translate encoded names here
      Nothing ->
          let ns = makeNamed n $ omdocToFormula e t
              res b = return $ Just $ ns { isAxiom = b }
          in case sr of
               Axiom -> res True
               Theorem -> res False
               _ -> return Nothing

omdocToSen _ sym _ = Fail.fail $ concat [ "omdocToSen: only TCSymbol is allowed,"
                                   , " but found: ", show sym ]


-- | Sort generation constraints are added as named formulas.
addOMadtToTheory :: Env
                 -> (Sign f e, [Named (FORMULA f)]) -> [[OmdADT]]
                 -> Result (Sign f e, [Named (FORMULA f)])
addOMadtToTheory e (sig, nsens) adts = do
    sgcs <- mapR (omdocToSortGenConstraint e) adts
    return (sig, nsens ++ sgcs)


-- | The subsort relation is recovered from exported sentences.
addOmdocToTheory :: Env -> (Sign f e, [Named (FORMULA f)]) -> [TCElement]
                 -> Result (Sign f e, [Named (FORMULA f)])
addOmdocToTheory e (sig, nsens) tcs = do
  srel <- omdocToSortRel e tcs
  return (sig { sortRel = Rel.transClosure srel }, nsens)


-- * Algebraic Data Types

omdocToSortGenConstraint :: Env -> [OmdADT] -> Result (Named (FORMULA f))
omdocToSortGenConstraint e sortdefs = do
  -- take the last type as the type of all constraints
  let (t, cs) = mapAccumL (const $ mkConstraint e) Generated sortdefs
  -- TODO: do we take newSort or origSort?
  return $ toSortGenNamed (mkSort_gen_ax cs $ t == Free) $ map newSort cs

mkConstraint :: Env -> OmdADT -> (ADTType, Constraint)
mkConstraint e (ADTSortDef nm t constrs) =
    let s = lookupSort e $ mkSimpleName nm
        l = map (mkConstructor e s) constrs
    in (t, Constraint s l s)

mkConstraint _ _ = error "mkConstraint: Malformed ADT expression"

mkConstructor :: Env -> SORT -> OmdADT -> (OP_SYMB, [Int])
mkConstructor e s (ADTConstr nm args) =
    let opn = nameToId $ lookupNotation e $ mkSimpleName nm
        l = map (mkArg e) args
    in (Qual_op_name opn (Op_type Total l s nullRange) nullRange, [0])


{- we have to create the name of this injection because we throw it away
during the export -}
mkConstructor e s (ADTInsort (_, omn)) =
    let argsort = lookupSort e omn
        opn = mkUniqueInjName argsort s
    in (Qual_op_name opn (Op_type Total [argsort] s nullRange) nullRange, [0])

mkConstructor _ _ _ = error "mkConstructor: Malformed ADT expression"

mkArg :: Env -> OmdADT -> SORT
mkArg e (ADTArg oms _) = lookupSortOMS "mkArg" e oms

mkArg _ _ = error "mkArg: Malformed ADT expression"


-- * Subsort Relation

omdocToSortRel :: Env -> [TCElement] -> Result (Rel.Rel SORT)
omdocToSortRel e = foldM (addMaybeToSortRel e) Rel.empty

addMaybeToSortRel :: Env -> Rel.Rel SORT -> TCElement -> Result (Rel.Rel SORT)
addMaybeToSortRel e r (TCSymbol n (OMA [sof, oms1, oms2]) Axiom _) =
    case nameDecode n of
      Just ("ST", _)
          | sof == const_subsortof ->
              let s1 = lookupSortOMS "addMaybeToSortRel: s1" e oms1
                  s2 = lookupSortOMS "addMaybeToSortRel: s2" e oms2
              in return $ Rel.insertKeyOrPair s1 s2 r
          | otherwise ->
              do
                warning () ("Use of subsortof in a non ST Statement: " ++ n)
                        nullRange
                return r
      _ -> return r

addMaybeToSortRel _ r _ = return r


-- * Types

omdocToType :: Env -> OMElement -> Either OpType PredType
omdocToType e (OMA (c : args)) =
    let sorts = map (lookupSortOMS "omdocToType" e) args
        opargs = init sorts
        oprange = last sorts
        res | c == const_predtype = Right $ PredType sorts
            | c == const_partialfuntype = Left $ OpType Partial opargs oprange
            | c == const_funtype = Left $ OpType Total opargs oprange
            | otherwise = error $ "omdocToType: unknown type constructor: "
                          ++ show c
    in res

omdocToType e oms@(OMS _)
    | oms == const_predtype = Right $ PredType []
    | otherwise = Left $ OpType Total [] $ lookupSortOMS "omdocToType" e oms

omdocToType _ ome = error $ "omdocToType: Non-supported element: " ++ show ome


-- * Terms and Formulas

type VarMap = Map.Map VAR SORT

type TermEnv = (Env, VarMap)

mkImplication, mkImplied, mkEquivalence
                 , mkNegation :: [FORMULA f] -> FORMULA f

mkImplication [x, y] = mkImpl x y
mkImplication _ = error "Malformed implication"
mkImplied [x, y] = mkRel RevImpl x y
mkImplied _ = error "Malformed if"
mkEquivalence [x, y] = mkEqv x y
mkEquivalence _ = error "Malformed equivalence"
mkNegation [x] = mkNeg x
mkNegation _ = error "Malformed negation"

mkDefinedness, mkExistl_equation, mkStrong_equation
    :: [TERM f] -> FORMULA f

mkDefinedness [x] = Definedness x nullRange
mkDefinedness _ = error "Malformed definedness"
mkExistl_equation [x, y] = mkExEq x y
mkExistl_equation _ = error "Malformed existl equation"
mkStrong_equation [x, y] = mkStEq x y
mkStrong_equation _ = error "Malformed strong equation"

-- Quantification, Predication and Membership are handled inside omdocToFormula

-- Term construction functions
mkT2 :: (OMElement -> a) -> (OMElement -> b) -> (a -> b -> Range -> TERM f)
     -> [OMElement] -> TERM f
mkT2 f g c l = case l of
                 [x, y] -> c (f x) (g y) nullRange
                 _ -> error "mkT2: 2 arguments expected"

mkT3 :: (OMElement -> a) -> (OMElement -> b) -> (OMElement -> c)
     -> (a -> b -> c -> Range -> TERM f) -> [OMElement] -> TERM f
mkT3 f g h c l = case l of
                   [x, y, z] -> c (f x) (g y) (h z) nullRange
                   _ -> error "mkT3: 3 arguments expected"


-- Formula construction functions
mkFF :: TermEnv -> ([FORMULA f] -> FORMULA f) -> [OMElement] -> FORMULA f
mkFF e f l = f $ map (omdocToFormula' e) l

mkTF :: TermEnv -> ([TERM f] -> FORMULA f) -> [OMElement] -> FORMULA f
mkTF e f l = f $ map (omdocToTerm' e) l

getQuantifier :: OMElement -> QUANTIFIER
getQuantifier oms
    | oms == const_forall = Universal
    | oms == const_exists = Existential
    | oms == const_existsunique = Unique_existential
    | otherwise = error $ "getQuantifier: unrecognized quantifier " ++ show oms

mkBinder :: TermEnv -> QUANTIFIER -> [OMElement] -> OMElement -> FORMULA f
mkBinder te@(e, _) q vars body =
    let (vm', vardecls) = toVarDecls te vars
        bd = omdocToFormula' (e, vm') body
    in Quantification q vardecls bd nullRange

toVarDecls :: TermEnv -> [OMElement] -> (VarMap, [VAR_DECL])
toVarDecls (e, vm) l =
    let f acc x = let (v, s) = toVarDecl e x
                      acc' = Map.insert v s acc
                  in (acc', (v, s))
        (vm', l') = mapAccumL f vm l
        -- group by same sort
        l'' = groupBy ((==) `Data.Function.on` snd) l'
        -- the lists returned by groupBy are never empty, so head will succeed
        g vsl = Var_decl (map fst vsl) (snd $ head vsl) nullRange
    in (vm', map g l'')

-- in CASL we expect all bound vars to be attributed (typed)
toVarDecl :: Env -> OMElement -> (VAR, SORT)
toVarDecl e (OMATTT (OMV v) (OMAttr ct t))
    | ct == const_type = (nameToToken $ name v, lookupSortOMS "toVarDecl" e t)
    | otherwise = error $ "toVarDecl: unrecognized attribution " ++ show ct

toVarDecl _ _ = error "toVarDecl: bound variables should be attributed."

-- Toplevel entry point
omdocToFormula :: Env -> OMElement -> FORMULA f
omdocToFormula e = omdocToFormula' (e, Map.empty)


-- Functions with given VarMap

-- omdocToTerm has no toplevel entry point
omdocToTerm' :: TermEnv -> OMElement -> TERM f
omdocToTerm' e@(ie, vm) f =
    case f of
      OMA (h : args)
          | h == const_cast ->
              mkT2 (omdocToTerm' e) (lookupSortOMS "omdocToTerm: Cast" ie)
                   Cast args
          | h == const_if ->
              mkT3 (omdocToTerm' e) (omdocToFormula' e) (omdocToTerm' e)
                   Conditional args
          -- all other heads mean application
          | otherwise ->
              let os = toOpSymb $ lookupOpOMS "omdocToTerm" ie h
                  args' = map (omdocToTerm' e) args
              in Application os args' nullRange
      OMS _ -> let os = toOpSymb $ lookupOpOMS "omdocToTerm-OMS:" ie f
               in Application os [] nullRange
      OMV omn -> let var = nameToToken $ name omn
                     -- lookup the type of the variable in the varmap
                     s = Map.findWithDefault
                         (error $ concat [ "omdocToTerm': Variable not in "
                                         , "varmap: ", show var ]) var vm
                 in Qual_var var s nullRange
      OMATTT ome (OMAttr ct t)
          | ct == const_type ->
              -- same as cast
              mkT2 (omdocToTerm' e) (lookupSortOMS "omdocToTerm: Sorted" ie)
                   Sorted_term [ome, t]
          | otherwise -> error $ "omdocToTerm: unrecognized attribution "
                         ++ show ct
      _ -> error $ "omdocToTerm: no valid term " ++ show f


omdocToFormula' :: TermEnv -> OMElement -> FORMULA f
omdocToFormula' e@(ie, _) f =
    case f of
      OMA (h : args)
          | h == const_in ->
              case args of
                [x, s] ->
                    Membership (omdocToTerm' e x) (lookupSortOMS
                                                   "omdocToFormula"
                                                  ie s) nullRange
                _ -> error "Malformed membership"
          | h == const_and ->
              mkFF e conjunct args
          | h == const_or ->
              mkFF e disjunct args
          | h == const_implies ->
              mkFF e mkImplication args
          | h == const_implied ->
              mkFF e mkImplied args
          | h == const_equivalent ->
              mkFF e mkEquivalence args
          | h == const_not ->
              mkFF e mkNegation args
          | h == const_def ->
              mkTF e mkDefinedness args
          | h == const_eeq ->
              mkTF e mkExistl_equation args
          | h == const_eq ->
              mkTF e mkStrong_equation args
          -- all other heads mean predication
          | otherwise ->
              let ps = toPredSymb $ lookupPredOMS "omdocToFormula" ie h
                  g l = Predication ps l nullRange in
              mkTF e g args

      OMBIND binder args body ->
          mkBinder e (getQuantifier binder) args body

      OMS _ | f == const_true -> trueForm
            | f == const_false -> falseForm
            -- Propositional Constants (0-ary predicates):
            | otherwise ->
                Predication (toPredSymb
                             $ lookupPredOMS
                                   ("omdocToFormula: can't handle constant "
                                    ++ show f) ie f) [] nullRange
      _ -> error $ "omdocToFormula: no valid formula " ++ show f
