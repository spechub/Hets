{- |
Module      :  $Header$
Description :  Hets-to-OMDoc conversion
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  ewaryst.schulz@dfki.de
Stability   :  provisional
Portability :  non-portable(Logic)

CASL implementation of the interface functions export_signToOmdoc,
export_morphismToOmdoc, export_senToOmdoc from class Logic. The actual
instantiation can be found in module CASL.Logic_CASL.
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
-- import qualified Common.Lib.Rel as Rel

import CASL.AS_Basic_CASL
import CASL.Sign
-- import CASL.Fold
-- import CASL.Quantification
import CASL.OMDoc

import qualified Data.Map as Map
import Data.List
import Data.Maybe

-- * Environment Interface

type Env = SigMapI Symbol

symbolToSort :: Symbol -> SORT
symbolToSort (Symbol n SortAsItemType) = n
symbolToSort _ = error "symbolToSort: Nonsort encountered"

symbolToOp :: Symbol -> (Id, OpType)
symbolToOp (Symbol n (OpAsItemType ot)) = (n, ot)
symbolToOp _ = error "symbolToOp: Nonop encountered"

symbolToPred :: Symbol -> (Id, PredType)
symbolToPred (Symbol n (PredAsItemType pt)) = (n, pt)
symbolToPred _ = error "symbolToPred: Nonpred encountered"

lookupSymbol :: Env -> OMName -> Symbol
lookupSymbol e omn =
    Map.findWithDefault
           (error $ concat [ "lookupSymbol failed for: "
                           , show omn, " map ", show $ sigMapISymbs e])
       omn $ sigMapISymbs e

lookupSort :: Env -> OMName -> SORT
lookupSort e = symbolToSort . lookupSymbol e

lookupSortOMS :: String -> Env -> OMElement -> SORT
lookupSortOMS msg = lookupOMS lookupSort $ msg ++ "(SORT)"

lookupPred :: Env -> OMName -> (Id, PredType)
lookupPred e = symbolToPred . lookupSymbol e

lookupPredOMS :: String -> Env -> OMElement -> (Id, PredType)
lookupPredOMS msg = lookupOMS lookupPred $ msg ++ "(PRED)"

lookupOMS :: (Env -> OMName -> a) -> String -> Env -> OMElement -> a
lookupOMS f msg e oms@(OMS (cd, omn)) =
    if cdIsEmpty cd then f e omn
    else error $ concat [ msg, ": lookupOMS: Nonempty cd in const: "
                        , show oms]
lookupOMS _ msg _ ome =
    error $ concat [msg, ": lookupOMS: Nonsymbol: ", show ome]


-- * TOPLEVEL Interface

-- | A TCSymbols is transformed to a CASL symbol with given name.
omdocToSym :: Env -> TCElement -> String -> Result Symbol
omdocToSym e sym@(TCSymbol _ ctp srole _) n =
    case srole of
      Typ | ctp == const_sort -> return $ idToSortSymbol $ nameToId n
          | otherwise -> fail $ "omdocToSym: No sorttype for " ++ show sym
      Obj -> return $
             case omdocToType e ctp of
               Left ot -> idToOpSymbol (nameToId n) ot
               Right pt -> idToPredSymbol (nameToId n) pt
      _ -> fail $ concat [ "omdocToSym: only type or object are allowed as"
                         , " symbol roles, but found: ", show srole ]

omdocToSym _ sym _ = fail $ concat [ "omdocToSym: only TCSymbol is allowed,"
                                   , " but found: ", show sym ]


omdocToSen :: Env -> TCElement -> String
           -> Result (Maybe (Named (FORMULA f)))
omdocToSen e (TCSymbol _ t sr _) n =
    case nameDecode n of
      Just _ ->
          return Nothing
      Nothing ->
          if elem sr [Axiom, Theorem]
          then return $ Just $ makeNamed n $ omdocToFormula e t
          else return Nothing

omdocToSen _ sym _ = fail $ concat [ "omdocToSen: only TCSymbol is allowed,"
                                   , " but found: ", show sym ]


-- | Sort generation constraints are added as named formulas.
addOMadtToTheory :: Env
                 -> (Sign f e, [Named (FORMULA f)]) -> [[OmdADT]]
                 -> Result (Sign f e, [Named (FORMULA f)])
addOMadtToTheory e (sig, nsens) adts = do
    sgcs <- mapR (omdocToSortGenConstraint e) adts
    return (sig, nsens ++ sgcs)


-- | The subsort relation is recovered from exported sentences.
addOmdocToTheory :: Env
                 -> (Sign f e, [Named (FORMULA f)]) -> [TCElement]
                 -> Result (Sign f e, [Named (FORMULA f)])
addOmdocToTheory _ t _ = return t


-- * Algebraic Data Types

omdocToSortGenConstraint :: Env -> [OmdADT] -> Result (Named (FORMULA f))
omdocToSortGenConstraint e sortdefs = do
  -- take the last type as the type of all constraints
  let (t, cs) = mapAccumL (const $ mkConstraint e) Generated sortdefs
  -- TODO: do we take newSort or origSort?
  return $ toSortGenNamed (Sort_gen_ax cs $ t == Free) $ map newSort cs

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


-- we have to create the name of this injection because we throw it away
-- during the export
mkConstructor e s (ADTInsort (_, omn)) =
    let opn = error "TODO: mkConstructor: create an injection name"
        argsort = lookupSort e omn
    in (Qual_op_name opn (Op_type Total [argsort] s nullRange) nullRange, [0])

mkConstructor _ _ _ = error "mkConstructor: Malformed ADT expression"

mkArg :: Env -> OmdADT -> SORT
mkArg e (ADTArg oms _) = lookupSortOMS "mkArg" e oms

mkArg _ _ = error "mkArg: Malformed ADT expression"


-- * Subsort Relation


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

omdocToType e oms@(OMS _) =
    Left $ OpType Total [] $ lookupSortOMS "omdocToType" e oms

omdocToType _ ome = error $ "omdocToType: Non-supported element: " ++ show ome


-- * Terms and Formulas

type VarMap = Map.Map VAR SORT

type TermEnv = (Env, VarMap)

mkConjunction, mkDisjunction, mkImplication, mkIf, mkEquivalence, mkNegation
    :: [FORMULA f] -> FORMULA f

mkConjunction l = Conjunction l nullRange
mkDisjunction l = Disjunction l nullRange
mkImplication [x, y] = Implication x y True nullRange
mkImplication _ = error "Malformed implication"
mkIf [x, y] = Implication x y False nullRange
mkIf _ = error "Malformed if"
mkEquivalence [x, y] = Equivalence x y nullRange
mkEquivalence _ = error "Malformed equivalence"
mkNegation [x] = Negation x nullRange
mkNegation _ = error "Malformed negation"

mkDefinedness, mkExistl_equation, mkStrong_equation
    :: [TERM f] -> FORMULA f

mkDefinedness [x] = Definedness x nullRange
mkDefinedness _ = error "Malformed definedness"
mkExistl_equation [x, y] = Existl_equation x y nullRange
mkExistl_equation _ = error "Malformed existl equation"
mkStrong_equation [x, y] = Strong_equation x y nullRange
mkStrong_equation _ = error "Malformed strong equation"

-- Quantification, Predication and Membership are handled inside omdocToFormula

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
        l'' = groupBy (\ x y -> snd x == snd y) l'
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
omdocToFormula e f = omdocToFormula' (e, Map.empty) f


-- Functions with given VarMap

-- omdocToTerm has no toplevel entry point
omdocToTerm' :: TermEnv -> OMElement -> TERM f
omdocToTerm' e _ = error "TODO:"

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
              mkFF e mkConjunction args
          | h == const_or ->
              mkFF e mkDisjunction args
          | h == const_implies ->
              mkFF e mkImplication args
          | h == const_implied ->
              mkFF e mkIf args
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
              let (i, t) = lookupPredOMS "omdocToFormula" ie h
                  g l = Predication (Qual_pred_name i (toPRED_TYPE t)
                                                    nullRange) l nullRange in
              mkTF e g args

      OMBIND binder args body ->
          mkBinder e (getQuantifier binder) args body

      _ | f == const_true -> True_atom nullRange
      _ | f == const_false -> False_atom nullRange
      _ | otherwise -> error $ "omdocToFormula: no valid formula " ++ show f

{-
    -- | Simple variable
  | OMV OMName
    -- | Attributed element needed for type annotations of elements
  | OMATTT OMElement OMAttribute
    -- | Application to a list of arguments,
    -- first argument is usually the functionhead
  | OMA [OMElement]
    -- | Bindersymbol, bound vars, body
  | OMBIND OMElement [OMElement] OMElement


data TERM f = Qual_var VAR SORT Range -- pos: "(", var, colon, ")"
          | Application OP_SYMB [TERM f] Range
            -- pos: parens around TERM f if any and seperating commas
          | Sorted_term (TERM f) SORT Range
            -- pos: colon
          | Cast (TERM f) SORT Range
            -- pos: "as"
          | Conditional (TERM f) (FORMULA f) (TERM f) Range

-}
