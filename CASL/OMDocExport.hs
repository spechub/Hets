{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{- |
Module      :  $Header$
Description :  CASL-to-OMDoc conversion
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2009
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  ewaryst.schulz@dfki.de
Stability   :  provisional
Portability :  portable

CASL implementation of the interface functions export_signToOmdoc,
export_morphismToOmdoc, export_senToOmdoc from class Logic. The actual
instantiation can be found in module "CASL.Logic_CASL".
-}

module CASL.OMDocExport
    ( exportSymToOmdoc
    , exportSenToOmdoc
    , exportTheoryToOmdoc
    , caslMetaTheory
    ) where

import OMDoc.DataTypes

import Common.Id
import Common.Result
import Common.AS_Annotation
import qualified Common.Lib.Rel as Rel

import Common.DocUtils

import CASL.AS_Basic_CASL
import CASL.Sign
import CASL.Fold
import CASL.Quantification
import CASL.OMDoc

import qualified Data.Map as Map
import Data.Maybe

-- --------------------------- TOPLEVEL Interface -----------------------------

type Env = NameMap Symbol


exportSymToOmdoc :: Env -> Symbol -> String -> Result TCElement
exportSymToOmdoc e sym n = toOMConstant e (n, symbType sym)


exportSenToOmdoc :: (GetRange f, Pretty f) => Env -> FORMULA f
                 -> Result TCorOMElement
exportSenToOmdoc e f =
    case f of
        Sort_gen_ax cs b -> return $ Left $ makeADTs e cs
                            (if b then Free else Generated)
        _ -> let err = const $ error "CASL extension not supported."
             in return $ Right $ foldFormula (omdocRec e err) f

-- | We have to export the subsort relation because it's not given in sentences
exportTheoryToOmdoc :: (Show f, Pretty e) => SigMap Symbol -> Sign f e
                    -> [Named (FORMULA f)] -> Result [TCElement]

exportTheoryToOmdoc sigm sig _ =
    return $ map (subsortToOmdoc $ sigMapSymbs sigm) $ Rel.toList $ sortRel sig


-- ------------------------ Sentences --------------------------

subsortToOmdoc :: Env -> (SORT, SORT) -> TCElement
subsortToOmdoc e (s1, s2) =
    let oms1@(OMS (_, OMName n1 _)) = oms e s1
        oms2@(OMS (_, OMName n2 _)) = oms e s2
    in TCSymbol (nameEncode "ST" [n1, n2])
           (OMA [const_subsortof, oms1, oms2]) Axiom Nothing


-- ------------------------ Symbol Interface --------------------------

class AsSymbol a where
    toSymbol :: a -> Symbol

instance AsSymbol SORT where
    toSymbol = idToSortSymbol

instance AsSymbol (Id, OpType) where
    toSymbol = uncurry idToOpSymbol

instance AsSymbol (Id, OP_TYPE) where
    toSymbol (x, y) = toSymbol (x, toOpType y)

instance AsSymbol OP_SYMB where
    toSymbol (Op_name n) = error $ "AsSymbol: Unqualified OP_SYMB: " ++ show n
    toSymbol (Qual_op_name n t _) = toSymbol (n, t)

instance AsSymbol (Id, PredType) where
    toSymbol = uncurry idToPredSymbol

instance AsSymbol (Id, PRED_TYPE) where
    toSymbol (x, y) = toSymbol (x, toPredType y)

instance AsSymbol PRED_SYMB where
    toSymbol (Pred_name n) = error $ "AsSymbol: Unqual. PRED_SYMB: " ++ show n
    toSymbol (Qual_pred_name n t _) = toSymbol (n, t)

-- ------------------------ OMDoc Constant Interface --------------------------

class AsOMConstant a where
    toOMConstant :: Env -> a -> Result TCElement


instance AsOMConstant (String, OMElement, SymbolRole) where
    toOMConstant _ (n, omelem, role) = return $ TCSymbol n omelem role Nothing

instance AsOMConstant (String, OpType) where
    toOMConstant e (n, ot) = toOMConstant e (n, makeObjectType e ot, Obj)

instance AsOMConstant (String, PredType) where
    toOMConstant e (n, pt) = toOMConstant e (n, makePredType e pt, Obj)

instance AsOMConstant String where
    toOMConstant e n = toOMConstant e (n, const_sort, Typ)

instance AsOMConstant (String, SymbType) where
    toOMConstant e (n, st) =
        case st of
          SortAsItemType -> toOMConstant e n
          OpAsItemType ot -> toOMConstant e (n, ot)
          PredAsItemType pt -> toOMConstant e (n, pt)

-- ------------------------ ADT --------------------------

makeADTs :: Env -> [Constraint] -> ADTType -> TCElement
makeADTs e cs b =
    TCADT $ map (makeADTSortDef e b) cs

makeADTSortDef :: Env -> ADTType -> Constraint -> OmdADT
makeADTSortDef e b (Constraint s l _) =
    ADTSortDef (omn e s) b $
    map (makeADTConstructor e . fst) l

makeADTConstructor :: Env -> OP_SYMB -> OmdADT
makeADTConstructor e os@(Qual_op_name n (Op_type _ args _ _) _) =
    if isInjName n then ADTInsort $ omqn e $ head args
    else ADTConstr (omn e os) $ map (makeADTArgument e) args

makeADTConstructor _ (Op_name (Id _ _ r)) =
    sfail "makeADTConstructor: No_qual_op" r

-- TODO: support for selectors
makeADTArgument :: Env -> SORT -> OmdADT
makeADTArgument e s = ADTArg (oms e s) Nothing


-- ------------------------ UTILS --------------------------

findInEnv :: (Ord k) => a -> Map.Map k a -> k -> a
findInEnv err m x = Map.findWithDefault err x m


sfail :: String -> Range -> a
sfail s r = error $ show (Diag Error ("unexpected " ++ s) r)

omn :: AsSymbol a => Env -> a -> String
omn e x = let s = toSymbol x
              err = error $ concat [ "omn: No mapping for ", show s, "\n"
                                   , "--------------------------------\n"
                                   , show e]
          in nameToString $ findInEnv err e s

omqn :: AsSymbol a => Env -> a -> OMQualName
omqn e x = let s = toSymbol x
               err = error $ concat [ "omqn: No mapping for ", show s, "\n"
                                    , "--------------------------------\n"
                                    , show e]
           in mkSimpleQualName $ findInEnv err e s

oms :: AsSymbol a => Env -> a -> OMElement
oms e x = let s = toSymbol x
              err = error $ "oms: No mapping for " ++ show s
          in simpleOMS $ findInEnv err e s


-- ------------------------ TYPES --------------------------

-- | Given an operator or predicate signature we construct the according type
makeType :: Env -> OpKind -> [SORT] -> Maybe SORT -> OMElement
makeType e _ [] (Just r) = oms e r
makeType e total domain range =
    if null args then funtypeconstr else OMA $ funtypeconstr : map (oms e) args
        where
          args = domain ++ maybeToList range
          funtypeconstr = case (total, range) of
                            (Total, Nothing) -> const_predtype
                            (Total, _) -> const_funtype
                            _ -> const_partialfuntype

makePredType :: Env -> PredType -> OMElement
makePredType e (PredType predargs) =
    makeType e Total predargs Nothing

makeObjectType :: Env -> OpType -> OMElement
makeObjectType e (OpType opkind opargs oprange) =
    makeType e opkind opargs (Just oprange)

-- ------------------------ TERMS --------------------------

appOrConst :: AsSymbol a => Env -> a -> [OMElement] -> OMElement
appOrConst e o [] = oms e o
appOrConst e o ts = OMA $ oms e o : ts

-- | The object e1 and its type e2
makeTyped :: OMElement -- ^ e1
          -> OMElement -- ^ e2
          -> OMElement
makeTyped e1 e2 = OMATTT e1 $ OMAttr const_type e2

varToOmdoc :: Token -> OMElement
varToOmdoc v = OMV $ mkSimpleName $ tokStr v

-- | typed vars can only be typed by a single sort (first order)
varDeclToOMDoc :: Env -> (VAR, SORT) -> OMElement
varDeclToOMDoc e (v, s) = makeTyped (varToOmdoc v) $ oms e s

omdocRec :: GetRange f => Env -> (f -> OMElement)
         -> Record f OMElement OMElement
omdocRec e mf = Record
    { foldQuantification = \ _ q vs f _ ->
      let s = case q of
                Universal -> const_forall
                Existential -> const_exists
                Unique_existential -> const_existsunique
          vl = map (varDeclToOMDoc e) $ flatVAR_DECLs vs
      in OMBIND s vl f
    , foldConjunction = \ _ fs _ -> OMA $ const_and : fs
    , foldDisjunction = \ _ fs _ -> OMA $ const_or : fs
    , foldImplication = \ _ f1 f2 b _ ->
        OMA [if b then const_implies else const_implied, f1, f2]
    , foldEquivalence = \ _ f1 f2 _ ->
                        OMA [const_equivalent, f1, f2]
    , foldNegation = \ _ f _ -> OMA [const_not, f]
    , foldTrue_atom = \ _ _ -> const_true
    , foldFalse_atom = \ _ _ -> const_false
    , foldPredication = \ _ p ts _ -> appOrConst e p ts
    , foldDefinedness = \ _ t _ -> OMA [const_def, t]
    , foldExistl_equation = \ _ t1 t2 _ -> OMA [const_eeq, t1, t2]
    , foldStrong_equation = \ _ t1 t2 _ -> OMA [const_eq, t1, t2]
    , foldMembership = \ _ t s _ -> OMA [const_in, t, oms e s]
    , foldMixfix_formula = \ t _ -> sfail "Mixfix_formula" $ getRange t
    , foldQuantOp = \ _ o _ _ -> sfail ("QuantOp " ++ show o) $ getRange o
    , foldQuantPred = \ _ p _ _ -> sfail ("QuantPred " ++ show p) $ getRange p
    , foldSort_gen_ax = \ t _ _ -> sfail
                        "Sort generating axioms should be filtered out before!"
                        $ getRange t
    , foldExtFORMULA = const mf
    , foldQual_var = \ _ v _ _ -> varToOmdoc v
    , foldApplication = \ _ o ts _ -> appOrConst e o ts
    , foldSorted_term = \ _ r s _ -> makeTyped r $ oms e s
    , foldCast = \ _ t s _ -> OMA [const_cast, t, oms e s]
    , foldConditional = \ _ e' f t _ -> OMA [const_if, e', f, t]
    , foldMixfix_qual_pred = \ _ p -> sfail "Mixfix_qual_pred" $ getRange p
    , foldMixfix_term = \ t _ -> sfail "Mixfix_term" $ getRange t
    , foldMixfix_token = \ _ t -> sfail "Mixfix_token" $ tokPos t
    , foldMixfix_sorted_term = \ _ _ r -> sfail "Mixfix_sorted_term" r
    , foldMixfix_cast = \ _ _ r -> sfail "Mixfix_cast" r
    , foldMixfix_parenthesized = \ _ _ r -> sfail "Mixfix_parenthesized" r
    , foldMixfix_bracketed = \ _ _ r -> sfail "Mixfix_bracketed" r
    , foldMixfix_braced = \ _ _ r -> sfail "Mixfix_braced" r
    , foldExtTERM = const mf }
