{- |
Module      :  $Header$
Description :  A formula wrapper from formulae defined in CASL.AS_Basic_CASL to data Formula defined in Common.Normalization
Copyright   :  (c) Immanuel Normann, Uni Bremen 2007
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  inormann@jacobs-university.de
Stability   :  provisional
Portability :  portable
-}
module Search.CASL.FormulaWrapper where

import Search.Common.Normalization
import qualified Common.Id as Id
import qualified CASL.AS_Basic_CASL as Casl

{- TODO:
- wrapFormula und wrapTerm vervollständigen!

Vielleicht wäre es ausserdem sauberer, wenn man formeln unterteilt in:
1) TypesAsFormula
2) TermsAsFormula
-}

data CaslVar = PredSymb Casl.PRED_SYMB
	     | OpSymb Casl.OP_SYMB
	     | VarSymb Casl.VAR Casl.SORT
             | TypeSymb Casl.SORT deriving (Eq,Ord)

instance Show CaslVar
    where show (PredSymb v) = show v
	  show (OpSymb v) = show v
          show (VarSymb v _) = show v
          show (TypeSymb t) = ":" ++ show t

data CaslConst = TrueAtom | FalseAtom | EEqual | SEqual | Definedness
               | Function | Predicate | Total | Partial | Cartesian
               | Untyped deriving (Eq,Ord,Show)

{- TODO:
Provisorische Typkodierung:
typeBool, typeEqual, typeQuantifier, defaultVar, defaultXXX
-}

wrapTermB :: Casl.QUANTIFIER -> (Constant CaslConst)
wrapTermB Casl.Universal = All
wrapTermB Casl.Existential = Some
-- wrapTermB Unique_existential = ???

wrapSort :: Casl.SORT -> Formula (Constant CaslConst) CaslVar
wrapSort sort = Var (TypeSymb sort) []

-- todo: bei Casl.Op_typ bleibt noch der FunKind unberücksichtigt. Wie müsste er kodiert werden?
wrapOpType :: Casl.OP_TYPE -> Formula (Constant CaslConst) CaslVar
wrapOpType (Casl.Op_type caslFunKind doms cod _) = Const (LogicDependent Function) [funkind,Const (LogicDependent Cartesian) (map wrapSort doms), wrapSort cod]
    where funkind = case caslFunKind
                    of Casl.Total -> Const (LogicDependent Total) []
                       Casl.Partial -> Const (LogicDependent Partial) []

wrapTerm :: Casl.TERM f -> Formula (Constant CaslConst) (Formula (Constant CaslConst) CaslVar)
wrapTerm (Casl.Qual_var var sort _) = Var (Var (VarSymb var sort) [wrapSort sort]) []
wrapTerm (Casl.Application opSymb terms _) = Var wrappedOpSymb (map wrapTerm terms)
    where wrappedOpSymb = case opSymb of
			  (Casl.Op_name opName) -> Var (OpSymb opSymb) [Const (LogicDependent Untyped) []]
			  (Casl.Qual_op_name opName opType _) -> Var (OpSymb opSymb) [wrapOpType opType]
{-
    Warning: Pattern match(es) are non-exhaustive
	     In the definition of `wrapTerm':
		 Patterns not matched:
		     CASL.AS_Basic_CASL.Simple_id _
		     CASL.AS_Basic_CASL.Sorted_term _ _ _
		     CASL.AS_Basic_CASL.Cast _ _ _
		     CASL.AS_Basic_CASL.Conditional _ _ _ _
		     ...
-}
-- todo: wrapVarName, zipvardecl in wrapFormula verstecken
wrapVarName :: Casl.VAR ->  Casl.SORT -> Formula (Constant CaslConst) CaslVar
wrapVarName var sort = Var (VarSymb var sort) [(wrapSort sort)]

zipvardecl :: Casl.VAR_DECL -> [Formula (Constant CaslConst) CaslVar]
zipvardecl (Casl.Var_decl cvars sort _) = map (\cvar -> (wrapVarName cvar sort)) cvars

wrapPredType :: Casl.PRED_TYPE -> Formula (Constant CaslConst) CaslVar
wrapPredType (Casl.Pred_type doms _) = Const (LogicDependent Predicate) (map wrapSort doms)

wrapFormula :: Casl.FORMULA f -> Formula (Constant CaslConst) (Formula (Constant CaslConst) CaslVar)
wrapFormula (Casl.Quantification cb cvardecls cf _) = Binder b vars f
    where b = wrapTermB cb
	  vars = foldr (++) [] (map zipvardecl cvardecls)
	  f = wrapFormula cf
wrapFormula (Casl.Negation f _) = Const Not [wrapFormula f]
wrapFormula (Casl.Conjunction fs _) = Const And (map wrapFormula fs)
wrapFormula (Casl.Disjunction fs _) = Const Or (map wrapFormula fs)
wrapFormula (Casl.Implication f1 f2 _ _) = Const Imp [wrapFormula f1,wrapFormula f2]
wrapFormula (Casl.Equivalence f1 f2 _) = Const Eqv [wrapFormula f1,wrapFormula f2]
wrapFormula (Casl.True_atom _) = Const (LogicDependent TrueAtom) []
wrapFormula (Casl.False_atom _) = Const (LogicDependent FalseAtom) []
wrapFormula (Casl.Predication predSymb terms _) = Var wrappedOpSymb (map wrapTerm terms)
    where wrappedOpSymb = case predSymb of
			  (Casl.Pred_name predName) -> Var (PredSymb predSymb) [Const (LogicDependent Untyped) []]
			  (Casl.Qual_pred_name predName predType _) -> Var (PredSymb predSymb) [wrapPredType predType]
wrapFormula (Casl.Definedness t _) = Const (LogicDependent Definedness) [wrapTerm t]
wrapFormula (Casl.Existl_equation t1 t2 _) = Const (LogicDependent EEqual) [wrapTerm t1,wrapTerm t2] 
wrapFormula (Casl.Strong_equation t1 t2 _) = Const (LogicDependent SEqual) [wrapTerm t1,wrapTerm t2] 
--wrapFormula (Casl.Membership term sort _) = Const (LogicDependent Membership) [wrapTerm term,wrappedSort]
--    where wrappedSort = Var (Var (VarSymb var sort) [wrapSort sort]) [] -- so nicht, aber so aehnlich mit Const
wrapFormula f = error ("wrapFormula currently can't wrap this formula")
{- xxx
-- TODO:
    Warning: Pattern match(es) are non-exhaustive
	     In the definition of `wrapFormula':
		 Patterns not matched:
		     CASL.AS_Basic_CASL.Membership _ _ _
		     CASL.AS_Basic_CASL.Mixfix_formula _
		     CASL.AS_Basic_CASL.Unparsed_formula _ _
		     CASL.AS_Basic_CASL.Sort_gen_ax
		     CASL.AS_Basic_CASL.ExtFORMULA
-}
normalizeCaslFormula :: Casl.FORMULA f -> (Skeleton CaslConst,[CaslVar])
normalizeCaslFormula f = (sceleton,symbols)
    where nf = normalizeTyped $ wrapFormula f
	  sceleton = fst nf
	  symbols =  concatMap getVs (snd nf)
	  getVs (_,vs,_) = vs

{- Aus CASL.AS_Basic_CASL.hs und Common.Id.hs

data TERM f = Simple_id SIMPLE_ID
          | Qual_var VAR SORT Range

data OP_SYMB = Op_name OP_NAME
             | Qual_op_name OP_NAME OP_TYPE Range
                 -- pos: "(", op, colon, ")"
               deriving (Show, Eq, Ord)
data OP_TYPE = Op_type FunKind [SORT] SORT Range

data PRED_SYMB = Pred_name PRED_NAME 
               | Qual_pred_name PRED_NAME PRED_TYPE Range
data PRED_TYPE = Pred_type [SORT] Range

type OP_NAME = Id
type PRED_NAME = Id
type SORT = Id
data Id = Id [Token] [Id] Range 

type VAR = SIMPLE_ID
type SIMPLE_ID = Token
data Token = Token { tokStr :: String
                   , tokPos :: Range
                   } deriving (Eq, Ord)

-}