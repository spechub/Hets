module CASL.ToTIP where

import TIP.AbsTIP
import TIP.Utils

import qualified CASL.Sign as CS
import CASL.AS_Basic_CASL
import CASL.Utils (codeOutUniqueExtF)
import CASL.Induction (inductionSentence)
import Common.DocUtils
import Common.Id (mkId)
import Common.AS_Annotation
import qualified Common.Lib.MapSet as MapSet

import qualified Data.Set as Set
import Data.Maybe (mapMaybe)
import Data.List (intercalate)

tipSign :: (CS.CASLSign, [Named CASLFORMULA]) -> [Decl]
tipSign (sig, thry) =
  map declareSort (Set.toList (Set.difference (CS.sortSet sig) freeTypes))
  ++ (declareData $ map tipDatatype $ concat fTAC)
  ++ map declarePred (MapSet.toPairList (CS.predMap sig))
  ++ map declareOp (filter ((flip Set.notMember) constructors) $ MapSet.toPairList (CS.opMap sig))
    where 
      fTAC = freeTypesAndCons thry
      constructors = Set.fromList $ map fromOP_SYMBtoOpMapPair $ concatMap snd $ concat fTAC
      freeTypes = Set.fromList $ map fst $ concat fTAC

fromOP_SYMBtoOpMapPair :: OP_SYMB -> (OP_NAME,CS.OpType)
fromOP_SYMBtoOpMapPair (Qual_op_name n ty _) = (n, CS.toOpType ty)
fromOP_SYMBtoOpMapPair o = error ("CASL.ToTIP.fromOP_SYMBtoOpMapPair" ++ (show.pretty) o)

tipAxiom :: Named CASLFORMULA -> Decl
tipAxiom f = 
  Formula Assert [toAttr ("axiom",Just $ senAttr f)] $ tipFORMULA $ sentence f

tipFORMULA :: CASLFORMULA -> Expr
tipFORMULA = tipSOFORMULA Set.empty

tipSOFORMULA :: Set.Set (PRED_NAME,CS.PredType) -> CASLFORMULA -> Expr
tipSOFORMULA qPreds f@(Quantification Unique_existential _ _ _) = tipSOFORMULA qPreds $ codeOutUniqueExtF id id f
tipSOFORMULA qPreds (Quantification q vds f _) = Binder (tipQUANTIFIER q) (concatMap tipVAR_DECL vds) (tipSOFORMULA qPreds f)
tipSOFORMULA qPreds (Junction j fs _) = App (tipJunctor j) $ map (tipSOFORMULA qPreds) fs
tipSOFORMULA qPreds (Relation lhs r rhs _) = App (tipRelation r) $ map (tipSOFORMULA qPreds) [lhs, rhs]
tipSOFORMULA qPreds (Negation f _) = App Not [tipSOFORMULA qPreds f]
tipSOFORMULA _Preds (Atom b _) = Lit (if b then LitTrue else LitFalse)
tipSOFORMULA qPreds (Predication p@(Qual_pred_name pName pType@(Pred_type pSorts _) _) ts _)
  | (pName,CS.toPredType pType) `Set.member` qPreds = App At (Var (NoAs $ tipPredVAR pSorts pName) : map (tipSOTERM qPreds) ts)
  | otherwise = App (Const $ tipPRED_SYMB p) $ map (tipSOTERM qPreds) ts
tipSOFORMULA qPreds (Equation lhs Strong rhs _) = App Equal $ map (tipSOTERM qPreds) [lhs, rhs] 
tipSOFORMULA qPreds (Sort_gen_ax cs _) = tipSOFORMULA qPreds $ inductionSentence cs
tipSOFORMULA qPreds (QuantPred pName pType f) =
  let pT = CS.toPredType pType in
      Binder Forall (tipPredVAR_DECL pName pT) $ tipSOFORMULA (Set.insert (pName,pT) qPreds) f
tipSOFORMULA _Preds f = error ("CASL.ToTIP.tipSOFORMULA" ++ (show.pretty) f)
--(Definedness (TERM f) Range)
--(Membership (TERM f) SORT Range)
--(Mixfix_formula (TERM f))
--(Unparsed_formula String Range)
--(QuantOp OP_NAME OP_TYPE (FORMULA f))
--(ExtFORMULA f)

tipSOTERM :: Set.Set (PRED_NAME,CS.PredType) -> TERM () -> Expr
tipSOTERM _Preds (Qual_var v s _) = Var $ NoAs (tipVAR s v)
tipSOTERM qPreds (Sorted_term t _ _) = tipSOTERM qPreds t
tipSOTERM qPreds (Application op ts _) = App (Const $ tipOP_SYMB op) $ map (tipSOTERM qPreds) ts
tipSOTERM qPreds (Conditional t c f _) = App IfThenElse [tipSOFORMULA qPreds c, tipSOTERM qPreds t, tipSOTERM qPreds f]
tipSOTERM _Preds t = error ("CASL.ToTIP.tipSOTERM" ++ (show.pretty) t)

tipOP_SYMB :: OP_SYMB -> PolySymbol
tipOP_SYMB (Qual_op_name n ot _) = NoAs $ tipOP_NAME (res_OP_TYPE ot) (args_OP_TYPE ot) n
tipOP_SYMB o = error ("CASL.ToTIP.tipOP_SYMB" ++ (show.pretty) o)

tipOP_NAME :: SORT -> [SORT] -> OP_NAME -> Symbol
tipOP_NAME = qualNameToSymbol "f" . Just

tipPRED_SYMB :: PRED_SYMB -> PolySymbol
tipPRED_SYMB (Qual_pred_name n (Pred_type as _) _) = NoAs $ tipPRED_NAME as n
tipPRED_SYMB p = error ("CASL.ToTIP.tipPRED_SYMB" ++ (show.pretty) p)

tipPRED_NAME :: [SORT] -> PRED_NAME -> Symbol
tipPRED_NAME = qualNameToSymbol "p" Nothing

tipProfile :: [SORT] -> Maybe SORT -> String
tipProfile as r = let addArrow = if null as then id else ("->"++) in
  intercalate "*" (map show as) ++ maybe "" (addArrow.show) r

tipRelation :: Relation -> Head
tipRelation Equivalence = Equal
tipRelation _ = Implies

tipJunctor :: Junctor -> Head
tipJunctor Con = And
tipJunctor Dis = Or

tipQUANTIFIER :: QUANTIFIER -> Binder
tipQUANTIFIER Universal = Forall
tipQUANTIFIER Existential = Exists
tipQUANTIFIER Unique_existential = error "CASL.ToTIP.tipQUANTIFIER: Unique_existential should have been coded out before getting here."

tipPredVAR_DECL :: PRED_NAME -> CS.PredType -> [Binding]
tipPredVAR_DECL pN pT = let pS = CS.predArgs pT in
  [Binding (tipPredVAR pS pN) $
    ArrowTy (map (TyVar . tipSORT) pS ++ [BoolTy])]

tipPredVAR :: [SORT] -> PRED_NAME -> Symbol
tipPredVAR = qualNameToSymbol "P" Nothing

tipVAR_DECL :: VAR_DECL -> [Binding]
tipVAR_DECL (Var_decl vars sort _) = map (\ v -> Binding (tipVAR sort v) (TyVar $ tipSORT sort)) vars

tipVAR :: SORT -> VAR -> Symbol
tipVAR s = qualNameToSymbol "F" (Just s) [] . mkId . (: [])

tipSORT :: SORT -> Symbol
tipSORT = qualNameToSymbol "s" Nothing []

qualNameToSymbol :: Show a => String -> Maybe SORT -> [SORT] -> a -> Symbol
qualNameToSymbol prefix resSort argSorts i =
  toSymbol (prefix ++ tipProfile argSorts resSort ++ "_" ++ show i)

tipDatatype :: (SORT, [OP_SYMB]) -> (DatatypeName, Datatype)
tipDatatype (s,cs) =
  ( DatatypeName (AttrSymbol (tipSORT s) []) 0
  , DatatypeMono $ InnerDatatype $ map tipConstructor cs)

tipConstructor :: OP_SYMB -> Constructor
tipConstructor (Qual_op_name n ts _) =
  let as = args_OP_TYPE ts; r = res_OP_TYPE ts; s = tipOP_NAME r as n in
      Constructor (AttrSymbol s []) $
        map (tipSelector s) (zip as [1..])
tipConstructor o = error ("CASL.ToTIP.tipConstructor" ++ (show.pretty) o)

tipSelector :: Symbol -> (SORT,Integer) -> Binding
tipSelector s (r,i) =
  Binding (qualNameToSymbol ('i' : show i) Nothing [] $
    pretty (fromSymbol s)) (TyVar $ tipSORT r)

freeTypesAndCons :: [Named (FORMULA f)] -> [[(SORT, [OP_SYMB])]]
freeTypesAndCons = mapMaybe $ justFTAC . sentence
  where
    justFTAC (Sort_gen_ax cs True) = Just $ recoverSortGen cs
    justFTAC _ = Nothing

declareSort :: SORT -> Decl
declareSort s = DeclareSort (AttrSymbol (tipSORT s) []) 0

declareOp :: (OP_NAME, CS.OpType) -> Decl
declareOp (o, ot)
  | null as
  = DeclareConst symbol $ ConstTypeMono ty
  | otherwise
  = DeclareFun symbol $ FunTypeMono $ InnerFunType (map (TyVar . tipSORT) as) ty
    where as = CS.opArgs ot
          r = CS.opRes ot
          symbol = AttrSymbol (tipOP_NAME r as o) []
          ty = TyVar $ tipSORT r

declarePred :: (PRED_NAME, CS.PredType) -> Decl
declarePred (p, pt)
  | null as
  = DeclareConst symbol $ ConstTypeMono BoolTy
  | otherwise
  = DeclareFun symbol $ FunTypeMono $ InnerFunType (map (TyVar . tipSORT) as) BoolTy
    where as = CS.predArgs pt
          symbol = AttrSymbol (tipPRED_NAME as p) []
