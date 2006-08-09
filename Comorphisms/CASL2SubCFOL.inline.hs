{- |
Module      :  $Header$
Copyright   :  (c) Zicheng Wang, C.Maeder Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Comorphism)

Coding out partiality (SubPCFOL= -> SubCFOL=),
-}

module Comorphisms.CASL2SubCFOL where

import Logic.Logic
import Logic.Comorphism

-- CASL
import CASL.Logic_CASL
import CASL.AS_Basic_CASL
import CASL.Sign
import CASL.Morphism
import CASL.Sublogic as SL hiding(bottom)
import CASL.Overload
import CASL.Fold
import CASL.Project
import CASL.Simplify
import CASL.StaticAna

import Common.Id
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Rel as Rel
import Common.AS_Annotation
import Common.ProofUtils

import Data.List (zip)

-- | The identity of the comorphism
data CASL2SubCFOL = CASL2SubCFOL deriving (Show)

instance Language CASL2SubCFOL -- default definition is okay

instance Comorphism CASL2SubCFOL
               CASL CASL_Sublogics
               CASLBasicSpec CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CASLSign
               CASLMor
               Symbol RawSymbol ()
               CASL CASL_Sublogics
               CASLBasicSpec CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CASLSign
               CASLMor
               Symbol RawSymbol () where
    sourceLogic CASL2SubCFOL = CASL
    sourceSublogic CASL2SubCFOL = SL.top
    targetLogic CASL2SubCFOL = CASL
    mapSublogic CASL2SubCFOL sl = if has_part sl then sl
        { has_part    = False -- partiality is coded out
        , has_pred    = True
        , which_logic = max Horn $ which_logic sl
        , has_eq      = True} else sl
    map_theory CASL2SubCFOL (sig, sens) =
        let bsrts = allSortsWithBottom sig $
                    Set.unions $ sortsWithBottom sig :
                       map (botFormulaSorts . sentence) sens
            constructors = foldr (\ ns l -> case sentence ns of
                Sort_gen_ax cs _ -> let (_, ops, _) = recover_Sort_gen_ax cs in
                                    ops ++ l
                _ -> l) [] sens
            genSens = concatMap (generateDefinedness bsrts) constructors
            sens1 = generateAxioms bsrts sig
            sens2 = map (mapNamed (simplifyFormula id . codeFormula bsrts))
                    sens
        in return (encodeSig bsrts sig, disambiguateSens Set.empty . nameSens
                        $ genSens ++ sens1 ++ sens2)
    map_morphism CASL2SubCFOL mor@Morphism{msource = src, mtarget = tar} =
        return
        mor { msource = encodeSig (allSortsWithBottom src
                                  $ sortsWithBottom src) src
            , mtarget = encodeSig (allSortsWithBottom tar
                                  $ sortsWithBottom tar) tar
            , fun_map = Map.map (\ (i, _) -> (i, Total)) $ fun_map mor }
    map_sentence CASL2SubCFOL sig sen =
        return $ simplifyFormula id $ codeFormula
           (allSortsWithBottom sig $
            Set.union (botFormulaSorts sen) $ sortsWithBottom sig) sen
    map_symbol CASL2SubCFOL s =
      Set.singleton s { symbType = totalizeSymbType $ symbType s }

generateDefinedness :: Set.Set SORT -> OP_SYMB -> [Named (FORMULA ())]
generateDefinedness bsrts o = case o of
    Qual_op_name i ot@(Op_type _ args res _) _ ->
        if Set.member res bsrts then
        let (_, v, t, _) = selForms1 "X"
                (i, makeTotal Total $ toOpType ot, map Sort args)
        in [(emptyName $ simplifyFormula id $ mkForall v
             (Implication (defVards bsrts v)
              (defined bsrts t res nullRange) True nullRange) nullRange)
            { senName = "ga_defined_" ++ showId i "" }]
        else []
    _ -> error "generateDefinedness"

totalizeSymbType :: SymbType -> SymbType
totalizeSymbType t = case t of
  OpAsItemType ot -> OpAsItemType ot { opKind = Total }
  _ -> t

sortsWithBottom :: Sign f e -> Set.Set SORT
sortsWithBottom sign =
    let ops = Map.elems $ opMap sign
        resSortsOfPartialFcts =
            Set.unions $ map (Set.map opRes .
                                 Set.filter ( \ t -> opKind t == Partial))
            ops
        collect given =
            let more = Set.unions $ map (Set.map opRes .
                                 Set.filter ( \ t -> any
                                 (flip Set.member given) $ opArgs t)) ops
            in if Set.isSubsetOf more given then given
               else collect $ Set.union more given
     in collect resSortsOfPartialFcts

-- all supersorts inherit the same bottom element
allSortsWithBottom :: Sign f e -> Set.Set SORT -> Set.Set SORT
allSortsWithBottom sign s =
    Set.unions $ s : map (flip supersortsOf sign) (Set.toList s)

bottom :: Id
bottom = mkId[mkSimpleId $ genNamePrefix ++ "bottom"]

defPred :: Id
defPred = mkId[mkSimpleId $ genNamePrefix ++ "defined"]

defined :: Set.Set SORT -> TERM f -> SORT -> Range -> FORMULA f
defined bsorts t s ps =
  if Set.member s bsorts then Predication
         (Qual_pred_name defPred (Pred_type [s] nullRange) nullRange) [t] ps
  else True_atom ps

defVards :: Set.Set SORT -> [VAR_DECL] -> FORMULA f
defVards bs [vs@(Var_decl [_] _ _)] = head $ defVars bs vs
defVards bs vs = Conjunction (concatMap (defVars bs) vs) nullRange

defVars :: Set.Set SORT -> VAR_DECL -> [FORMULA f]
defVars bs (Var_decl vns s _) = map (defVar bs s) vns

defVar :: Set.Set SORT -> SORT -> Token -> FORMULA f
defVar bs s v = defined bs (Qual_var v s nullRange) s nullRange

totalizeOpSymb :: OP_SYMB -> OP_SYMB
totalizeOpSymb o = case o of
    Qual_op_name i (Op_type _ args res ps) qs ->
        Qual_op_name i (Op_type Total args res ps) qs
    _ -> o

addBottomAlt :: Constraint -> Constraint
addBottomAlt c = c
    { opSymbs = opSymbs c ++
           [(Qual_op_name bottom
           (Op_type Total [] (newSort c) nullRange)
           nullRange, [])] }

argSorts :: Constraint -> Set.Set SORT
argSorts c = Set.unions $ map (argsOpSymb . fst) $ opSymbs c
    where argsOpSymb op = case op of
              Qual_op_name _ ot _ -> Set.fromList $ args_OP_TYPE ot
              _ -> error "argSorts"

totalizeConstraint :: Set.Set SORT -> Constraint -> Constraint
totalizeConstraint bsrts c =
    (if Set.member (newSort c) bsrts then addBottomAlt else id)
    c { opSymbs = map ( \ (o, is) -> (totalizeOpSymb o, is)) $ opSymbs c }

-- | Add projections to the signature
encodeSig :: Set.Set SORT -> Sign f e -> Sign f e
encodeSig bsorts sig = if Set.null bsorts then sig else
    sig { opMap = projOpMap, predMap = newpredMap } where
   newTotalMap = Map.map (Set.map $ makeTotal Total) $ opMap sig
   botType x = OpType {opKind = Total, opArgs=[], opRes=x }
   botTypes = Set.map botType bsorts
   botOpMap  = Map.insert bottom botTypes newTotalMap
   defType x = PredType{predArgs=[x]}
   defTypes = Set.map defType bsorts
   newpredMap = Map.insert defPred defTypes $ predMap sig
   rel = Rel.irreflex $ sortRel sig
   total (s, s') = OpType{opKind = Total, opArgs = [s'], opRes = s}
   setprojOptype = Set.map total $ Rel.toSet rel
   projOpMap = Set.fold ( \ t ->
                          Map.insert (uniqueProjName $ toOP_TYPE t)
                        $ Set.singleton t) botOpMap setprojOptype

generateAxioms :: Set.Set SORT -> Sign f e -> [Named (FORMULA ())]
generateAxioms bsorts sig = filter (not . is_True_atom . sentence) $
  map (mapNamed $ simplifyFormula id . rmDefs bsorts id) $
    map (mapNamed $ renameFormula id) (concat
    [inlineAxioms CASL
      " sort s < s'    \
      \ op pr : s'->s  \
      \ pred d:s       \
      \ forall x,y:s'. d(pr(x)) /\\ d(pr(y)) /\\ pr(x)=pr(y) => x=y \
      \ %(ga_projection_injectivity)% "
    ++ inlineAxioms CASL
     " sort s < s'     \
      \ op pr : s'->s  \
      \ pred d:s       \
      \ forall x:s . d(x) => pr(x)=x     %(ga_projection)% "
      | s <- sortList, let y =  mkSimpleId "y",
        s' <- minSupers s])
    ++ concat([inlineAxioms CASL
      " sort s          \
      \ pred d:s        \
      \ . exists x:s.d(x)            %(ga_nonEmpty)%" ++
     inlineAxioms CASL
      " sort s              \
      \ op bottom:s         \
      \ pred d:s            \
      \ forall x:s . x=bottom => not d(x)   %(ga_notDefBottom)%"
        | s <- sortList ] ++
    [inlineAxioms CASL
      " sort t             \
      \ sorts s_i          \
      \ sorts s_k          \
      \ op f:s_i->t     \
      \ var y_k:s_k             \
      \ forall y_i:s_i . def f(y_i) <=> def y_k /\\ def y_k %(ga_totality)%"
        | (f,typ) <- opList, opKind typ == Total,
          let s=opArgs typ; t=opRes typ; y= mkVars (length s) ] ++
    [inlineAxioms CASL
      " sort t             \
      \ sorts s_i          \
      \ sorts s_k          \
      \ op f:s_i->t     \
      \ var y_k:s_k             \
      \ forall y_i:s_i . def f(y_i) => def y_k /\\ def y_k %(ga_strictness)%"
        | (f,typ) <- opList, opKind typ == Partial,
          let s=opArgs typ; t=opRes typ; y= mkVars (length s) ] ++
    [inlineAxioms CASL
      " sorts s_i          \
      \ sorts s_k          \
      \ pred p:s_i     \
      \ var y_k:s_k             \
      \ forall y_i:s_i . p(y_i) => def y_k /\\ def y_k \
      \ %(ga_predicate_strictness)%"
        | (p,typ) <- predList, let s=predArgs typ; y=mkVars (length s) ] )
    where
        x = mkSimpleId "x"
        pr = projName
        minSupers so = keepMinimals sig2 id $ Set.toList $ Set.delete so
                           $ supersortsOf so sig2
        sig2 = sig { sortRel = Rel.irreflex $ sortRel sig }
        d = defPred
        sortList = Set.toList bsorts
        opList = [(f,t) | (f,types) <- Map.toList $ opMap sig,
                  t <- Set.toList types ]
        predList = [(p,t) | (p,types) <- Map.toList $ predMap sig,
                    t <- Set.toList types ]
        mkVars n = [mkSimpleId ("x_"++show i) | i<-[1..n]]

codeRecord :: Set.Set SORT -> (f -> f) -> Record f (FORMULA f) (TERM f)
codeRecord bsrts mf = (mapRecord mf)
    { foldQuantification = \  _ q vs qf ps ->
      case q of
      Universal ->
          Quantification q vs (Implication (defVards bsrts vs) qf True ps) ps
      _ -> Quantification q vs (Conjunction [defVards bsrts vs, qf] ps) ps
    , foldDefinedness = \ _ t ps -> defined bsrts t (term_sort t) ps
    , foldExistl_equation = \ _ t1 t2 ps ->
      Conjunction[Strong_equation t1 t2 ps,
                  defined bsrts t1 (term_sort t1) ps] ps
    , foldMembership = \ _ t s ps ->
          defined bsrts (projectUnique Total ps t s) s ps
    , foldSort_gen_ax = \ _ cs b ->
          Sort_gen_ax (map (totalizeConstraint bsrts) cs) b
    , foldApplication = \ _ o args ps -> Application (totalizeOpSymb o) args ps
    , foldCast = \ _ t s ps -> projectUnique Total ps t s
    }

codeFormula :: Set.Set SORT -> FORMULA () -> FORMULA ()
codeFormula bsorts = foldFormula (codeRecord bsorts $ error "CASL2SubCFol")

rmDefsRecord :: Set.Set SORT -> (f -> f) ->  Record f (FORMULA f) (TERM f)
rmDefsRecord  bsrts mf = (mapRecord mf)
    { foldDefinedness = \ _ t ps -> defined bsrts t (term_sort t) ps }

rmDefs :: Set.Set SORT -> (f -> f) -> FORMULA f -> FORMULA f
rmDefs bsrts = foldFormula . rmDefsRecord bsrts

-- | find sorts that need a bottom in membership formulas and casts

botSorts :: (f -> Set.Set SORT) -> Record f (Set.Set SORT) (Set.Set SORT)
botSorts mf = (constRecord mf Set.unions Set.empty)
     { foldMembership = \ _ _ s _ -> Set.singleton s
     , foldCast = \ _ _ s _ -> Set.singleton s }

botFormulaSorts :: FORMULA f -> Set.Set SORT
botFormulaSorts = foldFormula (botSorts $ const Set.empty)
