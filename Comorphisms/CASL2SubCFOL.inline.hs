{- |
Module      :  $Header$
Description :  coding out partiality
Copyright   :  (c) Zicheng Wang, C.Maeder Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Comorphism)

Coding out partiality (SubPCFOL= -> SubCFOL=) while keeping subsorting.
Without unique bottoms sort generation axioms are not allowed.
Then we have (SubPFOL= -> SubFOL=).
-}

module Comorphisms.CASL2SubCFOL where

import Logic.Logic
import Logic.Comorphism

import CASL.Logic_CASL
import CASL.AS_Basic_CASL
import CASL.Sign
import CASL.Morphism
import CASL.Sublogic as SL hiding (bottom)
import CASL.Overload
import CASL.Fold
import CASL.Project
import CASL.Simplify

import Common.Id
import Common.DocUtils
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Common.Lib.Rel as Rel
import Common.AS_Annotation
import Common.ProofUtils
import Common.ProofTree

import Data.List (zip)

-- | determine the need for bottom constants
data FormulaTreatment = NoMembershipOrCast | FormulaDependent | SubsortBottoms
    deriving Show

-- | a case selector for formula treatment
treatFormula :: FormulaTreatment -> a -> a -> a -> a
treatFormula g a b c = case g of
    NoMembershipOrCast -> a
    FormulaDependent -> b
    SubsortBottoms -> c

{- | The identity of the comorphism depending on parameters.
    'NoMembershipOrCast' reject membership test or cast to non-bottom sorts.
.   'FormulaDependent' creates a formula dependent signature translation.
    'SubsortBottoms' creates bottoms for all proper subsorts. -}
data CASL2SubCFOL = CASL2SubCFOL
    { uniqueBottom :: Bool -- ^ removes free types
    , formulaTreatment :: FormulaTreatment
    -- ^ deal with membership tests and casts
    } deriving Show

{- | create unique bottoms, sorts with bottom depend on membership
and casts in theory sentences. -}
defaultCASL2SubCFOL :: CASL2SubCFOL
defaultCASL2SubCFOL = CASL2SubCFOL True FormulaDependent

instance Language CASL2SubCFOL where
    language_name (CASL2SubCFOL _ m) = "CASL2SubCFOL"
        ++ treatFormula m (show m) "" (show m)

instance Comorphism CASL2SubCFOL
               CASL CASL_Sublogics
               CASLBasicSpec CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CASLSign
               CASLMor
               Symbol RawSymbol ProofTree
               CASL CASL_Sublogics
               CASLBasicSpec CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CASLSign
               CASLMor
               Symbol RawSymbol ProofTree where
    sourceLogic (CASL2SubCFOL _ _) = CASL
    sourceSublogic (CASL2SubCFOL b _) =
        if b then SL.caslTop else SL.caslTop { cons_features = NoSortGen }
    targetLogic (CASL2SubCFOL _ _) = CASL
    mapSublogic (CASL2SubCFOL _ _) sl = Just $ if has_part sl then sl
        { has_part    = False -- partiality is coded out
        , has_pred    = True
        , which_logic = max Horn $ which_logic sl
        , has_eq      = True} else sl
    map_theory (CASL2SubCFOL b m) (sig, sens) =
        let fbsrts = Set.unions $ map (botFormulaSorts . sentence) sens
            bsrts = sortsWithBottom m sig fbsrts
            sens1 = generateAxioms b bsrts sig
            sens2 =
              map (mapNamed (simplifyFormula id . codeFormula b bsrts)) sens
        in case m of
             NoMembershipOrCast
               | not $ Set.null $ Set.difference fbsrts bsrts ->
                 fail "CASL2SubCFOL: unexpected membership test or cast"
             _ -> return
                 ( encodeSig bsrts sig
                 , nameAndDisambiguate $ sens1 ++ sens2)
    map_morphism (CASL2SubCFOL _ m) mor@Morphism{msource = src, mtarget = tar}
        = return
        mor { msource = encodeSig (sortsWithBottom m src Set.empty) src
            , mtarget = encodeSig (sortsWithBottom m tar Set.empty) tar
            , fun_map = Map.map (\ (i, _) -> (i, Total)) $ fun_map mor }
    map_sentence (CASL2SubCFOL b m) sig sen = let
        fbsrts = botFormulaSorts sen
        bsrts = sortsWithBottom m sig fbsrts
        in case m of
             NoMembershipOrCast
               | not $ Set.null $ Set.difference fbsrts bsrts ->
                 fail $ "CASL2SubCFOL: unexpected membership test or cast:\n"
                      ++ showDoc sen ""
             _ -> return $ simplifyFormula id $ codeFormula b bsrts sen
    map_symbol (CASL2SubCFOL _ _) s =
      Set.singleton s { symbType = totalizeSymbType $ symbType s }
    has_model_expansion (CASL2SubCFOL _ _) = True
    is_weakly_amalgamable (CASL2SubCFOL _ _) = True

totalizeSymbType :: SymbType -> SymbType
totalizeSymbType t = case t of
  OpAsItemType ot -> OpAsItemType ot { opKind = Total }
  _ -> t

sortsWithBottom :: FormulaTreatment -> Sign f e -> Set.Set SORT -> Set.Set SORT
sortsWithBottom m sig formBotSrts =
    let bsrts = treatFormula m Set.empty formBotSrts $  Map.keysSet $
            Rel.toMap $ sortRel sig
        ops = Map.elems $ opMap sig
        -- all supersorts inherit the same bottom element
        allSortsWithBottom s =
            Set.unions $ s : map (flip supersortsOf sig) (Set.toList s)
        resSortsOfPartialFcts =
            allSortsWithBottom $ Set.unions $ bsrts :
               map (Set.map opRes . Set.filter
                    ( \ t -> opKind t == Partial)) ops
        collect given =
            let more = allSortsWithBottom $
                       Set.unions $ map (Set.map opRes .
                                 Set.filter ( \ t -> any
                                 (flip Set.member given) $ opArgs t)) ops
            in if Set.isSubsetOf more given then given
               else collect $ Set.union more given
     in collect resSortsOfPartialFcts

defPred :: Id
defPred = genName "defined"

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
addBottomAlt c = let t = Op_type Total [] (newSort c) nullRange in c
    {opSymbs = opSymbs c ++ [(Qual_op_name (uniqueBotName t) t nullRange, [])]}

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
   botType x = OpType {opKind = Total, opArgs = [], opRes = x }
   botOpMap  = Set.fold (\ bt -> addOpTo (uniqueBotName $ toOP_TYPE bt) bt)
       newTotalMap $ Set.map botType bsorts
   defType x = PredType{predArgs=[x]}
   defTypes = Set.map defType bsorts
   newpredMap = Map.insert defPred defTypes $ predMap sig
   rel = sortRel sig
   total (s, s') = OpType {opKind = Total, opArgs = [s'], opRes = s }
   setprojOptype = Set.map total $ Set.filter ( \ (s, _) ->
       Set.member s bsorts) $ Rel.toSet rel
   projOpMap = Set.fold (\ t -> addOpTo (uniqueProjName $ toOP_TYPE t) t)
       botOpMap setprojOptype

generateAxioms :: Bool -> Set.Set SORT -> Sign f e -> [Named (FORMULA ())]
generateAxioms b bsorts sig = filter (not . is_True_atom . sentence) $
  map (mapNamed $ simplifyFormula id . rmDefs bsorts id) $
    map (mapNamed $ renameFormula id) $ concat $
    [inlineAxioms CASL
      " sort s < s'     \
      \ op pr : s'->s   \
      \ pred d:s        \
      \ forall x,y:s'. d(pr(x)) /\\ d(pr(y)) /\\ pr(x)=pr(y) => x=y \
      \ %(ga_projection_injectivity)% "
    ++ inlineAxioms CASL
     " sort s < s'      \
      \ op pr : s'->s   \
      \ pred d:s        \
      \ forall x:s . d(x) => pr(x)=x %(ga_projection)% "
      | s <- sortList, let y = mkSimpleId "y",
        s' <- minSupers s]
    ++ [inlineAxioms CASL
      " sort s          \
      \ pred d:s        \
      \ . exists x:s.d(x) %(ga_nonEmpty)%" ++
     (if b then
     inlineAxioms CASL
      " sort s          \
      \ op bottom:s     \
      \ pred d:s        \
      \ . forall x:s . not d(x) <=> x=bottom %(ga_notDefBottom)%"
      else
     inlineAxioms CASL
      " sort s          \
      \ op bottom:s     \
      \ pred d:s        \
      \ . not d(bottom) %(ga_notDefBottom)%")
        | s <- sortList ] ++
    [inlineAxioms CASL
      " sort t          \
      \ sorts s_i       \
      \ op f:s_i->t     \
      \ forall y_k:s_i . def f(y_k) <=> def y_k /\\ def y_k %(ga_totality)%"
        | (f,typ) <- opList, opKind typ == Total,
          let s=opArgs typ; t=opRes typ; y= mkVars (length s) ] ++
    [inlineAxioms CASL
      " sort t          \
      \ sorts s_i       \
      \ op f:s_i->t     \
      \ forall y_k:s_i . def f(y_k) => def y_k /\\ def y_k %(ga_strictness)%"
        | (f,typ) <- opList, opKind typ == Partial,
          let s=opArgs typ; t=opRes typ; y= mkVars (length s) ] ++
    [inlineAxioms CASL
      " sorts s_i       \
      \ pred p:s_i      \
      \ forall y_k:s_i . p(y_k) => def y_k /\\ def y_k \
      \ %(ga_predicate_strictness)%"
        | (p,typ) <- predList, let s=predArgs typ; y=mkVars (length s) ]
    where
        x = mkSimpleId "x"
        pr = projName
        minSupers so = keepMinimals sig id $ Set.toList $ Set.delete so
                           $ supersortsOf so sig
        d = defPred
        sortList = Set.toList bsorts
        opList = [(f,t) | (f,types) <- Map.toList $ opMap sig,
                  t <- Set.toList types ]
        predList = [(p,t) | (p,types) <- Map.toList $ predMap sig,
                    t <- Set.toList types ]
        mkVars n = [mkSimpleId ("x_"++show i) | i<-[1..n]]

codeRecord :: Bool -> Set.Set SORT -> (f -> f) -> Record f (FORMULA f) (TERM f)
codeRecord uniBot bsrts mf = (mapRecord mf)
    { foldQuantification = \  _ q vs qf ps ->
      case q of
      Universal ->
          Quantification q vs (Implication (defVards bsrts vs) qf True ps) ps
      _ -> Quantification q vs (Conjunction [defVards bsrts vs, qf] ps) ps
    , foldDefinedness = \ _ t ps -> defined bsrts t (sortOfTerm t) ps
    , foldExistl_equation = \ _ t1 t2 ps ->
      Conjunction[Strong_equation t1 t2 ps,
                  defined bsrts t1 (sortOfTerm t1) ps] ps
    , foldMembership = \ _ t s ps ->
          defined bsrts (projectUnique Total ps t s) s ps
    , foldSort_gen_ax = \ _ cs b -> if uniBot then
          Sort_gen_ax (map (totalizeConstraint bsrts) cs) $
              if not uniBot || Set.null (Set.intersection bsrts
                $ Set.fromList $ map newSort cs) then b else False
          else error "SubPFOL2SubFOL: unexpected Sort_gen_ax"
    , foldApplication = \ _ o args ps -> Application (totalizeOpSymb o) args ps
    , foldCast = \ _ t s ps -> projectUnique Total ps t s }

codeFormula :: Bool -> Set.Set SORT -> FORMULA () -> FORMULA ()
codeFormula b bsorts = foldFormula (codeRecord b bsorts $ error "CASL2SubCFol")

rmDefsRecord :: Set.Set SORT -> (f -> f) ->  Record f (FORMULA f) (TERM f)
rmDefsRecord  bsrts mf = (mapRecord mf)
    { foldDefinedness = \ _ t ps -> defined bsrts t (sortOfTerm t) ps }

rmDefs :: Set.Set SORT -> (f -> f) -> FORMULA f -> FORMULA f
rmDefs bsrts = foldFormula . rmDefsRecord bsrts

-- | find sorts that need a bottom in membership formulas and casts

botSorts :: (f -> Set.Set SORT) -> Record f (Set.Set SORT) (Set.Set SORT)
botSorts mf = (constRecord mf Set.unions Set.empty)
     { foldMembership = \ _ _ s _ -> Set.singleton s
     , foldCast = \ _ _ s _ -> Set.singleton s }

botFormulaSorts :: FORMULA f -> Set.Set SORT
botFormulaSorts = foldFormula (botSorts $ const Set.empty)
