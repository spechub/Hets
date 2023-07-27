{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  ./Comorphisms/CASL2SubCFOL.hs
Description :  coding out partiality
Copyright   :  (c) Zicheng Wang, C.Maeder Uni Bremen 2002-2009
License     :  GPLv2 or higher, see LICENSE.txt

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
import CASL.Fold
import CASL.Project
import CASL.Simplify

import Common.Id
import Common.DocUtils
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Common.Lib.Rel as Rel
import qualified Common.Lib.MapSet as MapSet
import Common.AS_Annotation
import Common.ProofUtils
import Common.ProofTree
import Common.Utils
import qualified Control.Monad.Fail as Fail

-- | determine the need for bottom constants
data FormulaTreatment =
    NoMembershipOrCast
  | FormulaDependent
  | SubsortBottoms
  | AllSortBottoms
    deriving Show

-- | a case selector for formula treatment
treatFormula :: FormulaTreatment -> a -> a -> a -> a -> a
treatFormula g a b c d = case g of
    NoMembershipOrCast -> a
    FormulaDependent -> b
    SubsortBottoms -> c
    AllSortBottoms -> d

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
    language_name (CASL2SubCFOL b m) = "CASL2SubCFOL"
        ++ (if b then "" else "PersistentlyLiberal")
        ++ treatFormula m (show m) "" (show m) (show m)

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
        if b then SL.caslTop else SL.caslTop
          { cons_features = SL.SortGen False False SL.OnlyTotal }
    targetLogic (CASL2SubCFOL _ _) = CASL
    mapSublogic (CASL2SubCFOL b _) sl = Just $ if has_part sl then sl
        { has_part = False -- partiality is coded out
        , cons_features = let cf = cons_features sl in case cf of
          (SL.SortGen _ _ tcf) -> cf
            { totality = if b then SL.OnlyTotal else max tcf SL.OnlyTotal }
            -- …in constructors, too
          _ -> cf
        , has_pred = True
        , which_logic = max Horn $ which_logic sl
        , has_eq = True} else sl
    map_theory (CASL2SubCFOL b m) (sig, sens) =
        let fbsrts = Set.unions $ map (botFormulaSorts . sentence) sens
            bsrts = sortsWithBottom m sig fbsrts
            sens1 = generateAxioms b bsrts sig
            sens2 =
              map (mapNamed (simplifyFormula id . codeFormula b bsrts)) sens
        in case m of
             NoMembershipOrCast
               | not $ Set.null $ Set.difference fbsrts bsrts ->
                 Fail.fail "CASL2SubCFOL: unexpected membership test or cast"
             _ -> return
                 ( encodeSig bsrts sig
                 , nameAndDisambiguate $ sens1 ++ sens2)
    map_morphism (CASL2SubCFOL _ m) mor@Morphism {msource = src, mtarget = tar}
        = return
        mor { msource = encodeSig (sortsWithBottom m src Set.empty) src
            , mtarget = encodeSig (sortsWithBottom m tar Set.empty) tar
            , op_map = Map.map (\ (i, _) -> (i, Total)) $ op_map mor }
    map_sentence (CASL2SubCFOL b m) sig sen = let
        fbsrts = botFormulaSorts sen
        bsrts = sortsWithBottom m sig fbsrts
        in case m of
             NoMembershipOrCast
               | not $ Set.null $ Set.difference fbsrts bsrts ->
                 Fail.fail $ "CASL2SubCFOL: unexpected membership test or cast:\n"
                      ++ showDoc sen ""
             _ -> return $ simplifyFormula id $ codeFormula b bsrts sen
    map_symbol (CASL2SubCFOL _ _) _ s =
      Set.singleton s { symbType = totalizeSymbType $ symbType s }
    has_model_expansion (CASL2SubCFOL _ _) = True
    is_weakly_amalgamable (CASL2SubCFOL _ _) = True

totalizeSymbType :: SymbType -> SymbType
totalizeSymbType t = case t of
  OpAsItemType ot -> OpAsItemType $ mkTotal ot
  _ -> t

sortsWithBottom :: FormulaTreatment -> Sign f e -> Set.Set SORT -> Set.Set SORT
sortsWithBottom m sig formBotSrts =
    let bsrts = treatFormula m Set.empty formBotSrts
          (Rel.keysSet . Rel.rmNullSets $ sortRel sig) (sortSet sig)
        ops = MapSet.elems $ opMap sig
        -- all supersorts inherit the same bottom element
        allSortsWithBottom s =
            Set.unions $ s : map (`supersortsOf` sig) (Set.toList s)
        resSortsOfPartialFcts =
            allSortsWithBottom . Set.union bsrts
               . Set.map opRes $ Set.filter isPartial ops
        collect given =
            let more = allSortsWithBottom . Set.map opRes $ Set.filter
                      (any (`Set.member` given) . opArgs) ops
            in if Set.isSubsetOf more given then given
               else collect $ Set.union more given
     in collect resSortsOfPartialFcts

defPred :: Id
defPred = genName "defined"

defined :: TermExtension f => Set.Set SORT -> TERM f -> Range -> FORMULA f
defined bsorts t ps = let s = sortOfTerm t in
  if Set.member s bsorts then Predication
         (Qual_pred_name defPred (Pred_type [s] nullRange) nullRange) [t] ps
  else Atom True ps

defVards :: TermExtension f => Set.Set SORT -> [VAR_DECL] -> FORMULA f
defVards bs = conjunct . concatMap (defVars bs)

defVars :: TermExtension f => Set.Set SORT -> VAR_DECL -> [FORMULA f]
defVars bs (Var_decl vns s _) = map (defVar bs s) vns

defVar :: TermExtension f => Set.Set SORT -> SORT -> Token -> FORMULA f
defVar bs s v = defined bs (Qual_var v s nullRange) nullRange

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

botType :: SORT -> OpType
botType = sortToOpType

-- | Add projections to the signature
encodeSig :: Set.Set SORT -> Sign f e -> Sign f e
encodeSig bsorts sig = if Set.null bsorts then sig else
    sig { opMap = projOpMap, predMap = newpredMap } where
   newTotalMap = MapSet.map mkTotal $ opMap sig
   botOpMap = Set.fold (\ bt -> addOpTo (uniqueBotName $ toOP_TYPE bt) bt)
       newTotalMap $ Set.map botType bsorts
   defType x = PredType {predArgs = [x]}
   defTypes = Set.map defType bsorts
   newpredMap = MapSet.update (const defTypes) defPred $ predMap sig
   rel = sortRel sig
   total (s, s') = mkTotOpType [s'] s
   setprojOptype = Set.map total $ Set.filter ( \ (s, _) ->
       Set.member s bsorts) $ Rel.toSet rel
   projOpMap = Set.fold (\ t -> addOpTo (uniqueProjName $ toOP_TYPE t) t)
       botOpMap setprojOptype

-- | Make the name for the non empty axiom from s to s' to s''
mkNonEmptyAxiomName :: SORT -> String
mkNonEmptyAxiomName = mkAxNameSingle "nonEmpty"

-- | Make the name for the not defined bottom axiom
mkNotDefBotAxiomName :: SORT -> String
mkNotDefBotAxiomName = mkAxNameSingle "notDefBottom"

-- | Make the name for the totality axiom
mkTotalityAxiomName :: OP_NAME -> String
mkTotalityAxiomName f = "ga_strictness_" ++ show f

generateAxioms :: (Ord f, TermExtension f) =>
  Bool -> Set.Set SORT -> Sign f e -> [Named (FORMULA f)]
generateAxioms uniqBot bsorts sig = concatMap (\ s -> let
      vx = mkVarDeclStr "x" s
      xt = toQualVar vx
      hasBot = Set.member s bsorts
      prj z = projectUnique Total nullRange z s
      df z = defined bsorts z nullRange
      in concatMap (\ s' ->
      [makeNamed (mkAxName "total_projection_injectivity" s' s)
      $ let xv = mkVarDeclStr "x" s'
            yv = mkVarDeclStr "y" s'
            tx = toQualVar xv
            ty = toQualVar yv
            px = prj tx
            py = prj ty
            epxy = mkStEq px py
      -- forall x,y:s' . d(pr(x)) /\\ d(pr(y)) /\\ pr(x)=pr(y) => x=y
        in mkForall [xv, yv]
           $ mkImpl (if hasBot then conjunct [df px, df py, epxy]
                    else epxy) $ mkStEq tx ty
            -- forall x:s . d(x) => pr(x)=x
      , makeNamed (mkAxName "total_projection" s' s)
      $ let eq = mkStEq (prj $ Sorted_term xt s' nullRange) xt
        in mkForall [vx]
               $ if hasBot then mkImpl (df xt) eq else eq]) (minSupers s)
         -- exists x:s . d(x)
      ++ [makeNamed (mkNonEmptyAxiomName s)
         $ Quantification Existential [vx] (df xt) nullRange
         | hasBot]
      ++ [makeNamed (mkNotDefBotAxiomName s)
         $ let bty = toOP_TYPE $ botType s
               bt = mkAppl (mkQualOp (uniqueBotName bty) bty) []
           in if uniqBot then
              -- forall x:s . not d(x) <=> x=bottom
              mkForall [vx]
              $ mkEqv (mkNeg $ df xt) $ mkStEq xt bt
              else mkNeg $ df bt -- not d(bottom)
         | hasBot]) sortList
   ++ filter (not . is_True_atom . sentence)
   (map (mapNamed $ simplifyFormula id)
    $ map (\ (f, typ) ->
      let vs = map (\ (s, i) -> mkVarDeclStr ("x_" ++ show i) s)
              $ number $ opArgs typ
      in makeNamed (mkTotalityAxiomName f)
      -- forall x_i:s_i . d f(x_1, ..., x_n) {<}=> d x_1 /\\ ... /\\ d x_n
         $ mkForall vs
           $ (if isTotal typ then mkEqv else mkImpl)
            (defined bsorts
             (mkAppl (mkQualOp f $ toOP_TYPE $ mkTotal typ)
                      $ map toQualVar vs) nullRange)
            $ defVards bsorts vs) opList
    ++ map (\ (p, typ) ->
      let vs = map (\ (s, i) -> mkVarDeclStr ("x_" ++ show i) s)
              $ number $ predArgs typ
      in makeNamed ("ga_predicate_strictness_" ++ show p)
      -- forall x_i:s_i . p(x_1, ..., x_n) => d x_1 /\\ ... /\\ d x_n
         $ mkForall vs
           $ mkImpl
            (Predication (Qual_pred_name p (toPRED_TYPE typ) nullRange)
                      (map toQualVar vs) nullRange)
            $ defVards bsorts vs) predList)
    where
        rel1 = Rel.transClosure $ sortRel sig
        sccs = Rel.sccOfClosure rel1
        rel2 = Rel.transReduce $ Rel.collaps sccs rel1
        isos so = Set.insert so $ Set.unions $ filter (Set.member so) sccs
        minSupers so = Set.toList $ Set.delete so $ Set.union (isos so)
          $ Set.unions $ map isos $ Set.toList $ Rel.succs rel2 so
        sortList = Set.toList bsorts
        opList = mapSetToList $ opMap sig
        predList = mapSetToList $ predMap sig

codeRecord :: TermExtension f => Bool -> Set.Set SORT -> (f -> f)
  -> Record f (FORMULA f) (TERM f)
codeRecord uniBot bsrts mf = (mapRecord mf)
    { foldQuantification = \ _ q vs qf ps ->
      case q of
      Universal -> Quantification q vs
        (Relation (defVards bsrts vs) Implication qf ps) ps
      _ -> Quantification q vs (Junction Con [defVards bsrts vs, qf] ps) ps
    , foldDefinedness = const $ defined bsrts
    , foldEquation = \ _ t1 e t2 ps -> if e == Existl then
      Junction Con [Equation t1 Strong t2 ps,
                  defined bsrts t1 ps] ps else Equation t1 e t2 ps
    , foldMembership = \ _ t s ps ->
          defined bsrts (projectUnique Total ps t s) ps
    , foldSort_gen_ax = \ _ cs b ->
          mkSort_gen_ax (map (totalizeConstraint bsrts) cs)
              $ b && (not uniBot || Set.null (Set.intersection bsrts
                $ Set.fromList $ map newSort cs))
    , foldApplication = const $ Application . totalizeOpSymb
    , foldCast = \ _ t s ps -> projectUnique Total ps t s }

codeFormula :: Bool -> Set.Set SORT -> FORMULA () -> FORMULA ()
codeFormula b bsorts = foldFormula (codeRecord b bsorts $ error "CASL2SubCFol")

codeTerm :: Bool -> Set.Set SORT -> TERM () -> TERM ()
codeTerm b bsorts = foldTerm (codeRecord b bsorts $ error "CASL2SubCFol")

-- | find sorts that need a bottom in membership formulas and casts

botSorts :: (f -> Set.Set SORT) -> Record f (Set.Set SORT) (Set.Set SORT)
botSorts mf = (constRecord mf Set.unions Set.empty)
     { foldMembership = \ _ _ s _ -> Set.singleton s
     , foldCast = \ _ _ s _ -> Set.singleton s }

botFormulaSorts :: FORMULA f -> Set.Set SORT
botFormulaSorts = foldFormula (botSorts $ const Set.empty)

botTermSorts :: TERM f -> Set.Set SORT
botTermSorts = foldTerm (botSorts $ const Set.empty)
