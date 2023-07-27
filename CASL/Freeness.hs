{- |
Module      :  ./CASL/Freeness.hs
Description :  Computation of the constraints needed for free definition links.
Copyright   :  (c) Adrian Riesco, Facultad de Informatica UCM 2009
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  ariesco@fdi.ucm.es
Stability   :  experimental
Portability :  portable

Computation of the constraints needed for free definition links.
-}

module CASL.Freeness (quotientTermAlgebra) where

import CASL.Sign
import CASL.Morphism
import CASL.StaticAna

import CASL.AS_Basic_CASL

import Logic.Prover ()

import Common.Id
import Common.Result
import Common.AS_Annotation
import qualified Common.Lib.Rel as Rel
import qualified Common.Lib.MapSet as MapSet

import Data.Char
import Data.Maybe
import Data.List (groupBy, elemIndex)
import qualified Data.Map as Map
import qualified Data.Set as Set

-- | main function, in charge of computing the quotient term algebra
quotientTermAlgebra :: CASLMor -- sigma : Sigma -> SigmaM
                    -> [Named CASLFORMULA] -- Th(M)
                    -> Result (CASLSign, {- SigmaK
                               CASLMor, -- iota : SigmaM' -> SigmaK -}
                               [Named CASLFORMULA] -- Ax(K)
                              )
quotientTermAlgebra sigma sens =
                  let
                    sigma_0 = msource sigma
                    ss_0 = sortSet sigma_0
                    sigma_m = mtarget sigma
                    sigma_k = create_sigma_k ss_0 sigma_m
                    axs = create_axs ss_0 sigma_m sigma_k sens
                  in return (sigma_k, axs)

-- | generates the axioms of the module K
create_axs :: Set.Set SORT -> CASLSign -> CASLSign -> [Named CASLFORMULA]
              -> [Named CASLFORMULA]
create_axs sg_ss sg_m sg_k sens = forms
      where ss_m = sortSet sg_m
            ss = Set.map mkFreeName $ Set.difference ss_m sg_ss
            sr = sortRel sg_k
            comps = ops2comp $ opMap sg_k
            ss' = filterNoCtorSorts (opMap sg_k) ss
            ctor_sen = freeCons (ss', sr, comps)
            make_axs = make_forms sg_ss ++ make_hom_forms sg_ss
            h_axs_ops = homomorphism_axs_ops $ opMap sg_m
            h_axs_preds = homomorphism_axs_preds $ predMap sg_m
            h_axs_surj = hom_surjectivity $ sortSet sg_m
            q_axs = quotient_axs sens
            symm_ax = symmetry_axs ss_m
            tran_ax = transitivity_axs ss_m
            cong_ax = congruence_axs (opMap sg_m)
            satThM = sat_thm_ax sens
            prems = conjunct [symm_ax, tran_ax, cong_ax, satThM]
            ltkh = larger_than_ker_h ss_m (predMap sg_m)
            krnl_axs = [mkKernelAx ss_m (predMap sg_m) prems ltkh]
            forms = concat [ctor_sen, make_axs, h_axs_ops, h_axs_preds,
                            h_axs_surj, q_axs, krnl_axs]

filterNoCtorSorts :: OpMap -> Set.Set SORT -> Set.Set SORT
filterNoCtorSorts om = Set.filter (filterNoCtorSort om)

filterNoCtorSort :: OpMap -> SORT -> Bool
filterNoCtorSort om s = any (resultTypeSet s) . Map.elems $ MapSet.toMap om

resultTypeSet :: SORT -> Set.Set OpType -> Bool
resultTypeSet s = any (resultType s) . Set.toList

resultType :: SORT -> OpType -> Bool
resultType s = (s ==) . opRes

{- | generates formulas of the form make(h(x)) =e= x,
for any x of sort gn_free_s -}
make_hom_forms :: Set.Set SORT -> [Named CASLFORMULA]
make_hom_forms = Set.fold ((:) . make_hom_form) []

{- | generates a formula of the form make(h(x)) =e= x,
for gn_free_s given the SORT s -}
make_hom_form :: SORT -> Named CASLFORMULA
make_hom_form s = makeNamed ("ga_make_hom_" ++ show s) q_eq
      where free_s = mkFreeName s
            v = newVar free_s
            ot_hom = Op_type Partial [free_s] s nullRange
            os_hom = mkQualOp homId ot_hom
            term_hom = mkAppl os_hom [v]
            ot_mk = Op_type Total [s] free_s nullRange
            os_mk = mkQualOp makeId ot_mk
            term_mk = mkAppl os_mk [term_hom]
            eq = mkExEq term_mk v
            q_eq = quantifyUniversally eq

-- | generates the formulas relating the make functions with the homomorphism
make_forms :: Set.Set SORT -> [Named CASLFORMULA]
make_forms = Set.fold ((:) . make_form) []

{- | generates the formulas relating the make function for this sort
with the homomorphism -}
make_form :: SORT -> Named CASLFORMULA
make_form s = makeNamed ("ga_hom_make_" ++ show s) q_eq
      where free_s = mkFreeName s
            v = newVar s
            ot_mk = Op_type Total [s] free_s nullRange
            os_mk = mkQualOp makeId ot_mk
            term_mk = mkAppl os_mk [v]
            ot_hom = Op_type Partial [free_s] s nullRange
            os_hom = mkQualOp homId ot_hom
            term_hom = mkAppl os_hom [term_mk]
            eq = mkStEq term_hom v
            q_eq = quantifyUniversally eq

-- | computes the last part of the axioms to assert the kernel of h
larger_than_ker_h :: Set.Set SORT -> PredMap -> CASLFORMULA
larger_than_ker_h ss mis = conj
     where ltkhs = ltkh_sorts ss
           ltkhp = ltkh_preds mis
           conj = conjunct (ltkhs ++ ltkhp)

{- | computes the second part of the conjunction of the formula "largerThanKerH"
from the kernel of H -}
ltkh_preds :: PredMap -> [CASLFORMULA]
ltkh_preds = MapSet.foldWithKey (\ name -> (:) . ltkh_preds_aux name) []

{- | computes the second part of the conjunction of the formula "largerThanKerH"
from the kernel of H for a concrete predicate profile -}
ltkh_preds_aux :: Id -> PredType -> CASLFORMULA
ltkh_preds_aux name (PredType args) = imp'
     where free_name = mkFreeName name
           free_args = map mkFreeName args
           psi = psiName name
           pt = Pred_type free_args nullRange
           ps_name = mkQualPred free_name pt
           ps_psi = mkQualPred psi pt
           vars = createVars 1 free_args
           prem = mkPredication ps_name vars
           concl = mkPredication ps_psi vars
           imp = mkImpl prem concl
           imp' = quantifyUniversally imp

{- | computes the first part of the conjunction of the formula "largerThanKerH"
from the kernel of H -}
ltkh_sorts :: Set.Set SORT -> [CASLFORMULA]
ltkh_sorts = Set.fold ((:) . ltkh_sort) []

{- | computes the first part of the conjunction of the formula "largerThanKerH"
from the kernel of H for a concrete sort -}
ltkh_sort :: SORT -> CASLFORMULA
ltkh_sort s = imp'
     where free_s = mkFreeName s
           v1 = newVarIndex 1 free_s
           v2 = newVarIndex 2 free_s
           phi = phiName s
           pt = Pred_type [free_s, free_s] nullRange
           ps = mkQualPred phi pt
           ot_hom = Op_type Partial [free_s] s nullRange
           name_hom = mkQualOp homId ot_hom
           t1 = mkAppl name_hom [v1]
           t2 = mkAppl name_hom [v2]
           prem = mkExEq t1 t2
           concl = mkPredication ps [v1, v2]
           imp = mkImpl prem concl
           imp' = quantifyUniversally imp

-- | generates the axioms for satThM
sat_thm_ax :: [Named CASLFORMULA] -> CASLFORMULA
sat_thm_ax forms = final_form
     where forms' = map (free_formula . sentence)
             $ filter (no_gen . sentence) forms
           final_form = conjunct forms'

-- | checks if the formula is a sort generation constraint
no_gen :: CASLFORMULA -> Bool
no_gen (Sort_gen_ax _ _) = False
no_gen _ = True

-- | computes the axiom for the congruence of the kernel of h
congruence_axs :: OpMap -> CASLFORMULA
congruence_axs om = conj
     where axs = MapSet.foldWithKey (\ name -> (:) . congruence_ax_aux name)
                 [] om
           conj = conjunct axs

{- | computes the axiom for the congruence of the kernel of h
for a single type of an operator id -}
congruence_ax_aux :: Id -> OpType -> CASLFORMULA
congruence_ax_aux name ot = cong_form'
     where OpType _ args res = ot
           free_name = mkFreeName name
           free_args = map mkFreeName args
           free_res = mkFreeName res
           free_ot = Op_type Total free_args free_res nullRange
           free_os = mkQualOp free_name free_ot
           lgth = length free_args
           xs = createVars 1 free_args
           ys = createVars (1 + lgth) free_args
           fst_term = mkAppl free_os xs
           snd_term = mkAppl free_os ys
           phi = phiName res
           pt = Pred_type [free_res, free_res] nullRange
           ps = mkQualPred phi pt
           fst_form = mkPredication ps [fst_term, fst_term]
           snd_form = mkPredication ps [snd_term, snd_term]
           vars_forms = congruence_ax_vars args xs ys
           conj = conjunct $ fst_form : snd_form : vars_forms
           concl = mkPredication ps [fst_term, snd_term]
           cong_form = mkImpl conj concl
           cong_form' = quantifyUniversally cong_form


freePredNameAndType :: SORT -> (Id, PRED_TYPE)
freePredNameAndType s = let
    phi = phiName s
    free_s = mkFreeName s
    pt = Pred_type [free_s, free_s] nullRange
    in (phi, pt)

freePredSymb :: SORT -> PRED_SYMB
freePredSymb = uncurry mkQualPred . freePredNameAndType

-- | computes the formulas for the relations between variables
congruence_ax_vars :: [SORT] -> [CASLTERM] -> [CASLTERM] -> [CASLFORMULA]
congruence_ax_vars (s : ss) (x : xs) (y : ys) = form : forms
     where
           form = mkPredication (freePredSymb s) [x, y]
           forms = congruence_ax_vars ss xs ys
congruence_ax_vars _ _ _ = []

-- | computes the transitivity axioms for the kernel of h
transitivity_axs :: Set.Set SORT -> CASLFORMULA
transitivity_axs ss = conj
     where axs = Set.fold ((:) . transitivity_ax) [] ss
           conj = conjunct axs

twoFreeVars :: SORT -> (SORT, TERM (), TERM (), VAR, VAR, PRED_SYMB, FORMULA ())
twoFreeVars s = let
   free_sort = mkFreeName s
   v1@(Qual_var n1 _ _) = newVarIndex 1 free_sort
   v2@(Qual_var n2 _ _) = newVarIndex 2 free_sort
   ps = freePredSymb s
   fst_form = mkPredication ps [v1, v2]
   in (free_sort, v1, v2, n1, n2, ps, fst_form)

{- | computes the transitivity axiom of a concrete sort for
the kernel of h -}
transitivity_ax :: SORT -> CASLFORMULA
transitivity_ax s = quant
     where (free_sort, v1, v2, n1, n2, ps, fst_form) = twoFreeVars s
           v3@(Qual_var n3 _ _) = newVarIndex 3 free_sort
           snd_form = mkPredication ps [v2, v3]
           thr_form = mkPredication ps [v1, v3]
           conj = conjunct [fst_form, snd_form]
           imp = mkImpl conj thr_form
           vd = [Var_decl [n1, n2, n3] free_sort nullRange]
           quant = mkForall vd imp

-- | computes the symmetry axioms for the kernel of h
symmetry_axs :: Set.Set SORT -> CASLFORMULA
symmetry_axs ss = conj
     where axs = Set.fold ((:) . symmetry_ax) [] ss
           conj = conjunct axs

-- | computes the symmetry axiom of a concrete sort for the kernel of h
symmetry_ax :: SORT -> CASLFORMULA
symmetry_ax s = quant
     where (free_sort, v1, v2, n1, n2, ps, lhs) = twoFreeVars s
           rhs = mkPredication ps [v2, v1]
           inner_form = mkImpl lhs rhs
           vd = [Var_decl [n1, n2] free_sort nullRange]
           quant = mkForall vd inner_form

-- | generates the name of the phi variable of a concrete sort
phiName :: SORT -> Id
phiName s = mkId [mkSimpleId $ "Phi_" ++ show s]

-- | generates the name of the phi variable of a concrete predicate
psiName :: Id -> Id
psiName s = mkId [mkSimpleId $ "Psi_" ++ show s]

{- | creates the axiom for the kernel of h given the sorts and the predicates
in M, the premises and the conclusion -}
mkKernelAx :: Set.Set SORT -> PredMap -> CASLFORMULA
              -> CASLFORMULA -> Named CASLFORMULA
mkKernelAx ss preds prem conc = makeNamed "freeness_kernel" q2
     where imp = mkImpl prem conc
           q1 = quantifyPredsSorts ss imp
           q2 = quantifyPredsPreds preds q1

{- | applies the second order quantification to the formula for the given
set of sorts -}
quantifyPredsSorts :: Set.Set SORT -> CASLFORMULA -> CASLFORMULA
quantifyPredsSorts ss f = Set.fold quantifyPredsSort f ss

{- | applies the second order quantification to the formula for the given
sort -}
quantifyPredsSort :: SORT -> CASLFORMULA -> CASLFORMULA
quantifyPredsSort = uncurry QuantPred . freePredNameAndType

{- | applies the second order quantification to the formula for the given
predicates -}
quantifyPredsPreds :: PredMap -> CASLFORMULA -> CASLFORMULA
quantifyPredsPreds = flip $ MapSet.foldWithKey quantifyPredsPred

{- | applies the second order quantification to the formula for the given
predicate -}
quantifyPredsPred :: Id -> PredType -> CASLFORMULA -> CASLFORMULA
quantifyPredsPred name (PredType args) f = q_form
     where psi = psiName name
           free_args = map mkFreeName args
           pt = Pred_type free_args nullRange
           q_form = QuantPred psi pt f

{- | given the axioms in the module M, the function computes the
axioms obtained for the homomorphisms -}
quotient_axs :: [Named CASLFORMULA] -> [Named CASLFORMULA]
quotient_axs = map quotient_ax

{- | given an axiom in the module M, the function computes the
axioms obtained for the homomorphisms -}
quotient_ax :: Named CASLFORMULA -> Named CASLFORMULA
quotient_ax nsen = nsen'
      where sen = sentence nsen
            sen' = homomorphy_form sen
            nsen' = nsen { sentence = sen' }

-- | applies the homomorphism operator to the terms of the given formula
homomorphy_form :: CASLFORMULA -> CASLFORMULA
homomorphy_form (Quantification q _ f r) = Quantification q var_decl f' r
     where f' = homomorphy_form f
           vars = getVars f'
           var_decl = listVarDecl vars
homomorphy_form (Junction j fs r) = Junction j fs' r
     where fs' = map homomorphy_form fs
homomorphy_form (Relation f1 c f2 r) = Relation f1' c f2' r
     where f1' = homomorphy_form f1
           f2' = homomorphy_form f2
homomorphy_form (Negation f r) = Negation f' r
     where f' = homomorphy_form f
homomorphy_form (Predication ps ts r) = Predication ps ts' r
     where ts' = map homomorphy_term ts
homomorphy_form (Definedness t r) = Definedness t' r
     where t' = homomorphy_term t
homomorphy_form (Equation t1 e t2 r) = Equation t1' e t2' r
     where t1' = homomorphy_term t1
           t2' = homomorphy_term t2
homomorphy_form (Membership t s r) = Membership t' s r
     where t' = homomorphy_term t
homomorphy_form (Mixfix_formula t) = Mixfix_formula t'
     where t' = homomorphy_term t
homomorphy_form f = f

-- | applies the homomorphism operator to the term when possible
homomorphy_term :: CASLTERM -> CASLTERM
homomorphy_term (Qual_var v s r) = t
      where free_s = mkFreeName s
            v' = Qual_var v free_s r
            ot_hom = Op_type Partial [free_s] s nullRange
            name_hom = mkQualOp homId ot_hom
            t = mkAppl name_hom [v']
homomorphy_term (Application os ts r) = t'
      where ts' = map free_term ts
            Qual_op_name op_name ot op_r = os
            Op_type _ ar co ot_r = ot
            op_name' = mkFreeName op_name
            ar' = map mkFreeName ar
            co' = mkFreeName co
            ot' = Op_type Total ar' co' ot_r
            os' = Qual_op_name op_name' ot' op_r
            t = Application os' ts' r
            ot_hom = Op_type Partial [co'] co nullRange
            name_hom = mkQualOp homId ot_hom
            t' = mkAppl name_hom [t]
homomorphy_term t = t

hom_surjectivity :: Set.Set SORT -> [Named CASLFORMULA]
hom_surjectivity = Set.fold f []
      where f x = (sort_surj x :)

-- | generates the formula to state the homomorphism is surjective
sort_surj :: SORT -> Named CASLFORMULA
sort_surj s = form'
      where v1 = newVarIndex 0 $ mkFreeName s
            id_v1 = mkSimpleId "V0"
            vd1 = mkVarDecl id_v1 (mkFreeName s)
            v2 = newVarIndex 1 s
            id_v2 = mkSimpleId "V1"
            vd2 = mkVarDecl id_v2 s
            ot_hom = Op_type Partial [mkFreeName s] s nullRange
            name_hom = mkQualOp homId ot_hom
            lhs = mkAppl name_hom [v1]
            inner_form = mkExEq lhs v2
            inner_form' = mkExist [vd1] inner_form
            form = mkForall [vd2] inner_form'
            form' = makeNamed ("ga_hom_surj_" ++ show s) form

-- | generates the axioms for the homomorphisms applied to the predicates
homomorphism_axs_preds :: PredMap -> [Named CASLFORMULA]
homomorphism_axs_preds =
  MapSet.foldWithKey (\ p_name -> (:) . homomorphism_form_pred p_name) []

-- | generates the axioms for the homomorphisms applied to a predicate
homomorphism_form_pred :: Id -> PredType -> Named CASLFORMULA
homomorphism_form_pred name (PredType args) = named_form
      where free_args = map mkFreeName args
            vars_lhs = createVars 0 free_args
            lhs_pt = Pred_type free_args nullRange
            lhs_pred_name = mkQualPred (mkFreeName name) lhs_pt
            lhs = mkPredication lhs_pred_name vars_lhs
            inner_rhs = apply_hom_vars args vars_lhs
            pt_rhs = Pred_type args nullRange
            name_rhs = mkQualPred name pt_rhs
            rhs = mkPredication name_rhs inner_rhs
            form = mkEqv lhs rhs
            form' = quantifyUniversally form
            named_form = makeNamed "" form'

-- | generates the axioms for the homomorphisms applied to the operators
homomorphism_axs_ops :: OpMap -> [Named CASLFORMULA]
homomorphism_axs_ops =
  MapSet.foldWithKey (\ op_name -> (:) . homomorphism_form_op op_name) []

-- | generates the axiom for the homomorphism applied to a concrete op
homomorphism_form_op :: Id -> OpType -> Named CASLFORMULA
homomorphism_form_op name (OpType _ args res) = named_form
      where free_args = map mkFreeName args
            vars_lhs = createVars 0 free_args
            ot_lhs = Op_type Total free_args (mkFreeName res) nullRange
            ot_hom = Op_type Partial [mkFreeName res] res nullRange
            name_hom = mkQualOp homId ot_hom
            name_lhs = mkQualOp (mkFreeName name) ot_lhs
            inner_lhs = mkAppl name_lhs vars_lhs
            lhs = mkAppl name_hom [inner_lhs]
            ot_rhs = Op_type Total args res nullRange
            name_rhs = mkQualOp name ot_rhs
            inner_rhs = apply_hom_vars args vars_lhs
            rhs = mkAppl name_rhs inner_rhs
            form = mkStEq lhs rhs
            form' = quantifyUniversally form
            named_form = makeNamed "" form'

-- | generates the variables for the homomorphisms
apply_hom_vars :: [SORT] -> [CASLTERM] -> [CASLTERM]
apply_hom_vars (s : ss) (t : ts) = t' : ts'
      where ot_hom = Op_type Partial [mkFreeName s] s nullRange
            name_hom = mkQualOp homId ot_hom
            t' = mkAppl name_hom [t]
            ts' = apply_hom_vars ss ts
apply_hom_vars _ _ = []

-- | generates a list of differents variables of the given sorts
createVars :: Int -> [SORT] -> [CASLTERM]
createVars _ [] = []
createVars i (s : ss) = var : ts
      where var = newVarIndex i s
            ts = createVars (i + 1) ss

-- | computes the set of components from the map of operators
ops2comp :: OpMap -> Set.Set Component
ops2comp = MapSet.foldWithKey (\ n -> Set.insert . Component n) Set.empty

-- | computes the sentence for the constructors
freeCons :: GenAx -> [Named CASLFORMULA]
freeCons (sorts, rel, ops) =
    let sortList = Set.toList sorts
        opSyms = map ( \ c -> let iden = compId c in Qual_op_name iden
                      (toOP_TYPE $ compType c) $ posOfId iden) $ Set.toList ops
        injSyms = map ( \ (s, t) -> let p = posOfId s in
                        Qual_op_name (mkUniqueInjName s t)
                         (Op_type Total [s] t p) p)
                  $ Rel.toList $ Rel.irreflex rel
        allSyms = opSyms ++ injSyms
        resType _ (Op_name _) = False
        resType s (Qual_op_name _ t _) = res_OP_TYPE t == s
        getIndex s = fromMaybe (-1) $ elemIndex s sortList
        addIndices (Op_name _) =
          error "CASL/StaticAna: Internal error in function addIndices"
        addIndices os@(Qual_op_name _ t _) =
            (os, map getIndex $ args_OP_TYPE t)
        collectOps s =
          Constraint s (map addIndices $ filter (resType s) allSyms) s
        constrs = map collectOps sortList
        f = mkSort_gen_ax constrs True
 -- added by me:
        nonSub (Qual_op_name n _ _) = not $ isInjName n
        nonSub _ = error "use qualified names"
        consSymbs = map (filter nonSub . map fst . opSymbs) constrs
        toTuple (Qual_op_name n ot@(Op_type _ args _ _) _) =
                  (n, toOpType ot, map Sort args)
        toTuple _ = error "use qualified names"
        consSymbs' = map (map toTuple) consSymbs
        sortSymbs = map (filter (not . nonSub) . map fst . opSymbs) constrs
        getSubsorts (Qual_op_name _ (Op_type _ [ss] _ _) _) = ss
        getSubsorts _ = error "error in injSyms"
        sortSymbs' = map (\ l ->
                       case l of
                        Qual_op_name _ (Op_type _ _ rs _) _ : _ ->
                          (rs, map getSubsorts l)
                        _ -> error "empty list filtered")
                     $ filter (not . null) sortSymbs
        sortAx = concatMap (uncurry makeDisjSubsorts) sortSymbs'
        freeAx = concatMap (\ l -> makeDisjoint l ++
                              map makeInjective (
                                  filter (\ (_, _, x) -> not $ null x) l))
                   consSymbs'
        sameSort (Constraint s _ _) (Constraint s' _ _) = s == s'
        disjToSortAx = concatMap (\ ctors -> let
                         cs = map (map fst . opSymbs) ctors
                         cSymbs = concatMap (map toTuple
                                             . filter nonSub) cs
                         sSymbs = concatMap (map getSubsorts
                                      . filter (not . nonSub)) cs
                         in
                         concatMap (\ c -> map (makeDisjToSort c) sSymbs)
                                   cSymbs) $ groupBy sameSort constrs
    in case constrs of
     [] -> []
     _ -> [toSortGenNamed f sortList]
           ++ freeAx ++ sortAx ++ disjToSortAx

-- | given the signature in M the function computes the signature K
create_sigma_k :: Set.Set SORT -> CASLSign -> CASLSign
create_sigma_k ss sg_m = usg'
      where iota_sg = totalSignCopy sg_m
            usg = addSig const sg_m iota_sg
            om' = homomorphism_ops (sortSet sg_m) (opMap usg)
            om'' = make_ops ss om'
            usg' = usg { opMap = om'' }

{- | adds the make functions for the sorts in the initial module to the
operator map -}
make_ops :: Set.Set SORT -> OpMap -> OpMap
make_ops ss om = Set.fold make_op om ss

-- | adds the make functions for the sort to the operator map
make_op :: SORT -> OpMap -> OpMap
make_op s = MapSet.insert makeId $ mkTotOpType [s] $ mkFreeName s

-- | identifier of the make function
makeId :: Id
makeId = mkId [mkSimpleId "make"]

-- | identifier of the homomorphism function
homId :: Id
homId = mkId [mkSimpleId "hom"]

-- | creates the homomorphism operators and adds it to the given operator map
homomorphism_ops :: Set.Set SORT -> OpMap -> OpMap
homomorphism_ops ss om = Set.fold f om ss
    where ot sort = OpType Partial [mkFreeName sort] sort
          f = MapSet.insert homId . ot

-- | applies the iota renaming to a signature
totalSignCopy :: CASLSign -> CASLSign
totalSignCopy sg = sg {
                    emptySortSet = ess,
                    sortRel = sr,
                    opMap = om,
                    assocOps = aom,
                    predMap = pm,
                    varMap = vm,
                    sentences = [],
                    declaredSymbols = sms,
                    annoMap = am
                      }
     where ess = iota_sort_set $ emptySortSet sg
           sr = iota_sort_rel $ sortRel sg
           om = iota_op_map $ opMap sg
           aom = iota_op_map $ assocOps sg
           pm = iota_pred_map $ predMap sg
           vm = iota_var_map $ varMap sg
           sms = iota_syms $ declaredSymbols sg
           am = iota_anno_map $ annoMap sg

-- | applies the iota renaming to a set of sorts
iota_sort_set :: Set.Set SORT -> Set.Set SORT
iota_sort_set = Set.map mkFreeName

-- | applies the iota renaming to a sort relation
iota_sort_rel :: Rel.Rel SORT -> Rel.Rel SORT
iota_sort_rel = Rel.map mkFreeName

-- | applies the iota renaming to an operator map
iota_op_map :: OpMap -> OpMap
iota_op_map = MapSet.foldWithKey
  (\ op (OpType _ args res) -> MapSet.insert (mkFreeName op)
       $ mkTotOpType (map mkFreeName args) (mkFreeName res)) MapSet.empty

-- | applies the iota renaming to a predicate map
iota_pred_map :: PredMap -> PredMap
iota_pred_map = MapSet.foldWithKey
  (\ p (PredType args) -> MapSet.insert (mkFreeName p)
       $ PredType $ map mkFreeName args) MapSet.empty

-- | applies the iota renaming to a variable map
iota_var_map :: Map.Map SIMPLE_ID SORT -> Map.Map SIMPLE_ID SORT
iota_var_map = Map.map mkFreeName

-- | applies the iota renaming to symbols
iota_syms :: Set.Set Symbol -> Set.Set Symbol
iota_syms = Set.map iota_symbol

-- | applies the iota renaming to a symbol
iota_symbol :: Symbol -> Symbol
iota_symbol (Symbol name ty) = Symbol (mkFreeName name) $ case ty of
  SortAsItemType -> SortAsItemType
  SubsortAsItemType s -> SubsortAsItemType $ mkFreeName s
  OpAsItemType (OpType _ args res) -> OpAsItemType
    $ mkTotOpType (map mkFreeName args) (mkFreeName res)
  PredAsItemType (PredType args) -> PredAsItemType
    $ PredType $ map mkFreeName args

-- | applies the iota renaming to the annotations
iota_anno_map :: MapSet.MapSet Symbol Annotation
  -> MapSet.MapSet Symbol Annotation
iota_anno_map = MapSet.fromMap . Map.mapKeys iota_symbol . MapSet.toMap

-- Some auxiliary functions

-- | create a new name for the iota morphism
mkFreeName :: Id -> Id
mkFreeName i@(Id ts cs r) = case ts of
  t : s -> let st = tokStr t in case st of
    c : _ | isAlphaNum c -> Id (freeToken st : s) cs r
          | otherwise -> Id [mkSimpleId "gn_free"] [i] r
    _ -> Id (mkSimpleId "gn_free_f" : ts) cs r
  _ -> i

-- | a prefix for free names
freeNamePrefix :: String
freeNamePrefix = "gn_free_"

-- | create a generated simple identifier
freeToken :: String -> Token
freeToken str = mkSimpleId $ freeNamePrefix ++ str

-- | obtains the sorts of the given list of term
getSorts :: [CASLTERM] -> [SORT]
getSorts = mapMaybe getSort

-- | compute the sort of the term, if possible
getSort :: CASLTERM -> Maybe SORT
getSort (Qual_var _ kind _) = Just kind
getSort (Application op _ _) = case op of
            Qual_op_name _ (Op_type _ _ kind _) _ -> Just kind
            _ -> Nothing
getSort _ = Nothing

-- | extracts the predicate name from the predicate symbol
pred_symb_name :: PRED_SYMB -> PRED_NAME
pred_symb_name (Pred_name pn) = pn
pred_symb_name (Qual_pred_name pn _ _) = pn

{- | extract the variables from a CASL formula and put them in a map
with keys the sort of the variables and value the set of variables
in this sort -}
getVars :: CASLFORMULA -> Map.Map Id (Set.Set Token)
getVars (Quantification _ _ f _) = getVars f
getVars (QuantOp _ _ f) = getVars f
getVars (QuantPred _ _ f) = getVars f
getVars (Junction _ fs _) =
    foldr (Map.unionWith Set.union . getVars) Map.empty fs
getVars (Relation f1 _ f2 _) = Map.unionWith Set.union v1 v2
     where v1 = getVars f1
           v2 = getVars f2
getVars (Negation f _) = getVars f
getVars (Predication _ ts _) =
    foldr (Map.unionWith Set.union . getVarsTerm) Map.empty ts
getVars (Definedness t _) = getVarsTerm t
getVars (Equation t1 _ t2 _) = Map.unionWith Set.union v1 v2
     where v1 = getVarsTerm t1
           v2 = getVarsTerm t2
getVars (Membership t _ _) = getVarsTerm t
getVars (Mixfix_formula t) = getVarsTerm t
getVars _ = Map.empty

-- | extract the variables of a CASL term
getVarsTerm :: CASLTERM -> Map.Map Id (Set.Set Token)
getVarsTerm (Qual_var var sort _) =
    Map.insert sort (Set.singleton var) Map.empty
getVarsTerm (Application _ ts _) =
    foldr (Map.unionWith Set.union . getVarsTerm) Map.empty ts
getVarsTerm (Sorted_term t _ _) = getVarsTerm t
getVarsTerm (Cast t _ _) = getVarsTerm t
getVarsTerm (Conditional t1 f t2 _) = Map.unionWith Set.union v3 m
     where v1 = getVarsTerm t1
           v2 = getVarsTerm t2
           v3 = getVars f
           m = Map.unionWith Set.union v1 v2
getVarsTerm (Mixfix_term ts) =
    foldr (Map.unionWith Set.union . getVarsTerm) Map.empty ts
getVarsTerm (Mixfix_parenthesized ts _) =
    foldr (Map.unionWith Set.union . getVarsTerm) Map.empty ts
getVarsTerm (Mixfix_bracketed ts _) =
    foldr (Map.unionWith Set.union . getVarsTerm) Map.empty ts
getVarsTerm (Mixfix_braced ts _) =
    foldr (Map.unionWith Set.union . getVarsTerm) Map.empty ts
getVarsTerm _ = Map.empty

-- | add universal quantification of all variables in the formula
quantifyUniversally :: CASLFORMULA -> CASLFORMULA
quantifyUniversally form = if null var_decl
                           then form
                           else Quantification Universal var_decl form nullRange
      where vars = getVars form
            var_decl = listVarDecl vars

{- | traverses a map with sorts as keys and sets of variables as value
and creates a list of variable declarations -}
listVarDecl :: Map.Map Id (Set.Set Token) -> [VAR_DECL]
listVarDecl = Map.foldrWithKey f []
      where f sort var_set = (Var_decl (Set.toList var_set) sort nullRange :)

-- | generates a new variable qualified with the given number
newVarIndex :: Int -> SORT -> CASLTERM
newVarIndex i sort = Qual_var var sort nullRange
    where var = mkSimpleId $ 'V' : show i

-- | generates a new variable
newVar :: SORT -> CASLTERM
newVar sort = Qual_var var sort nullRange
    where var = mkSimpleId "V"

-- | generates the free representation of an OP_SYMB
free_op_sym :: OP_SYMB -> OP_SYMB
free_op_sym (Op_name on) = Op_name $ mkFreeName on
free_op_sym (Qual_op_name on ot r) = Qual_op_name on' ot' r
     where on' = mkFreeName on
           ot' = free_op_type ot

-- | generates the free representation of an OP_TYPE
free_op_type :: OP_TYPE -> OP_TYPE
free_op_type (Op_type _ args res r) = Op_type Total args' res' r
     where args' = map mkFreeName args
           res' = mkFreeName res

-- | generates the free representation of a PRED_SYMB
free_pred_sym :: PRED_SYMB -> PRED_SYMB
free_pred_sym (Pred_name pn) = Pred_name $ mkFreeName pn
free_pred_sym (Qual_pred_name pn pt r) = Qual_pred_name pn' pt' r
     where pn' = mkFreeName pn
           pt' = free_pred_type pt

-- | generates the free representation of a PRED_TYPE
free_pred_type :: PRED_TYPE -> PRED_TYPE
free_pred_type (Pred_type args r) = Pred_type args' r
     where args' = map mkFreeName args

-- | generates the free representation of a CASLTERM
free_term :: CASLTERM -> CASLTERM
free_term (Qual_var v s r) = Qual_var v (mkFreeName s) r
free_term (Application os ts r) = Application os' ts' r
     where ts' = map free_term ts
           os' = free_op_sym os
free_term (Sorted_term t s r) = Sorted_term t' s' r
     where t' = free_term t
           s' = mkFreeName s
free_term (Cast t s r) = Cast t' s' r
     where t' = free_term t
           s' = mkFreeName s
free_term (Conditional t1 f t2 r) = Conditional t1' f' t2' r
     where t1' = free_term t1
           t2' = free_term t2
           f' = free_formula f
free_term (Mixfix_qual_pred ps) = Mixfix_qual_pred ps'
     where ps' = free_pred_sym ps
free_term (Mixfix_term ts) = Mixfix_term ts'
     where ts' = map free_term ts
free_term (Mixfix_sorted_term s r) = Mixfix_sorted_term s' r
     where s' = mkFreeName s
free_term (Mixfix_cast s r) = Mixfix_cast s' r
     where s' = mkFreeName s
free_term (Mixfix_parenthesized ts r) = Mixfix_parenthesized ts' r
     where ts' = map free_term ts
free_term (Mixfix_bracketed ts r) = Mixfix_bracketed ts' r
     where ts' = map free_term ts
free_term (Mixfix_braced ts r) = Mixfix_braced ts' r
     where ts' = map free_term ts
free_term t = t

-- | generates the free representation of a list of variable declarations
free_var_decls :: [VAR_DECL] -> [VAR_DECL]
free_var_decls = map free_var_decl

-- | generates the free representation of a variable declaration
free_var_decl :: VAR_DECL -> VAR_DECL
free_var_decl (Var_decl vs s r) = Var_decl vs s' r
     where s' = mkFreeName s

{- | computes the substitution needed for the kernel of h to the
sentences of the theory of M -}
free_formula :: CASLFORMULA -> CASLFORMULA
free_formula (Quantification q vs f r) = Quantification q vs' f' r
     where vs' = free_var_decls vs
           f' = free_formula f
free_formula (Junction j fs r) = Junction j fs' r
     where fs' = map free_formula fs
free_formula (Relation f1 c f2 r) = Relation f1' c f2' r
     where f1' = free_formula f1
           f2' = free_formula f2
free_formula (Negation f r) = Negation f' r
     where f' = free_formula f
free_formula (Predication ps ts r) = pr
     where ss = getSorts ts
           free_ss = map mkFreeName ss
           ts' = map free_term ts
           psi = psiName $ pred_symb_name ps
           pt = Pred_type free_ss nullRange
           ps' = Qual_pred_name psi pt nullRange
           pr = Predication ps' ts' r
free_formula (Definedness t r) = case sort of
        Nothing -> Definedness t' r
        Just s -> mkPredication (freePredSymb s) [t', t']
     where t' = free_term t
           sort = getSort t
free_formula (Equation t1 e t2 r) = let
     t1' = free_term t1
     t2' = free_term t2
     sort = getSort t1
     in case sort of
        Nothing -> Equation t1' e t2' r
        Just s -> let
            ps = freePredSymb s
            pred1 = mkPredication ps [t1', t2']
            pred2 = mkNeg $ mkPredication ps [t1', t1']
            pred3 = mkNeg $ mkPredication ps [t2', t2']
            pred4 = conjunct [pred2, pred3]
            pred5 = disjunct [pred1, pred4]
            in if e == Existl then pred1 else pred5
free_formula (Membership t s r) = Membership t' s' r
     where t' = free_term t
           s' = mkFreeName s
free_formula (Mixfix_formula t) = Mixfix_formula t'
     where t' = free_term t
free_formula (QuantOp on ot f) = QuantOp on' ot' f'
     where on' = mkFreeName on
           ot' = free_op_type ot
           f' = free_formula f
free_formula (QuantPred pn pt f) = QuantPred pn' pt' f'
     where pn' = mkFreeName pn
           pt' = free_pred_type pt
           f' = free_formula f
free_formula f = f
