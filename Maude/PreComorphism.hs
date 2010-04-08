{- |
Module      :  $Header$
Description :  Maude Comorphisms
Copyright   :  (c) Adrian Riesco, Facultad de Informatica UCM 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  ariesco@fdi.ucm.es
Stability   :  experimental
Portability :  portable

Comorphism from Maude to CASL.
-}

module Maude.PreComorphism where

import Data.Maybe
import qualified Data.List as List
import qualified Data.Set as Set
import qualified Data.Map as Map

import qualified Maude.Sign as MSign
import qualified Maude.Sentence as MSentence
import qualified Maude.Morphism as MMorphism
import qualified Maude.AS_Maude as MAS
import qualified Maude.Symbol as MSym
import Maude.Meta.HasName

import qualified CASL.Sign as CSign
import qualified CASL.Morphism as CMorphism
import qualified CASL.AS_Basic_CASL as CAS
import CASL.StaticAna
import CASL.Logic_CASL

import Common.Id
import Common.Result
import Common.AS_Annotation
import Common.ProofUtils (charMap)
import qualified Common.Lib.Rel as Rel

import Comorphisms.GetPreludeLib (readLib)

import System.IO.Unsafe

import Static.GTheory

import Logic.Prover
import Logic.Coerce

type IdMap = Map.Map Id Id
type OpTransTuple = (CSign.OpMap, CSign.OpMap, Set.Set Component)

-- | generates a CASL morphism from a Maude morphism
mapMorphism :: MMorphism.Morphism -> Result (CMorphism.CASLMor)
mapMorphism morph = 
         let
           src = MMorphism.source morph
           tgt = MMorphism.target morph
           mk = arrangeKinds (MSign.sorts src) (MSign.subsorts src)
           cs = kindsFromMap mk
           smap = MMorphism.sortMap morph
           omap = MMorphism.opMap morph
           smap' = applySortMap2CASLSorts smap cs
           omap' = maudeOpMap2CASLOpMap mk omap
           pmap = createPredMap mk smap
           (src', _) = maude2casl src []
           (tgt', _) = maude2casl tgt []
         in return $ CMorphism.Morphism src' tgt' smap' omap' pmap ()

-- | translates the Maude morphism between operators into a CASL morpshim between
-- operators
maudeOpMap2CASLOpMap :: IdMap -> MMorphism.OpMap -> CMorphism.Op_map
maudeOpMap2CASLOpMap im = Map.foldWithKey (translateOpMapEntry im) Map.empty

-- | translates the mapping between two symbols representing operators into
-- a CASL operators map
translateOpMapEntry :: IdMap -> MSym.Symbol -> MSym.Symbol -> CMorphism.Op_map
                       -> CMorphism.Op_map
translateOpMapEntry im (MSym.Operator from ar co) (MSym.Operator to _ _) copm = copm'
       where f = token2id . getName
             g = \ x -> Map.findWithDefault (errorId "translate op map entry") (f x) im
             ot = CSign.OpType CAS.Total (map g ar) (g co)
             cop = (token2id from, ot)
             to' = (token2id to, CAS.Total)
             copm' = Map.insert cop to' copm
translateOpMapEntry _ _ _ _ = Map.empty

-- | generates a set of CASL symbol from a Maude Symbol
mapSymbol :: MSign.Sign -> MSym.Symbol -> Set.Set CSign.Symbol
mapSymbol sg (MSym.Sort q) = Set.singleton csym
           where mk = arrangeKinds (MSign.sorts sg) (MSign.subsorts sg)
                 sym_id = token2id q
                 kind = Map.findWithDefault (errorId "map symbol") sym_id mk
                 pred_data = CSign.PredType [kind]
                 csym = CSign.Symbol sym_id $ CSign.PredAsItemType pred_data
mapSymbol sg (MSym.Operator q ar co) = Set.singleton csym
           where mk = arrangeKinds (MSign.sorts sg) (MSign.subsorts sg)
                 q' = token2id q
                 ar' = map (maudeSort2caslId mk) ar
                 co' = token2id $ getName co
                 op_data = CSign.OpType CAS.Total ar' co'
                 csym = CSign.Symbol q' $ CSign.OpAsItemType op_data
mapSymbol _ _ = Set.empty

-- | returns the sort in CASL of the Maude sort symbol
maudeSort2caslId :: IdMap -> MSym.Symbol -> Id
maudeSort2caslId im sym = Map.findWithDefault (errorId "sort to id") (token2id $ getName sym) im

-- | creates the predicate map for the CASL morphism from the Maude sort map and
-- the map between sorts and kinds
createPredMap :: IdMap -> MMorphism.SortMap -> CMorphism.Pred_map
createPredMap im = Map.foldWithKey (createPredMap4sort im) Map.empty

-- | creates an entry of the predicate map for a single sort
createPredMap4sort :: IdMap -> MSym.Symbol -> MSym.Symbol -> CMorphism.Pred_map
                      -> CMorphism.Pred_map
createPredMap4sort im from to m = Map.insert key id_to m
           where id_from = token2id $ getName from
                 id_to = token2id $ getName to
                 kind = Map.findWithDefault (errorId "predicate for sort") id_from im
                 key = (id_from, CSign.PredType [kind])

-- | computes the sort morphism of CASL from the sort morphism in Maude and the set
-- of kinds
applySortMap2CASLSorts :: MMorphism.SortMap -> Set.Set Id -> CMorphism.Sort_map
applySortMap2CASLSorts sm = Set.fold (applySortMap2CASLSort sm) Map.empty

-- | computes the morphism for a single kind
applySortMap2CASLSort :: MMorphism.SortMap -> Id -> CMorphism.Sort_map -> CMorphism.Sort_map
applySortMap2CASLSort sm sort csm = new_csm
          where toks = getTokens sort
                new_toks = map (rename sm) toks
                new_sort = mkId new_toks
                new_csm = if new_sort == sort
                          then csm
                          else Map.insert sort new_sort csm

-- | renames the sorts in a given kind
rename :: MMorphism.SortMap -> Token -> Token
rename sm tok = new_tok
          where sym = MSym.Sort tok
                sym' = if Map.member sym sm
                       then fromJust $ Map.lookup sym sm
                       else sym
                new_tok = getName sym'

-- | translates a Maude sentence into a CASL formula
mapSentence :: MSign.Sign -> MSentence.Sentence -> Result CAS.CASLFORMULA
mapSentence sg sen@(MSentence.Equation eq) = case any MAS.owise ats of
             False -> return $ sentence $ noOwiseSen2Formula mk named
             True -> let
                       sg_sens = map (makeNamed "") $ Set.toList $ MSign.sentences sg
                       (no_owise_sens, _, _) = splitOwiseEqs sg_sens
                       no_owise_forms = map (noOwiseSen2Formula mk) no_owise_sens
                       trans = sentence $ owiseSen2Formula mk no_owise_forms named
                     in return trans
          where mk = arrangeKinds (MSign.sorts sg) (MSign.subsorts sg)
                MAS.Eq _ _ _ ats = eq
                named = makeNamed "" sen
mapSentence sg sen@(MSentence.Membership mb) = return $ sentence form
          where mk = arrangeKinds (MSign.sorts sg) (MSign.subsorts sg)
                MAS.Mb _ _ _ _ = mb
                named = makeNamed "" sen
                form = mb_rl2formula mk named
mapSentence sg sen@(MSentence.Rule rl) = return $ sentence form
          where mk = arrangeKinds (MSign.sorts sg) (MSign.subsorts sg)
                MAS.Rl _ _ _ _ = rl
                named = makeNamed "" sen
                form = mb_rl2formula mk named

-- | applies maude2casl to compute the CASL signature and sentences from
-- the Maude ones, and wraps them into a Result datatype
mapTheory :: (MSign.Sign, [Named MSentence.Sentence]) 
              -> Result (CSign.CASLSign, [Named CAS.CASLFORMULA])
mapTheory (sg, nsens) = return $ maude2casl sg nsens

-- | computes new signature and sentences of CASL associated to the
-- given Maude signature and sentences
maude2casl :: MSign.Sign -> [Named MSentence.Sentence]
              -> (CSign.CASLSign, [Named CAS.CASLFORMULA])
maude2casl msign nsens = (csign { CSign.sortSet = cs,
                            CSign.sortRel = sbs',
                            CSign.opMap = cops',
                            CSign.assocOps = assoc_ops,
                            CSign.predMap = preds,
                            CSign.declaredSymbols = syms }, new_sens)
   where csign = CSign.emptySign ()
         ss = MSign.sorts msign
         ss' = Set.map sym2id ss
         mk = arrangeKinds ss (MSign.subsorts msign)
         mk' = arrangeKinds2 ss (MSign.subsorts msign)
         sbs = MSign.subsorts msign
         sbs' = maudeSbs2caslSbs sbs mk
         cs = Set.union ss' $ kindsFromMap mk -- (Set.map kindId ss')
         preds = rewPredicates cs
         rs = rewPredicatesSens cs
         ops = deleteUniversal $ MSign.ops msign
         ksyms = kinds2syms cs
         (cops, assoc_ops, _) = translateOps mk ops -- (cops, assoc_ops, comps)
         ctor_sen = [] -- [ctorSen False (cs, Rel.empty, comps)]
         cops' = universalOps cs cops $ booleanImported ops
         rs' = rewPredicatesCongSens cops'
         pred_forms = loadLibraries (MSign.sorts msign) ops
         ops_syms = ops2symbols cops'
         (no_owise_sens, owise_sens, mbs_rls_sens) = splitOwiseEqs nsens
         no_owise_forms = map (noOwiseSen2Formula mk') no_owise_sens
         owise_forms = map (owiseSen2Formula mk' no_owise_forms) owise_sens
         mb_rl_forms = map (mb_rl2formula mk') mbs_rls_sens
         preds_syms = preds2syms preds
         syms = Set.union ksyms $ Set.union ops_syms preds_syms
         new_sens = concat [rs, rs', no_owise_forms, owise_forms, 
                            mb_rl_forms, ctor_sen, pred_forms]

-- | translates the Maude subsorts into CASL subsorts, and adds the subsorts
-- for the kinds
maudeSbs2caslSbs :: MSign.SubsortRel -> IdMap -> Rel.Rel CAS.SORT
maudeSbs2caslSbs sbs im = Rel.fromDistinctMap m4
      where l = Map.toList $ Rel.toMap sbs
            l1 = map maudeSb2caslSb l
            l2 = idList2Subsorts $ Map.toList im
            l3 = map subsortsKinds l
            m1 = Map.fromList l1
            m2 = Map.fromList l2
            m3 = Map.fromList l3
            m4 = Map.unionWith Set.union m1 $ Map.unionWith Set.union m2 m3

idList2Subsorts :: [(Id, Id)] -> [(Id, Set.Set Id)]
idList2Subsorts [] = []
idList2Subsorts ((id1, id2) : il) = t1 : idList2Subsorts il
      where t1 = (id1, Set.singleton id2)

maudeSb2caslSb :: (MSym.Symbol, Set.Set MSym.Symbol) -> (Id, Set.Set Id)
maudeSb2caslSb (sym, st) = (kindId $ sortSym2id sym, Set.map (kindId . sortSym2id) st)

subsortsKinds :: (MSym.Symbol, Set.Set MSym.Symbol) -> (Id, Set.Set Id)
subsortsKinds (sym, st) = (sortSym2id sym, Set.map sortSym2id st)

sortSym2id :: MSym.Symbol -> Id
sortSym2id (MSym.Sort q) = token2id q
sortSym2id _ = token2id $ mkSimpleId $ "error_translation"

-- | generates the sentences to state that the rew predicates are a congruence
rewPredicatesCongSens :: CSign.OpMap -> [Named CAS.CASLFORMULA]
rewPredicatesCongSens = Map.foldWithKey rewPredCongSet []

-- | generates the sentences to state that the rew predicates are a congruence
-- for the operator types in the set
rewPredCongSet :: Id -> Set.Set CSign.OpType -> [Named CAS.CASLFORMULA] -> [Named CAS.CASLFORMULA]
rewPredCongSet idn ots fs = fs ++ fs'
      where fs' = Set.fold (rewPredCong idn) [] ots

-- | generates the sentences to state that the rew predicates are a congruence
-- for a single operator
rewPredCong :: Id -> CSign.OpType -> [Named CAS.CASLFORMULA] -> [Named CAS.CASLFORMULA]
rewPredCong op ot fs = case args of
                        [] -> fs
                        _ -> nq_form : fs
       where args = CSign.opArgs ot
             vars1 = rewPredCongPremise 0 args
             vars2 = rewPredCongPremise (length args) args
             res = CSign.opRes ot
             res_pred_type = CAS.Pred_type [res, res] nullRange
             pn = CAS.Qual_pred_name rewID res_pred_type nullRange
             name = "rew_cong_" ++ show op
             prems = rewPredsCong args vars1 vars2
             prems_conj = createConjForm prems
             os = CAS.Qual_op_name op (CSign.toOP_TYPE ot) nullRange
             conc_term1 = CAS.Application os vars1 nullRange
             conc_term2 = CAS.Application os vars2 nullRange
             conc_form = CAS.Predication pn [conc_term1, conc_term2] nullRange
             form = createImpForm prems_conj conc_form
             nq_form = makeNamed name $ quantifyUniversally form

-- | generates a list of variables of the given sorts
rewPredCongPremise :: Int -> [CAS.SORT] -> [CAS.CASLTERM]
rewPredCongPremise n (s : ss) = newVarIndex n s : rewPredCongPremise (n + 1) ss
rewPredCongPremise _ [] = []

-- | generates a list of rew predicates with the given variables
rewPredsCong :: [CAS.SORT] -> [CAS.CASLTERM] -> [CAS.CASLTERM] -> [CAS.CASLFORMULA]
rewPredsCong (s : ss) (t : ts) (t' : ts') = form : forms
          where pred_type = CAS.Pred_type [s, s] nullRange
                pn = CAS.Qual_pred_name rewID pred_type nullRange
                form = CAS.Predication pn [t, t'] nullRange
                forms = rewPredsCong ss ts ts'
rewPredsCong _ _ _ = []

-- | load the CASL libraries for the Maude built-in operators
loadLibraries :: MSign.SortSet -> MSign.OpMap -> [Named CAS.CASLFORMULA]
loadLibraries ss om = case natImported ss om of
        False -> []
        True -> loadNaturalNatSens

-- | loads the sentences associated to the natural numbers
loadNaturalNatSens :: [Named CAS.CASLFORMULA]
loadNaturalNatSens = 
         let lib = head $ unsafePerformIO $ readLib "Maude/MaudeNumbers.casl"
         in case lib of
             G_theory lid _ _ thSens _ -> let sens = toNamedList thSens
                                          in do
                                              sens' <- coerceSens lid CASL "" sens
                                              filter (not . ctorCons) sens'

-- | checks if a sentence is an constructor sentence
ctorCons :: Named CAS.CASLFORMULA -> Bool
ctorCons f = case sentence f of
      CAS.Sort_gen_ax _ _ -> True
      _ -> False

-- | checks if the boolean values are imported
booleanImported :: MSign.OpMap -> Bool
booleanImported = Map.member (mkSimpleId "if_then_else_fi")

-- | checks if the natural numbers are imported
natImported :: MSign.SortSet -> MSign.OpMap -> Bool
natImported ss om = b1 && b2 && b3
     where b1 = Set.member (MSym.Sort $ mkSimpleId "Nat") ss
           b2 = Map.member (mkSimpleId "s_") om
           b3 = case b2 of
                 False -> True
                 True -> specialZeroSet $ om Map.! (mkSimpleId "s_")

specialZeroSet :: MSign.OpDeclSet -> Bool
specialZeroSet = Set.fold specialZero False

specialZero :: MSign.OpDecl -> Bool -> Bool
specialZero (_, ats) b = b' || b
         where b' = isSpecial ats

isSpecial :: [MAS.Attr] -> Bool
isSpecial [] = False
isSpecial ((MAS.Special _) : _) = True
isSpecial (_ : ats) = isSpecial ats

-- | delete the universal operators from Maude specifications, that will be
-- substituted for one operator for each sort in the specification
deleteUniversal :: MSign.OpMap -> MSign.OpMap
deleteUniversal om = om5
         where om1 = Map.delete (mkSimpleId "if_then_else_fi") om
               om2 = Map.delete (mkSimpleId "_==_") om1
               om3 = Map.delete (mkSimpleId "_=/=_") om2
               om4 = Map.delete (mkSimpleId "upTerm") om3
               om5 = Map.delete (mkSimpleId "downTerm") om4

-- | generates the universal operators for all the sorts in the module
universalOps :: Set.Set Id -> CSign.OpMap -> Bool -> CSign.OpMap
universalOps kinds om True = Set.fold universalOpKind om kinds
universalOps _ om False = om

-- | generates the universal operators for a concrete module
universalOpKind :: Id -> CSign.OpMap -> CSign.OpMap
universalOpKind kind om = om3
        where if_id = str2id "if_then_else_fi"
              double_eq_id = str2id "_==_"
              neg_double_eq_id = str2id "_=/=_"
              bool_id = str2id "Bool"
              if_opt = Set.singleton $ CSign.OpType CAS.Total [bool_id, kind, kind] kind
              eq_opt = Set.singleton $ CSign.OpType CAS.Total [kind, kind] bool_id
              om1 = Map.insertWith Set.union if_id if_opt om
              om2 = Map.insertWith Set.union double_eq_id eq_opt om1
              om3 = Map.insertWith Set.union neg_double_eq_id eq_opt om2

-- | generates the formulas for the universal operators
universalSens :: Set.Set Id -> [Named CAS.CASLFORMULA]
universalSens = Set.fold universalSensKind []

-- | generates the formulas for the universal operators for the given sort
universalSensKind :: Id -> [Named CAS.CASLFORMULA] -> [Named CAS.CASLFORMULA]
universalSensKind kind acc = concat [iss, eqs, neqs, acc]
         where iss = ifSens kind
               eqs = equalitySens kind
               neqs = nonEqualitySens kind

-- | generates the formulas for the if statement
ifSens :: Id -> [Named CAS.CASLFORMULA]
ifSens kind = [form'', neg_form'']
         where v1 = newVarIndex 1 kind
               v2 = newVarIndex 2 kind
               bk = str2id "Bool"
               bv = newVarIndex 2 bk
               true_type = CAS.Op_type CAS.Total [] bk nullRange
               true_id = CAS.Qual_op_name (str2id "true") true_type nullRange
               true_term = CAS.Application true_id [] nullRange
               if_type = CAS.Op_type CAS.Total [bk, kind, kind] kind nullRange
               if_name = str2id "if_then_else_fi"
               if_id = CAS.Qual_op_name if_name if_type nullRange
               if_term = CAS.Application if_id [bv, v1, v2] nullRange
               prem = CAS.Strong_equation bv true_term nullRange
               concl = CAS.Strong_equation if_term v1 nullRange
               form = CAS.Implication prem concl True nullRange
               form' = quantifyUniversally form
               neg_prem = CAS.Negation prem nullRange
               neg_concl = CAS.Strong_equation if_term v2 nullRange
               neg_form = CAS.Implication neg_prem neg_concl True nullRange
               neg_form' = quantifyUniversally neg_form
               name1 = show kind ++ "_if_true"
               name2 = show kind ++ "_if_false"
               form'' = makeNamed name1 form'
               neg_form'' = makeNamed name2 neg_form'

-- | generates the formulas for the equality
equalitySens :: Id -> [Named CAS.CASLFORMULA]
equalitySens kind = [form'', comp_form'']
         where v1 = newVarIndex 1 kind
               v2 = newVarIndex 2 kind
               bk = str2id "Bool"
               b_type = CAS.Op_type CAS.Total [] bk nullRange
               true_id = CAS.Qual_op_name (str2id "true") b_type nullRange
               true_term = CAS.Application true_id [] nullRange
               false_id = CAS.Qual_op_name (str2id "false") b_type nullRange
               false_term = CAS.Application false_id [] nullRange
               prem = CAS.Strong_equation v1 v2 nullRange
               double_eq_type = CAS.Op_type CAS.Total [kind, kind] kind nullRange
               double_eq_name = str2id "_==_"
               double_eq_id = CAS.Qual_op_name double_eq_name double_eq_type nullRange
               double_eq_term = CAS.Application double_eq_id [v1, v2] nullRange
               concl = CAS.Strong_equation double_eq_term true_term nullRange
               form = CAS.Implication prem concl True nullRange
               form' = quantifyUniversally form
               neg_prem = CAS.Negation prem nullRange
               new_concl = CAS.Strong_equation double_eq_term false_term nullRange
               comp_form = CAS.Implication neg_prem new_concl True nullRange
               comp_form' = quantifyUniversally comp_form
               name1 = show kind ++ "_==_true"
               name2 = show kind ++ "_==_false"
               form'' = makeNamed name1 form'
               comp_form'' = makeNamed name2 comp_form'

-- | generates the formulas for the inequality
nonEqualitySens :: Id -> [Named CAS.CASLFORMULA]
nonEqualitySens kind = [form'', comp_form'']
         where v1 = newVarIndex 1 kind
               v2 = newVarIndex 2 kind
               bk = str2id "Bool"
               b_type = CAS.Op_type CAS.Total [] bk nullRange
               true_id = CAS.Qual_op_name (str2id "true") b_type nullRange
               true_term = CAS.Application true_id [] nullRange
               false_id = CAS.Qual_op_name (str2id "false") b_type nullRange
               false_term = CAS.Application false_id [] nullRange
               prem = CAS.Strong_equation v1 v2 nullRange
               double_eq_type = CAS.Op_type CAS.Total [kind, kind] kind nullRange
               double_eq_name = str2id "_==_"
               double_eq_id = CAS.Qual_op_name double_eq_name double_eq_type nullRange
               double_eq_term = CAS.Application double_eq_id [v1, v2] nullRange
               concl = CAS.Strong_equation double_eq_term false_term nullRange
               form = CAS.Implication prem concl True nullRange
               form' = quantifyUniversally form
               neg_prem = CAS.Negation prem nullRange
               new_concl = CAS.Strong_equation double_eq_term true_term nullRange
               comp_form = CAS.Implication neg_prem new_concl True nullRange
               comp_form' = quantifyUniversally comp_form
               name1 = show kind ++ "_=/=_false"
               name2 = show kind ++ "_=/=_true"
               form'' = makeNamed name1 form'
               comp_form'' = makeNamed name2 comp_form'

-- | translates the Maude operator map into a tuple of CASL operators, CASL
-- associative operators, membership induced from each Maude operator,
-- and the set of sorts with the ctor attribute
translateOps :: IdMap -> MSign.OpMap -> OpTransTuple
translateOps im = Map.fold (translateOpDeclSet im) (Map.empty, Map.empty, Set.empty)

-- | translates an operator declaration set into a tern as described above
translateOpDeclSet :: IdMap -> MSign.OpDeclSet -> OpTransTuple -> OpTransTuple
translateOpDeclSet im ods tpl = Set.fold (translateOpDecl im) tpl ods

-- | given an operator declaration updates the accumulator with the translation
-- to CASL operator, checking if the operator has the assoc attribute to insert
-- it in the map of associative operators, generating the membership predicate
-- induced by the operator declaration, and checking if it has the ctor attribute
-- to introduce the operator in the generators sentence
translateOpDecl :: IdMap -> MSign.OpDecl -> OpTransTuple -> OpTransTuple
translateOpDecl im (syms, ats) (ops, assoc_ops, cs) = case tl of
                      [] -> (ops', assoc_ops', cs')
                      _ -> translateOpDecl im (syms', ats) (ops', assoc_ops', cs')
      where sym = head $ Set.toList syms
            tl = tail $ Set.toList syms
            syms' = Set.fromList tl
            (cop_id, ot, _) = fromJust $ maudeSym2CASLOp im sym
            cop_type = Set.singleton ot -- Set.union (Set.singleton ot) (Set.singleton ot')
            ops' = Map.insertWith (Set.union) cop_id cop_type ops
            assoc_ops' = if any MAS.assoc ats
                         then Map.insertWith (Set.union) cop_id cop_type assoc_ops
                         else assoc_ops
            cs' = if any MAS.ctor ats
                  then Set.insert (Component cop_id ot) cs
                  else cs

-- | translates a Maude operator symbol into a pair with the id of the operator
-- and its CASL type
maudeSym2CASLOp :: IdMap -> MSym.Symbol -> Maybe (Id, CSign.OpType, CSign.OpType)
maudeSym2CASLOp im (MSym.Operator op ar co) = Just (token2id op, ot, ot')
      where f = token2id . getName
            g = \ x -> maudeSymbol2caslSort x im -- \ x -> Map.findWithDefault (errorId "Maude_sym2CASL_sym") (f x) im
            ot = CSign.OpType CAS.Total (map g ar) (g co)
            ot' = CSign.OpType CAS.Total (map f ar) (f co)
maudeSym2CASLOp _ _ = Nothing

-- | creates a conjuctive formula distinguishing the size of the list
createConjForm :: [CAS.CASLFORMULA] -> CAS.CASLFORMULA
createConjForm [] = CAS.True_atom nullRange
createConjForm [a] = a
createConjForm fs = CAS.Conjunction fs nullRange

-- | creates a implication formula distinguishing the size of the premises
createImpForm :: CAS.CASLFORMULA -> CAS.CASLFORMULA -> CAS.CASLFORMULA
createImpForm (CAS.True_atom _) form = form
createImpForm form1 form2 = CAS.Implication form1 form2 True nullRange

-- | generates the predicates asserting the "true" sort of the operator if all
-- the arguments have the correct sort 
ops2predPremises :: IdMap -> [MSym.Symbol] -> Int -> ([CAS.CASLTERM], [CAS.CASLFORMULA])
ops2predPremises im (MSym.Sort s : ss) i = (var : terms, form : forms)
         where s' = token2id s
               kind = Map.findWithDefault (errorId "mb of op as predicate") s' im
               pred_type = CAS.Pred_type [kind] nullRange
               pred_name = CAS.Qual_pred_name s' pred_type nullRange
               var = newVarIndex i kind
               form = CAS.Predication pred_name [var] nullRange
               (terms, forms) = ops2predPremises im ss (i + 1)
ops2predPremises im (MSym.Kind k : ss) i = (var : terms, forms)
         where k' = token2id k
               kind = Map.findWithDefault (errorId "mb of op as predicate") k' im
               var = newVarIndex i kind
               (terms, forms) = ops2predPremises im ss (i + 1)
ops2predPremises _ _ _ = ([], [])


-- | traverses the Maude sentences, returning a pair of list of sentences.
-- The first list in the pair are the equations without the attribute "owise",
-- while the second one are the equations with this attribute
splitOwiseEqs :: [Named MSentence.Sentence] -> 
                ([Named MSentence.Sentence], [Named MSentence.Sentence], [Named MSentence.Sentence])
splitOwiseEqs [] = ([], [], [])
splitOwiseEqs (s : ss) = res
        where (no_owise_sens, owise_sens, mbs_rls) = splitOwiseEqs ss
              sen = sentence s
              res = case sen of
                     MSentence.Equation (MAS.Eq _ _ _ ats) -> case any MAS.owise ats of
                                            True -> (no_owise_sens, s : owise_sens, mbs_rls)
                                            False -> (s : no_owise_sens, owise_sens, mbs_rls)
                     _ -> (no_owise_sens, owise_sens, s : mbs_rls)

-- | translates a Maude equation defined without the "owise" attribute into
-- a CASL formula
noOwiseSen2Formula ::  IdMap -> Named MSentence.Sentence
                       -> Named CAS.CASLFORMULA
noOwiseSen2Formula im s = s'
       where MSentence.Equation eq = sentence s
             sen' = noOwiseEq2Formula im eq
             s' = s { sentence = sen' }

-- | translates a Maude equation defined with the "owise" attribute into
-- a CASL formula
owiseSen2Formula ::  IdMap -> [Named CAS.CASLFORMULA] 
                     -> Named MSentence.Sentence -> Named CAS.CASLFORMULA
owiseSen2Formula im owise_forms s = s'
       where MSentence.Equation eq = sentence s
             sen' = owiseEq2Formula im owise_forms eq
             s' = s { sentence = sen' }

-- | translates a Maude membership or rule into a CASL formula
mb_rl2formula :: IdMap -> Named MSentence.Sentence -> Named CAS.CASLFORMULA
mb_rl2formula im s = case sen of
                MSentence.Membership mb -> let 
                                             mb' = mb2formula im mb
                                           in s { sentence = mb' }
                MSentence.Rule rl -> let
                                       rl' = rl2formula im rl
                                     in s { sentence = rl' }
                _ -> makeNamed "" $ CAS.False_atom nullRange
       where sen = sentence s

-- | generates a new variable qualified with the given number
newVarIndex :: Int -> Id -> CAS.CASLTERM
newVarIndex i sort = CAS.Qual_var var sort nullRange
    where var = mkSimpleId $ "V" ++ show i

-- | generates a new variable
newVar :: Id -> CAS.CASLTERM
newVar sort = CAS.Qual_var var sort nullRange
    where var = mkSimpleId "V"

-- | Id for the rew predicate
rewID :: Id
rewID = token2id $ mkSimpleId "rew"

-- | translates a Maude equation without the "owise" attribute into a CASL formula
noOwiseEq2Formula :: IdMap -> MAS.Equation -> CAS.CASLFORMULA
noOwiseEq2Formula im eq@(MAS.Eq t t' [] _) = quantifyUniversally vars_form
      where ct = maudeTerm2caslTerm im t
            ct' = maudeTerm2caslTerm im t'
            form = CAS.Strong_equation ct ct' nullRange
            vars_form = varsImp (MSentence.Equation eq) im form
noOwiseEq2Formula im eq@(MAS.Eq t t' conds@(_:_) _) = quantifyUniversally vars_form
      where ct = maudeTerm2caslTerm im t
            ct' = maudeTerm2caslTerm im t'
            conds_form = conds2formula im conds
            concl_form = CAS.Strong_equation ct ct' nullRange
            form = createImpForm conds_form concl_form
            vars_form = varsImp (MSentence.Equation eq) im form

-- | transforms a Maude equation defined with the otherwise attribute into
-- a CASL formula
owiseEq2Formula :: IdMap -> [Named CAS.CASLFORMULA] -> MAS.Equation
                   -> CAS.CASLFORMULA
owiseEq2Formula im no_owise_form eq = form
      where (eq_form, vars) = noQuantification $ noOwiseEq2Formula im eq
            (op, ts, _) = fromJust $ getLeftApp eq_form
            ex_form = existencialNegationOtherEqs op ts no_owise_form
            imp_form = createImpForm ex_form eq_form
            form = CAS.Quantification CAS.Universal vars imp_form nullRange

-- | generates a conjunction of negation of existencial quantifiers
existencialNegationOtherEqs :: CAS.OP_SYMB -> [CAS.CASLTERM] ->
                               [Named CAS.CASLFORMULA] -> CAS.CASLFORMULA
existencialNegationOtherEqs op ts forms = form
      where ex_forms = foldr ((++) . existencialNegationOtherEq op ts) [] forms
            form = if length ex_forms > 1
                   then CAS.Conjunction ex_forms nullRange
                   else head ex_forms

-- | given a formula, if it refers to the same operator indicated by the parameters
-- the predicate creates a list with the negation of the existence of variables that
-- match the pattern described in the formula. In other case it returns an empty list
existencialNegationOtherEq :: CAS.OP_SYMB -> [CAS.CASLTERM] ->
                              Named CAS.CASLFORMULA -> [CAS.CASLFORMULA]
existencialNegationOtherEq req_op terms form = case ok of
                  False -> []
                  True -> let
                     (_, ts, conds) = fromJust tpl
                     ts' = qualifyExVarsTerms ts
                     conds' = qualifyExVarsForms conds
                     prems = (createEqs ts' terms) ++ conds'
                     conj_form = CAS.Conjunction prems nullRange
                     ex_form = if vars' /= []
                               then CAS.Quantification CAS.Existential vars' conj_form nullRange
                               else conj_form
                     neg_form = CAS.Negation ex_form nullRange
                          in [neg_form]
      where (inner_form, vars) = noQuantification $ sentence form
            vars' = qualifyExVars vars
            tpl = getLeftApp inner_form
            ok = case tpl of
                  Nothing -> False
                  Just _ -> let (op, ts, _) = fromJust tpl
                            in req_op == op && length terms == length ts

-- | qualifies the variables in a list of formulas with the suffix "_ex" to
-- distinguish them from the variables already bound
qualifyExVarsForms :: [CAS.CASLFORMULA] -> [CAS.CASLFORMULA]
qualifyExVarsForms = map qualifyExVarsForm

-- | qualifies the variables in a formula with the suffix "_ex" to distinguish them
-- from the variables already bound
qualifyExVarsForm :: CAS.CASLFORMULA -> CAS.CASLFORMULA
qualifyExVarsForm (CAS.Strong_equation t t' r) = CAS.Strong_equation qt qt' r
        where qt = qualifyExVarsTerm t
              qt' = qualifyExVarsTerm t'
qualifyExVarsForm (CAS.Predication op ts r) = CAS.Predication op ts' r
        where ts' = qualifyExVarsTerms ts
qualifyExVarsForm f = f

-- | qualifies the variables in a list of terms with the suffix "_ex" to
-- distinguish them from the variables already bound
qualifyExVarsTerms :: [CAS.CASLTERM] -> [CAS.CASLTERM]
qualifyExVarsTerms = map qualifyExVarsTerm

-- | qualifies the variables in a term with the suffix "_ex" to distinguish them
-- from the variables already bound
qualifyExVarsTerm :: CAS.CASLTERM -> CAS.CASLTERM
qualifyExVarsTerm (CAS.Qual_var var sort r) = CAS.Qual_var (qualifyExVarAux var) sort r
qualifyExVarsTerm (CAS.Application op ts r) = CAS.Application op ts' r
           where ts' = map qualifyExVarsTerm ts
qualifyExVarsTerm (CAS.Sorted_term t s r) = CAS.Sorted_term (qualifyExVarsTerm t) s r
qualifyExVarsTerm (CAS.Cast t s r) = CAS.Cast (qualifyExVarsTerm t) s r
qualifyExVarsTerm (CAS.Conditional t1 f t2 r) = CAS.Conditional t1' f t2' r
     where t1' = qualifyExVarsTerm t1
           t2' = qualifyExVarsTerm t2
qualifyExVarsTerm (CAS.Mixfix_term ts) = CAS.Mixfix_term ts'
           where ts' = map qualifyExVarsTerm ts
qualifyExVarsTerm (CAS.Mixfix_parenthesized ts r) = CAS.Mixfix_parenthesized ts' r
           where ts' = map qualifyExVarsTerm ts
qualifyExVarsTerm (CAS.Mixfix_bracketed ts r) = CAS.Mixfix_bracketed ts' r
           where ts' = map qualifyExVarsTerm ts
qualifyExVarsTerm (CAS.Mixfix_braced ts r) = CAS.Mixfix_braced ts' r
           where ts' = map qualifyExVarsTerm ts
qualifyExVarsTerm t = t

-- | qualifies a list of variables with the suffix "_ex" to
-- distinguish them from the variables already bound
qualifyExVars :: [CAS.VAR_DECL] -> [CAS.VAR_DECL]
qualifyExVars = map qualifyExVar

-- | qualifies a variable with the suffix "_ex" to distinguish it from
-- the variables already bound
qualifyExVar :: CAS.VAR_DECL -> CAS.VAR_DECL
qualifyExVar (CAS.Var_decl vars s r) = CAS.Var_decl vars' s r
     where vars' = map qualifyExVarAux vars

-- | qualifies a token with the suffix "_ex"
qualifyExVarAux :: Token -> Token
qualifyExVarAux var = mkSimpleId $ show var ++ "_ex"

-- | creates a list of strong equalities from two lists of terms
createEqs :: [CAS.CASLTERM] -> [CAS.CASLTERM] -> [CAS.CASLFORMULA]
createEqs (t1 : ts1) (t2 : ts2) = CAS.Strong_equation t1 t2 nullRange : ls
      where ls = createEqs ts1 ts2
createEqs _ _ = []

-- | extracts the operator at the top and the arguments of the lefthand side
-- in a strong equation
getLeftApp :: CAS.CASLFORMULA -> Maybe (CAS.OP_SYMB, [CAS.CASLTERM], [CAS.CASLFORMULA])
getLeftApp (CAS.Strong_equation term _ _) = case getLeftAppTerm term of
                    Nothing -> Nothing
                    Just (op, ts) -> Just (op, ts, [])
getLeftApp (CAS.Implication prem concl _ _) = case getLeftApp concl of
                    Nothing -> Nothing
                    Just (op, ts, _) -> Just (op, ts, conds)
        where conds = getPremisesImplication prem
getLeftApp _ = Nothing

-- | extracts the operator at the top and the arguments of the lefthand side
-- in an application term
getLeftAppTerm :: CAS.CASLTERM -> Maybe (CAS.OP_SYMB, [CAS.CASLTERM])
getLeftAppTerm (CAS.Application op ts _) = Just (op, ts)
getLeftAppTerm _ = Nothing

-- | extracts the formulas of the given premise, distinguishing whether it is
-- a conjunction or not
getPremisesImplication :: CAS.CASLFORMULA -> [CAS.CASLFORMULA]
getPremisesImplication (CAS.Conjunction forms _) = forms
getPremisesImplication form = [form]

-- | translate a Maude membership into a CASL formula
mb2formula :: IdMap -> MAS.Membership -> CAS.CASLFORMULA
mb2formula im (MAS.Mb t s [] _) = quantifyUniversally form
      where ct = maudeTerm2caslTerm im t
            s' = token2id $ getName s
            form = CAS.Membership ct s' nullRange
mb2formula im (MAS.Mb t s conds@(_ : _) _) = quantifyUniversally form
      where ct = maudeTerm2caslTerm im t
            s' = token2id $ getName s
            conds_form = conds2formula im conds
            concl_form = CAS.Membership ct s' nullRange
            form = CAS.Implication conds_form concl_form True nullRange

-- | translate a Maude rule into a CASL formula
rl2formula :: IdMap -> MAS.Rule -> CAS.CASLFORMULA
rl2formula im (MAS.Rl t t' [] _) = quantifyUniversally form
       where ty = token2id $ getName $ MAS.getTermType t
             kind = Map.findWithDefault (errorId "rl to formula") ty im
             pred_type = CAS.Pred_type [kind, kind] nullRange
             pred_name = CAS.Qual_pred_name rewID pred_type nullRange
             ct = maudeTerm2caslTerm im t
             ct' = maudeTerm2caslTerm im t'
             form = CAS.Predication pred_name [ct, ct'] nullRange
rl2formula im (MAS.Rl t t' conds@(_:_) _) = quantifyUniversally form
       where ty = token2id $ getName $ MAS.getTermType t
             kind = Map.findWithDefault (errorId "rl to formula") ty im
             pred_type = CAS.Pred_type [kind, kind] nullRange
             pred_name = CAS.Qual_pred_name rewID pred_type nullRange
             ct = maudeTerm2caslTerm im t
             ct' = maudeTerm2caslTerm im t'
             conds_form = conds2formula im conds
             concl_form = CAS.Predication pred_name [ct, ct'] nullRange
             form = CAS.Implication conds_form concl_form True nullRange

-- | translate a conjunction of Maude conditions to a CASL formula
conds2formula :: IdMap -> [MAS.Condition] -> CAS.CASLFORMULA
conds2formula im conds = CAS.Conjunction forms nullRange
        where forms = map (cond2formula im) conds

-- | translate a single Maude condition to a CASL formula
cond2formula :: IdMap -> MAS.Condition -> CAS.CASLFORMULA
cond2formula im (MAS.EqCond t t') = CAS.Strong_equation ct ct' nullRange
       where ct = maudeTerm2caslTerm im t
             ct' = maudeTerm2caslTerm im t'
cond2formula im (MAS.MatchCond t t') = CAS.Strong_equation ct ct' nullRange
       where ct = maudeTerm2caslTerm im t
             ct' = maudeTerm2caslTerm im t'
cond2formula im (MAS.MbCond t s) = CAS.Predication pred_name [ct] nullRange
      where ct = maudeTerm2caslTerm im t
            s' = token2id $ getName s
            kind = Map.findWithDefault (errorId "mb cond to formula") s' im
            pred_type = CAS.Pred_type [kind] nullRange
            pred_name = CAS.Qual_pred_name s' pred_type nullRange
cond2formula im (MAS.RwCond t t') = CAS.Predication pred_name [ct, ct'] nullRange
       where ct = maudeTerm2caslTerm im t
             ct' = maudeTerm2caslTerm im t'
             ty = token2id $ getName $ MAS.getTermType t
             kind = Map.findWithDefault (errorId "rw cond to formula") ty im
             pred_type = CAS.Pred_type [kind, kind] nullRange
             pred_name = CAS.Qual_pred_name rewID pred_type nullRange

-- | translates a Maude term into a CASL term
maudeTerm2caslTerm :: IdMap -> MAS.Term -> CAS.CASLTERM
maudeTerm2caslTerm im (MAS.Var q ty) = CAS.Qual_var q ty' nullRange
        where ty' = maudeType2caslSort ty im
maudeTerm2caslTerm im (MAS.Const q ty) = CAS.Application op [] nullRange
        where name = token2id q
              ty' = maudeType2caslSort ty im
              op_type = CAS.Op_type CAS.Total [] ty' nullRange
              op = CAS.Qual_op_name name op_type nullRange
maudeTerm2caslTerm im (MAS.Apply q ts ty) = CAS.Application op tts nullRange
        where name = token2id q
              tts = map (maudeTerm2caslTerm im) ts
              ty' = maudeType2caslSort ty im
              types_tts = getTypes tts
              op_type = CAS.Op_type CAS.Total types_tts ty' nullRange
              op = CAS.Qual_op_name name op_type nullRange

maudeSymbol2caslSort :: MSym.Symbol -> IdMap -> CAS.SORT
maudeSymbol2caslSort (MSym.Sort q) im = Map.findWithDefault err q' im -- token2id q
      where q' = token2id q
            err = errorId "error translate symbol"
maudeSymbol2caslSort (MSym.Kind q) im = Map.findWithDefault err q' im
      where q' = token2id q
            err = errorId "error translate symbol"
maudeSymbol2caslSort _ _ = errorId "error translate symbol"

maudeType2caslSort :: MAS.Type -> IdMap -> CAS.SORT
maudeType2caslSort (MAS.TypeSort q) im = Map.findWithDefault err q' im -- token2id $ getName q
      where q' = token2id $ getName q
            err = errorId "error translate type"
maudeType2caslSort (MAS.TypeKind q) im = Map.findWithDefault err q' im
      where q' = token2id $ getName q
            err = errorId "error translate type"

-- | obtains the types of the given terms
getTypes :: [CAS.CASLTERM] -> [Id]
getTypes = mapMaybe getType

-- | extracts the type of the temr
getType :: CAS.CASLTERM -> Maybe Id
getType (CAS.Qual_var _ kind _) = Just kind
getType (CAS.Application op _ _) = case op of
            CAS.Qual_op_name _ (CAS.Op_type _ _ kind _) _ -> Just kind
            _ -> Nothing
getType _ = Nothing

-- | generates the formulas for the rewrite predicates 
rewPredicatesSens :: Set.Set Id -> [Named CAS.CASLFORMULA]
rewPredicatesSens = Set.fold rewPredicateSens []

-- | generates the formulas for the rewrite predicate of the given sort
rewPredicateSens :: Id -> [Named CAS.CASLFORMULA] -> [Named CAS.CASLFORMULA]
rewPredicateSens kind acc = ref : trans : acc
        where ref = reflSen kind
              trans = transSen kind

-- | creates the reflexivity predicate for the given kind
reflSen :: Id -> Named CAS.CASLFORMULA
reflSen kind = makeNamed name $ quantifyUniversally form
        where v = newVar kind
              pred_type = CAS.Pred_type [kind, kind] nullRange
              pn = CAS.Qual_pred_name rewID pred_type nullRange
              form = CAS.Predication pn [v, v] nullRange
              name = "rew_refl_" ++ show kind

-- | creates the transitivity predicate for the given kind
transSen :: Id -> Named CAS.CASLFORMULA
transSen kind = makeNamed name $ quantifyUniversally form
        where v1 = newVarIndex 1 kind
              v2 = newVarIndex 2 kind
              v3 = newVarIndex 3 kind
              pred_type = CAS.Pred_type [kind, kind] nullRange
              pn = CAS.Qual_pred_name rewID pred_type nullRange
              prem1 = CAS.Predication pn [v1, v2] nullRange
              prem2 = CAS.Predication pn [v2, v3] nullRange
              concl = CAS.Predication pn [v1, v3] nullRange
              conj_form = CAS.Conjunction [prem1, prem2] nullRange
              form = CAS.Implication conj_form concl True nullRange
              name = "rew_trans_" ++ show kind

-- | generate the predicates for the rewrites
rewPredicates :: Set.Set Id -> Map.Map Id (Set.Set CSign.PredType)
rewPredicates = Set.fold rewPredicate Map.empty

-- | generate the predicates for the rewrites of the given sort
rewPredicate :: Id -> Map.Map Id (Set.Set CSign.PredType)
                -> Map.Map Id (Set.Set CSign.PredType)
rewPredicate kind m = Map.insertWith (Set.union) rewID ar m
   where ar = Set.singleton $ CSign.PredType [kind, kind]

-- | create the predicates that assign sorts to each term
kindPredicates :: IdMap -> Map.Map Id (Set.Set CSign.PredType)
kindPredicates = Map.foldWithKey kindPredicate Map.empty

-- | create the predicates that assign the current sort to the
-- corresponding terms
kindPredicate :: Id -> Id -> Map.Map Id (Set.Set CSign.PredType)
                 -> Map.Map Id (Set.Set CSign.PredType)
kindPredicate sort kind mis = case sort == (str2id "Universal") of
                  True -> mis
                  False -> let ar = Set.singleton $ CSign.PredType [kind]
                           in Map.insertWith (Set.union) sort ar mis

-- | extract the kinds from the map of id's
kindsFromMap :: IdMap -> Set.Set Id
kindsFromMap = Map.fold Set.insert Set.empty

-- | return a map where each sort is mapped to its kind, both of them
-- already converted to Id
arrangeKinds :: MSign.SortSet -> MSign.SubsortRel -> IdMap
arrangeKinds ss _ = Map.fromList l'
       where l = Set.toList ss
             l' = map arrangeSortKind l

arrangeSortKind :: MSym.Symbol -> (Id, Id)
arrangeSortKind s = (i, kindId i)
       where i = sort2id [s]

-- | return a map where each sort is mapped to its kind, both of them
-- already converted to Id
arrangeKinds2 :: MSign.SortSet -> MSign.SubsortRel -> IdMap
arrangeKinds2 ss r = arrangeKindsList (Set.toList ss) r Map.empty

-- | traverse the sorts and creates a table that assigns to each sort its kind
arrangeKindsList :: [MSym.Symbol] -> MSign.SubsortRel -> IdMap -> IdMap
arrangeKindsList [] _ m = m
arrangeKindsList l@(s : _) r m = arrangeKindsList not_rel r m'
      where tops = List.sort $ getTop r s
            tc = Rel.transClosure r
            (rel, not_rel) = sameKindList s tc l
            f = \ x y z -> Map.insert (sym2id y) (kindId $ sort2id x) z
            m' = foldr (f tops) m rel

-- | creates two list distinguishing in the first componente the symbols
-- with the same kind than the given one and in the second one the
-- symbols with different kind
sameKindList :: MSym.Symbol -> MSign.SubsortRel -> [MSym.Symbol]
                -> ([MSym.Symbol], [MSym.Symbol])
sameKindList _ _ [] = ([], [])
sameKindList t r (t' : ts) = if MSym.sameKind r t t'
                       then (t' : hold, not_hold)
                       else (hold, t' : not_hold)
      where (hold, not_hold) = sameKindList t r ts

-- | transform the set of Maude sorts in a set of CASL sorts, including
-- only one sort for each kind.
sortsTranslation :: MSign.SortSet -> MSign.SubsortRel -> Set.Set Id
sortsTranslation ss r = sortsTranslationList (Set.toList ss) r

-- | transform a list representing the Maude sorts in a set of CASL sorts,
-- including only one sort for each kind.
sortsTranslationList :: [MSym.Symbol] -> MSign.SubsortRel -> Set.Set Id
sortsTranslationList [] _ = Set.empty
sortsTranslationList (s : ss) r = Set.insert (sort2id tops) res
      where tops@(top : _) = List.sort $ getTop r s
            ss' = deleteRelated ss top r
            res = sortsTranslation ss' r

-- | return the maximal elements from the sort relation 
getTop :: MSign.SubsortRel -> MSym.Symbol -> [MSym.Symbol]
getTop r tok = case succs of
           [] -> [tok]
           toks@(_:_) -> foldr ((++) . (getTop r)) [] toks
      where succs = Set.toList $ Rel.succs r tok

-- | delete from the list of sorts those in the same kind that the parameter
deleteRelated :: [MSym.Symbol] -> MSym.Symbol -> MSign.SubsortRel -> MSign.SortSet
deleteRelated ss sym r = foldr (f sym tc) Set.empty ss
      where tc = Rel.transClosure r
            f = \ sort trC x y -> if MSym.sameKind trC sort x
                                  then y
                                  else Set.insert x y

-- | build an Id from a token with the function mkId
token2id :: Token -> Id
token2id t = mkId ts
    where ts = maudeSymbol2validCASLSymbol t

-- | build an Id from a Maude symbol
sym2id :: MSym.Symbol -> Id
sym2id = token2id . getName

-- | generates an Id from a string
str2id :: String -> Id
str2id = token2id . mkSimpleId

-- | build an Id from a list of sorts, taking the first from the ordered list
sort2id :: [MSym.Symbol] -> Id
sort2id syms = mkId sym''
     where sym = head $ List.sort syms
           sym' = getName sym
           sym'' = maudeSymbol2validCASLSymbol sym'

-- | add universal quantification of all variables in the formula
quantifyUniversally :: CAS.CASLFORMULA -> CAS.CASLFORMULA
quantifyUniversally form = if null var_decl
                           then form
                           else CAS.Quantification CAS.Universal var_decl form nullRange
      where vars = getVars form
            var_decl = listVarDecl vars

-- | traverses a map with sorts as keys and sets of variables as value and creates
-- a list of variable declarations
listVarDecl :: Map.Map Id (Set.Set Token) -> [CAS.VAR_DECL]
listVarDecl = Map.foldWithKey f []
      where f = \ sort var_set acc -> CAS.Var_decl (Set.toList var_set) sort nullRange : acc

-- | removes a quantification from a formula
noQuantification :: CAS.CASLFORMULA -> (CAS.CASLFORMULA, [CAS.VAR_DECL])
noQuantification (CAS.Quantification _ vars form _) = (form, vars)
noQuantification form = (form, [])

-- | translate the CASL sorts to symbols
kinds2syms :: Set.Set Id -> Set.Set CSign.Symbol
kinds2syms = Set.map kind2sym 

-- | translate a CASL sort to a CASL symbol
kind2sym :: Id -> CSign.Symbol
kind2sym k = CSign.Symbol k CSign.SortAsItemType

-- | translates the CASL predicates into CASL symbols
preds2syms :: Map.Map Id (Set.Set CSign.PredType) -> Set.Set CSign.Symbol
preds2syms = Map.foldWithKey pred2sym Set.empty

-- | translates a CASL predicate into a CASL symbol
pred2sym :: Id -> Set.Set CSign.PredType -> Set.Set CSign.Symbol -> Set.Set CSign.Symbol
pred2sym pn spt acc = Set.fold (createSym4id pn) acc spt

-- | creates a CASL symbol for a predicate
createSym4id :: Id -> CSign.PredType -> Set.Set CSign.Symbol -> Set.Set CSign.Symbol
createSym4id pn pt acc = Set.insert sym acc
      where sym = CSign.Symbol pn $ CSign.PredAsItemType pt

-- | translates the CASL operators into CASL symbols
ops2symbols :: CSign.OpMap -> Set.Set CSign.Symbol
ops2symbols = Map.foldWithKey op2sym Set.empty

-- | translates a CASL operator into a CASL symbol
op2sym :: Id -> Set.Set CSign.OpType -> Set.Set CSign.Symbol -> Set.Set CSign.Symbol
op2sym on sot acc = Set.union set acc
      where set = Set.fold (createSymOp4id on) Set.empty sot

-- | creates a CASL symbol for an operator
createSymOp4id :: Id -> CSign.OpType -> Set.Set CSign.Symbol -> Set.Set CSign.Symbol
createSymOp4id on ot acc = Set.insert sym acc
      where sym = CSign.Symbol on $ CSign.OpAsItemType ot

-- | extract the variables from a CASL formula and put them in a map
-- with keys the sort of the variables and value the set of variables
-- in this sort
getVars :: CAS.CASLFORMULA -> Map.Map Id (Set.Set Token)
getVars (CAS.Quantification _ _ f _) = getVars f
getVars (CAS.Conjunction fs _) = foldr (Map.unionWith (Set.union) . getVars) Map.empty fs
getVars (CAS.Disjunction fs _) = foldr (Map.unionWith (Set.union) . getVars) Map.empty fs
getVars (CAS.Implication f1 f2 _ _) = Map.unionWith (Set.union) v1 v2
     where v1 = getVars f1
           v2 = getVars f2
getVars (CAS.Equivalence f1 f2 _) = Map.unionWith (Set.union) v1 v2
     where v1 = getVars f1
           v2 = getVars f2
getVars (CAS.Negation f _) = getVars f
getVars (CAS.Predication _ ts _) = foldr (Map.unionWith (Set.union) . getVarsTerm) Map.empty ts
getVars (CAS.Definedness t _) = getVarsTerm t
getVars (CAS.Existl_equation t1 t2 _) = Map.unionWith (Set.union) v1 v2
     where v1 = getVarsTerm t1
           v2 = getVarsTerm t2
getVars (CAS.Strong_equation t1 t2 _) = Map.unionWith (Set.union) v1 v2
     where v1 = getVarsTerm t1
           v2 = getVarsTerm t2
getVars (CAS.Membership t _ _) = getVarsTerm t
getVars (CAS.Mixfix_formula t) = getVarsTerm t
getVars _ = Map.empty

-- | extract the variables of a CASL term
getVarsTerm :: CAS.CASLTERM -> Map.Map Id (Set.Set Token)
getVarsTerm (CAS.Qual_var var sort _) = Map.insert sort (Set.singleton var) Map.empty
getVarsTerm (CAS.Application _ ts _) = foldr (Map.unionWith (Set.union) . getVarsTerm) Map.empty ts
getVarsTerm (CAS.Sorted_term t _ _) = getVarsTerm t
getVarsTerm (CAS.Cast t _ _) = getVarsTerm t
getVarsTerm (CAS.Conditional t1 f t2 _) = Map.unionWith (Set.union) v3 m
     where v1 = getVarsTerm t1
           v2 = getVarsTerm t2
           v3 = getVars f
           m = Map.unionWith (Set.union) v1 v2
getVarsTerm (CAS.Mixfix_term ts) = foldr (Map.unionWith (Set.union) . getVarsTerm) Map.empty ts
getVarsTerm (CAS.Mixfix_parenthesized ts _) = 
                   foldr (Map.unionWith (Set.union) . getVarsTerm) Map.empty ts
getVarsTerm (CAS.Mixfix_bracketed ts _) = 
                   foldr (Map.unionWith (Set.union) . getVarsTerm) Map.empty ts
getVarsTerm (CAS.Mixfix_braced ts _) =
                   foldr (Map.unionWith (Set.union) . getVarsTerm) Map.empty ts
getVarsTerm _ = Map.empty

-- | generates the constructor constraint
ctorSen :: Bool -> GenAx -> Named CAS.CASLFORMULA
ctorSen isFree (sorts, _, ops) = do
    let sortList = Set.toList sorts
        opSyms = map ( \ c -> let ide = compId c in CAS.Qual_op_name ide
                      (CSign.toOP_TYPE $ compType c) $ posOfId ide) $ Set.toList ops
        allSyms = opSyms
        resType _ (CAS.Op_name _) = False
        resType s (CAS.Qual_op_name _ t _) = CAS.res_OP_TYPE t == s
        getIndex s = maybe (-1) id $ List.findIndex (== s) sortList
        addIndices (CAS.Op_name _) =
          error "CASL/StaticAna: Internal error in function addIndices"
        addIndices os@(CAS.Qual_op_name _ t _) =
            (os,map getIndex $ CAS.args_OP_TYPE t)
        collectOps s =
          CAS.Constraint s (map addIndices $ filter (resType s) allSyms) s
        constrs = map collectOps sortList
        f = CAS.Sort_gen_ax constrs isFree
    makeNamed ("ga_generated_" ++ showSepList (showString "_") showId sortList "") f

-- | transforms a maude identifier into a valid CASL identifier
maudeSymbol2validCASLSymbol :: Token -> [Token]
maudeSymbol2validCASLSymbol t = splitDoubleUnderscores str ""
    where str = ms2vcs $ show t

-- | transforms a string coding a Maude identifier into another string
-- representing a CASL identifier
ms2vcs :: String -> String
ms2vcs s@('k' : 'i' : 'n' : 'd' : '_' : _) = s
ms2vcs s = case Map.member s stringMap of
    True -> Map.findWithDefault "" s stringMap
    False -> let f = \ x y -> if Map.member x charMap
                              then (charMap Map.! x) ++ ['\''] ++ y
                              else if x == '_'
                                   then "__" ++ y
                                   else x : y
             in foldr f [] s

-- | map of reserved words
stringMap :: Map.Map String String
stringMap = Map.fromList 
    [("true", "maudeTrue"),
     ("false", "maudeFalse"),
     ("not_", "neg__"),
     ("s_", "suc"),
     ("_+_", "__+__"),
     ("_*_", "__*__"),
     ("_<_", "__<__"),
     ("_<=_", "__<=__"),
     ("_>_", "__>__"),
     ("_>=_", "__>=__"),
     ("_and_", "__maudeAnd__")]

-- | splits the string into a list of tokens, separating the double
-- underscores from the rest of characters
splitDoubleUnderscores :: String -> String -> [Token]
splitDoubleUnderscores [] acc = if null acc
                                then []
                                else [mkSimpleId acc]
splitDoubleUnderscores ('_' : '_' : cs) acc = if null acc
                                              then dut : rest
                                              else acct : dut : rest
     where acct = mkSimpleId acc
           dut = mkSimpleId "__"
           rest = splitDoubleUnderscores cs []
splitDoubleUnderscores (c : cs) acc = splitDoubleUnderscores cs (acc ++ [c])
           

-- | error Id
errorId :: String -> Id
errorId s = token2id $ mkSimpleId $ "ERROR: " ++ s

kindId :: Id -> Id
kindId i = token2id $ mkSimpleId $ "kind_" ++ show i

-- | generates an implication formula with the constraints produced by
-- the sorts of the variables
varsImp :: MSentence.Sentence -> IdMap -> CAS.CASLFORMULA -> CAS.CASLFORMULA
varsImp sen im form = createImpForm imp_form form
      where forms = varsImplication sen im
            forms' = deleteDuplicated forms form
            imp_form = createConjForm forms'

deleteDuplicated :: [CAS.CASLFORMULA] -> CAS.CASLFORMULA -> [CAS.CASLFORMULA]
deleteDuplicated fs (CAS.Implication f _ True _) = deleteDuplicatedAux fs f
deleteDuplicated fs (CAS.Implication _ f False _) = deleteDuplicatedAux fs f
deleteDuplicated fs _ = fs

deleteDuplicatedAux :: [CAS.CASLFORMULA] -> CAS.CASLFORMULA -> [CAS.CASLFORMULA]
deleteDuplicatedAux fs (CAS.Conjunction fs' _) = filter (\ x -> not $ elem x fs') fs
deleteDuplicatedAux fs f = filter (\ x -> not $ elem x [f]) fs

-- | generates the implication obtained from the implicit information given
-- in Maude variables
varsImplication :: MSentence.Sentence -> IdMap -> [CAS.CASLFORMULA]
varsImplication (MSentence.Membership mb) im = forms
      where MAS.Mb t _ conds _ = mb
            formsTerm = varsImpTerm im t
            formsCond = varsImpConds im conds
            forms = Set.toList $ Set.union formsTerm formsCond
varsImplication (MSentence.Equation eq) im = forms
      where MAS.Eq t _ conds _ = eq
            formsTerm = varsImpTerm im t
            formsCond = varsImpConds im conds
            forms = Set.toList $ Set.union formsTerm formsCond
varsImplication (MSentence.Rule rl) im = forms
      where MAS.Rl t _ conds _ = rl
            formsTerm = varsImpTerm im t
            formsCond = varsImpConds im conds
            forms = Set.toList $ Set.union formsTerm formsCond

-- | computes the predicates with the information associated to the variables in
-- matching conditions
varsImpConds :: IdMap -> [MAS.Condition] -> Set.Set CAS.CASLFORMULA
varsImpConds im = foldr (Set.union . (varsImpCond im)) Set.empty

-- | auxiliary function that computes the predicates with the information associated 
-- to the variables in matching conditions
varsImpCond :: IdMap -> MAS.Condition -> Set.Set CAS.CASLFORMULA
varsImpCond im (MAS.MatchCond t _) = varsImpTerm im t
varsImpCond im (MAS.RwCond _ t) = varsImpTerm im t
varsImpCond _ _ = Set.empty

-- | computes the predicates with the information associated to the variables in
-- the terms
varsImpTerms :: IdMap -> [MAS.Term] -> Set.Set CAS.CASLFORMULA
varsImpTerms im = foldr (Set.union . (varsImpTerm im)) Set.empty

-- | computes the predicates with the information associated to the variables in
-- a term
varsImpTerm :: IdMap -> MAS.Term -> Set.Set CAS.CASLFORMULA
varsImpTerm im t@(MAS.Var _ (MAS.TypeSort s)) = 
                                  Set.singleton $ CAS.Membership t' sort nullRange
      where sort = token2id $ getName s
            t' = maudeTerm2caslTerm im t
-- The variable is declared on the kind
varsImpTerm _ (MAS.Var _ _) = Set.empty
varsImpTerm im (MAS.Apply _ terms _) = varsImpTerms im terms
varsImpTerm _ _ = Set.empty
