

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

import Common.Id
import Common.Result
import Common.AS_Annotation
import qualified Common.Lib.Rel as Rel

type IdMap = Map.Map Id Id

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
         in Result [] $ Just $ CMorphism.Morphism src' tgt' smap' omap' pmap ()

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
             g = \ x -> fromJust $ Map.lookup (f x) im
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
                 kind = fromJust $ Map.lookup sym_id mk
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
maudeSort2caslId im sym = fromJust $ Map.lookup (token2id $ getName sym) im

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
                 kind = fromJust $ Map.lookup id_from im
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
mapSentence sg sen@(MSentence.Equation eq) = case owise ats of
             False -> Result [] $ Just $ sentence $ noOwiseSen2Formula mk named
             True -> let
                       sg_sens = map (makeNamed "") $ Set.toList $ MSign.sentences sg
                       (no_owise_sens, _, _) = splitOwiseEqs sg_sens
                       no_owise_forms = map (noOwiseSen2Formula mk) no_owise_sens
                       trans = sentence $ owiseSen2Formula mk no_owise_forms named
                     in Result [] $ Just trans
          where mk = arrangeKinds (MSign.sorts sg) (MSign.subsorts sg)
                MAS.Eq _ _ _ ats = eq
                named = makeNamed "" sen
mapSentence sg sen@(MSentence.Membership mb) = Result [] $ Just $ sentence form
          where mk = arrangeKinds (MSign.sorts sg) (MSign.subsorts sg)
                MAS.Mb _ _ _ _ = mb
                named = makeNamed "" sen
                form = mb_rl2formula mk named
mapSentence sg sen@(MSentence.Rule rl) = Result [] $ Just $ sentence form
          where mk = arrangeKinds (MSign.sorts sg) (MSign.subsorts sg)
                MAS.Rl _ _ _ _ = rl
                named = makeNamed "" sen
                form = mb_rl2formula mk named

-- | applies maude2casl to compute the CASL signature and sentences from
-- the Maude ones, and wraps them into a Result datatype
mapTheory :: (MSign.Sign, [Named MSentence.Sentence]) 
              -> Result (CSign.CASLSign, [Named CAS.CASLFORMULA])
mapTheory (sg, nsens) = Result [] $ Just $ maude2casl sg nsens

-- | computes new signature and sentences of CASL associated to the
-- given Maude signature and sentences
maude2casl :: MSign.Sign -> [Named MSentence.Sentence]
              -> (CSign.CASLSign, [Named CAS.CASLFORMULA])
maude2casl msign nsens = (csign { CSign.sortSet = cs,
                            CSign.emptySortSet = cs,
                            CSign.opMap = cops,
                            CSign.assocOps = assoc_ops,
                            CSign.predMap = preds,
                            CSign.declaredSymbols = syms }, new_sens)
   where csign = CSign.emptySign ()
         mk = arrangeKinds (MSign.sorts msign) (MSign.subsorts msign)
         cs = kindsFromMap mk
         ks = kindPredicates mk
         rp = rewPredicates ks cs
         ops = MSign.ops msign
         ksyms = kinds2syms cs
         (cops, assoc_ops, ops_forms) = translateOps mk ops
         ops_syms = ops2symbols cops
         pred_sens = subsortSens mk (Rel.toList $ MSign.subsorts msign)
         named_sens = map (makeNamed "") pred_sens
         sg_sens = map (makeNamed "") $ Set.toList $ MSign.sentences msign
         (no_owise_sens, owise_sens, mbs_rls_sens) = splitOwiseEqs (nsens ++ sg_sens)
         no_owise_forms = map (noOwiseSen2Formula mk) no_owise_sens
         owise_forms = map (owiseSen2Formula mk no_owise_forms) owise_sens
         mb_rl_forms = map (mb_rl2formula mk) mbs_rls_sens
         preds = Map.unionWith (Set.union) ks rp
         preds_syms = preds2syms preds
         syms = Set.union ksyms $ Set.union ops_syms preds_syms
         new_sens = ops_forms ++ named_sens ++ no_owise_forms ++ owise_forms ++ mb_rl_forms

-- | translates the Maude operator map into a tuple of CASL operators, CASL
-- associative operators and the formulas generated by the operator attributes
-- and the membership induced from each Maude operator
translateOps :: IdMap -> MSign.OpMap -> (CSign.OpMap, CSign.OpMap, [Named CAS.CASLFORMULA])
translateOps im = Map.fold (translateOpDeclSet im) (Map.empty, Map.empty, [])

-- | translates an operator declaration set into a tern as described above
translateOpDeclSet :: IdMap -> MSign.OpDeclSet 
                      -> (CSign.OpMap, CSign.OpMap, [Named CAS.CASLFORMULA])
                      -> (CSign.OpMap, CSign.OpMap, [Named CAS.CASLFORMULA])
translateOpDeclSet im ods tpl = Set.fold (translateOpDecl im) tpl ods

translateOpDecl :: IdMap -> MSign.OpDecl
                   -> (CSign.OpMap, CSign.OpMap, [Named CAS.CASLFORMULA])
                   -> (CSign.OpMap, CSign.OpMap, [Named CAS.CASLFORMULA])
translateOpDecl im (syms, ats) (ops, assoc_ops, forms) = (ops', assoc_ops', forms6)
      where predOps = ops2pred im syms
            (sym : _) = Set.toList syms
            (cop_id, ot) = fromJust $ maudeSym2CASLOp im sym
            cop_type = Set.singleton ot
            forms' = forms ++ predOps
            ops' = Map.insertWith (Set.union) cop_id cop_type ops
            assoc_ops' = if assoc ats
                         then Map.insertWith (Set.union) cop_id cop_type assoc_ops
                         else assoc_ops
            op_name = CAS.Op_name cop_id
            forms1 = if assoc ats
                     then forms'
                     else let assoc_f = associativeSen op_name (head $ CSign.opArgs ot)
                          in makeNamed "" assoc_f : forms'
            forms2 = if comm ats
                     then forms1
                     else let comm_f = commutativeSen op_name (head $ CSign.opArgs ot)
                          in makeNamed "" comm_f : forms1
            forms3 = if idem ats
                     then forms2
                     else let idem_f = idempotentSen op_name (head $ CSign.opArgs ot)
                          in makeNamed "" idem_f : forms2
            forms4 = if identity ats
                     then forms3
                     else let iden = maudeTerm2caslTerm im $ fromJust $ getIdentity ats
                              identity_f = identitySens op_name (head $ CSign.opArgs ot) iden
                          in map (makeNamed "") identity_f ++ forms3
            forms5 = if leftId ats
                     then forms4
                     else let lid = maudeTerm2caslTerm im $ fromJust $ getIdentity ats
                              lid_f = left_identitySen op_name (head $ CSign.opArgs ot) lid
                          in makeNamed "" lid_f : forms4
            forms6 = if rightId ats
                     then forms5
                     else let rid = maudeTerm2caslTerm im $ fromJust $ getIdentity ats
                              rid_f = right_identitySen op_name (head $ CSign.opArgs ot) rid
                          in makeNamed "" rid_f : forms5

-- | translates a Maude operator symbol into a pair with the id of the operator
-- and its CASL type
maudeSym2CASLOp :: IdMap -> MSym.Symbol -> Maybe (Id, CSign.OpType)
maudeSym2CASLOp im (MSym.Operator op ar co) = Just (token2id op, ot)
      where f = token2id . getName
            g = \ x -> fromJust $ Map.lookup (f x) im
            ot = CSign.OpType CAS.Total (map g ar) (g co)
maudeSym2CASLOp _ _ = Nothing

-- | generates the predicates associated to each operator declaration in Maude
-- due to the associated membership if the coarity is a sort and not a kind
ops2pred :: IdMap -> MSym.SymbolSet -> [Named CAS.CASLFORMULA]
ops2pred im = Set.fold (op2pred im) []

-- | generates the memebership predicate associated to an operator
op2pred :: IdMap -> MSym.Symbol -> [Named CAS.CASLFORMULA] -> [Named CAS.CASLFORMULA]
op2pred im (MSym.Operator op ar co) acc = case co of
                  MSym.Sort s -> let 
                             op' = CAS.Op_name $ token2id op
                             co' = token2id s
                             (vars, prems) = ops2predPremises im ar 0
                             pred_name = CAS.Pred_name co'
                             op_term = CAS.Application op' vars nullRange
                             op_pred = CAS.Predication pred_name [op_term] nullRange
                             conj_form = createConjForm prems
                             imp_form = if null prems
                                        then op_pred
                                        else CAS.Implication conj_form op_pred True nullRange
                             q_form = quantifyUniversally imp_form
                             final_form = makeNamed "" q_form
                                 in final_form : acc
                  _ -> acc
op2pred _ _ acc = acc

createConjForm :: [CAS.CASLFORMULA] -> CAS.CASLFORMULA
createConjForm [] = CAS.True_atom nullRange
createConjForm [a] = a
createConjForm fs = CAS.Conjunction fs nullRange

ops2predPremises :: IdMap -> [MSym.Symbol] -> Int -> ([CAS.CASLTERM], [CAS.CASLFORMULA])
ops2predPremises im (MSym.Sort s : ss) i = (var : terms, form : forms)
         where s' = token2id s
               kind = fromJust $ Map.lookup s' im
               pred_name = CAS.Pred_name s'
               var = newVarIndex i kind
               form = CAS.Predication pred_name [var] nullRange
               (terms, forms) = ops2predPremises im ss (i + 1)
ops2predPremises im (MSym.Kind k : ss) i = (var : terms, forms)
         where k' = token2id k
               kind = fromJust $ Map.lookup k' im
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
                     MSentence.Equation (MAS.Eq _ _ _ ats) -> case owise ats of
                                            True -> (no_owise_sens, s : owise_sens, mbs_rls)
                                            False -> (s : no_owise_sens, owise_sens, mbs_rls)
                     _ -> (no_owise_sens, owise_sens, s : mbs_rls)

-- | check if a list of attribute statements contains the owise attribute
owise :: [MAS.StmntAttr] -> Bool
owise [] = False
owise (a : as) = case a of
       MAS.Owise -> True
       _ -> owise as

-- | check if a list of attributes contains the assoc attribute
assoc :: [MAS.Attr] -> Bool
assoc [] = False
assoc (a : as) = case a of
       MAS.Assoc -> True
       _ -> assoc as

-- | check if a list of attributes contains the comm attribute
comm :: [MAS.Attr] -> Bool
comm [] = False
comm (a : as) = case a of
       MAS.Comm -> True
       _ -> comm as

-- | check if a list of attributes contains the idem attribute
idem :: [MAS.Attr] -> Bool
idem [] = False
idem (a : as) = case a of
       MAS.Idem -> True
       _ -> idem as

-- | check if a list of attributes contains the identity attribute
identity :: [MAS.Attr] -> Bool
identity [] = False
identity (a : as) = case a of
       MAS.Id _ -> True
       _ -> identity as

-- | check if a list of attributes contains the left identity attribute
leftId :: [MAS.Attr] -> Bool
leftId [] = False
leftId (a : as) = case a of
       MAS.LeftId _ -> True
       _ -> leftId as

-- | check if a list of attributes contains the right identity attribute
rightId :: [MAS.Attr] -> Bool
rightId [] = False
rightId (a : as) = case a of
       MAS.RightId _ -> True
       _ -> rightId as

-- | returns the identity term from the attribute set
getIdentity ::  [MAS.Attr] -> Maybe MAS.Term
getIdentity [] = Nothing
getIdentity (a : as) = case a of
       MAS.RightId t -> Just t
       _ -> getIdentity as

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

-- | create the CASL predicates derived from Maude subsort declarations 
subsortSens :: IdMap -> [(MSym.Symbol, MSym.Symbol)] -> [CAS.CASLFORMULA]
subsortSens im = map (subsortSen im)

-- | create a CASL predicate from a Maude subsort declaration 
subsortSen :: IdMap -> (MSym.Symbol, MSym.Symbol) -> CAS.CASLFORMULA
subsortSen im (sub, super) = quantifyUniversally form
    where sub' = getName sub
          super' = getName super
          kind = fromJust $ Map.lookup (token2id sub') im
          sub_pred_name = CAS.Pred_name $ token2id sub'
          super_pred_name = CAS.Pred_name $ token2id super'
          var = newVar kind
          sub_form = CAS.Predication sub_pred_name [var] nullRange
          super_form = CAS.Predication super_pred_name [var] nullRange
          form = CAS.Implication sub_form super_form True nullRange

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

-- | translate a Maude equation without the "owise" attribute into a CASL formula
noOwiseEq2Formula :: IdMap -> MAS.Equation -> CAS.CASLFORMULA
noOwiseEq2Formula im (MAS.Eq t t' [] _) = quantifyUniversally form
      where ct = maudeTerm2caslTerm im t
            ct' = maudeTerm2caslTerm im t'
            form = CAS.Strong_equation ct ct' nullRange
noOwiseEq2Formula im (MAS.Eq t t' conds@(_ : _) _) = quantifyUniversally form
      where ct = maudeTerm2caslTerm im t
            ct' = maudeTerm2caslTerm im t'
            conds_form = conds2formula im conds
            concl_form = CAS.Strong_equation ct ct' nullRange
            form = CAS.Implication conds_form concl_form True nullRange

-- | transforms a Maude equation defined with the otherwise attribute into
-- a CASL formula
owiseEq2Formula :: IdMap -> [Named CAS.CASLFORMULA] -> MAS.Equation
                   -> CAS.CASLFORMULA
owiseEq2Formula im no_owise_form eq = form
      where (eq_form, vars) = noQuantification $ noOwiseEq2Formula im eq
            (op, ts) = fromJust $ getLeftApp eq_form
            ex_form = existencialNegationOtherEqs op ts no_owise_form
            imp_form = CAS.Implication ex_form eq_form True nullRange
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
                            conj_form = CAS.Conjunction (createEqs ts' terms) nullRange
                            ex_form = if vars' /= []
                                      then CAS.Quantification CAS.Existential vars' conj_form nullRange
                                      else conj_form
                            neg_form = CAS.Negation ex_form nullRange
                          in [neg_form]
      where (inner_form, vars) = noQuantification $ sentence form
            vars' = qualifyExVars vars
            (op, ts) = fromJust $ getLeftApp inner_form
            ts' = qualifyExVarsTerms ts
            ok = req_op == op && length terms == length ts

-- | qualifies the variables in a list of terms with the suffix "_ex" to
-- distinguish them from the variables already bound
qualifyExVarsTerms :: [CAS.CASLTERM] -> [CAS.CASLTERM]
qualifyExVarsTerms = map qualifyExVarsTerm

-- | qualifies the variable in a term with the suffix "_ex" to distinguish them
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
getLeftApp :: CAS.CASLFORMULA -> Maybe (CAS.OP_SYMB, [CAS.CASLTERM])
getLeftApp (CAS.Strong_equation term _ _) = getLeftAppTerm term
getLeftApp _ = Nothing

-- | extracts the operator at the top and the arguments of the lefthand side
-- in an application term
getLeftAppTerm :: CAS.CASLTERM -> Maybe (CAS.OP_SYMB, [CAS.CASLTERM])
getLeftAppTerm (CAS.Application op ts _) = Just (op, ts)
getLeftAppTerm _ = Nothing

-- | translate a Maude membership into a CASL formula
mb2formula :: IdMap -> MAS.Membership -> CAS.CASLFORMULA
mb2formula im (MAS.Mb t s [] _) = quantifyUniversally form
      where ct = maudeTerm2caslTerm im t
            pred_name = CAS.Pred_name $ token2id $ getName s
            form = CAS.Predication pred_name [ct] nullRange
mb2formula im (MAS.Mb t s conds@(_ : _) _) = quantifyUniversally form
      where ct = maudeTerm2caslTerm im t
            pred_name = CAS.Pred_name $ token2id $ getName s
            conds_form = conds2formula im conds
            concl_form = CAS.Predication pred_name [ct] nullRange
            form = CAS.Implication conds_form concl_form True nullRange

-- | translate a Maude rule into a CASL formula
rl2formula :: IdMap -> MAS.Rule -> CAS.CASLFORMULA
rl2formula im (MAS.Rl t t' [] _) = quantifyUniversally form
       where ct = maudeTerm2caslTerm im t
             ct' = maudeTerm2caslTerm im t'
             pred_name = CAS.Pred_name rewID
             form = CAS.Predication pred_name [ct, ct'] nullRange
rl2formula im (MAS.Rl t t' conds@(_:_) _) = quantifyUniversally form
       where ct = maudeTerm2caslTerm im t
             ct' = maudeTerm2caslTerm im t'
             pred_name = CAS.Pred_name rewID
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
            pred_name = CAS.Pred_name $ token2id $ getName s
cond2formula im (MAS.RwCond t t') = CAS.Predication pred_name [ct, ct'] nullRange
       where ct = maudeTerm2caslTerm im t
             ct' = maudeTerm2caslTerm im t'
             pred_name = CAS.Pred_name rewID

-- | translate a Maude term into a CASL term
maudeTerm2caslTerm :: IdMap -> MAS.Term -> CAS.CASLTERM
maudeTerm2caslTerm im (MAS.Var q ty) = CAS.Qual_var q kind nullRange
        where kind = fromJust $ Map.lookup (token2id $ getName ty) im
maudeTerm2caslTerm _ (MAS.Const q _) = CAS.Application (CAS.Op_name name) [] nullRange
        where name = token2id q
maudeTerm2caslTerm im (MAS.Apply q ts _) = CAS.Application (CAS.Op_name name) tts nullRange
        where name = token2id q
              tts = map (maudeTerm2caslTerm im) ts

-- | generate the predicates
rewPredicates :: Map.Map Id (Set.Set CSign.PredType) -> Set.Set Id
                 -> Map.Map Id (Set.Set CSign.PredType)
rewPredicates m = Set.fold rewPredicate m

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
kindPredicate sort kind mis = Map.insertWith (Set.union) sort ar mis
   where ar = Set.singleton $ CSign.PredType [kind]

-- | extract the kinds from the map of id's
kindsFromMap :: IdMap -> Set.Set Id
kindsFromMap = Map.fold Set.insert Set.empty

-- | return a map where each sort is mapped to its kind, both of them
-- already converted to Id
arrangeKinds :: MSign.SortSet -> MSign.SubsortRel -> IdMap
arrangeKinds ss r = arrangeKindsList (Set.toList ss) r Map.empty

-- | traverse the sorts and creates a table that assigns to each sort its kind
arrangeKindsList :: [MSym.Symbol] -> MSign.SubsortRel -> IdMap -> IdMap
arrangeKindsList [] _ m = m
arrangeKindsList l@(s : _) r m = arrangeKindsList not_rel r m'
      where tops = List.sort $ getTop r s
            tc = Rel.transClosure r
            (rel, not_rel) = sameKindList s tc l
            f = \ x y z -> Map.insert (sym2id y) (sort2id x) z
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

-- | return a maximal element from the sort relation 
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
token2id t = mkId [t]

-- | build an Id from a Maude symbol
sym2id :: MSym.Symbol -> Id
sym2id = token2id . getName

-- | build an Id from a list of sorts, including the "[" and "," if needed
sort2id :: [MSym.Symbol] -> Id
sort2id syms = mkId tokens'
     where tokens = map getName syms
           tokens' = mkSimpleId "[" : (putCommas tokens) ++ [mkSimpleId "]"]

-- | inserts commas between tokens
putCommas :: [Token] -> [Token]
putCommas [] = []
putCommas [t] = [t]
putCommas (t : ts) = t : (mkSimpleId ",") : putCommas ts

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

-- | create the sentence to state that an operator is associative
associativeSen :: CAS.OP_SYMB -> Id -> CAS.CASLFORMULA
associativeSen op sort = quantifyUniversally form
      where v1 = newVarIndex 1 sort
            v2 = newVarIndex 2 sort
            v3 = newVarIndex 3 sort
            t1 = CAS.Application op [v2, v3] nullRange
            t = CAS.Application op [v1, t1] nullRange
            t2 = CAS.Application op [v1, v2] nullRange
            t' = CAS.Application op [t2, v3] nullRange
            form = CAS.Strong_equation t t' nullRange

-- | create the sentence to state that an operator is commutative
commutativeSen :: CAS.OP_SYMB -> Id -> CAS.CASLFORMULA
commutativeSen op sort = quantifyUniversally form
      where v1 = newVarIndex 1 sort
            v2 = newVarIndex 2 sort
            t = CAS.Application op [v1, v2] nullRange
            t' = CAS.Application op [v2, v1] nullRange
            form = CAS.Strong_equation t t' nullRange

-- | create the sentences to state that an operator has identity
identitySens :: CAS.OP_SYMB -> Id -> CAS.CASLTERM -> [CAS.CASLFORMULA]
identitySens op sort t = [form1, form2]
      where v = newVar sort
            t1 = CAS.Application op [v, t] nullRange
            t2 = CAS.Application op [t, v] nullRange
            form1 = quantifyUniversally $ CAS.Strong_equation t1 v nullRange
            form2 = quantifyUniversally $ CAS.Strong_equation t2 v nullRange

-- | create the sentences to state that an operator has left-identity
left_identitySen :: CAS.OP_SYMB -> Id -> CAS.CASLTERM -> CAS.CASLFORMULA
left_identitySen op sort t = form
      where v = newVar sort
            t' = CAS.Application op [t, v] nullRange
            form = quantifyUniversally $ CAS.Strong_equation t' v nullRange

-- | create the sentences to state that an operator has right-identity
right_identitySen :: CAS.OP_SYMB -> Id -> CAS.CASLTERM -> CAS.CASLFORMULA
right_identitySen op sort t = form
      where v = newVar sort
            t' = CAS.Application op [v, t] nullRange
            form = quantifyUniversally $ CAS.Strong_equation t' v nullRange

-- | create the sentences to state that an operator is idempotent
idempotentSen :: CAS.OP_SYMB -> Id -> CAS.CASLFORMULA
idempotentSen op sort = quantifyUniversally form
      where v1 = newVarIndex 1 sort
            v2 = newVarIndex 2 sort
            t = CAS.Application op [v1, v2] nullRange
            form = CAS.Strong_equation t v1 nullRange

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
pred2sym pn spt acc = Set.union set acc
      where set = Set.fold (createSym4id pn) Set.empty spt

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