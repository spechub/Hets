{- |
Module      :  ./TPTP/StaticAnalysis.hs
Description :  Static Analysis for TPTP.
Copyright   :  (c) Eugen Kuksa University of Magdeburg 2017
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Eugen Kuksa <kuksa@iks.cs.ovgu.de>
Stability   :  provisional
Portability :  portable

Static Analysis for TPTP.
-}

module TPTP.StaticAnalysis ( basicAnalysis
                           , signatureUnionR
                           , signOfSentence
                           ) where

import TPTP.AS
import TPTP.Sign
import TPTP.Morphism

import Common.AS_Annotation hiding (Name)
import Common.ExtSign
import Common.GlobalAnnotations
import Common.Id
import Common.Result

import qualified Data.Map as Map
import qualified Data.Set as Set

import Debug.Trace

basicAnalysis :: (BASIC_SPEC, Sign, GlobalAnnos)
              -> Result (BASIC_SPEC, ExtSign Sign Symbol, [Named Sentence])
basicAnalysis (basicSpec, signOfIncludes, _) =
  let ns = toNamedSen basicSpec
      specSign = signOfSentences ns
      nonImportedSyms = symbolsOfSign specSign
      completeSignWithTypeConstants = specSign `signatureUnion` signOfIncludes
      completeSign = postProcessSign completeSignWithTypeConstants
  in  return (basicSpec, ExtSign completeSign nonImportedSyms, ns)

toNamedSen :: BASIC_SPEC -> [Named Sentence]
toNamedSen (Basic_spec annotedItems) =
  concatMap (toNamedSenTPTP . item)  annotedItems
  where
    toNamedSenTPTP :: TPTP -> [Named Sentence]
    toNamedSenTPTP (TPTP inputs) = concatMap toNamedSenI inputs

    toNamedSenI :: TPTP_input -> [Named Sentence]
    toNamedSenI i = case i of
      Annotated_formula af ->
        [(makeNamed (nameS af) af) { isAxiom = formulaIsAxiom af
                                   , isDef = formulaIsDef af
                                   , wasTheorem = formulaWasTheorem af
                                   }]
      _ -> []

    formulaIsAxiom :: Annotated_formula -> Bool
    formulaIsAxiom af = case formulaRole af of
      Conjecture -> False
      _ -> True

    formulaIsDef :: Annotated_formula -> Bool
    formulaIsDef af = case formulaRole af of
      Definition -> True
      _ -> False

    formulaWasTheorem :: Annotated_formula -> Bool
    formulaWasTheorem af = case formulaRole af of
      Theorem -> True
      Lemma -> True
      _ -> False

signatureUnionR :: Sign -> Sign -> Result Sign
signatureUnionR s1 s2 = Result [Diag Debug "All fine sigUnion" nullRange]
                  $ Just $ postProcessSign $ signatureUnion s1 s2

signatureUnion :: Sign -> Sign -> Sign
signatureUnion s1 s2 =
  Sign { constantSet = constantSet s1 `Set.union` constantSet s2
       , numberSet = numberSet s1 `Set.union` numberSet s2
       , propositionSet = propositionSet s1 `Set.union` propositionSet s2
       , thfPredicateMap = thfPredicateMap s1 `Map.union` thfPredicateMap s2
       , tffPredicateMap = tffPredicateMap s1 `Map.union` tffPredicateMap s2
       , fofPredicateMap = unionFOFPredicate (fofPredicateMap s1) (fofPredicateMap s2)
       , fofFunctorMap = unionFOFFunctor (fofFunctorMap s1) (fofFunctorMap s2)
       , thfTypeConstantMap = thfTypeConstantMap s1 `Map.union` thfTypeConstantMap s2
       , tffTypeConstantMap = tffTypeConstantMap s1 `Map.union` tffTypeConstantMap s2
       , thfTypeFunctorMap = thfTypeFunctorMap s1 `Map.union` thfTypeFunctorMap s2
       , tffTypeFunctorMap = tffTypeFunctorMap s1 `Map.union` tffTypeFunctorMap s2
       , thfSubtypeMap = thfSubtypeMap s1 `Map.union` thfSubtypeMap s2
       , tffSubtypeMap = tffSubtypeMap s1 `Map.union` tffSubtypeMap s2
       , thfTypeDeclarationMap = thfTypeDeclarationMap s1 `Map.union` thfTypeDeclarationMap s2
       , tffTypeDeclarationMap = tffTypeDeclarationMap s1 `Map.union` tffTypeDeclarationMap s2
       }
  where
    unionFOFPredicate :: FOFPredicateMap -> FOFPredicateMap -> FOFPredicateMap
    unionFOFPredicate = Map.unionWith Set.union

    unionFOFFunctor :: FOFFunctorMap -> FOFFunctorMap -> FOFFunctorMap
    unionFOFFunctor = Map.unionWith Set.union

signatureUnions :: [Sign] -> Sign
signatureUnions signs = foldr signatureUnion emptySign signs

signOfSentences :: [Named Sentence] -> Sign
signOfSentences nss =
  postProcessSign $
    foldr (\ sign result -> signatureUnion sign result) emptySign $
      map (signOfSentenceNaive . sentence) nss

postProcessSign :: Sign -> Sign
postProcessSign = partitionTypeDeclarations . removeTypeDeclarationsFromConstantSet
  where
    partitionTypeDeclarations :: Sign -> Sign
    partitionTypeDeclarations sign =
      let (thfPredicates, thfRemainder) =
            Map.partition isTHFBooleanType $ thfTypeDeclarationMap sign
          (thfTypes, thfRemainder') = Map.partition isTHFType thfRemainder
          (tffPredicates, tffRemainder) =
            Map.partition isTFFBooleanType $ tffTypeDeclarationMap sign
          (tffTypes, tffRemainder') = Map.partition isTFFType tffRemainder
      in sign { thfPredicateMap = thfPredicates
              , thfTypeConstantMap = thfTypes
              , thfTypeFunctorMap = thfRemainder'
              , tffPredicateMap = tffPredicates
              , tffTypeConstantMap = tffTypes
              , tffTypeFunctorMap = tffRemainder'
              }

    -- Type helpers
    isTHFBooleanType :: THF_top_level_type -> Bool
    isTHFBooleanType x = case x of
      THFTLT_unitary (THFUT_unitary (THFUF_atom (THF_atom_function (THFF_atom (Atom_constant (DF_atomic_defined_word w)))))) -> tokStr w == "$o"
      THFTLT_mapping types -> isTHFBooleanType $ THFTLT_unitary $ last types
      _ -> False

    isTHFType :: THF_top_level_type -> Bool
    isTHFType x = case x of
      THFTLT_unitary (THFUT_unitary (THFUF_atom (THF_atom_function (THFF_atom (Atom_constant (DF_atomic_defined_word w)))))) -> tokStr w == "$tType"
      _ -> False

    isTFFBooleanType :: TFF_top_level_type -> Bool
    isTFFBooleanType x = case x of
      TFFTLT_mapping (TFF_mapping_type _ (TFFAT_defined O)) -> True
      _ -> False

    isTFFType :: TFF_top_level_type -> Bool
    isTFFType x = case x of
      TFFTLT_atomic (TFFAT_defined TType) -> True
      _ -> False

    removeTypeDeclarationsFromConstantSet :: Sign -> Sign
    removeTypeDeclarationsFromConstantSet sign =
      let tffTypeKeys = Map.keysSet $ tffTypeDeclarationMap sign
          tffTypeNames = Set.map unpackConstant $ Set.filter isConstant $ tffTypeKeys
          thfTypeKeys = Map.keysSet $ thfTypeDeclarationMap sign
          thfTypeNames = Set.map unpackConstantTHF $ Set.filter isConstantTHF $
                           thfTypeKeys
          typeNames = tffTypeNames `Set.union` thfTypeNames
      in  sign { constantSet = constantSet sign Set.\\ typeNames }

    isConstant :: Untyped_atom -> Bool
    isConstant ua = case ua of
      UA_constant _ -> True
      _ -> False

    unpackConstant :: Untyped_atom -> Constant
    unpackConstant ua = case ua of
      UA_constant c -> c
      _ -> error "Error in TPTP.StaticAnalysis.unpackConstant: Non-constant encountered."

    isConstantTHF :: THFTypeable -> Bool
    isConstantTHF x = case x of
      THFTypeConstant _ -> True
      _ -> False

    unpackConstantTHF :: THFTypeable -> Constant
    unpackConstantTHF x = case x of
      THFTypeConstant c -> c
      _ -> error "Error in TPTP.StaticAnalysis.unpackConstant: Non-constant encountered."

signOfSentence :: Sentence -> Sign
signOfSentence sen = signOfSentences [makeNamed "" sen]

signOfSentenceNaive :: Sentence -> Sign
signOfSentenceNaive sen = case sen of
  AF_THF_Annotated f -> signOfTHF_annotated f
  AF_TFX_Annotated f -> signOfTFX_annotated f
  AF_TFF_Annotated f -> signOfTFF_annotated f
  AF_TCF_Annotated f -> signOfTCF_annotated f
  AF_FOF_Annotated f -> signOfFOF_annotated f
  AF_CNF_Annotated f -> signOfCNF_annotated f
  AF_TPI_Annotated f -> signOfTPI_annotated f

signOfTPI_annotated :: TPI_annotated -> Sign
signOfTPI_annotated x = case x of
  TPI_annotated _ _ f _ -> signOfFOF_formula f

signOfTHF_annotated :: THF_annotated -> Sign
signOfTHF_annotated x = case x of
  THF_annotated _ _ f _ -> signOfTHF_formula f

signOfTFX_annotated :: TFX_annotated -> Sign
signOfTFX_annotated x = case x of
  TFX_annotated _ _ f _ -> signOfTFX_formula f

signOfTFF_annotated :: TFF_annotated -> Sign
signOfTFF_annotated x = case x of
  TFF_annotated _ _ f _ -> signOfTFF_formula f

signOfTCF_annotated :: TCF_annotated -> Sign
signOfTCF_annotated x = case x of
  TCF_annotated _ _ f _ -> signOfTCF_formula f

signOfFOF_annotated :: FOF_annotated -> Sign
signOfFOF_annotated x = case x of
  FOF_annotated _ _ f _ -> signOfFOF_formula f

signOfCNF_annotated :: CNF_annotated -> Sign
signOfCNF_annotated x = case x of
  CNF_annotated _ _ f _ -> signOfCNF_formula f

-- signOfAnnotations :: Annotations -> Sign
-- signOfAnnotations _ = emptySign

-- signOfFormula_role :: Formula_role -> Sign
-- signOfFormula_role _ = emptySign

signOfTHF_formula :: THF_formula -> Sign
signOfTHF_formula x = case x of
  THFF_logic f -> signOfTHF_logic_formula f
  THFF_sequent s -> signOfTHF_sequent s

signOfTHF_logic_formula :: THF_logic_formula -> Sign
signOfTHF_logic_formula x = case x of
  THFLF_binary f -> signOfTHF_binary_formula f
  THFLF_unitary f -> signOfTHF_unitary_formula f
  THFLF_type f -> signOfTHF_type_formula f
  THFLF_subtype f -> signOfTHF_subtype f

signOfTHF_binary_formula :: THF_binary_formula -> Sign
signOfTHF_binary_formula x = case x of
  THFBF_pair a -> signOfTHF_binary_pair a
  THFBF_tuple a -> signOfTHF_binary_tuple a

signOfTHF_binary_pair :: THF_binary_pair -> Sign
signOfTHF_binary_pair x = case x of
  THF_binary_pair _ f1 f2 ->
    signatureUnions $ map signOfTHF_unitary_formula [f1, f2]

signOfTHF_binary_tuple :: THF_binary_tuple -> Sign
signOfTHF_binary_tuple x = case x of
  THFBT_or fs -> signOfTHF_or_formula fs
  THFBT_and fs -> signOfTHF_and_formula fs
  THFBT_apply fs -> signOfTHF_apply_formula fs

signOfTHF_or_formula :: THF_or_formula -> Sign
signOfTHF_or_formula = signatureUnions . map signOfTHF_unitary_formula

signOfTHF_and_formula :: THF_or_formula -> Sign
signOfTHF_and_formula = signatureUnions . map signOfTHF_unitary_formula

signOfTHF_apply_formula :: THF_or_formula -> Sign
signOfTHF_apply_formula = signatureUnions . map signOfTHF_unitary_formula

signOfTHF_unitary_formula :: THF_unitary_formula -> Sign
signOfTHF_unitary_formula x = case x of
  THFUF_quantified a -> signOfTHF_quantified_formula a
  THFUF_unary a -> signOfTHF_unary_formula a
  THFUF_atom a -> signOfTHF_atom a
  THFUF_conditional a -> signOfTHF_conditional a
  THFUF_let a -> signOfTHF_let a
  THFUF_tuple a -> signOfTHF_tuple a
  THFUF_logic a -> signOfTHF_logic_formula a

signOfTHF_quantified_formula :: THF_quantified_formula -> Sign
signOfTHF_quantified_formula x = case x of
  THF_quantified_formula q f ->
    signatureUnions [signOfTHF_quantification q, signOfTHF_unitary_formula f]

signOfTHF_quantification :: THF_quantification -> Sign
signOfTHF_quantification x = case x of
  THF_quantification q vars ->
    signatureUnions [signOfTHF_quantifier q, signOfTHF_variable_list vars]

signOfTHF_variable_list :: THF_variable_list -> Sign
signOfTHF_variable_list = signatureUnions . map signOfTHF_variable

signOfTHF_variable :: THF_variable -> Sign
signOfTHF_variable x = case x of
  THFV_typed a -> signOfTHF_typed_variable a
  THFV_variable a -> signOfVariable a

signOfTHF_typed_variable :: THF_typed_variable -> Sign
signOfTHF_typed_variable x = case x of
  THF_typed_variable v tlt ->
    signatureUnions [signOfVariable v, signOfTHF_top_level_type tlt]

signOfTHF_unary_formula :: THF_unary_formula -> Sign
signOfTHF_unary_formula x = case x of
  THF_unary_formula c f ->
    signatureUnions [signOfTHF_unary_connective c, signOfTHF_logic_formula f]

signOfTHF_atom :: THF_atom -> Sign
signOfTHF_atom x = case x of
  THF_atom_function a -> signOfTHF_function a
  THF_atom_variable a -> signOfVariable a
  THF_atom_defined a -> signOfDefined_term a
  THF_atom_conn a -> signOfTHF_conn_term a

signOfTHF_function :: THF_function -> Sign
signOfTHF_function x = case x of
  THFF_atom a -> signOfAtom a
  THFF_functor f args ->
    signatureUnions [ signOfTPTP_functor f $ length args
                    , signOfTHF_arguments args]
  THFF_defined f args ->
    signatureUnions [signOfDefined_functor f, signOfTHF_arguments args]
  THFF_system f args ->
    signatureUnions [signOfSystem_functor f, signOfTHF_arguments args]

signOfTHF_conn_term :: THF_conn_term -> Sign
signOfTHF_conn_term x = case x of
  THFC_pair a -> signOfTHF_pair_connective a
  THFC_assoc a -> signOfAssoc_connective a
  THFC_unary a -> signOfTHF_unary_connective a

signOfTHF_conditional :: THF_conditional -> Sign
signOfTHF_conditional x = case x of
  THF_conditional f_if f_then f_else ->
    signatureUnions $ map signOfTHF_logic_formula [f_if, f_then, f_else]

signOfTHF_let :: THF_let -> Sign
signOfTHF_let x = case x of
  THF_let defns f ->
    signatureUnions [signOfTHF_let_defns defns, signOfTHF_formula f]

signOfTHF_let_defns :: THF_let_defns -> Sign
signOfTHF_let_defns x = case x of
  THFLD_single a -> signOfTHF_let_defn a
  THFLD_many a -> signOfTHF_let_defn_list a

signOfTHF_let_defn_list :: THF_let_defn_list -> Sign
signOfTHF_let_defn_list = signatureUnions . map signOfTHF_let_defn

signOfTHF_let_defn :: THF_let_defn -> Sign
signOfTHF_let_defn x = case x of
  THFLD_quantified a -> signOfTHF_let_quantified_defn a
  THFLD_plain a -> signOfTHF_let_plain_defn a

signOfTHF_let_quantified_defn :: THF_let_quantified_defn -> Sign
signOfTHF_let_quantified_defn x = case x of
  THF_let_quantified_defn q lpd ->
    signatureUnions [signOfTHF_quantification q, signOfTHF_let_plain_defn lpd]

signOfTHF_let_plain_defn :: THF_let_plain_defn -> Sign
signOfTHF_let_plain_defn x = case x of
  THF_let_plain_defn lhs f ->
    signatureUnions [signOfTHF_let_defn_LHS lhs, signOfTHF_formula f]

signOfTHF_let_defn_LHS :: THF_let_defn_LHS -> Sign
signOfTHF_let_defn_LHS x = case x of
  THFLDL_constant a -> signOfConstant a
  THFLDL_functor f args ->
    signatureUnions [ signOfTPTP_functor f $ length args
                    , signOfFOF_arguments args]
  THFLDL_tuple a -> signOfTHF_tuple a

signOfTHF_arguments :: THF_arguments -> Sign
signOfTHF_arguments = signOfTHF_formula_list

signOfTHF_type_formula :: THF_type_formula -> Sign
signOfTHF_type_formula x = case x of
  THFTF_typeable f tlt -> signatureUnions
    [ emptySign { thfTypeDeclarationMap = Map.singleton (THFTypeFormula f) tlt }
    , signOfTHF_typeable_formula f
    , signOfTHF_top_level_type tlt
    ]
  THFTF_constant c tlt -> signatureUnions
    [ emptySign { thfTypeDeclarationMap = Map.singleton (THFTypeConstant c) tlt }
    , signOfConstant c
    , signOfTHF_top_level_type tlt
    ]

signOfTHF_typeable_formula :: THF_typeable_formula -> Sign
signOfTHF_typeable_formula x = case x of
  THFTF_atom a -> signOfTHF_atom a
  THFTF_logic a -> signOfTHF_logic_formula a

signOfTHF_subtype :: THF_subtype -> Sign
signOfTHF_subtype x = case x of
  THF_subtype a1 a2 -> signatureUnions
    [ emptySign { thfSubtypeMap = Map.singleton a1 a2 }
    , signOfTHF_atom a1, signOfTHF_atom a2
    ]

signOfTHF_top_level_type :: THF_top_level_type -> Sign
signOfTHF_top_level_type x = case x of
  THFTLT_unitary a -> signOfTHF_unitary_type a
  THFTLT_mapping a -> signOfTHF_mapping_type a

signOfTHF_unitary_type :: THF_unitary_type -> Sign
signOfTHF_unitary_type x = case x of
  THFUT_unitary a -> signOfTHF_unitary_formula a
  THFUT_binary a -> signOfTHF_binary_type a

signOfTHF_binary_type :: THF_binary_type -> Sign
signOfTHF_binary_type x = case x of
  THFBT_mapping a -> signOfTHF_mapping_type a
  THFBT_xprod a -> signOfTHF_xprod_type a
  THFBT_union a -> signOfTHF_union_type a

signOfTHF_mapping_type :: THF_mapping_type -> Sign
signOfTHF_mapping_type = signatureUnions . map signOfTHF_unitary_type

signOfTHF_xprod_type :: THF_xprod_type -> Sign
signOfTHF_xprod_type = signatureUnions . map signOfTHF_unitary_type

signOfTHF_union_type :: THF_union_type -> Sign
signOfTHF_union_type = signatureUnions . map signOfTHF_unitary_type

signOfTHF_sequent :: THF_sequent -> Sign
signOfTHF_sequent x = case x of
  THFS_plain t1 t2 -> signatureUnions $ map signOfTHF_tuple [t1, t2]
  THFS_parens a -> signOfTHF_sequent a

signOfTHF_tuple :: THF_tuple -> Sign
signOfTHF_tuple x = case x of
  THF_tuple a -> signOfTHF_formula_list a

signOfTHF_formula_list :: THF_formula_list -> Sign
signOfTHF_formula_list = signatureUnions . map signOfTHF_logic_formula

signOfTFX_formula :: TFX_formula -> Sign
signOfTFX_formula x = case x of
  TFXF_logic a -> signOfTFX_logic_formula a
  TFXF_sequent a -> signOfTHF_sequent a

signOfTFX_logic_formula :: TFX_logic_formula -> Sign
signOfTFX_logic_formula x = case x of
  TFXLF_binary a -> signOfTHF_binary_formula a
  TFXLF_unitary a -> signOfTHF_unitary_formula a
  TFXLF_typed a -> signOfTFF_typed_atom a
  TFXLF_subtype a -> signOfTFF_subtype a

signOfTFF_formula :: TFF_formula -> Sign
signOfTFF_formula x = case x of
  TFFF_logic a -> signOfTFF_logic_formula a
  TFFF_atom a -> signOfTFF_typed_atom a
  TFFF_sequent a -> signOfTFF_sequent a

signOfTFF_logic_formula :: TFF_logic_formula -> Sign
signOfTFF_logic_formula x = case x of
  TFFLF_binary a -> signOfTFF_binary_formula a
  TFFLF_unitary a -> signOfTFF_unitary_formula a
  TFFLF_subtype a -> signOfTFF_subtype a

signOfTFF_binary_formula :: TFF_binary_formula -> Sign
signOfTFF_binary_formula x = case x of
  TFFBF_nonassoc a -> signOfTFF_binary_nonassoc a
  TFFBF_assoc a -> signOfTFF_binary_assoc a

signOfTFF_binary_nonassoc :: TFF_binary_nonassoc -> Sign
signOfTFF_binary_nonassoc x = case x of
  TFF_binary_nonassoc c f1 f2 ->
    signatureUnions $
      signOfBinary_connective c : map signOfTFF_unitary_formula [f1, f2]

signOfTFF_binary_assoc :: TFF_binary_assoc -> Sign
signOfTFF_binary_assoc x = case x of
  TFFBA_or a -> signOfTFF_or_formula a
  TFFBA_and a -> signOfTFF_and_formula a

signOfTFF_or_formula :: TFF_or_formula -> Sign
signOfTFF_or_formula = signatureUnions . map signOfTFF_unitary_formula

signOfTFF_and_formula :: TFF_and_formula -> Sign
signOfTFF_and_formula = signatureUnions . map signOfTFF_unitary_formula

signOfTFF_unitary_formula :: TFF_unitary_formula -> Sign
signOfTFF_unitary_formula x = case x of
  TFFUF_quantified a -> signOfTFF_quantified_formula a
  TFFUF_unary a -> signOfTFF_unary_formula a
  TFFUF_atomic a -> signOfTFF_atomic_formula a
  TFFUF_conditional a -> signOfTFF_conditional a
  TFFUF_let a -> signOfTFF_let a
  TFFUF_logic a -> signOfTFF_logic_formula a

signOfTFF_quantified_formula :: TFF_quantified_formula -> Sign
signOfTFF_quantified_formula x = case x of
  TFF_quantified_formula q vars f ->
    signatureUnions [ signOfFOF_quantifier q
                    , signOfTFF_variable_list vars
                    , signOfTFF_unitary_formula f
                    ]

signOfTFF_variable_list :: TFF_variable_list -> Sign
signOfTFF_variable_list = signatureUnions . map signOfTFF_variable

signOfTFF_variable :: TFF_variable -> Sign
signOfTFF_variable x = case x of
  TFFV_typed a -> signOfTFF_typed_variable a
  TFFV_variable a -> signOfVariable a

signOfTFF_typed_variable :: TFF_typed_variable -> Sign
signOfTFF_typed_variable x = case x of
  TFF_typed_variable v t ->
    signatureUnions [signOfVariable v, signOfTFF_atomic_type t]

signOfTFF_unary_formula :: TFF_unary_formula -> Sign
signOfTFF_unary_formula x = case x of
  TFFUF_connective c f ->
    signatureUnions [signOfUnary_connective c, signOfTFF_unitary_formula f]
  TFFUF_infix a -> signOfFOF_infix_unary a

signOfTFF_atomic_formula :: TFF_atomic_formula -> Sign
signOfTFF_atomic_formula = signOfFOF_atomic_formula

signOfTFF_conditional :: TFF_conditional -> Sign
signOfTFF_conditional x = case x of
  TFF_conditional f_if f_then f_else ->
    signatureUnions $ map signOfTFF_logic_formula [f_if, f_then, f_else]

signOfTFF_let :: TFF_let -> Sign
signOfTFF_let x = case x of
  TFF_let_term_defns defns f ->
    signatureUnions [signOfTFF_let_term_defns defns, signOfTFF_formula f]
  TFF_let_formula_defns defns f ->
    signatureUnions [signOfTFF_let_formula_defns defns, signOfTFF_formula f]

signOfTFF_let_term_defns :: TFF_let_term_defns -> Sign
signOfTFF_let_term_defns x = case x of
  TFFLTD_single a -> signOfTFF_let_term_defn a
  TFFLTD_many a -> signOfTFF_let_term_list a

signOfTFF_let_term_list :: TFF_let_term_list -> Sign
signOfTFF_let_term_list = signatureUnions . map signOfTFF_let_term_defn

signOfTFF_let_term_defn :: TFF_let_term_defn -> Sign
signOfTFF_let_term_defn x = case x of
  TFFLTD_variable vars defn ->
    signatureUnions [ signOfTFF_variable_list vars
                    , signOfTFF_let_term_defn defn
                    ]
  TFFLTD_binding a -> signOfTFF_let_term_binding a

signOfTFF_let_term_binding :: TFF_let_term_binding -> Sign
signOfTFF_let_term_binding x = case x of
  TFFLTB_plain pt t ->
    signatureUnions [signOfFOF_plain_term pt, signOfFOF_term t]
  TFFLTB_binding a -> signOfTFF_let_term_binding a

signOfTFF_let_formula_defns :: TFF_let_formula_defns -> Sign
signOfTFF_let_formula_defns x = case x of
  TFFLFD_single a -> signOfTFF_let_formula_defn a
  TFFLFD_many a -> signOfTFF_let_formula_list a

signOfTFF_let_formula_list :: TFF_let_formula_list -> Sign
signOfTFF_let_formula_list = signatureUnions . map signOfTFF_let_formula_defn

signOfTFF_let_formula_defn :: TFF_let_formula_defn -> Sign
signOfTFF_let_formula_defn x = case x of
  TFFLFD_variable vars defn ->
    signatureUnions [ signOfTFF_variable_list vars
                    , signOfTFF_let_formula_defn defn
                    ]
  TFFLFD_binding a -> signOfTFF_let_formula_binding a

signOfTFF_let_formula_binding :: TFF_let_formula_binding -> Sign
signOfTFF_let_formula_binding x = case x of
  TFFLFB_plain paf uf ->
    signatureUnions [ signOfFOF_plain_atomic_formula paf
                    , signOfTFF_unitary_formula uf
                    ]
  TFFLFB_binding a -> signOfTFF_let_formula_binding a

signOfTFF_sequent :: TFF_sequent -> Sign
signOfTFF_sequent x = case x of
  TFFS_plain t1 t2 -> signatureUnions $ map signOfTFF_formula_tuple [t1, t2]
  TFFS_parens a -> signOfTFF_sequent a

signOfTFF_formula_tuple :: TFF_formula_tuple -> Sign
signOfTFF_formula_tuple x = case x of
  TFF_formula_tuple a -> signOfTFF_formula_tuple_list a

signOfTFF_formula_tuple_list :: TFF_formula_tuple_list -> Sign
signOfTFF_formula_tuple_list = signatureUnions . map signOfTFF_logic_formula

signOfTFF_typed_atom :: TFF_typed_atom -> Sign
signOfTFF_typed_atom x = case x of
  TFFTA_plain ua tlt -> signatureUnions
    [ emptySign { tffTypeDeclarationMap = Map.singleton ua tlt }
    , signOfUntyped_atom ua
    , signOfTFF_top_level_type tlt
    ]
  TFFTA_parens a -> signOfTFF_typed_atom a

signOfTFF_subtype :: TFF_subtype -> Sign
signOfTFF_subtype x = case x of
  TFF_subtype ua a -> signatureUnions
    [ emptySign { tffSubtypeMap = Map.singleton ua a }
    , signOfUntyped_atom ua, signOfAtom a
    ]

signOfTFF_top_level_type :: TFF_top_level_type -> Sign
signOfTFF_top_level_type x = case x of
  TFFTLT_atomic a -> signOfTFF_atomic_type a
  TFFTLT_mapping a -> signOfTFF_mapping_type a
  TFFTLT_quantified a -> signOfTF1_quantified_type a
  TFFTLT_parens a -> signOfTFF_top_level_type a

signOfTF1_quantified_type :: TF1_quantified_type -> Sign
signOfTF1_quantified_type x = case x of
  TF1_quantified_type vars t ->
    signatureUnions [ signOfTFF_variable_list vars
                    , signOfTFF_monotype t
                    ]

signOfTFF_monotype :: TFF_monotype -> Sign
signOfTFF_monotype x = case x of
  TFFMT_atomic a -> signOfTFF_atomic_type a
  TFFMT_mapping a -> signOfTFF_mapping_type a

signOfTFF_unitary_type :: TFF_unitary_type -> Sign
signOfTFF_unitary_type x = case x of
  TFFUT_atomic a -> signOfTFF_atomic_type a
  TFFUT_xprod a -> signOfTFF_xprod_type a

signOfTFF_atomic_type :: TFF_atomic_type -> Sign
signOfTFF_atomic_type x = case x of
  TFFAT_constant a -> signOfType_constant a
  TFFAT_defined a -> signOfDefined_type a
  TFFAT_functor f args ->
    signatureUnions [signOfType_functor f, signOfTFF_type_arguments args]
  TFFAT_variable a -> signOfVariable a

signOfTFF_type_arguments :: TFF_type_arguments -> Sign
signOfTFF_type_arguments = signatureUnions . map signOfTFF_atomic_type

signOfTFF_mapping_type :: TFF_mapping_type -> Sign
signOfTFF_mapping_type x = case x of
  TFF_mapping_type ut at ->
    signatureUnions [signOfTFF_unitary_type ut, signOfTFF_atomic_type at]

signOfTFF_xprod_type :: TFF_xprod_type -> Sign
signOfTFF_xprod_type x = case x of
  TFF_xprod_type ut ats ->
    signatureUnions $ signOfTFF_unitary_type ut : map signOfTFF_atomic_type ats


signOfTCF_formula :: TCF_formula -> Sign
signOfTCF_formula x = case x of
  TCFF_logic a -> signOfTCF_logic_formula a
  TCFF_atom a -> signOfTFF_typed_atom a

signOfTCF_logic_formula :: TCF_logic_formula -> Sign
signOfTCF_logic_formula x = case x of
  TCFLF_quantified a -> signOfTCF_quantified_formula a
  TCFLF_cnf a -> signOfCNF_formula a

signOfTCF_quantified_formula :: TCF_quantified_formula -> Sign
signOfTCF_quantified_formula x = case x of
  TCF_quantified vars f ->
    signatureUnions [ signOfTFF_variable_list vars
                    , signOfCNF_formula f
                    ]

signOfFOF_formula :: FOF_formula -> Sign
signOfFOF_formula x = case x of
  FOFF_logic a -> signOfFOF_logic_formula a
  FOFF_sequent a -> signOfFOF_sequent a

signOfFOF_logic_formula :: FOF_logic_formula -> Sign
signOfFOF_logic_formula x = case x of
  FOFLF_binary a -> signOfFOF_binary_formula a
  FOFLF_unitary a -> signOfFOF_unitary_formula a

signOfFOF_binary_formula :: FOF_binary_formula -> Sign
signOfFOF_binary_formula x = case x of
  FOFBF_nonassoc a -> signOfFOF_binary_nonassoc a
  FOFBF_assoc a -> signOfFOF_binary_assoc a

signOfFOF_binary_nonassoc :: FOF_binary_nonassoc -> Sign
signOfFOF_binary_nonassoc x = case x of
  FOF_binary_nonassoc c f1 f2 ->
    signatureUnions $
      signOfBinary_connective c : map signOfFOF_unitary_formula [f1, f2]

signOfFOF_binary_assoc :: FOF_binary_assoc -> Sign
signOfFOF_binary_assoc x = case x of
  FOFBA_or a -> signOfFOF_or_formula a
  FOFBA_and a -> signOfFOF_and_formula a

signOfFOF_or_formula :: FOF_or_formula -> Sign
signOfFOF_or_formula = signatureUnions . map signOfFOF_unitary_formula

signOfFOF_and_formula :: FOF_and_formula -> Sign
signOfFOF_and_formula = signatureUnions . map signOfFOF_unitary_formula

signOfFOF_unitary_formula :: FOF_unitary_formula -> Sign
signOfFOF_unitary_formula x = case x of
  FOFUF_quantified a -> signOfFOF_quantified_formula a
  FOFUF_unary a -> signOfFOF_unary_formula a
  FOFUF_atomic a -> signOfFOF_atomic_formula a
  FOFUF_logic a -> signOfFOF_logic_formula a

signOfFOF_quantified_formula :: FOF_quantified_formula -> Sign
signOfFOF_quantified_formula x = case x of
  FOF_quantified_formula q vars f ->
    signatureUnions [ signOfFOF_quantifier q
                    , signOfFOF_variable_list vars
                    , signOfFOF_unitary_formula f
                    ]

signOfFOF_variable_list :: FOF_variable_list -> Sign
signOfFOF_variable_list = signatureUnions . map signOfVariable

signOfFOF_unary_formula :: FOF_unary_formula -> Sign
signOfFOF_unary_formula x = case x of
  FOFUF_connective c f ->
    signatureUnions [signOfUnary_connective c, signOfFOF_unitary_formula f]
  FOFUF_infix a -> signOfFOF_infix_unary a

signOfFOF_infix_unary :: FOF_infix_unary -> Sign
signOfFOF_infix_unary x = case x of
  FOF_infix_unary t1 t2 ->
    signatureUnions $ map signOfFOF_term [t1, t2]

signOfFOF_atomic_formula :: FOF_atomic_formula -> Sign
signOfFOF_atomic_formula x = case x of
  FOFAT_plain a -> signOfFOF_plain_atomic_formula a
  FOFAT_defined a -> signOfFOF_defined_atomic_formula a
  FOFAT_system a -> signOfFOF_system_atomic_formula a

signOfFOF_plain_atomic_formula :: FOF_plain_atomic_formula -> Sign
signOfFOF_plain_atomic_formula x = case x of
  FOFPAF_proposition a -> signOfProposition a
  FOFPAF_predicate p args ->
    signatureUnions [signOfPredicate p $ length args, signOfFOF_arguments args]

signOfFOF_defined_atomic_formula :: FOF_defined_atomic_formula -> Sign
signOfFOF_defined_atomic_formula x = case x of
  FOFDAF_plain a -> signOfFOF_defined_plain_formula a
  FOFDAF_infix a -> signOfFOF_defined_infix_formula a

signOfFOF_defined_plain_formula :: FOF_defined_plain_formula -> Sign
signOfFOF_defined_plain_formula x = case x of
  FOFDPF_proposition a -> signOfDefined_proposition a
  FOFDPF_predicate p args ->
    signatureUnions [signOfDefined_predicate p, signOfFOF_arguments args]

signOfFOF_defined_infix_formula :: FOF_defined_infix_formula -> Sign
signOfFOF_defined_infix_formula x = case x of
  FOF_defined_infix_formula dip t1 t2 -> signatureUnions
    [signOfFOF_term t1, signOfDefined_infix_pred dip, signOfFOF_term t2]

signOfFOF_system_atomic_formula :: FOF_system_atomic_formula -> Sign
signOfFOF_system_atomic_formula x = case x of
  FOF_system_atomic_formula a -> signOfFOF_system_term a

signOfFOF_plain_term :: FOF_plain_term -> Sign
signOfFOF_plain_term x = case x of
  FOFPT_constant a -> signOfConstant a
  FOFPT_functor f args ->
    signatureUnions [ signOfTPTP_functor f $ length args
                    , signOfFOF_arguments args]

signOfFOF_defined_term :: FOF_defined_term -> Sign
signOfFOF_defined_term x = case x of
  FOFDT_term a -> signOfDefined_term a
  FOFDT_atomic a -> signOfFOF_defined_atomic_term a

signOfFOF_defined_atomic_term :: FOF_defined_atomic_term -> Sign
signOfFOF_defined_atomic_term x = case x of
  FOFDAT_plain a -> signOfFOF_defined_plain_term a
  -- | FOFDAT_indix a -> signOfDefined_infix_term a

signOfFOF_defined_plain_term :: FOF_defined_plain_term -> Sign
signOfFOF_defined_plain_term x = case x of
  FOFDPT_constant a -> signOfDefined_constant a
  FOFDPT_functor f args ->
    signatureUnions [signOfDefined_functor f, signOfFOF_arguments args]

signOfFOF_system_term :: FOF_system_term -> Sign
signOfFOF_system_term x = case x of
  FOFST_constant a -> signOfSystem_constant a
  FOFST_functor f args ->
    signatureUnions [signOfSystem_functor f, signOfFOF_arguments args]

signOfFOF_arguments :: FOF_arguments -> Sign
signOfFOF_arguments = signatureUnions . map signOfFOF_term

signOfFOF_term :: FOF_term -> Sign
signOfFOF_term x = case x of
  FOFT_function a -> signOfFOF_function_term a
  FOFT_variable a -> signOfVariable a
  FOFT_conditional a -> signOfTFF_conditional_term a
  FOFT_let a -> signOfTFF_let_term a

signOfFOF_function_term :: FOF_function_term -> Sign
signOfFOF_function_term x = case x of
  FOFFT_plain a -> signOfFOF_plain_term a
  FOFFT_defined a -> signOfFOF_defined_term a
  FOFFT_system a -> signOfFOF_system_term a

signOfTFF_conditional_term :: TFF_conditional_term -> Sign
signOfTFF_conditional_term x = case x of
  TFF_conditional_term f_if t_then t_else ->
    signatureUnions $
      signOfTFF_logic_formula f_if : map signOfFOF_term [t_then, t_else]

signOfTFF_let_term :: TFF_let_term -> Sign
signOfTFF_let_term x = case x of
  TFFLT_formula defns t ->
    signatureUnions [signOfTFF_let_formula_defns defns, signOfFOF_term t]
  TFFLT_term defns t ->
    signatureUnions [signOfTFF_let_term_defns defns, signOfFOF_term t]

{-
%----This section is the FOFX syntax. Not yet in use.
% <fof_let>            ::= := [<fof_let_list>] : <fof_unitary_formula>
% <fof_let_list>       ::= <fof_defined_var> |
%                          <fof_defined_var>,<fof_let_list>
% <fof_defined_var>    ::= <variable> := <fof_logic_formula> |
%                          <variable> :- <fof_term> | (<fof_defined_var>)
%
% <fof_conditional>    ::= $ite_f(<fof_logic_formula>,<fof_logic_formula>,
%                          <fof_logic_formula>)
%
% <fof_conditional_term> ::= $ite_t(<fof_logic_formula>,<fof_term>,<fof_term>)
-}

signOfFOF_sequent :: FOF_sequent -> Sign
signOfFOF_sequent x = case x of
  FOFS_plain t1 t2 ->
    signatureUnions $ map signOfFOF_formula_tuple [t1, t2]
  FOFS_parens a -> signOfFOF_sequent a

signOfFOF_formula_tuple :: FOF_formula_tuple -> Sign
signOfFOF_formula_tuple x = case x of
  FOF_formula_tuple a -> signOfFOF_formula_tuple_list a

signOfFOF_formula_tuple_list :: FOF_formula_tuple_list -> Sign
signOfFOF_formula_tuple_list = signatureUnions . map signOfFOF_logic_formula


signOfCNF_formula :: CNF_formula -> Sign
signOfCNF_formula x = case x of
  CNFF_plain a -> signOfDisjunction a
  CNFF_parens a -> signOfDisjunction a

signOfDisjunction :: Disjunction -> Sign
signOfDisjunction x = case x of
  Disjunction ls -> signatureUnions $ map signOfLiteral ls

signOfLiteral :: Literal -> Sign
signOfLiteral x = case x of
  Lit_atomic a -> signOfFOF_atomic_formula a
  Lit_negative a -> signOfFOF_atomic_formula a
  Lit_fof_infix a -> signOfFOF_infix_unary a

signOfTHF_quantifier :: THF_quantifier -> Sign
signOfTHF_quantifier x = case x of
  THFQ_fof a -> signOfFOF_quantifier a
  THFQ_th0 a -> signOfTH0_quantifier a
  THFQ_th1 a -> signOfTH1_quantifier a


signOfTH1_quantifier :: TH1_quantifier -> Sign
signOfTH1_quantifier x = case x of
  TH1_DependentProduct -> emptySign
  TH1_DependentSum -> emptySign

signOfTH0_quantifier :: TH0_quantifier -> Sign
signOfTH0_quantifier x = case x of
  TH0_LambdaBinder -> emptySign
  TH0_IndefiniteDescription -> emptySign
  TH0_DefiniteDescription -> emptySign

signOfTHF_pair_connective :: THF_pair_connective -> Sign
signOfTHF_pair_connective x = case x of
  THF_infix_equality -> emptySign
  Infix_inequality -> emptySign
  THFPC_binary a -> signOfBinary_connective a
  THF_assignment -> emptySign

signOfTHF_unary_connective :: THF_unary_connective -> Sign
signOfTHF_unary_connective x = case x of
  THFUC_unary a -> signOfUnary_connective a
  THFUC_th1 a -> signOfTH1_unary_connective a

signOfTH1_unary_connective :: TH1_unary_connective -> Sign
signOfTH1_unary_connective x = case x of
  TH1_PiForAll -> emptySign
  TH1_PiSigmaExists -> emptySign
  TH1_PiIndefiniteDescription -> emptySign
  TH1_PiDefiniteDescription -> emptySign
  TH1_PiEquality -> emptySign

signOfFOF_quantifier :: FOF_quantifier -> Sign
signOfFOF_quantifier x = case x of
  ForAll -> emptySign
  Exists -> emptySign

signOfBinary_connective :: Binary_connective -> Sign
signOfBinary_connective x = case x of
  Equivalence -> emptySign
  Implication -> emptySign
  ReverseImplication -> emptySign
  XOR -> emptySign
  NOR -> emptySign
  NAND -> emptySign

signOfAssoc_connective :: Assoc_connective -> Sign
signOfAssoc_connective x = case x of
  OR -> emptySign
  AND -> emptySign

signOfUnary_connective :: Unary_connective -> Sign
signOfUnary_connective x = case x of
  NOT -> emptySign

signOfType_constant :: Type_constant -> Sign
signOfType_constant a = emptySign -- Handled by thfTypeConstantMap and tffTypeConstantMap

signOfType_functor :: Type_functor -> Sign
signOfType_functor a = emptySign -- Handled by thfTypeFunctorMap and tffTypeFunctorMap

signOfDefined_type :: Defined_type -> Sign
signOfDefined_type x = case x of
  OType -> emptySign
  O -> emptySign
  IType -> emptySign
  I -> emptySign
  TType -> emptySign
  Real -> emptySign
  Rat -> emptySign
  Int -> emptySign

signOfAtom :: Atom -> Sign
signOfAtom x = case x of
  Atom_untyped a -> signOfUntyped_atom a
  Atom_constant a -> signOfDefined_constant a

signOfUntyped_atom :: Untyped_atom -> Sign
signOfUntyped_atom x = case x of
  UA_constant a -> signOfConstant a
  UA_system a -> signOfSystem_constant a

signOfProposition :: Proposition -> Sign
signOfProposition a = emptySign { propositionSet = Set.singleton a }

signOfPredicate :: Predicate -> Int -> Sign
signOfPredicate a arity =
  emptySign { fofPredicateMap = Map.singleton a $ Set.singleton arity }

signOfDefined_proposition :: Defined_proposition -> Sign
signOfDefined_proposition x = case x of
  TPTP_true -> emptySign
  TPTP_false -> emptySign

signOfDefined_predicate :: Defined_predicate -> Sign
signOfDefined_predicate x = case x of
  Distinct -> emptySign
  Less -> emptySign
  Lesseq -> emptySign
  Greater -> emptySign
  Greatereq -> emptySign
  Is_int -> emptySign
  Is_rat -> emptySign
  Box_P -> emptySign
  Box_i -> emptySign
  Box_int -> emptySign
  Box -> emptySign
  Dia_P -> emptySign
  Dia_i -> emptySign
  Dia_int -> emptySign
  Dia -> emptySign

signOfDefined_infix_pred :: Defined_infix_pred -> Sign
signOfDefined_infix_pred x = case x of
  Defined_infix_equality -> emptySign
  Defined_assignment -> emptySign

signOfConstant :: Constant -> Sign
signOfConstant a = emptySign { constantSet = Set.singleton a }

signOfTPTP_functor :: TPTP_functor -> Int -> Sign
signOfTPTP_functor a arity =
  emptySign { fofFunctorMap = Map.singleton a $ Set.singleton arity }

signOfSystem_constant :: System_constant -> Sign
signOfSystem_constant _ = emptySign

signOfSystem_functor :: System_functor -> Sign
signOfSystem_functor _ = emptySign

signOfDefined_constant :: Defined_constant -> Sign
signOfDefined_constant _ = emptySign

signOfDefined_functor :: Defined_functor -> Sign
signOfDefined_functor x = case x of
  Uminus -> emptySign
  Sum -> emptySign
  Difference -> emptySign
  Product -> emptySign
  Quotient -> emptySign
  Quotient_e -> emptySign
  Quotient_t -> emptySign
  Quotient_f -> emptySign
  Remainder_e -> emptySign
  Remainder_t -> emptySign
  Remainder_f -> emptySign
  Floor -> emptySign
  Ceiling -> emptySign
  Truncate -> emptySign
  Round -> emptySign
  To_int -> emptySign
  To_rat -> emptySign
  To_real -> emptySign
  DF_atomic_defined_word _ -> emptySign

signOfDefined_term :: Defined_term -> Sign
signOfDefined_term x = case x of
  DT_number a -> signOfNumber a
  DT_object a -> signOfDistinct_object a

signOfVariable :: Variable -> Sign
signOfVariable a = emptySign

-- signOfSource :: Source -> Sign
-- signOfSource x = case x of
  -- Source_DAG a -> emptySign
  -- Source_internal a -> emptySign
  -- Source_external a -> emptySign
  -- Unknown_source -> emptySign
  -- Source_many a -> emptySign

-- signOfSources :: Sources -> Sign
-- signOfSources _ = emptySign

-- signOfDAG_source :: DAG_source -> Sign
-- signOfDAG_source x = case x of
  -- DAGS_name a -> emptySign
  -- DAGS_record a -> emptySign

-- signOfInference_record :: Inference_record -> Sign
-- signOfInference_record x = case x of
  -- Inference_record ir ui ip -> emptySign

-- signOfInference_rule :: Inference_rule -> Sign
-- signOfInference_rule _ = emptySign

-- signOfInference_parents :: Inference_parents -> Sign
-- signOfInference_parents _ = emptySign

-- signOfParent_list :: Parent_list -> Sign
-- signOfParent_list _ = emptySign

-- signOfParent_info :: Parent_info -> Sign
-- signOfParent_info x = case x of
  -- Parent_info s d -> emptySign

-- signOfParent_details :: Parent_details -> Sign
-- signOfParent_details x = case x of
  -- Just gl -> emptySign
  -- Nothing -> emptySign

-- signOfInternal_source :: Internal_source -> Sign
-- signOfInternal_source x = case x of
  -- Internal_source it oi -> emptySign

-- signOfIntro_type :: Intro_type -> Sign
-- signOfIntro_type x = case x of
  -- IntroTypeDefinition -> emptySign
  -- AxiomOfChoice -> emptySign
  -- Tautology -> emptySign
  -- IntroTypeAssumption -> emptySign

-- signOfExternal_source :: External_source -> Sign
-- signOfExternal_source x = case x of
  -- ExtSrc_file a -> emptySign
  -- ExtSrc_theory a -> emptySign
  -- ExtSrc_creator a -> emptySign

-- signOfFile_source :: File_source -> emptySign
-- signOfFile_source x = case x of
  -- File_source fn fi -> emptySign

-- signOfFile_info :: File_info -> Sign
-- signOfFile_info x = case x of
  -- Just n -> emptySign
  -- Nothing -> emptySign

-- signOfTheory :: Theory -> Sign
-- signOfTheory x = case x of
  -- Theory tn oi -> emptySign

-- signOfTheory_name :: Theory_name -> Sign
-- signOfTheory_name x = case x of
  -- TN_equality -> emptySign
  -- TN_ac -> emptySign

-- signOfCreator_source :: Creator_source -> Sign
-- signOfCreator_source x = case x of
  -- Creator_source cn oi -> emptySign

-- signOfCreator_name :: Creator_name -> Sign
-- signOfCreator_name _ = emptySign


-- signOfOptional_info :: Optional_info -> Sign
-- signOfOptional_info x = case x of
  -- Just ui -> emptySign
  -- Nothing -> emptySign

-- signOfUseful_info :: Useful_info -> Sign
-- signOfUseful_info x = case x of
  -- UI_items a -> emptySign
  -- UI_general_list a -> emptySign

-- signOfInfo_items :: Info_items -> Sign
-- signOfInfo_items _ = emptySign

-- signOfInfo_item :: Info_item -> Sign
-- signOfInfo_item x = case x of
  -- Info_formula a -> emptySign
  -- Info_inference a -> emptySign
  -- Info_general a -> emptySign

-- signOfFormula_item :: Formula_item -> Sign
-- signOfFormula_item x = case x of
  -- FI_description a -> emptySign
  -- FI_iquote a -> emptySign

-- signOfDescription_item :: Description_item -> Sign
-- signOfDescription_item _ = emptySign

-- signOfIquote_item :: Iquote_item -> Sign
-- signOfIquote_item _ = emptySign

-- signOfInference_item :: Inference_item -> Sign
-- signOfInference_item x = case x of
  -- Inf_status a -> emptySign
  -- Inf_assumption a -> emptySign
  -- Inf_symbol a -> emptySign
  -- Inf_refutation a -> emptySign

-- signOfInference_status :: Inference_status -> Sign
-- signOfInference_status x = case x of
  -- Inf_value sv -> emptySign
  -- Inf_info a -> emptySign

-- signOfStatus_value :: Status_value -> Sign
-- signOfStatus_value x = case x of
  -- SUC -> emptySign
  -- UNP -> emptySign
  -- SAP -> emptySign
  -- ESA -> emptySign
  -- SAT -> emptySign
  -- FSA -> emptySign
  -- THM -> emptySign
  -- EQV -> emptySign
  -- TAC -> emptySign
  -- WEC -> emptySign
  -- ETH -> emptySign
  -- TAU -> emptySign
  -- WTC -> emptySign
  -- WTH -> emptySign
  -- CAX -> emptySign
  -- SCA -> emptySign
  -- TCA -> emptySign
  -- WCA -> emptySign
  -- CUP -> emptySign
  -- CSP -> emptySign
  -- ECS -> emptySign
  -- CSA -> emptySign
  -- CTH -> emptySign
  -- CEQ -> emptySign
  -- UNC -> emptySign
  -- WCC -> emptySign
  -- ECT -> emptySign
  -- FUN -> emptySign
  -- UNS -> emptySign
  -- WUC -> emptySign
  -- WCT -> emptySign
  -- SCC -> emptySign
  -- UCA -> emptySign
  -- NOC -> emptySign

-- signOfInference_info :: Inference_info -> Sign
-- signOfInference_info x = case x of
  -- Inference_info ir aw gl -> emptySign

-- signOfAssumptions_record :: Assumptions_record -> Sign
-- signOfAssumptions_record _ = emptySign

-- signOfRefutation :: Refutation -> emptySign
-- signOfRefutation _ = emptySign

-- signOfNew_symbol_record :: New_symbol_record -> Sign
-- signOfNew_symbol_record x = case x of
  -- New_symbol_record aw nsl -> emptySign

-- signOfNew_symbol_list :: New_symbol_list -> Sign
-- signOfNew_symbol_list _ = emptySign

-- signOfPrincipal_symbol :: Principal_symbol -> Sign
-- signOfPrincipal_symbol x = case x of
  -- PS_functor a -> emptySign
  -- PS_variable a -> emptySign

-- signOfInclude :: Include -> Sign
-- signOfInclude x = case x of
  -- Include fn fs -> emptySign

-- signOfFormula_selection :: Formula_selection -> Sign
-- signOfFormula_selection x = case x of
  -- Just ns -> emptySign
  -- Nothing -> emptySign

-- signOfName_list :: Name_list -> Sign
-- signOfName_list _ = emptySign

-- signOfGeneral_term :: General_term -> Sign
-- signOfGeneral_term x = case x of
--   GT_data a -> emptySign
--   GT_DataTerm gd gt -> emptySign
--   GT_list a -> emptySign

-- signOfGeneral_data :: General_data -> Sign
-- signOfGeneral_data x = case x of
--   GD_atomic_word a -> emptySign
--   GD_general_function a -> emptySign
--   GD_variable a -> emptySign
--   GD_number a -> emptySign
--   GD_distinct_object a -> emptySign
--   GD_formula_data a -> emptySign
--   GD_bind v fd -> emptySign

-- signOfGeneral_function :: General_function -> Sign
-- signOfGeneral_function x = case x of
--   General_function aw gt -> emptySign

-- signOfFormula_data :: Formula_data -> Sign
-- signOfFormula_data x = case x of
--   FD_THF a -> emptySign
--   FD_TFF a -> emptySign
--   FD_FOF a -> emptySign
--   FD_CNF a -> emptySign
--   FD_FOT a -> emptySign

-- signOfGeneral_list :: General_list -> Sign
-- signOfGeneral_list _ = emptySign

-- signOfGeneral_terms :: General_terms -> Sign
-- signOfGeneral_terms _ = emptySign

-- signOfName :: Name -> Sign
-- signOfName x = case x of
--   NameString a -> emptySign
--   NameInteger a -> emptySign

-- signOfAtomic_word :: Atomic_word -> Sign
-- signOfAtomic_word _ = emptySign

-- signOfAtomic_defined_word :: Atomic_defined_word -> Sign
-- signOfAtomic_defined_word _ = emptySign

-- signOfAtomic_system_word :: Atomic_system_word -> Sign
-- signOfAtomic_system_word _ = emptySign

signOfNumber :: Number -> Sign
signOfNumber a = emptySign { numberSet = Set.singleton a }

signOfDistinct_object :: Distinct_object -> Sign
signOfDistinct_object _ = emptySign

-- signOfFile_name :: File_name -> Sign
-- signOfFile_name _ = emptySign

nameS :: Annotated_formula -> String
nameS f = case name f of
  NameString s -> tokStr s
  NameInteger i -> show i
