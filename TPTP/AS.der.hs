{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./TPTP/AS.der.hs
Description :  Abstract syntax for TPTP v6.4.0.11
Copyright   :  (c) Eugen Kuksa University of Magdeburg 2017
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Eugen Kuksa <kuksa@iks.cs.ovgu.de>
Stability   :  provisional
Portability :  portable

Definition of abstract syntax for TPTP taken from [1]

References

[1] G. Sutcliffe et al.: The TPTP language grammar in BNF.
    <http://www.cs.miami.edu/~tptp/TPTP/SyntaxBNF.html>

    Note: The implemented version is saved at TPTP/Documents/SyntaxBNF.html

    Note: The names of the data types are aligned with the names of the
    grammar rules at this reference page (modulo case).

[2] C. Kaliszyk, G. Sutcliffe and F. Rabe:
    TH1: The TPTP Typed Higher-Order Form with Rank-1 Polymorphism
    <https://kwarc.info/people/frabe/Research/KRS_thf1_16.pdf>
    Note: for further information on TF0, TF1, TH0 and TH1
-}

module TPTP.AS where

import Common.Id as Id
import Common.IRI
import Syntax.AS_Structured ()
import qualified Common.AS_Annotation as AS_Anno

import Data.Data

-- DrIFT command
{-! global: GetRange !-}

newtype BASIC_SPEC = Basic_spec [AS_Anno.Annoted TPTP]
                     deriving (Show, Ord, Eq, Data, Typeable)

-- Files

-- %----Files. Empty file is OK.
-- <TPTP_file>            ::= <TPTP_input>*<Paste>
newtype TPTP = TPTP [TPTP_input]
               deriving (Show, Ord, Eq, Data, Typeable)

-- <TPTP_input>           ::= <annotated_formula> | <include>
data TPTP_input = Annotated_formula Annotated_formula
                | TPTP_include Include
                | TPTP_comment Comment
                | TPTP_defined_comment DefinedComment
                | TPTP_system_comment SystemComment
                  deriving (Show, Ord, Eq, Data, Typeable)

-- Comments

data Comment = Comment_line Token
             | Comment_block Token
               deriving (Show, Eq, Ord, Data, Typeable)

data DefinedComment = Defined_comment_line Token
                    | Defined_comment_block Token
                      deriving (Show, Eq, Ord, Data, Typeable)

data SystemComment = System_comment_line Token
                   | System_comment_block Token
                     deriving (Show, Eq, Ord, Data, Typeable)

-- %----Formula records
-- <annotated_formula>    ::= <thf_annotated> | <tfx_annotated> | <tff_annotated> |
--                            <tcf_annotated> | <fof_annotated> | <cnf_annotated> |
--                            <tpi_annotated>
data Annotated_formula = AF_THF_Annotated THF_annotated
                       | AF_TFX_Annotated TFX_annotated
                       | AF_TFF_Annotated TFF_annotated
                       | AF_TCF_Annotated TCF_annotated
                       | AF_FOF_Annotated FOF_annotated
                       | AF_CNF_Annotated CNF_annotated
                       | AF_TPI_Annotated TPI_annotated
                         deriving (Show, Ord, Eq, Data, Typeable)

-- <tpi_annotated>        ::= tpi(<name>,<formula_role>,<tpi_formula><annotations>).
data TPI_annotated = TPI_annotated Name Formula_role TPI_formula Annotations
                     deriving (Show, Ord, Eq, Data, Typeable)

-- <tpi_formula>          ::= <fof_formula>
type TPI_formula = FOF_formula

-- <thf_annotated>        ::= thf(<name>,<formula_role>,<thf_formula>
--                            <annotations>).
data THF_annotated = THF_annotated Name Formula_role THF_formula Annotations
                     deriving (Show, Ord, Eq, Data, Typeable)

-- <tfx_annotated>        ::= tfx(<name>,<formula_role>,<tfx_formula>
--                            <annotations>).
data TFX_annotated = TFX_annotated Name Formula_role TFX_formula Annotations
                     deriving (Show, Ord, Eq, Data, Typeable)

-- <tff_annotated>        ::= tff(<name>,<formula_role>,<tff_formula>
--                            <annotations>).
data TFF_annotated = TFF_annotated Name Formula_role TFF_formula Annotations
                     deriving (Show, Ord, Eq, Data, Typeable)

-- <tcf_annotated>        ::= tcf(<name>,<formula_role>,<tcf_formula>
--                            <annotations>).
data TCF_annotated = TCF_annotated Name Formula_role TCF_formula Annotations
                     deriving (Show, Ord, Eq, Data, Typeable)

-- <fof_annotated>        ::= fof(<name>,<formula_role>,<fof_formula>
--                            <annotations>).
data FOF_annotated = FOF_annotated Name Formula_role FOF_formula Annotations
                     deriving (Show, Ord, Eq, Data, Typeable)

-- <cnf_annotated>        ::= cnf(<name>,<formula_role>,<cnf_formula>
--                            <annotations>).
data CNF_annotated = CNF_annotated Name Formula_role CNF_formula Annotations
                     deriving (Show, Ord, Eq, Data, Typeable)

name :: Annotated_formula -> Name
name f = case f of
  AF_THF_Annotated (THF_annotated n _ _ _) -> n
  AF_TFX_Annotated (TFX_annotated n _ _ _) -> n
  AF_TFF_Annotated (TFF_annotated n _ _ _) -> n
  AF_TCF_Annotated (TCF_annotated n _ _ _) -> n
  AF_FOF_Annotated (FOF_annotated n _ _ _) -> n
  AF_CNF_Annotated (CNF_annotated n _ _ _) -> n
  AF_TPI_Annotated (TPI_annotated n _ _ _) -> n

formulaRole :: Annotated_formula -> Formula_role
formulaRole f = case f of
  AF_THF_Annotated (THF_annotated _ r _ _) -> r
  AF_TFX_Annotated (TFX_annotated _ r _ _) -> r
  AF_TFF_Annotated (TFF_annotated _ r _ _) -> r
  AF_TCF_Annotated (TCF_annotated _ r _ _) -> r
  AF_FOF_Annotated (FOF_annotated _ r _ _) -> r
  AF_CNF_Annotated (CNF_annotated _ r _ _) -> r
  AF_TPI_Annotated (TPI_annotated _ r _ _) -> r

annotations :: Annotated_formula -> Annotations
annotations f = case f of
  AF_THF_Annotated (THF_annotated _ _ _ a) -> a
  AF_TFX_Annotated (TFX_annotated _ _ _ a) -> a
  AF_TFF_Annotated (TFF_annotated _ _ _ a) -> a
  AF_TCF_Annotated (TCF_annotated _ _ _ a) -> a
  AF_FOF_Annotated (FOF_annotated _ _ _ a) -> a
  AF_CNF_Annotated (CNF_annotated _ _ _ a) -> a
  AF_TPI_Annotated (TPI_annotated _ _ _ a) -> a

-- <annotations>          ::= ,<source><optional_info> | <null>
newtype Annotations = Annotations (Maybe (Source, Optional_info))
                      deriving (Show, Ord, Eq, Data, Typeable)

-- Types for problems

-- %----Types for problems.
-- <formula_role>         ::= <lower_word>
-- <formula_role>         :== axiom | hypothesis | definition | assumption |
--                            lemma | theorem | corollary | conjecture |
--                            negated_conjecture | plain | type |
--                            fi_domain | fi_functors | fi_predicates | unknown
data Formula_role = Axiom
                  | Hypothesis
                  | Definition
                  | Assumption
                  | Lemma
                  | Theorem
                  | Corollary
                  | Conjecture
                  | Negated_conjecture
                  | Plain
                  | Type
                  | Fi_domain
                  | Fi_functors
                  | Fi_predicates
                  | Unknown
                  | Other_formula_role Token
                    -- ^ For future updates. Should not be used.
                    deriving (Show, Ord, Eq, Data, Typeable)

-- %----THF formulae.
-- <thf_formula>          ::= <thf_logic_formula> | <thf_sequent>
data THF_formula = THFF_logic THF_logic_formula
                 | THFF_sequent THF_sequent
                   deriving (Show, Ord, Eq, Data, Typeable)

-- <thf_logic_formula>    ::= <thf_binary_formula> | <thf_unitary_formula> |
--                            <thf_type_formula> | <thf_subtype>
data THF_logic_formula = THFLF_binary THF_binary_formula
                       | THFLF_unitary THF_unitary_formula
                       | THFLF_type THF_type_formula
                       | THFLF_subtype THF_subtype
                         deriving (Show, Ord, Eq, Data, Typeable)

-- <thf_binary_formula>   ::= <thf_binary_pair> | <thf_binary_tuple>
data THF_binary_formula = THFBF_pair THF_binary_pair
                        | THFBF_tuple THF_binary_tuple
                          deriving (Show, Ord, Eq, Data, Typeable)

-- %----Only some binary connectives can be written without ()s.
-- %----There's no precedence among binary connectives
-- <thf_binary_pair>      ::= <thf_unitary_formula> <thf_pair_connective>
--                            <thf_unitary_formula>
data THF_binary_pair = THF_binary_pair THF_pair_connective THF_unitary_formula THF_unitary_formula
                       deriving (Show, Ord, Eq, Data, Typeable)

-- <thf_binary_tuple>     ::= <thf_or_formula> | <thf_and_formula> |
--                            <thf_apply_formula>
data THF_binary_tuple = THFBT_or THF_or_formula
                      | THFBT_and THF_and_formula
                      | THFBT_apply THF_apply_formula
                        deriving (Show, Ord, Eq, Data, Typeable)

-- <thf_or_formula>       ::= <thf_unitary_formula> <vline> <thf_unitary_formula> |
--                            <thf_or_formula> <vline> <thf_unitary_formula>

type THF_or_formula = [THF_unitary_formula]

-- <thf_and_formula>      ::= <thf_unitary_formula> & <thf_unitary_formula> |
--                            <thf_and_formula> & <thf_unitary_formula>
type THF_and_formula = [THF_unitary_formula]

-- <thf_apply_formula>    ::= <thf_unitary_formula> @ <thf_unitary_formula> |
--                            <thf_apply_formula> @ <thf_unitary_formula>
type THF_apply_formula = [THF_unitary_formula]

-- <thf_unitary_formula>  ::= <thf_quantified_formula> | <thf_unary_formula> |
--                            <thf_atom> | <thf_conditional> | <thf_let> |
--                            <thf_tuple> | (<thf_logic_formula>)
data THF_unitary_formula = THFUF_quantified THF_quantified_formula
                         | THFUF_unary THF_unary_formula
                         | THFUF_atom THF_atom
                         | THFUF_conditional THF_conditional
                         | THFUF_let THF_let
                         | THFUF_tuple THF_tuple
                         | THFUF_logic THF_logic_formula
                           deriving (Show, Ord, Eq, Data, Typeable)

-- <thf_quantified_formula> ::= <thf_quantification> <thf_unitary_formula>
data THF_quantified_formula = THF_quantified_formula THF_quantification THF_unitary_formula
                              deriving (Show, Ord, Eq, Data, Typeable)

-- <thf_quantification>   ::= <thf_quantifier> [<thf_variable_list>] :
data THF_quantification = THF_quantification THF_quantifier THF_variable_list
                          deriving (Show, Ord, Eq, Data, Typeable)

-- <thf_variable_list>    ::= <thf_variable> | <thf_variable>,<thf_variable_list>
type THF_variable_list = [THF_variable]

-- <thf_variable>         ::= <thf_typed_variable> | <variable>
data THF_variable = THFV_typed THF_typed_variable
                  | THFV_variable Variable
                    deriving (Show, Ord, Eq, Data, Typeable)

-- <thf_typed_variable>   ::= <variable> : <thf_top_level_type>
data THF_typed_variable = THF_typed_variable Variable THF_top_level_type
                          deriving (Show, Ord, Eq, Data, Typeable)

-- <thf_unary_formula>    ::= <thf_unary_connective> (<thf_logic_formula>)
data THF_unary_formula = THF_unary_formula THF_unary_connective THF_logic_formula
                         deriving (Show, Ord, Eq, Data, Typeable)

-- <thf_atom>             ::= <thf_function> | <variable> | <defined_term> |
--                            <thf_conn_term>
data THF_atom = THF_atom_function THF_function
              | THF_atom_variable Variable
              | THF_atom_defined Defined_term
              | THF_atom_conn THF_conn_term
                deriving (Show, Ord, Eq, Data, Typeable)

-- <thf_function>         ::= <atom> | <functor>(<thf_arguments>) |
--                            <defined_functor>(<thf_arguments>) |
--                            <system_functor>(<thf_arguments>)
data THF_function = THFF_atom Atom
                  | THFF_functor TPTP_functor THF_arguments
                  | THFF_defined Defined_functor THF_arguments
                  | THFF_system System_functor THF_arguments
                    deriving (Show, Ord, Eq, Data, Typeable)

-- <thf_conn_term>        ::= <thf_pair_connective> | <assoc_connective> |
--                            <thf_unary_connective>
data THF_conn_term = THFC_pair THF_pair_connective
                   | THFC_assoc Assoc_connective
                   | THFC_unary THF_unary_connective
                     deriving (Show, Ord, Eq, Data, Typeable)

-- <thf_conditional>      ::= $ite(<thf_logic_formula>,<thf_logic_formula>,
--                             <thf_logic_formula>)
data THF_conditional = THF_conditional THF_logic_formula THF_logic_formula THF_logic_formula -- $ite
                       deriving (Show, Ord, Eq, Data, Typeable)

-- %----The LHS of a term or formula binding must be a non-variable term that
-- %----is flat with pairwise distinct variable arguments, and the variables in
-- %----the LHS must be exactly those bound in the universally quantified variable
-- %----list, in the same order. Let definitions are not recursive: a non-variable
-- %----symbol introduced in the LHS of a let definition cannot occur in the RHS.
-- %----If a symbol with the same signature as the one in the LHS of the binding
-- %----is declared above the let expression (at the top level or in an
-- %----encompassing let) then it can be used in the RHS of the binding, but it is
-- %----not accessible in the term or formula of the let expression. Let
-- %----expressions can be eliminated by a simple definition expansion.
-- <thf_let>              ::= $let(<thf_unitary_formula>,<thf_formula>)
-- <thf_let>              :== $let(<thf_let_defns>,<thf_formula>)
data THF_let = THF_let THF_let_defns THF_formula
               deriving (Show, Ord, Eq, Data, Typeable)

-- <thf_let_defns>        :== <thf_let_defn> | [<thf_let_defn_list>]
data THF_let_defns = THFLD_single THF_let_defn
                   | THFLD_many THF_let_defn_list
                     deriving (Show, Ord, Eq, Data, Typeable)

-- <thf_let_defn_list>    :== <thf_let_defn> | <thf_let_defn>,<thf_let_defn_list>
type THF_let_defn_list = [THF_let_defn]

-- <thf_let_defn>         :== <thf_let_quantified_defn> | <thf_let_plain_defn>
data THF_let_defn = THFLD_quantified THF_let_quantified_defn
                  | THFLD_plain THF_let_plain_defn
                    deriving (Show, Ord, Eq, Data, Typeable)

-- <thf_let_quantified_defn> :== <thf_quantification> (<thf_let_plain_defn>)
data THF_let_quantified_defn = THF_let_quantified_defn THF_quantification THF_let_plain_defn
                               deriving (Show, Ord, Eq, Data, Typeable)

-- <thf_let_plain_defn>   :== <thf_let_defn_LHS> <assignment> <thf_formula>
data THF_let_plain_defn = THF_let_plain_defn THF_let_defn_LHS THF_formula
                          deriving (Show, Ord, Eq, Data, Typeable)

-- <thf_let_defn_LHS>     :== <constant> | <functor>(<fof_arguments>) |
--                            <thf_tuple>
-- %----The <fof_arguments> must all be <variable>s, and the <thf_tuple> may
-- %----contain only <constant>s and <functor>(<fof_arguments>)s
data THF_let_defn_LHS = THFLDL_constant Constant
                      | THFLDL_functor TPTP_functor FOF_arguments
                      | THFLDL_tuple THF_tuple
                        deriving (Show, Ord, Eq, Data, Typeable)

-- <thf_arguments>        ::= <thf_formula_list>
type THF_arguments = THF_formula_list

-- <thf_type_formula>     ::= <thf_typeable_formula> : <thf_top_level_type>
-- <thf_type_formula>     :== <constant> : <thf_top_level_type>
data THF_type_formula = THFTF_typeable THF_typeable_formula THF_top_level_type
                      | THFTF_constant Constant THF_top_level_type
                        deriving (Show, Ord, Eq, Data, Typeable)

-- <thf_typeable_formula> ::= <thf_atom> | (<thf_logic_formula>)
data THF_typeable_formula = THFTF_atom THF_atom
                          | THFTF_logic THF_logic_formula
                            deriving (Show, Ord, Eq, Data, Typeable)

-- <thf_subtype>          ::= <thf_atom> <subtype_sign> <thf_atom>
data THF_subtype = THF_subtype THF_atom THF_atom
                   deriving (Show, Ord, Eq, Data, Typeable)


-- %----<thf_top_level_type> appears after ":", where a type is being specified
-- %----for a term or variable. <thf_unitary_type> includes <thf_unitary_formula>,
-- %----so the syntax allows just about any lambda expression with "enough"
-- %----parentheses to serve as a type. The expected use of this flexibility is
-- %----parametric polymorphism in types, expressed with lambda abstraction.
-- %----Mapping is right-associative: o > o > o means o > (o > o).
-- %----Xproduct is left-associative: o * o * o means (o * o) * o.
-- %----Union is left-associative: o + o + o means (o + o) + o.
-- <thf_top_level_type>   ::= <thf_unitary_type> | <thf_mapping_type>
data THF_top_level_type = THFTLT_unitary THF_unitary_type
                        | THFTLT_mapping THF_mapping_type
                          deriving (Show, Ord, Eq, Data, Typeable)

-- <thf_unitary_type>     ::= <thf_unitary_formula> | (<thf_binary_type>)
data THF_unitary_type = THFUT_unitary THF_unitary_formula
                      | THFUT_binary THF_binary_type
                        deriving (Show, Ord, Eq, Data, Typeable)

-- Each of these binary types has at least two (!) list entries.
-- <thf_binary_type>      ::= <thf_mapping_type> | <thf_xprod_type> |
--                            <thf_union_type>
data THF_binary_type = THFBT_mapping THF_mapping_type
                     | THFBT_xprod THF_xprod_type
                     | THFBT_union THF_union_type
                       deriving (Show, Ord, Eq, Data, Typeable)

-- <thf_mapping_type>     ::= <thf_unitary_type> <arrow> <thf_unitary_type> |
--                            <thf_unitary_type> <arrow> <thf_mapping_type>
type THF_mapping_type = [THF_unitary_type] -- right associative

-- <thf_xprod_type>       ::= <thf_unitary_type> <star> <thf_unitary_type> |
--                            <thf_xprod_type> <star> <thf_unitary_type>
type THF_xprod_type = [THF_unitary_type] -- left associative

-- <thf_union_type>       ::= <thf_unitary_type> <plus> <thf_unitary_type> |
--                            <thf_union_type> <plus> <thf_unitary_type>
type THF_union_type = [THF_unitary_type] -- right associative

-- %----Sequents using the Gentzen arrow
-- <thf_sequent>          ::= <thf_tuple> <gentzen_arrow> <thf_tuple> |
--                            (<thf_sequent>)
data THF_sequent = THFS_plain THF_tuple THF_tuple
                 | THFS_parens THF_sequent
                   deriving (Show, Ord, Eq, Data, Typeable)

-- <thf_tuple>            ::= [] | [<thf_formula_list>]
newtype THF_tuple = THF_tuple THF_formula_list
                    deriving (Show, Ord, Eq, Data, Typeable)

-- <thf_formula_list>     ::= <thf_logic_formula> |
--                            <thf_logic_formula>,<thf_formula_list>
type THF_formula_list = [THF_logic_formula]

-- NOTE: not used by parser
-- %----New material for modal logic semantics, not integrated yet
-- <logic_defn_rule>      :== <logic_defn_LHS> <assignment> <logic_defn_RHS>-
-- data Logic_defn_rule = Logic_defn_rule Logic_defn_LHS Logic_defn_RHS
--                        deriving (Show, Ord, Eq, Data, Typeable)

-- NOTE: not used by parser
-- <logic_defn_LHS>       :== <logic_defn_value> | <thf_top_level_type>  | <name>
-- <logic_defn_LHS>       :== $constants | $quantification | $consequence |
--                            $modalities
--                            %----The $constants, $quantification, and $consequence apply to all of the
--                            %----$modalities. Each of these may be specified only once, but not necessarily
--                            %----all in a single annotated formula.-
-- data Logic_defn_LHS = Logic_defn_LHS_value Logic_defn_value
--                     | Logic_defn_LHS_THF_Top_level_type THF_top_level_type
--                     | Logic_defn_LHS_name Name
--                     | LDLC_constants
--                     | LDLC_quantification
--                     | LDLC_consequence
--                     | LDLC_modalities
--                       deriving (Show, Ord, Eq, Data, Typeable)

-- NOTE: not used by parser
-- <logic_defn_RHS>       :== <logic_defn_value> | <thf_unitary_formula>-
-- data Logic_defn_RHS = Logic_defn_RHS_value Logic_defn_value
--                     | Logic_defn_RNG_THF_Unitary_forumla THF_unitary_formula
--                       deriving (Show, Ord, Eq, Data, Typeable)

-- NOTE: not used by parser
-- <logic_defn_value>     :== <defined_constant>
-- <logic_defn_value>     :== $rigid | $flexible |
--                            $constant | $varying | $cumulative | $decreasing |
--                            $local | $global |
--                            $modal_system_K | $modal_system_T | $modal_system_D |
--                            $modal_system_S4 | $modal_system_S5 |
--                            $modal_axiom_K | $modal_axiom_T | $modal_axiom_B |
--                            $modal_axiom_D | $modal_axiom_4 | $modal_axiom_5-
-- data Logic_defn_value = Rigid
--                       | Flexible
--                       | Constant
--                       | Varying
--                       | Cumulative
--                       | Decreasing
--                       | Local
--                       | Global
--                       | Modal_system_K
--                       | Modal_system_T
--                       | Modal_system_D
--                       | Modal_system_S4
--                       | Modal_system_S5
--                       | Modal_axiom_K
--                       | Modal_axiom_T
--                       | Modal_axiom_B
--                       | Modal_axiom_D
--                       | Modal_axiom_4
--                       | Modal_axiom_5
--                       deriving (Show, Ord, Eq, Data, Typeable)

-- %----TFX formulae
-- <tfx_formula>          ::= <tfx_logic_formula> | <thf_sequent>
data TFX_formula = TFXF_logic TFX_logic_formula
                 | TFXF_sequent THF_sequent
                   deriving (Show, Ord, Eq, Data, Typeable)

-- <tfx_logic_formula>    ::= <thf_logic_formula>
-- % <tfx_logic_formula>    ::= <thf_binary_formula> | <thf_unitary_formula> |
-- %                            <tff_typed_atom> | <tff_subtype>
data TFX_logic_formula = TFXLF_binary THF_binary_formula
                       | TFXLF_unitary THF_unitary_formula
                       | TFXLF_typed TFF_typed_atom
                       | TFXLF_subtype TFF_subtype
                         deriving (Show, Ord, Eq, Data, Typeable)

-- %----TFF formulae.
-- <tff_formula>          ::= <tff_logic_formula> | <tff_typed_atom> |
--                            <tff_sequent>
data TFF_formula = TFFF_logic TFF_logic_formula
                 | TFFF_atom TFF_typed_atom
                 | TFFF_sequent TFF_sequent
                   deriving (Show, Ord, Eq, Data, Typeable)

-- <tff_logic_formula>    ::= <tff_binary_formula> | <tff_unitary_formula> |
--                            <tff_subtype>
data TFF_logic_formula = TFFLF_binary TFF_binary_formula
                       | TFFLF_unitary TFF_unitary_formula
                       | TFFLF_subtype TFF_subtype
                         deriving (Show, Ord, Eq, Data, Typeable)

-- <tff_binary_formula>   ::= <tff_binary_nonassoc> | <tff_binary_assoc>
data TFF_binary_formula = TFFBF_nonassoc TFF_binary_nonassoc
                        | TFFBF_assoc TFF_binary_assoc
                          deriving (Show, Ord, Eq, Data, Typeable)

-- <tff_binary_nonassoc>  ::= <tff_unitary_formula> <binary_connective>
--                            <tff_unitary_formula>
data TFF_binary_nonassoc = TFF_binary_nonassoc Binary_connective TFF_unitary_formula TFF_unitary_formula
                           deriving (Show, Ord, Eq, Data, Typeable)

-- <tff_binary_assoc>     ::= <tff_or_formula> | <tff_and_formula>
data TFF_binary_assoc = TFFBA_or TFF_or_formula
                      | TFFBA_and TFF_and_formula
                        deriving (Show, Ord, Eq, Data, Typeable)

-- <tff_or_formula>       ::= <tff_unitary_formula> <vline> <tff_unitary_formula> |
--                            <tff_or_formula> <vline> <tff_unitary_formula>
type TFF_or_formula = [TFF_unitary_formula]

-- <tff_and_formula>      ::= <tff_unitary_formula> & <tff_unitary_formula> |
--                            <tff_and_formula> & <tff_unitary_formula>
type TFF_and_formula = [TFF_unitary_formula]

-- <tff_unitary_formula>  ::= <tff_quantified_formula> | <tff_unary_formula> |
--                            <tff_atomic_formula> | <tff_conditional> |
--                            <tff_let> | (<tff_logic_formula>)
data TFF_unitary_formula = TFFUF_quantified TFF_quantified_formula
                         | TFFUF_unary TFF_unary_formula
                         | TFFUF_atomic TFF_atomic_formula
                         | TFFUF_conditional TFF_conditional
                         | TFFUF_let TFF_let
                         | TFFUF_logic TFF_logic_formula
                           deriving (Show, Ord, Eq, Data, Typeable)

-- <tff_quantified_formula> ::= <fof_quantifier> [<tff_variable_list>] :
--                            <tff_unitary_formula>
data TFF_quantified_formula = TFF_quantified_formula FOF_quantifier TFF_variable_list TFF_unitary_formula
                              deriving (Show, Ord, Eq, Data, Typeable)

-- <tff_variable_list>    ::= <tff_variable> | <tff_variable>,<tff_variable_list>
type TFF_variable_list = [TFF_variable]

-- <tff_variable>         ::= <tff_typed_variable> | <variable>
data TFF_variable = TFFV_typed TFF_typed_variable
                  | TFFV_variable Variable
                    deriving (Show, Ord, Eq, Data, Typeable)

-- <tff_typed_variable>   ::= <variable> : <tff_atomic_type>
data TFF_typed_variable = TFF_typed_variable Variable TFF_atomic_type
                          deriving (Show, Ord, Eq, Data, Typeable)

-- <tff_unary_formula>    ::= <unary_connective> <tff_unitary_formula> |
--                            <fof_infix_unary>
data TFF_unary_formula = TFFUF_connective Unary_connective TFF_unitary_formula
                       | TFFUF_infix FOF_infix_unary
                         deriving (Show, Ord, Eq, Data, Typeable)

-- <tff_atomic_formula>   ::= <fof_atomic_formula>
type TFF_atomic_formula = FOF_atomic_formula

-- <tff_conditional>      ::= $ite_f(<tff_logic_formula>,<tff_logic_formula>,
--                            <tff_logic_formula>)
data TFF_conditional = TFF_conditional TFF_logic_formula TFF_logic_formula TFF_logic_formula -- $ite_f
                       deriving (Show, Ord, Eq, Data, Typeable)

-- <tff_let>              ::= $let_tf(<tff_let_term_defns>,<tff_formula>) |
--                            $let_ff(<tff_let_formula_defns>,<tff_formula>)
data TFF_let = TFF_let_term_defns TFF_let_term_defns TFF_formula
             | TFF_let_formula_defns TFF_let_formula_defns TFF_formula
               deriving (Show, Ord, Eq, Data, Typeable)

-- %----See the commentary for <thf_let>.
-- <tff_let_term_defns>   ::= <tff_let_term_defn> | [<tff_let_term_list>]
data TFF_let_term_defns = TFFLTD_single TFF_let_term_defn
                        | TFFLTD_many TFF_let_term_list
                          deriving (Show, Ord, Eq, Data, Typeable)

-- <tff_let_term_list>    ::= <tff_let_term_defn> |
--                            <tff_let_term_defn>,<tff_let_term_list>
type TFF_let_term_list = [TFF_let_term_defn]

-- <tff_let_term_defn>    ::= ! [<tff_variable_list>] : <tff_let_term_defn> |
--                            <tff_let_term_binding>
data TFF_let_term_defn = TFFLTD_variable TFF_variable_list TFF_let_term_defn
                       | TFFLTD_binding TFF_let_term_binding
                         deriving (Show, Ord, Eq, Data, Typeable)

-- <tff_let_term_binding> ::= <fof_plain_term> = <fof_term> |
--                            (<tff_let_term_binding>)
data TFF_let_term_binding = TFFLTB_plain FOF_plain_term FOF_term
                          | TFFLTB_binding TFF_let_term_binding
                            deriving (Show, Ord, Eq, Data, Typeable)

-- <tff_let_formula_defns> ::= <tff_let_formula_defn> | [<tff_let_formula_list>]
data TFF_let_formula_defns = TFFLFD_single TFF_let_formula_defn
                           | TFFLFD_many TFF_let_formula_list
                             deriving (Show, Ord, Eq, Data, Typeable)

-- <tff_let_formula_list> ::= <tff_let_formula_defn> |
--                            <tff_let_formula_defn>,<tff_let_formula_list>
type TFF_let_formula_list = [TFF_let_formula_defn]

-- <tff_let_formula_defn> ::= ! [<tff_variable_list>] : <tff_let_formula_defn> |
--                            <tff_let_formula_binding>
data TFF_let_formula_defn = TFFLFD_variable TFF_variable_list TFF_let_formula_defn
                          | TFFLFD_binding TFF_let_formula_binding
                            deriving (Show, Ord, Eq, Data, Typeable)

-- <tff_let_formula_binding> ::= <fof_plain_atomic_formula> <=>
--                            <tff_unitary_formula> | (<tff_let_formula_binding>)
data TFF_let_formula_binding = TFFLFB_plain FOF_plain_atomic_formula TFF_unitary_formula
                             | TFFLFB_binding TFF_let_formula_binding
                               deriving (Show, Ord, Eq, Data, Typeable)

-- <tff_sequent>          ::= <tff_formula_tuple> <gentzen_arrow>
--                            <tff_formula_tuple> | (<tff_sequent>)
data TFF_sequent = TFFS_plain TFF_formula_tuple TFF_formula_tuple
                 | TFFS_parens TFF_sequent
                   deriving (Show, Ord, Eq, Data, Typeable)

-- <tff_formula_tuple>    ::= [] | [<tff_formula_tuple_list>]
newtype TFF_formula_tuple = TFF_formula_tuple TFF_formula_tuple_list
                            deriving (Show, Ord, Eq, Data, Typeable)

-- <tff_formula_tuple_list> ::= <tff_logic_formula> |
--                            <tff_logic_formula>,<tff_formula_tuple_list>
type TFF_formula_tuple_list = [TFF_logic_formula]

-- %----<tff_typed_atom> can appear only at top level
-- <tff_typed_atom>       ::= <untyped_atom> : <tff_top_level_type> |
--                            (<tff_typed_atom>)
data TFF_typed_atom = TFFTA_plain Untyped_atom TFF_top_level_type
                    | TFFTA_parens TFF_typed_atom
                      deriving (Show, Ord, Eq, Data, Typeable)

-- <tff_subtype>          ::= <untyped_atom> <subtype_sign> <atom>
data TFF_subtype = TFF_subtype Untyped_atom Atom
                   deriving (Show, Ord, Eq, Data, Typeable)

-- %----See <thf_top_level_type> for commentary.
-- <tff_top_level_type>   ::= <tff_atomic_type> | <tff_mapping_type> |
--                            <tf1_quantified_type> | (<tff_top_level_type>)
data TFF_top_level_type = TFFTLT_atomic TFF_atomic_type
                        | TFFTLT_mapping TFF_mapping_type
                        | TFFTLT_quantified TF1_quantified_type
                        | TFFTLT_parens TFF_top_level_type
                          deriving (Show, Ord, Eq, Data, Typeable)

-- <tf1_quantified_type>  ::= !> [<tff_variable_list>] : <tff_monotype>
data TF1_quantified_type = TF1_quantified_type TFF_variable_list TFF_monotype
                           deriving (Show, Ord, Eq, Data, Typeable)

-- <tff_monotype>         ::= <tff_atomic_type> | (<tff_mapping_type>)
data TFF_monotype = TFFMT_atomic TFF_atomic_type
                  | TFFMT_mapping TFF_mapping_type
                    deriving (Show, Ord, Eq, Data, Typeable)

-- <tff_unitary_type>     ::= <tff_atomic_type> | (<tff_xprod_type>)
data TFF_unitary_type = TFFUT_atomic TFF_atomic_type
                      | TFFUT_xprod TFF_xprod_type
                        deriving (Show, Ord, Eq, Data, Typeable)
-- <tff_atomic_type>      ::= <type_constant> | <defined_type> |
--                            <type_functor>(<tff_type_arguments>) | <variable>
data TFF_atomic_type = TFFAT_constant Type_constant
                     | TFFAT_defined Defined_type
                     | TFFAT_functor Type_functor TFF_type_arguments
                     | TFFAT_variable Variable
                       deriving (Show, Ord, Eq, Data, Typeable)

-- <tff_type_arguments>   ::= <tff_atomic_type> |
--                            <tff_atomic_type>,<tff_type_arguments>
type TFF_type_arguments = [TFF_atomic_type]

-- %----For consistency with <thf_unitary_type> (the analogue in thf),
-- %----<tff_atomic_type> should also allow (<tff_atomic_type>), but that causes
-- %----ambiguity.
-- <tff_mapping_type>     ::= <tff_unitary_type> <arrow> <tff_atomic_type>
data TFF_mapping_type = TFF_mapping_type TFF_unitary_type TFF_atomic_type
                        deriving (Show, Ord, Eq, Data, Typeable)

-- <tff_xprod_type>       ::= <tff_unitary_type> <star> <tff_atomic_type> |
--                            <tff_xprod_type> <star> <tff_atomic_type>
data TFF_xprod_type = TFF_xprod_type TFF_unitary_type [TFF_atomic_type]
                      deriving (Show, Ord, Eq, Data, Typeable)


-- %----TCF formulae.
-- <tcf_formula>          ::= <tcf_logic_formula> | <tff_typed_atom>
data TCF_formula = TCFF_logic TCF_logic_formula
                 | TCFF_atom TFF_typed_atom
                   deriving (Show, Ord, Eq, Data, Typeable)

-- <tcf_logic_formula>    ::= <tcf_quantified_formula> | <cnf_formula>
data TCF_logic_formula = TCFLF_quantified TCF_quantified_formula
                       | TCFLF_cnf CNF_formula
                         deriving (Show, Ord, Eq, Data, Typeable)

-- <tcf_quantified_formula> ::= ! [<tff_variable_list>] : <cnf_formula>
data TCF_quantified_formula = TCF_quantified TFF_variable_list CNF_formula
                              deriving (Show, Ord, Eq, Data, Typeable)


-- %----FOF formulae.
-- <fof_formula>          ::= <fof_logic_formula> | <fof_sequent>
data FOF_formula = FOFF_logic FOF_logic_formula
                 | FOFF_sequent FOF_sequent
                   deriving (Show, Ord, Eq, Data, Typeable)

-- <fof_logic_formula>    ::= <fof_binary_formula> | <fof_unitary_formula>
data FOF_logic_formula = FOFLF_binary FOF_binary_formula
                       | FOFLF_unitary FOF_unitary_formula
                         deriving (Show, Ord, Eq, Data, Typeable)

-- %----Future answer variable ideas | <answer_formula>
-- <fof_binary_formula>   ::= <fof_binary_nonassoc> | <fof_binary_assoc>
data FOF_binary_formula = FOFBF_nonassoc FOF_binary_nonassoc
                        | FOFBF_assoc FOF_binary_assoc
                          deriving (Show, Ord, Eq, Data, Typeable)

-- %----Only some binary connectives are associative
-- %----There's no precedence among binary connectives
-- <fof_binary_nonassoc>  ::= <fof_unitary_formula> <binary_connective>
--                            <fof_unitary_formula>
data FOF_binary_nonassoc = FOF_binary_nonassoc Binary_connective FOF_unitary_formula FOF_unitary_formula
                           deriving (Show, Ord, Eq, Data, Typeable)

-- %----Associative connectives & and | are in <binary_assoc>
-- <fof_binary_assoc>     ::= <fof_or_formula> | <fof_and_formula>
data FOF_binary_assoc = FOFBA_or FOF_or_formula
                      | FOFBA_and FOF_and_formula
                        deriving (Show, Ord, Eq, Data, Typeable)

-- <fof_or_formula>       ::= <fof_unitary_formula> <vline> <fof_unitary_formula> |
--                            <fof_or_formula> <vline> <fof_unitary_formula>
type FOF_or_formula = [FOF_unitary_formula]

-- <fof_and_formula>      ::= <fof_unitary_formula> & <fof_unitary_formula> |
--                            <fof_and_formula> & <fof_unitary_formula>
type FOF_and_formula = [FOF_unitary_formula]

-- %----<fof_unitary_formula> are in ()s or do not have a <binary_connective> at
-- %----the top level.
-- <fof_unitary_formula>  ::= <fof_quantified_formula> | <fof_unary_formula> |
--                            <fof_atomic_formula> | (<fof_logic_formula>)
data FOF_unitary_formula = FOFUF_quantified FOF_quantified_formula
                         | FOFUF_unary FOF_unary_formula
                         | FOFUF_atomic FOF_atomic_formula
                         | FOFUF_logic FOF_logic_formula
                           deriving (Show, Ord, Eq, Data, Typeable)

-- <fof_quantified_formula> ::= <fof_quantifier> [<fof_variable_list>] :
--                            <fof_unitary_formula>
data FOF_quantified_formula = FOF_quantified_formula FOF_quantifier FOF_variable_list FOF_unitary_formula
                              deriving (Show, Ord, Eq, Data, Typeable)

-- <fof_variable_list>    ::= <variable> | <variable>,<fof_variable_list>
type FOF_variable_list = [Variable]

-- <fof_unary_formula>    ::= <unary_connective> <fof_unitary_formula> |
--                            <fof_infix_unary>
data FOF_unary_formula = FOFUF_connective Unary_connective FOF_unitary_formula
                       | FOFUF_infix FOF_infix_unary
                         deriving (Show, Ord, Eq, Data, Typeable)

-- <fof_infix_unary>      ::= <fof_term> <infix_inequality> <fof_term>
data FOF_infix_unary = FOF_infix_unary FOF_term FOF_term
                       deriving (Show, Ord, Eq, Data, Typeable)

-- <fof_atomic_formula>   ::= <fof_plain_atomic_formula> |
--                            <fof_defined_atomic_formula> |
--                            <fof_system_atomic_formula>
data FOF_atomic_formula = FOFAT_plain FOF_plain_atomic_formula
                        | FOFAT_defined FOF_defined_atomic_formula
                        | FOFAT_system FOF_system_atomic_formula
                          deriving (Show, Ord, Eq, Data, Typeable)

-- <fof_plain_atomic_formula> ::= <fof_plain_term>
-- <fof_plain_atomic_formula> :== <proposition> | <predicate>(<fof_arguments>)
data FOF_plain_atomic_formula = FOFPAF_proposition Proposition
                              | FOFPAF_predicate Predicate FOF_arguments
                                deriving (Show, Ord, Eq, Data, Typeable)

-- <fof_defined_atomic_formula> ::= <fof_defined_plain_formula> |
--                            <fof_defined_infix_formula>
data FOF_defined_atomic_formula = FOFDAF_plain FOF_defined_plain_formula
                                | FOFDAF_infix FOF_defined_infix_formula
                                  deriving (Show, Ord, Eq, Data, Typeable)

-- <fof_defined_plain_formula> ::= <fof_defined_plain_term>
-- <fof_defined_plain_formula> :== <defined_proposition> |
--                            <defined_predicate>(<fof_arguments>)
data FOF_defined_plain_formula = FOFDPF_proposition Defined_proposition
                               | FOFDPF_predicate Defined_predicate FOF_arguments
                                 deriving (Show, Ord, Eq, Data, Typeable)

-- <fof_defined_infix_formula> ::= <fof_term> <defined_infix_pred> <fof_term>
data FOF_defined_infix_formula = FOF_defined_infix_formula Defined_infix_pred FOF_term FOF_term
                                 deriving (Show, Ord, Eq, Data, Typeable)

-- %----System terms have system specific interpretations
-- <fof_system_atomic_formula> ::= <fof_system_term>
-- %----<fof_system_atomic_formula>s are used for evaluable predicates that are
-- %----available in particular tools. The predicate names are not controlled
-- %----by the TPTP syntax, so use with due care. The same is true for
-- %----<fof_system_term>s.
newtype FOF_system_atomic_formula = FOF_system_atomic_formula FOF_system_term
                                    deriving (Show, Ord, Eq, Data, Typeable)

-- %----FOF terms.
-- <fof_plain_term>       ::= <constant> | <functor>(<fof_arguments>)
data FOF_plain_term = FOFPT_constant Constant
                    | FOFPT_functor TPTP_functor FOF_arguments
                      deriving (Show, Ord, Eq, Data, Typeable)

-- %----Defined terms have TPTP specific interpretations
-- <fof_defined_term>     ::= <defined_term> | <fof_defined_atomic_term>
data FOF_defined_term = FOFDT_term Defined_term
                      | FOFDT_atomic FOF_defined_atomic_term
                        deriving (Show, Ord, Eq, Data, Typeable)

-- <fof_defined_atomic_term>  ::= <fof_defined_plain_term>
-- %----None yet             | <defined_infix_term>
data FOF_defined_atomic_term = FOFDAT_plain FOF_defined_plain_term
                             -- | FOFDAT_indix Defined_infix_term
                               deriving (Show, Ord, Eq, Data, Typeable)

-- %----None yet <defined_infix_term> ::= <fof_term> <defined_infix_func> <fof_term>
-- data Defined_infix_term = Defined_infix_term Defined_infix_func FOF_term FOF_term
--                           deriving (Show, Ord, Eq, Data, Typeable)

-- %----None yet <defined_infix_func> ::=
-- data Defined_infix_func =

-- <fof_defined_plain_term>   ::= <defined_constant> |
--                            <defined_functor>(<fof_arguments>)
-- %----Add $tuple for tuples, because [<fof_arguments>] doesn't work.
data FOF_defined_plain_term = FOFDPT_constant Defined_constant
                            | FOFDPT_functor Defined_functor FOF_arguments
                              deriving (Show, Ord, Eq, Data, Typeable)

-- %----System terms have system specific interpretations
-- <fof_system_term>      ::= <system_constant> | <system_functor>(<fof_arguments>)
data FOF_system_term = FOFST_constant System_constant
                     | FOFST_functor System_functor FOF_arguments
                       deriving (Show, Ord, Eq, Data, Typeable)

-- %----Arguments recurse back up to terms (this is the FOF world here)
-- <fof_arguments>        ::= <fof_term> | <fof_term>,<fof_arguments>
type FOF_arguments = [FOF_term]

-- %----These are terms used as arguments. Not the entry point for terms because
-- %----<fof_plain_term> is also used as <fof_plain_atomic_formula>
-- <fof_term>             ::= <fof_function_term> | <variable> |
--                            <tff_conditional_term> | <tff_let_term>
data FOF_term = FOFT_function FOF_function_term
              | FOFT_variable Variable
              | FOFT_conditional TFF_conditional_term
              | FOFT_let TFF_let_term
                deriving (Show, Ord, Eq, Data, Typeable)

-- %% DAMN THIS JUST WON'T WORK | <tuple_term>
-- %----<tuple_term> is for TFF only, but it's here because it's used in
-- %----<fof_atomic_formula>, which is also used as <tff_atomic_formula>.
-- % <tuple_term>           ::= [] | [<fof_arguments>]
-- <fof_function_term>    ::= <fof_plain_term> | <fof_defined_term> |
--                            <fof_system_term>
data FOF_function_term = FOFFT_plain FOF_plain_term
                       | FOFFT_defined FOF_defined_term
                       | FOFFT_system FOF_system_term
                         deriving (Show, Ord, Eq, Data, Typeable)

-- %----Conditional terms should be used by only TFF.
-- <tff_conditional_term> ::= $ite_t(<tff_logic_formula>,<fof_term>,<fof_term>)
data TFF_conditional_term = TFF_conditional_term TFF_logic_formula FOF_term FOF_term
                            deriving (Show, Ord, Eq, Data, Typeable)

-- %----Let terms should be used by only TFF. $let_ft is for use when there is
-- %----a $ite_t in the <fof_term>. See the commentary for $let_tf and $let_ff.
-- <tff_let_term>         ::= $let_ft(<tff_let_formula_defns>,<fof_term>) |
--                            $let_tt(<tff_let_term_defns>,<fof_term>)
data TFF_let_term = TFFLT_formula TFF_let_formula_defns FOF_term
                  | TFFLT_term TFF_let_term_defns FOF_term
                    deriving (Show, Ord, Eq, Data, Typeable)

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

-- <fof_sequent>          ::= <fof_formula_tuple> <gentzen_arrow>
--                            <fof_formula_tuple> | (<fof_sequent>)
data FOF_sequent = FOFS_plain FOF_formula_tuple FOF_formula_tuple
                 | FOFS_parens FOF_sequent
                   deriving (Show, Ord, Eq, Data, Typeable)

-- <fof_formula_tuple>    ::= [] | [<fof_formula_tuple_list>]
newtype FOF_formula_tuple = FOF_formula_tuple FOF_formula_tuple_list
                            deriving (Show, Ord, Eq, Data, Typeable)

-- <fof_formula_tuple_list> ::= <fof_logic_formula> |
--                            <fof_logic_formula>,<fof_formula_tuple_list>
type FOF_formula_tuple_list = [FOF_logic_formula]


-- %----CNF formulae (variables implicitly universally quantified)
-- <cnf_formula>          ::= <disjunction> | (<disjunction>)
data CNF_formula = CNFF_plain Disjunction
                 | CNFF_parens Disjunction
                   deriving (Show, Ord, Eq, Data, Typeable)

-- <disjunction>          ::= <literal> | <disjunction> <vline> <literal>
newtype Disjunction = Disjunction [Literal]
                      deriving (Show, Ord, Eq, Data, Typeable)

-- <literal>              ::= <fof_atomic_formula> | ~ <fof_atomic_formula> |
--                            <fof_infix_unary>
data Literal = Lit_atomic FOF_atomic_formula
             | Lit_negative FOF_atomic_formula
             | Lit_fof_infix FOF_infix_unary
               deriving (Show, Ord, Eq, Data, Typeable)



-- %----Connectives - THF
-- <thf_quantifier>       ::= <fof_quantifier> | <th0_quantifier> |
--                            <th1_quantifier>
data THF_quantifier = THFQ_fof FOF_quantifier
                    | THFQ_th0 TH0_quantifier
                    | THFQ_th1 TH1_quantifier
                      deriving (Show, Ord, Eq, Data, Typeable)


-- %----TH0 quantifiers are also available in TH1
-- <th1_quantifier>       ::= !> | ?*
data TH1_quantifier = TH1_DependentProduct       -- !>
                    | TH1_DependentSum           -- ?*
                      deriving (Show, Ord, Eq, Data, Typeable)

-- <th0_quantifier>       ::= ^ | @+ | @-
data TH0_quantifier = TH0_LambdaBinder           -- ^
                    | TH0_IndefiniteDescription  -- @+
                    | TH0_DefiniteDescription    -- @-
                      deriving (Show, Ord, Eq, Data, Typeable)

-- <thf_pair_connective>  ::= <infix_equality> | <infix_inequality> |
--                            <binary_connective> | <assignment>
data THF_pair_connective = THF_infix_equality
                         | Infix_inequality
                         | THFPC_binary Binary_connective
                         | THF_assignment
                           deriving (Show, Ord, Eq, Data, Typeable)

-- <thf_unary_connective> ::= <unary_connective> | <th1_unary_connective>
data THF_unary_connective = THFUC_unary Unary_connective
                          | THFUC_th1 TH1_unary_connective
                            deriving (Show, Ord, Eq, Data, Typeable)

-- <th1_unary_connective> ::= !! | ?? | @@+ | @@- | @=
data TH1_unary_connective = TH1_PiForAll                -- !!
                          | TH1_PiSigmaExists           -- ??
                          | TH1_PiIndefiniteDescription -- @@+
                          | TH1_PiDefiniteDescription   -- @@-
                          | TH1_PiEquality              -- @=
                            deriving (Show, Ord, Eq, Data, Typeable)


-- %----Connectives - TFF
-- % <tff_pair_connective>  ::= <binary_connective> | <assignment>
-- Note: not used
-- data TFF_pair_connective = TFFPC_binary Binary_connective
--                          | TFFPC_assignment TFF_assignment
--                            deriving (Show, Ord, Eq, Data, Typeable)

-- %----Connectives - FOF
-- <fof_quantifier>       ::= ! | ?
data FOF_quantifier = ForAll -- !
                    | Exists -- ?
                      deriving (Show, Ord, Eq, Data, Typeable)

-- <binary_connective>    ::= <=> | => | <= | <~> | ~<vline> | ~&
data Binary_connective = Equivalence
                       | Implication
                       | ReverseImplication
                       | XOR
                       | NOR
                       | NAND
                         deriving (Show, Ord, Eq, Data, Typeable)

-- <assoc_connective>     ::= <vline> | &
data Assoc_connective = OR
                      | AND
                        deriving (Show, Ord, Eq, Data, Typeable)

-- <unary_connective>     ::= ~
data Unary_connective = NOT deriving (Show, Ord, Eq, Data, Typeable)


-- %----Types for THF and TFF
-- <type_constant>        ::= <type_functor>
type Type_constant = Type_functor

-- <type_functor>         ::= <atomic_word>
type Type_functor = Token

-- <defined_type>         ::= <atomic_defined_word>
-- <defined_type>         :== $oType | $o | $iType | $i | $tType |
--                            $real | $rat | $int
data Defined_type = OType -- $oType/$o is the Boolean type, i.e., the type of $true and $false.
                  | O     -- $oType/$o is the Boolean type, i.e., the type of $true and $false.
                  | IType -- $iType/$i is non-empty type of individuals, which may be finite or infinite.
                  | I     -- $iType/$i is non-empty type of individuals, which may be finite or infinite.
                  | TType -- $tType is the type (kind) of all types.
                  | Real  -- $real is the type of <real>s.
                  | Rat   -- $rat is the type of <rational>s.
                  | Int   -- $int is the type of <signed_integer>s and <unsigned_integer>s.
                    deriving (Show, Ord, Eq, Data, Typeable)

-- <system_type>          :== <atomic_system_word>
-- Note: not used
-- type System_type = Token

-- %----For all language types
-- <atom>                 ::= <untyped_atom> | <defined_constant>
data Atom = Atom_untyped Untyped_atom
          | Atom_constant Defined_constant
            deriving (Show, Ord, Eq, Data, Typeable)

-- <untyped_atom>         ::= <constant> | <system_constant>
data Untyped_atom = UA_constant Constant
                  | UA_system System_constant
                    deriving (Show, Ord, Eq, Data, Typeable)

type Proposition = Predicate
type Predicate = Token

-- <defined_proposition>  :== <atomic_defined_word>
-- <defined_proposition>  :== $true | $false
data Defined_proposition = TPTP_true
                         | TPTP_false
                           deriving (Show, Ord, Eq, Data, Typeable)

-- <defined_predicate>    :== <atomic_defined_word>
-- <defined_predicate>    :== $distinct |
--                            $less | $lesseq | $greater | $greatereq |
--                            $is_int | $is_rat |
--                            $box_P | $box_i | $box_int | $box |
--                            $dia_P | $dia_i | $dia_int | $dia
-- %----$distinct means that each of it's constant arguments are pairwise !=. It
-- %----is part of the TFF syntax. It can be used only as a fact, not under any
-- %----connective.
data Defined_predicate = Distinct
                       | Less
                       | Lesseq
                       | Greater
                       | Greatereq
                       | Is_int
                       | Is_rat
                       | Box_P
                       | Box_i
                       | Box_int
                       | Box
                       | Dia_P
                       | Dia_i
                       | Dia_int
                       | Dia
                         deriving (Show, Ord, Eq, Data, Typeable)

-- <defined_infix_pred>   ::= <infix_equality> | <assignment>
-- <infix_equality>       ::= =
-- <infix_inequality>     ::= !=
data Defined_infix_pred = Defined_infix_equality
                        | Defined_assignment
                          deriving (Show, Ord, Eq, Data, Typeable)

-- <constant>             ::= <functor>
type Constant = TPTP_functor

-- <functor>              ::= <atomic_word>
type TPTP_functor = Token

-- <system_constant>      ::= <system_functor>
type System_constant = System_functor

-- <system_functor>       ::= <atomic_system_word>
type System_functor = Token

-- <defined_constant>     ::= <defined_functor>
type Defined_constant = Defined_functor

-- <defined_functor>      ::= <atomic_defined_word>
-- <defined_functor>      :== $uminus | $sum | $difference | $product |
--                            $quotient | $quotient_e | $quotient_t | $quotient_f |
--                            $remainder_e | $remainder_t | $remainder_f |
--                            $floor | $ceiling | $truncate | $round |
--                            $to_int | $to_rat | $to_real
data Defined_functor = Uminus
                     | Sum
                     | Difference
                     | Product
                     | Quotient
                     | Quotient_e
                     | Quotient_t
                     | Quotient_f
                     | Remainder_e
                     | Remainder_t
                     | Remainder_f
                     | Floor
                     | Ceiling
                     | Truncate
                     | Round
                     | To_int
                     | To_rat
                     | To_real
                     | DF_atomic_defined_word Atomic_defined_word
                       deriving (Show, Ord, Eq, Data, Typeable)

-- <defined_term>         ::= <number> | <distinct_object>
data Defined_term = DT_number Number
                  | DT_object Distinct_object
                    deriving (Show, Ord, Eq, Data, Typeable)

-- <variable>             ::= <upper_word>
type Variable = Token


-- %----Formula sources
-- <source>               ::= <general_term>
-- <source>               :== <dag_source> | <internal_source> |
--                            <external_source> | unknown | [<sources>]
data Source = Source_DAG DAG_source
            | Source_internal Internal_source
            | Source_external External_source
            | Unknown_source
            | Source_many Sources
              deriving (Show, Ord, Eq, Data, Typeable)

-- %----Alternative sources are recorded like this, thus allowing representation
-- %----of alternative derivations with shared parts.
-- <sources>              :== <source> | <source>,<sources>
type Sources = [Source]

-- %----Only a <dag_source> can be a <name>, i.e., derived formulae can be
-- %----identified by a <name> or an <inference_record>
-- <dag_source>           :== <name> | <inference_record>
data DAG_source = DAGS_name Name
                | DAGS_record Inference_record
                  deriving (Show, Ord, Eq, Data, Typeable)

-- <inference_record>     :== inference(<inference_rule>,<useful_info>,
--                            <inference_parents>)
data Inference_record = Inference_record Inference_rule Useful_info Inference_parents
                        deriving (Show, Ord, Eq, Data, Typeable)

-- <inference_rule>       :== <atomic_word>
-- %----Examples are          deduction | modus_tollens | modus_ponens | rewrite |
-- %                          resolution | paramodulation | factorization |
-- %                          cnf_conversion | cnf_refutation | ...
type Inference_rule = Token

-- %----<inference_parents> can be empty in cases when there is a justification
-- %----for a tautologous theorem. In case when a tautology is introduced as
-- %----a leaf, e.g., for splitting, then use an <internal_source>.
-- <inference_parents>    :== [] | [<parent_list>]
type Inference_parents = Parent_list

-- <parent_list>          :== <parent_info> | <parent_info>,<parent_list>
type Parent_list = [Parent_info]

-- <parent_info>          :== <source><parent_details>
data Parent_info = Parent_info Source Parent_details
                   deriving (Show, Ord, Eq, Data, Typeable)

-- <parent_details>       :== :<general_list> | <null>
type Parent_details = Maybe General_list

-- <internal_source>      :== introduced(<intro_type><optional_info>)
data Internal_source = Internal_source Intro_type Optional_info
                       deriving (Show, Ord, Eq, Data, Typeable)

-- <intro_type>           :== definition | axiom_of_choice | tautology | assumption
-- %----This should be used to record the symbol being defined, or the function
-- %----for the axiom of choice
data Intro_type = IntroTypeDefinition
                | AxiomOfChoice
                | Tautology
                | IntroTypeAssumption
                  deriving (Show, Ord, Eq, Data, Typeable)

-- <external_source>      :== <file_source> | <theory> | <creator_source>
data External_source = ExtSrc_file File_source
                     | ExtSrc_theory Theory
                     | ExtSrc_creator Creator_source
                       deriving (Show, Ord, Eq, Data, Typeable)

-- <file_source>          :== file(<file_name><file_info>)
data File_source = File_source File_name File_info
                   deriving (Show, Ord, Eq, Data, Typeable)

-- <file_info>            :== ,<name> | <null>
type File_info = Maybe Name

-- <theory>               :== theory(<theory_name><optional_info>)
data Theory = Theory Theory_name Optional_info
              deriving (Show, Ord, Eq, Data, Typeable)

-- <theory_name>          :== equality | ac
data Theory_name = TN_equality
                 | TN_ac
                   deriving (Show, Ord, Eq, Data, Typeable)

-- %----More theory names may be added in the future. The <optional_info> is
-- %----used to store, e.g., which axioms of equality have been implicitly used,
-- %----e.g., theory(equality,[rst]). Standard format still to be decided.
-- <creator_source>       :== creator(<creator_name><optional_info>)
data Creator_source = Creator_source Creator_name Optional_info
                      deriving (Show, Ord, Eq, Data, Typeable)

-- <creator_name>         :== <atomic_word>
type Creator_name = Token


-- %----Useful info fields
-- <optional_info>        ::= ,<useful_info> | <null>
type Optional_info = Maybe Useful_info

-- <useful_info>          ::= <general_list>
-- <useful_info>          :== [] | [<info_items>]
data Useful_info = UI_items Info_items
                 | UI_general_list General_list
                   deriving (Show, Ord, Eq, Data, Typeable)

-- <info_items>           :== <info_item> | <info_item>,<info_items>
type Info_items = [Info_item]

-- <info_item>            :== <formula_item> | <inference_item> |
--                            <general_function>
data Info_item = Info_formula Formula_item
               | Info_inference Inference_item
               | Info_general General_function
                 deriving (Show, Ord, Eq, Data, Typeable)

-- %----Useful info for formula records
-- <formula_item>         :== <description_item> | <iquote_item>
data Formula_item = FI_description Description_item
                  | FI_iquote Iquote_item
                    deriving (Show, Ord, Eq, Data, Typeable)

-- <description_item>     :== description(<atomic_word>)
type Description_item = Token

-- <iquote_item>          :== iquote(<atomic_word>)
-- %----<iquote_item>s are used for recording exactly what the system output about
-- %----the inference step. In the future it is planned to encode this information
-- %----in standardized forms as <parent_details> in each <inference_record>.
-- %----Useful info for inference records
type Iquote_item = Token

-- <inference_item>       :== <inference_status> | <assumptions_record> |
--                            <new_symbol_record> | <refutation>
data Inference_item = Inf_status Inference_status
                    | Inf_assumption Assumptions_record
                    | Inf_symbol New_symbol_record
                    | Inf_refutation Refutation
                      deriving (Show, Ord, Eq, Data, Typeable)

-- <inference_status>     :== status(<status_value>) | <inference_info>
data Inference_status = Inf_value Status_value
                      | Inf_info Inference_info
                        deriving (Show, Ord, Eq, Data, Typeable)

-- %----These are the success status values from the SZS ontology. The most
-- %----commonly used values are:
-- %----  thm - Every model of the parent formulae is a model of the inferred
-- %----        formula. Regular logical consequences.
-- %----  cth - Every model of the parent formulae is a model of the negation of
-- %----        the inferred formula. Used for negation of conjectures in FOF to
-- %----        CNF conversion.
-- %----  esa - There exists a model of the parent formulae iff there exists a
-- %----        model of the inferred formula. Used for Skolemization steps.
-- %----For the full hierarchy see the SZSOntology file distributed with the TPTP.
-- <status_value>         :== suc | unp | sap | esa | sat | fsa | thm | eqv | tac |
--                            wec | eth | tau | wtc | wth | cax | sca | tca | wca |
--                            cup | csp | ecs | csa | cth | ceq | unc | wcc | ect |
--                            fun | uns | wuc | wct | scc | uca | noc
data Status_value = SUC | UNP | SAP | ESA | SAT | FSA | THM | EQV | TAC
                  | WEC | ETH | TAU | WTC | WTH | CAX | SCA | TCA | WCA
                  | CUP | CSP | ECS | CSA | CTH | CEQ | UNC | WCC | ECT
                  | FUN | UNS | WUC | WCT | SCC | UCA | NOC
                    deriving (Show, Ord, Eq, Data, Typeable)

-- %----<inference_info> is used to record standard information associated with an
-- %----arbitrary inference rule. The <inference_rule> is the same as the
-- %----<inference_rule> of the <inference_record>. The <atomic_word> indicates
-- %----the information being recorded in the <general_list>. The <atomic_word>
-- %----are (loosely) set by TPTP conventions, and include esplit, sr_split, and
-- %----discharge.
-- <inference_info>       :== <inference_rule>(<atomic_word>,<general_list>)
data Inference_info = Inference_info Inference_rule Atomic_word General_list
                      deriving (Show, Ord, Eq, Data, Typeable)

-- %----An <assumptions_record> lists the names of assumptions upon which this
-- %----inferred formula depends. These must be discharged in a completed proof.
-- <assumptions_record>   :== assumptions([<name_list>])
type Assumptions_record = Name_list

-- %----A <refutation> record names a file in which the inference recorded here
-- %----is recorded as a proof by refutation.
-- <refutation>           :== refutation(<file_source>)
type Refutation = File_source

-- %----A <new_symbol_record> provides information about a newly introduced symbol.
-- <new_symbol_record>    :== new_symbols(<atomic_word>,[<new_symbol_list>])
data New_symbol_record = New_symbol_record Atomic_word  New_symbol_list
                         deriving (Show, Ord, Eq, Data, Typeable)

-- <new_symbol_list>      :== <principal_symbol> |
--                            <principal_symbol>,<new_symbol_list>
type New_symbol_list = [Principal_symbol]

-- %----Principal symbols are predicates, functions, variables
-- <principal_symbol>   :== <functor> | <variable>
data Principal_symbol = PS_functor TPTP_functor
                      | PS_variable Variable
                        deriving (Show, Ord, Eq, Data, Typeable)

-- %----Include directives
-- <include>              ::= include(<file_name><formula_selection>).
data Include = Include File_name Formula_selection
               deriving (Show, Ord, Eq, Data, Typeable)

-- <formula_selection>    ::= ,[<name_list>] | <null>
type Formula_selection = Maybe [Name]

-- <name_list>            ::= <name> | <name>,<name_list>
type Name_list = [Name]


-- %----Non-logical data
-- <general_term>         ::= <general_data> | <general_data>:<general_term> |
--                            <general_list>
data General_term = GT_data General_data
                  | GT_DataTerm General_data General_term
                  | GT_list General_list
                    deriving (Show, Ord, Eq, Data, Typeable)

-- <general_data>         ::= <atomic_word> | <general_function> |
--                            <variable> | <number> | <distinct_object> |
--                            <formula_data>
data General_data = GD_atomic_word Atomic_word
                  | GD_general_function General_function
                  | GD_variable Variable
                  | GD_number Number
                  | GD_distinct_object Distinct_object
                  | GD_formula_data Formula_data
-- %----A <general_data> bind() term is used to record a variable binding in an
-- %----inference, as an element of the <parent_details> list.
-- <general_data>         :== bind(<variable>,<formula_data>)
                  | GD_bind Variable Formula_data -- only used in inference
                    deriving (Show, Ord, Eq, Data, Typeable)

-- <general_function>     ::= <atomic_word>(<general_terms>)
data General_function = General_function Atomic_word General_terms
                        deriving (Show, Ord, Eq, Data, Typeable)

-- <formula_data>         ::= $thf(<thf_formula>) | $tff(<tff_formula>) |
--                            $fof(<fof_formula>) | $cnf(<cnf_formula>) |
--                            $fot(<fof_term>)
-- only used in inference
data Formula_data = FD_THF THF_formula
                  | FD_TFF TFF_formula
                  | FD_FOF FOF_formula
                  | FD_CNF CNF_formula
                  | FD_FOT FOF_term
                    deriving (Show, Ord, Eq, Data, Typeable)

-- <general_list>         ::= [] | [<general_terms>]
type General_list = [General_term]

-- <general_terms>        ::= <general_term> | <general_term>,<general_terms>
type General_terms = [General_term]


-- %----General purpose
-- <name>                 ::= <atomic_word> | <integer>
-- %----Integer names are expected to be unsigned
data Name = NameString Token
          | NameInteger Integer
            deriving (Show, Ord, Eq, Data, Typeable)

-- <atomic_word>          ::= <lower_word> | <single_quoted>
type Atomic_word = Token

-- <atomic_defined_word>  ::= <dollar_word>
type Atomic_defined_word = Token

-- <atomic_system_word>   ::= <dollar_dollar_word>
type Atomic_system_word = Token

-- <number>               ::= <integer> | <rational> | <real>
data Number = NumInteger Integer
            | NumRational Rational
            | NumReal Double
              deriving (Show, Ord, Eq, Data, Typeable)


-- <distinct_object>      ::- <double_quote><do_char>*<double_quote>
type Distinct_object = Token

-- <file_name>            ::= <single_quoted>
type File_name = IRI
