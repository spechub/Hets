{- |
Module      :  $Header$
Description :  A abstract syntax for the TPTP-THF Syntax
Copyright   :  (c) A.Tsogias, DFKI Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :
Stability   :
Portability :

A Abstract Syntax for the TPTP-THF Input Syntax v5.1.0.2 taken from
<http://www.cs.miami.edu/~tptp/TPTP/SyntaxBNF.html>
-}

module THF.As where

-- A las Question: at the example of <source>: Sould <general_term> be also
-- tried when all ather cariations fail?

-- <TPTP_input>       ::= <annotated_formula> | <include>
-- <thf_annotated>    ::= thf(<name>,<formula_role>,<thf_formula><annotations>).
data TPTP_THF =
    TPTP_THF_Annotated_Formula  Name FormulaRole THFFormula Annotations
  | TPTP_Include                Include
  | TPTP_Comment                Comment
  | TPTP_Defined_Comment        DefinedComment
  | TPTP_System_Comment         SystemComment
--  | TPTP_Empty_Line
    deriving (Show, Eq)

-- <comment>            ::- <comment_line>|<comment_block>
-- <comment_line>       ::- [%]<printable_char>*
-- <comment_block>      ::: [/][*]<not_star_slash>[*][*]*[/]
-- <not_star_slash>     ::: ([^*]*[*][*]*[^/*])*[^*]*
data Comment =
    Comment_Line    String
  | Comment_Block   [String]
    deriving (Show, Eq)

-- <defined_comment>    ::- <def_comment_line>|<def_comment_block>
-- <def_comment_line>   ::: [%]<dollar><printable_char>*
-- <def_comment_block>  ::: [/][*]<dollar><not_star_slash>[*][*]*[/]
data DefinedComment =
    Defined_Comment_Line    String
  | Defined_Comment_Block   [String]
    deriving (Show, Eq)

-- <system_comment>     ::- <sys_comment_line>|<sys_comment_block>
-- <sys_comment_line>   ::: [%]<dollar><dollar><printable_char>*
-- <sys_comment_block>  ::: [/][*]<dollar><dollar><not_star_slash>[*][*]*[/]
data SystemComment =
    System_Comment_Line    String
  | System_Comment_Block   [String]
    deriving (Show, Eq)

-- <include>            ::= include(<file_name><formula_selection>).
-- <formula_selection>  ::= ,[<name_list>] | <null>
data Include =
    I_Include   FileName (Maybe NameList)
    deriving (Show, Eq)

-- <annotations>        ::= ,<source><optional_info> | <null>
data Annotations =
    Annotations Source OptionalInfo
  | Null
    deriving (Show, Eq)

-- <formula_role>       ::= <lower_word>
-- <formula_role>       :== axiom | hypothesis | definition | assumption |
--                          lemma | theorem | conjecture | negated_conjecture |
--                          plain | fi_domain | fi_functors | fi_predicates |
--                          type | unknown
data FormulaRole =
    Axiom | Hypothesis | Definition  | Assumption
  | Lemma | Theorem    | Conjecture  | Negated_Conjecture
  | Plain | Fi_Domain  | Fi_Functors | Fi_Predicates
  | Type  | Unknown
    deriving (Show, Eq)

-- <thf_formula>        ::= <thf_logic_formula> | <thf_sequent>
data THFFormula =
    TF_THF_Logic_Formula    THFLogicFormula
  | TF_THF_Sequent          THFSequent
    deriving (Show, Eq)

-- <thf_logic_formula>  ::= <thf_binary_formula> | <thf_unitary_formula> |
--                         <thf_type_formula> | <thf_subtype>
data THFLogicFormula =
    TLF_THF_Binary_Formula  THFBinaryFormula
  | TLF_THF_Unitary_Formula THFUnitaryFormula
  | TLF_THF_Type_Formula    THFTypeFormula
  | TLF_THF_Sub_Type        THFSubType
    deriving (Show, Eq)

-- <thf_binary_formula> ::= <thf_binary_pair> | <thf_binary_tuple> |
--                          <thf_binary_type>
-- <thf_binary_pair>    ::= <thf_unitary_formula> <thf_pair_connective>
--                          <thf_unitary_formula>
data THFBinaryFormula =
    TBF_THF_Binary_Pair     THFUnitaryFormula THFPairConnective THFUnitaryFormula
  | TBF_THF_Binary_Tuple    THFBinaryTuple
  | TBF_THF_Binary_Type     THFBinaryType
    deriving (Show, Eq)

-- <thf_binary_tuple>   ::= <thf_or_formula> | <thf_and_formula> |
--                          <thf_apply_formula>
-- <thf_or_formula>     ::= <thf_unitary_formula> <vline> <thf_unitary_formula> |
--                          <thf_or_formula> <vline> <thf_unitary_formula>
-- <thf_and_formula>    ::= <thf_unitary_formula> & <thf_unitary_formula> |
--                          thf_and_formula> & <thf_unitary_formula>
-- <thf_apply_formula>  ::= <thf_unitary_formula> @ <thf_unitary_formula> |
--                          <thf_apply_formula> @ <thf_unitary_formula>
data THFBinaryTuple =
    TBT_THF_Or_Formula      THFUnitaryFormula [THFUnitaryFormula]
  | TBT_THF_And_Formula     THFUnitaryFormula [THFUnitaryFormula]
  | TBT_THF_Apply_Formula   THFUnitaryFormula [THFUnitaryFormula]
    deriving (Show, Eq)

-- <thf_unitary_formula>    ::= <thf_quantified_formula> | <thf_unary_formula> |
--                              <thf_atom> | <thf_tuple> | <thf_let> |
--                              <thf_conditional> | (<thf_logic_formula>)
-- <thf_quantified_formula> ::= <thf_quantifier> [<thf_variable_list>] :
--                              <thf_unitary_formula>
-- thf_unary_formula>       ::= <thf_unary_connective> (<thf_logic_formula>)
-- <thf_let>                ::= := [<thf_let_list>] : <thf_unitary_formula>
-- <thf_let_list>           ::= <thf_defined_var> |
--                              <thf_defined_var>,<thf_let_list>
-- <thf_conditional>        ::= $itef(<thf_logic_formula>,<thf_logic_formula>,
--                              <thf_logic_formula>)
-- <thf_variable_list>      ::= <thf_variable> |
--                              <thf_variable>,<thf_variable_list>
data THFUnitaryFormula =
    TUF_THF_Quantified_Formula  THFQuantifier [THFVariable] THFUnitaryFormula
  | TUF_THF_Unary_Formula       THFUnaryConnective THFLogicFormula
  | TUF_THF_Atom                THFAtom
  | TUF_THF_Tuple               THFTuple
  | TUF_THF_Let                 [THFDefinedVar] THFUnitaryFormula
  | TUF_THF_Conditional         THFLogicFormula THFLogicFormula THFLogicFormula
  | TUF_THF_Logic_Formula_Par   THFLogicFormula
    deriving (Show, Eq)

-- <thf_variable> ::= <thf_typed_variable> | <variable>
-- <thf_typed_variable> ::= <variable> : <thf_top_level_type>
data THFVariable =
    TV_THF_Typed_Variable   Variable THFTopLevelType
  | TV_Variable             Variable
    deriving (Show, Eq)

-- <thf_type_formula> ::= <thf_typeable_formula> : <thf_top_level_type>
-- <thf_type_formula> :== <constant> : <thf_top_level_type>
data THFTypeFormula =
    TTF_THF_Type_Formula    THFTypeableFormula THFTopLevelType
  | TTF_THF_Role_Type       Constant THFTopLevelType
    deriving (Show, Eq)

-- <thf_typeable_formula> ::= <thf_atom> | <thf_tuple> | (<thf_logic_formula>)
data THFTypeableFormula =
    TTyF_THF_Atom           THFAtom
  | TTyF_THF_Tuple          THFTuple
  | TTyF_THF_Logic_Formula  THFLogicFormula
    deriving (Show, Eq)

-- <thf_subtype> ::= <constant> <subtype_sign> <constant>
-- <subtype_sign> == <<
data THFSubType =
    TST_THF_Sub_Type        Constant Constant
    deriving (Show, Eq)

-- <thf_top_level_type> ::= <thf_logic_formula>
type THFTopLevelType = THFLogicFormula

-- <thf_unitary_type>   ::= <thf_unitary_formula>
type THFUnitaryType = THFUnitaryFormula

-- <thf_binary_type> ::= <thf_mapping_type> | <thf_xprod_type> |
--                       <thf_union_type>
-- <thf_mapping_type> ::= <thf_unitary_type> <arrow> <thf_unitary_type> |
--                        <thf_unitary_type> <arrow> <thf_mapping_type>
-- <arrow> ::- >
-- <thf_xprod_type> ::= <thf_unitary_type> <star> <thf_unitary_type> |
--                      <thf_xprod_type> <star> <thf_unitary_type>
-- <star> ::- *
-- <thf_union_type> ::= <thf_unitary_type> <plus> <thf_unitary_type> |
--                      <thf_union_type> <plus> <thf_unitary_type>
-- <plus> ::- +
data THFBinaryType =
    TBT_THF_Mapping_Type    THFUnitaryType [THFUnitaryType]
  | TBT_THF_Xprod_Type      THFUnitaryType [THFUnitaryType]
  | TBT_THF_Union_Type      THFUnitaryType [THFUnitaryType]
    deriving (Show, Eq)

-- <thf_atom> ::= <term> | <thf_conn_term>
-- %----<thf_atom> can also be <defined_type> | <defined_plain_formula> |
-- %----<system_type> | <system_atomic_formula>, but they are syntactically
-- %----captured by <term>.
-- <system_type>        :== <atomic_system_word>
-- <system_atomic_formula> ::= <system_term>
data THFAtom =
    TA_Term                     Term
  | TA_THF_Conn_Term            THFConnTerm
  | TA_Defined_Type             DefinedType
  | TA_Defined_Plain_Formula    DefinedPlainFormula
  | TA_System_Type              AtomicSystemWord
  | TA_System_Atomic_Formula    SystemTerm
    deriving (Show, Eq)

-- <thf_tuple> ::= [] | [<thf_tuple_list>]
-- <thf_tuple_list> ::= <thf_unitary_formula> |
--                      <thf_unitary_formula>,<thf_tuple_list>
-- THFTupleList must not be empty
type THFTuple = [THFUnitaryFormula]

-- <thf_defined_var> ::= <thf_variable> := <thf_logic_formula> |
--                       (<thf_defined_var>)
data THFDefinedVar =
    TDV_THF_Defined_Var      THFVariable THFLogicFormula
  | TDV_THF_Defined_Var_Par   THFDefinedVar
    deriving (Show, Eq)

-- <thf_sequent> ::= <thf_tuple> <gentzen_arrow> <thf_tuple> |
--                   (<thf_sequent>)
-- <gentzen_arrow> ::= -->
data THFSequent =
    TS_THF_Sequent      THFTuple THFTuple
  | TS_THF_Sequent_Par  THFSequent
    deriving (Show, Eq)

-- <thf_conn_term> ::= <thf_pair_connective> | <assoc_connective> |
--                     <thf_unary_connective>
data THFConnTerm =
    TCT_THF_Pair_Connective     THFPairConnective
  | TCT_Assoc_Connective        AssocConnective
  | TCT_THF_Unary_Connective    THFUnaryConnective
    deriving (Show, Eq)

-- <thf_quantifier>     ::= <fol_quantifier> | ^ | !> | ?* | @+ | @-
-- <fol_quantifier>     ::= ! | ?
data THFQuantifier =
    ForAll                  -- !
  | Exists                  -- ?
  | Lambda_Binder           -- ^
  | Dependent_Product       -- !>
  | Dependent_Sum           -- ?*
  | Indefinite_Description  -- @+
  | Definite_Description    -- @-
    deriving (Show, Eq)

-- <thf_pair_connective> ::= <infix_equality> | <infix_inequality> |
--                          <binary_connective>
-- <binary_connective>  ::= <=> | => | <= | <~> | ~<vline> | ~&
-- <infix_equality>     ::= =
-- <infix_inequality>   ::= !=
data THFPairConnective =
    Infix_Equality          -- =
  | Infix_Inequality        -- !=
  | Equivalent              -- <=>
  | Implication             -- =>
  | IF                      -- <=
  | XOR                     -- <~>
  | NOR                     -- ~|
  | NAND                    -- ~&
    deriving (Show, Eq)

-- <thf_unary_connective> ::= <unary_connective> | !! | ??
-- <unary_connective>   ::= ~
data THFUnaryConnective =
    Negation                -- ~
  | PiForAll                -- !!
  | SigmaExists             -- ??
    deriving (Show, Eq)

-- <assoc_connective>   ::= <vline> | &
data AssocConnective =
    OR      -- |
  | AND     -- &
    deriving (Show, Eq)

-- <defined_type>       ::= <atomic_defined_word>
-- <defined_type>       :== $oType | $o | $iType | $i | $tType |
--                          $real | $rat | $int
data DefinedType =
    DT_oType | DT_o    | DT_iType | DT_i
  | DT_tType | DT_real | DT_rat   | DT_int
    deriving (Show, Eq)

-- <defined_plain_formula> ::= <defined_plain_term>
-- <defined_plain_formula> :== <defined_prop> | <defined_pred>(<arguments>)
data DefinedPlainFormula =
    DPF_Defined_Prop    DefinedProp
  | DPF_Defined_Formula DefinedPred Arguments
    deriving (Show, Eq)

-- <defined_prop>       :== <atomic_defined_word>
-- <defined_prop>       :== $true | $false
data DefinedProp =
    DP_True | DP_False
    deriving (Show, Eq)

-- <defined_pred>       :== <atomic_defined_word>
-- <defined_pred>       :== $equal | $distinct | $itef | $less |
--                          $lesseq | $greater | $greatereq | $evaleq |
--                          $is_int | $is_rat
data DefinedPred =
    Equal  | Disrinct | Itef      | Less
  | Lesseq | Greater  | Greatereq | Evaleq
  | Is_int | Is_rat
    deriving (Show, Eq)

-- <term> ::= <function_term> | <variable> | <conditional_term>
-- %----Conditional terms should not be used by THF.
-- Thus tey are not implemented.
data Term =
    T_Function_Term     FunctionTerm
  | T_Variable          Variable
    deriving (Show, Eq)

-- <function_term> ::= <plain_term> | <defined_term> | <system_term>
data FunctionTerm =
    FT_Plain_Term   PlainTerm
  | FT_Defined_Term DefinedTerm
  | FT_System_Term  SystemTerm
    deriving (Show, Eq)

-- <plain_term> ::= <constant> | <functor>(<arguments>)
data PlainTerm =
    PT_Plain_Term   TPTPFunctor Arguments
  | PT_Constant     Constant

    deriving (Show, Eq)

-- <constant> ::= <functor>
type Constant = TPTPFunctor

-- <functor>  ::= <atomic_word>
type TPTPFunctor = AtomicWord

-- <defined_term> ::= <defined_atom> | <defined_atomic_term>
-- <defined_atomic_term> ::= <defined_plain_term>
data DefinedTerm =
    DT_Defined_Atom         DefinedAtom
  | DT_Defined_Atomic_Term  DefinedPlainTerm
    deriving (Show, Eq)

-- <defined_atom> ::= <number> | <distinct_object>
data DefinedAtom =
    DA_Number           Number
  | DA_Distinct_Object  DistinctObject
    deriving (Show, Eq)

-- <defined_plain_term> ::= <defined_constant> | <defined_functor>(<arguments>)
-- <defined_constant> ::= <defined_functor>
data DefinedPlainTerm =
    DPT_Defined_Function    DefinedFunctor Arguments
  | DPT_Defined_Constant    DefinedFunctor

    deriving (Show, Eq)

-- <defined_functor> ::= <atomic_defined_word>
-- <defined_functor> :== $itett | $uminus | $sum | $difference |
--                       $product | $to_int | $to_rat | $to_real
data DefinedFunctor =
    Itett   | Uminus | Sum    | Difference
  | Product | To_int | To_rat | To_real
    deriving (Show, Eq)

-- <system_term>        ::= <system_constant> | <system_functor>(<arguments>)
-- <system_constant>    ::= <system_functor>
data SystemTerm =
    ST_System_Term      SystemFunctor Arguments
  | ST_System_Constant  SystemFunctor
    deriving (Show, Eq)

-- <system_functor>     ::= <atomic_system_word>
-- <upper_word>         ::- <upper_alpha><alpha_numeric>*
type SystemFunctor = AtomicSystemWord

-- <variable>           ::= <upper_word>
type Variable = String

-- <arguments> ::= <term> | <term>,<arguments>
-- at least one term is neaded
type Arguments = [Term]

-- <principal_symbol>   :== <functor> | <variable>
data PrincipalSymbol =
    PS_Functor  TPTPFunctor
  | PS_Variable Variable
    deriving (Show, Eq)

-- <source>             ::= <general_term>
-- <source>             :== <dag_source> | <internal_source> | <external_source> |
--                          unknown | [<sources>]
-- <internal_source>    :== introduced(<intro_type><optional_info>)
-- <sources>            :== <source> | <source>,<sources>
data Source =
    S_Dag_Source        DagSource
  | S_Internal_Source   IntroType OptionalInfo
  | S_External_Source   ExternalSource
  | S_Sources           [Source]
  | S_Unknown
    deriving (Show, Eq)

-- <dag_source>         :== <name> | <inference_record>
-- <inference_record>   :== inference(<inference_rule>,<useful_info>,
--                              [<parent_list>])
-- <inference_rule>     :== <atomic_word>
-- <parent_list>        :== <parent_info> | <parent_info>,<parent_list>
data DagSource =
    DS_Name             Name
  | DS_Inference_Record AtomicWord UsefulInfo [ParentInfo]
    deriving (Show, Eq)

-- <parent_info>        :== <source><parent_details>
-- <parent_details>     :== :<general_list> | <null>
data ParentInfo =
    PI_Parent_Info  Source (Maybe GeneralList)
    deriving (Show, Eq)

-- <intro_type>         :== definition | axiom_of_choice | tautology | assumption
data IntroType =
   IT_definition | IT_axiom_of_choice | IT_tautology | IT_assumption
   deriving (Show, Eq)

-- <external_source>    :== <file_source> | <theory> | <creator_source>
-- <theory>             :== theory(<theory_name><optional_info>)
-- <creator_source>     :== creator(<creator_name><optional_info>)
-- <creator_name>       :== <atomic_word>
data ExternalSource =
    ES_File_Source      FileSource
  | ES_Theory           TheoryName OptionalInfo
  | ES_Creator_Source   AtomicWord OptionalInfo
    deriving (Show, Eq)

-- <file_source>        :== file(<file_name><file_info>)
-- <file_info>          :== ,<name> | <null>
data FileSource =
    FS_File FileName (Maybe Name)
    deriving (Show, Eq)

-- <theory_name>        :== equality | ac
data TheoryName =
    Equality | Ac
    deriving (Show, Eq)

-- <optional_info>      ::= ,<useful_info> | <null>
type OptionalInfo = (Maybe UsefulInfo)

-- <useful_info>        ::= <general_list>
-- <useful_info>        :== [] | [<info_items>]
-- <info_items>         :== <info_item> | <info_item>,<info_items>
type UsefulInfo = [InfoItem]

-- <info_item>          :== <formula_item> | <inference_item> |
--                          <general_function>
data InfoItem =
    II_Formula_Item     FormulaItem
  | II_Inference_Item   InferenceItem
  | II_General_Function GeneralFunction
    deriving (Show, Eq)

-- <formula_item>       :== <description_item> | <iquote_item>
-- <description_item>   :== description(<atomic_word>)
-- <iquote_item>        :== iquote(<atomic_word>)
data FormulaItem =
    FI_Description_Item AtomicWord
  | FI_Iquote_Item      AtomicWord
    deriving (Show, Eq)

-- <inference_item>     :== <inference_status> | <assumptions_record> |
--                          <new_symbol_record> | <refutation>
-- <assumptions_record> :== assumptions([<name_list>])
-- <refutation>         :== refutation(<file_source>)
-- <new_symbol_record>  :== new_symbols(<atomic_word>,[<new_symbol_list>])
-- <new_symbol_list>    :== <principal_symbol> |
--                          <principal_symbol>,<new_symbol_list>
data InferenceItem =
    II_Inference_Status     InferenceStatus
  | II_Assumptions_Record   NameList
  | II_New_Symbol_Record    AtomicWord [PrincipalSymbol]
  | II_Refutation           FileSource
    deriving (Show, Eq)

-- <inference_status>   :== status(<status_value>) | <inference_info>
-- <inference_info>     :== <inference_rule>(<atomic_word>,<general_list>)
-- <inference_rule>     :== <atomic_word>
data InferenceStatus =
    IS_Status           StatusValue
  | IS_Inference_Info   AtomicWord AtomicWord GeneralList
    deriving (Show, Eq)

-- <status_value>       :== suc | unp | sap | esa | sat | fsa | thm | eqv | tac |
--                          wec | eth | tau | wtc | wth | cax | sca | tca | wca |
--                          cup | csp | ecs | csa | cth | ceq | unc | wcc | ect |
--                          fun | uns | wuc | wct | scc | uca | noc
data StatusValue =
    Suc | Unp | Sap | Esa | Sat | Fsa | Thm | Eqv | Tac
  | Wec | Eth | Tau | Wtc | Wth | Cax | Sca | Tca | Wca
  | Cup | Csp | Ecs | Csa | Cth | Ceq | Unc | Wcc | Ect
  | Fun | Uns | Wuc | Wct | Scc | Uca | Noc
  deriving (Show, Eq)

-- <name_list>          ::= <name> | <name>,<name_list>
-- the list must mot be empty
type NameList = [Name]

-- <general_term>       ::= <general_data> | <general_data>:<general_term> |
--                          <general_list>
data GeneralTerm =
    GT_General_Data         GeneralData
  | GT_General_Data_Term    GeneralData GeneralTerm
  | GT_General_List         GeneralList
    deriving (Show, Eq)

-- <general_data>       ::= <atomic_word> | <general_function> |
--                          <variable> | <number> | <distinct_object> |
--                          <formula_data>
-- <general_data>       :== bind(<variable>,<formula_data>)
data GeneralData =
    GD_Atomic_Word      AtomicWord
  | GD_Variable         Variable
  | GD_Number           Number
  | GD_Distinct_Object  DistinctObject
  | GD_Formula_Data     FormulaData
  | GD_Bind             Variable FormulaData
  | GD_General_Function GeneralFunction
    deriving (Show, Eq)

-- <general_function>   ::= <atomic_word>(<general_terms>)
-- general_terms must not be empty
data GeneralFunction =
    GF_General_Function AtomicWord GeneralTerms
    deriving (Show, Eq)

-- <formula_data>       ::= $thf(<thf_formula>) | $tff(<tff_formula>) |
--                          $fof(<fof_formula>) | $cnf(<cnf_formula>) |
--                          $fot(<term>)
-- only thf is used here
data FormulaData =
    THF_Formula THFFormula
    deriving (Show, Eq)

-- <general_list>       ::= [] | [<general_terms>]
type GeneralList = GeneralTerms

-- <general_terms>      ::= <general_term> | <general_term>,<general_terms>
type GeneralTerms = [GeneralTerm]

-- <name>               ::= <atomic_word> | <integer>
data Name =
    N_Atomic_Word   AtomicWord
  | N_Integer       String
    deriving (Show, Eq)

-- <atomic_word>        ::= <lower_word> | <single_quoted>
data AtomicWord =
    A_Lower_Word    LowerWord
  | A_Single_Quoted SingleQuoted
    deriving (Show, Eq)

-- <atomic_system_word> ::= <dollar_dollar_word>
-- <dollar_dollar_word> ::- <dollar><dollar><lower_word>
-- <dollar>             ::: [$]
type AtomicSystemWord = LowerWord

-- <number> ::= <integer> | <rational> | <real>
-- <real>               ::- (<signed_real>|<unsigned_real>)
-- <signed_real>        ::- <sign><unsigned_real>
-- <unsigned_real>      ::- (<decimal_fraction>|<decimal_exponent>)
-- <rational>           ::- (<signed_rational>|<unsigned_rational>)
-- <signed_rational>    ::- <sign><unsigned_rational>
-- <unsigned_rational>  ::- <decimal><slash><positive_decimal>
-- <integer>            ::- (<signed_integer>|<unsigned_integer>)
-- <signed_integer>     ::- <sign><unsigned_integer>
-- <unsigned_integer>   ::- <decimal>
-- <decimal>            ::- (<zero_numeric>|<positive_decimal>)
-- <positive_decimal>   ::- <non_zero_numeric><numeric>*
-- <decimal_exponent>   ::- (<decimal>|<decimal_fraction>)<exponent><decimal>
-- <decimal_fraction>   ::- <decimal><dot_decimal>
-- <dot_decimal>        ::- <dot><numeric><numeric>*
-- <sign>               ::: [+-]
-- <dot>                ::: [.]
-- <exponent>           ::: [Ee]
-- <slash>              ::: [/]
-- <zero_numeric>       ::: [0]
-- <non_zero_numeric>   ::: [1-9]
-- <numeric>            ::: [0-9]
data Number =
    Num_Integer   String
  | Num_Rational  String
  | Num_Real      String
    deriving (Show, Eq)

-- <file_name>          ::= <single_quoted>
type FileName = SingleQuoted

-- <single_quoted>      ::- <single_quote><sq_char><sq_char>*<single_quote>
-- <single_quote>       ::: [']
-- <sq_char>            ::: ([\40-\46\50-\133\135-\176]|[\\]['\\])
type SingleQuoted = String

-- <distinct_object> ::- <double_quote><do_char>*<double_quote>
-- <do_char> ::: ([\40-\41\43-\133\135-\176]|[\\]["\\])
-- <double_quote> ::: ["]
type DistinctObject = String

-- <lower_word>         ::- <lower_alpha><alpha_numeric>*
-- <alpha_numeric>      ::: (<lower_alpha>|<upper_alpha>|<numeric>|[_])
-- <lower_alpha>        ::: [a-z]
-- <upper_alpha>        ::: [A-Z]
-- <numeric>            ::: [0-9]
type LowerWord = String
