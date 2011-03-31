{- |
Module      :  $Header$
Description :  A abstract syntax for the TPTP-THF Syntax
Copyright   :  (c) A.Tsogias, DFKI Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :
Stability   :
Portability :

A Abstract Syntax for the TPTP-THF Input Syntax v5.1.0.1 taken from
<http://www.cs.miami.edu/~tptp/TPTP/SyntaxBNF.html>
-}

module THF.As where

-- <TPTP_input>         ::= <annotated_formula> | <include>
-- <thf_annotated>      ::= thf(<name>,<formula_role>,<thf_formula><annotations>).
data TPTP_THF =
    TPTP_THF_Annotated_Formula  {ttaf_name         :: Name,
                                 ttaf_formula_role :: FormulaRole,
                                 ttaf_thf_formula  :: THFFormula,
                                 ttaf_annotations  :: Annotations}
  | TPTP_Include                Include
  | TPTP_Comment                Comment
  | TPTP_Defined_Comment        DefinedComment
  | TPTP_System_Comment         SystemComment
--  | TPTP_Empty_Line
    deriving Show

-- <comment>            ::- <comment_line>|<comment_block>
-- <comment_line>       ::- [%]<printable_char>*
-- <comment_block>      ::: [/][*]<not_star_slash>[*][*]*[/]
-- <not_star_slash>     ::: ([^*]*[*][*]*[^/*])*[^*]*
data Comment =
    Comment_Line    String
  | Comment_Block   [String]
    deriving Show

-- <defined_comment>    ::- <def_comment_line>|<def_comment_block>
-- <def_comment_line>   ::: [%]<dollar><printable_char>*
-- <def_comment_block>  ::: [/][*]<dollar><not_star_slash>[*][*]*[/]
data DefinedComment =
    Defined_Comment_Line    String
  | Defined_Comment_Block   [String]
    deriving Show

-- <system_comment>     ::- <sys_comment_line>|<sys_comment_block>
-- <sys_comment_line>   ::: [%]<dollar><dollar><printable_char>*
-- <sys_comment_block>  ::: [/][*]<dollar><dollar><not_star_slash>[*][*]*[/]
data SystemComment =
    System_Comment_Line    String
  | System_Comment_Block   [String]
    deriving Show

-- <include>            ::= include(<file_name><formula_selection>).
data Include =
    I_Include   {file_name          :: FileName,
                 formula_selection  :: FormulaSelection}
    deriving Show

-- <annotations>        ::= ,<source><optional_info> | <null>
data Annotations =
    Annotations   {a_source        :: Source,
                   a_optional_info :: OptionalInfo}
  | Null
    deriving Show

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
    deriving Show

-- <thf_formula>        ::= <thf_logic_formula> | <thf_sequent>
data THFFormula =
    TF_THF_Logic_Formula    THFLogicFormula
  | TF_THF_Sequent          THFSequent
    deriving Show

-- <thf_logic_formula>  ::= <thf_binary_formula> | <thf_unitary_formula> |
--                         <thf_type_formula> | <thf_subtype>
data THFLogicFormula =
    TLF_THF_Binary_Formula  THFBinaryFormula
  | TLF_THF_Unitary_Formula THFUnitaryFormula
  | TLF_THF_Type_Formula    THFTypeFormula
  | TLF_THF_Sub_Type        THFSubType
    deriving Show

-- <thf_binary_formula> ::= <thf_binary_pair> | <thf_binary_tuple> |
--                          <thf_binary_type>
data THFBinaryFormula =
    TBF_THF_Binary_Pair     THFBinaryPair
  | TBF_THF_Binary_Tuple    THFBinaryTuple
  | TBF_THF_Binary_Type     THFBinaryType
    deriving Show

-- <thf_binary_pair>    ::= <thf_unitary_formula> <thf_pair_connective>
--                          <thf_unitary_formula>
data THFBinaryPair =
    TBP_THF_Binary_Pair {thf_unitary_formula_front  :: THFUnitaryFormula,
                         thf_pair_connective        :: THFPairConnective,
                         thf_unitary_formula_back   :: THFUnitaryFormula}
    deriving Show

-- <thf_binary_tuple>   ::= <thf_or_formula> | <thf_and_formula> |
--                          <thf_apply_formula>
data THFBinaryTuple =
    TBT_THF_Or_Formula      THFOrFormula
  | TBT_THF_And_Formula     THFAndFormula
  | TBT_THF_Apply_Formula   THFApplyFormula
    deriving Show

-- <thf_or_formula>     ::= <thf_unitary_formula> <vline> <thf_unitary_formula> |
--                          <thf_or_formula> <vline> <thf_unitary_formula>
data THFOrFormula =
    TOF_THF_Or_Formula      THFUnitaryFormula THFUnitaryFormula
  | TOF_THF_Or_Formula_Il   THFOrFormula THFUnitaryFormula
    deriving Show

-- <thf_and_formula>    ::= <thf_unitary_formula> & <thf_unitary_formula> |
--                          thf_and_formula> & <thf_unitary_formula>
data THFAndFormula =
    TAF_THF_And_Formula     THFUnitaryFormula THFUnitaryFormula
  | TAF_THF_And_Formula_Il  THFAndFormula THFUnitaryFormula
    deriving Show

-- <thf_apply_formula>  ::= <thf_unitary_formula> @ <thf_unitary_formula> |
--                          <thf_apply_formula> @ <thf_unitary_formula>
data THFApplyFormula =
    TApF_THF_Apply_Formula      THFUnitaryFormula THFUnitaryFormula
  | TApF_THF_Apply_Formula_Il   THFApplyFormula THFUnitaryFormula
    deriving Show

-- <thf_unitary_formula> ::= <thf_quantified_formula> | <thf_unary_formula> |
--                           <thf_atom> | <thf_tuple> | <thf_let> |
--                           <thf_conditional> | (<thf_logic_formula>)
data THFUnitaryFormula =
    TUF_THF_Quantified_Formula  THFQuantifiedFormula
  | TUF_THF_Unary_Formula       THFUnaryFormula
  | TUF_THF_atom                THFAtom
  | TUF_THF_Tuple               THFTuple
  | TUF_THF_Let                 THFLet
  | TUF_THF_Conditional         THFConditional
  | TUF_THF_Logic_Formula       THFLogicFormula
    deriving Show

-- <thf_quantified_formula> ::= <thf_quantifier> [<thf_variable_list>] :
--                              <thf_unitary_formula>
data THFQuantifiedFormula =
    TQF_THF_Quantified_Formula {thf_quantifier      :: THFQuantifier,
                                thf_variable_list   :: THFVariableList,
                                thf_unitary_formula :: THFUnitaryFormula}
    deriving Show

-- <thf_variable_list> ::= <thf_variable> |
--                         <thf_variable>,<thf_variable_list>
-- THFVariableList must not be empty
type THFVariableList = [THFVariable]

-- <thf_variable> ::= <thf_typed_variable> | <variable>
data THFVariable =
    TV_THF_Typed_Variable   THFTypedVariable
  | TV_Variable             Variable
    deriving Show

-- <thf_typed_variable> ::= <variable> : <thf_top_level_type>
data THFTypedVariable =
    TTV_THF_Typed_Variable {ttv_variable            :: Variable,
                            ttv_thf_top_level_type  :: THFTopLevelType}
    deriving Show

-- thf_unary_formula>  ::= <thf_unary_connective> (<thf_logic_formula>)
data THFUnaryFormula =
    TUnF_THF_Unary_Formula {thf_unary_connective    :: THFUnaryConnective,
                            thf_logic_formula       :: THFLogicFormula}
    deriving Show

-- <thf_type_formula> ::= <thf_typeable_formula> : <thf_top_level_type>
-- <thf_type_formula> :== <constant> : <thf_top_level_type>
data THFTypeFormula =
    TTF_THF_Type_Formula    {ttf_thf_typeable_formula  :: THFTypeableFormula,
                             ttf_thf_top_level_type    :: THFTopLevelType}
  | TTF_THF_Role_Type       {ttf_constant              :: Constant,
                             ttf_thf_top_level_type    :: THFTopLevelType}
    deriving Show

-- <thf_typeable_formula> ::= <thf_atom> | <thf_tuple> | (<thf_logic_formula>)
data THFTypeableFormula =
    TTyF_THF_Atom           THFAtom
  | TTyF_THF_Tuple          THFTuple
  | TTyF_THF_Logic_Formula  THFLogicFormula
    deriving Show

-- <thf_subtype> ::= <constant> <subtype_sign> <constant>
-- <subtype_sign> == <<
data THFSubType =
    TST_THF_Sub_Type {constant_front    :: Constant,
                      constant_back     :: Constant}
    deriving Show

-- <thf_top_level_type> ::= <thf_logic_formula>
type THFTopLevelType = THFLogicFormula

-- <thf_unitary_type>   ::= <thf_unitary_formula>
type THFUnitaryType = THFUnitaryFormula

-- <thf_binary_type> ::= <thf_mapping_type> | <thf_xprod_type> |
--                       <thf_union_type>
data THFBinaryType =
    TBT_THF_Mapping_Type    THFMappingType
  | TBT_THF_Xprod_Type      THFXprodType
  | TBT_THF_Union_Type      THFUnionType
    deriving Show

-- <thf_mapping_type> ::= <thf_unitary_type> <arrow> <thf_unitary_type> |
--                        <thf_unitary_type> <arrow> <thf_mapping_type>
-- <arrow> ::- >
data THFMappingType =
    TMT_THF_Mapping_Type    THFUnitaryType THFUnitaryType
  | TMT_THF_Mapping_Type_Il THFUnitaryType THFMappingType
    deriving Show

-- <thf_xprod_type> ::= <thf_unitary_type> <star> <thf_unitary_type> |
--                      <thf_xprod_type> <star> <thf_unitary_type>
-- <star> ::- *
data THFXprodType =
    TXT_THF_Xprod_Type      THFUnitaryType THFUnitaryType
  | TXT_THF_Xprod_Type_Il   THFXprodType THFUnitaryType
    deriving Show

-- <thf_union_type> ::= <thf_unitary_type> <plus> <thf_unitary_type> |
--                      <thf_union_type> <plus> <thf_unitary_type>
-- <plus> ::- +
data THFUnionType =
    TUT_THF_Union_Type      THFUnitaryType THFUnitaryType
  | TUT_THF_Union_Type_Il   THFUnionType THFUnitaryType
    deriving Show

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
    deriving Show

-- <thf_tuple> ::= [] | [<thf_tuple_list>]
-- <thf_tuple_list> ::= <thf_unitary_formula> |
--                      <thf_unitary_formula>,<thf_tuple_list>
-- THFTupleList must not be empty
type THFTuple = [THFUnitaryFormula]

-- <thf_let> ::= := [<thf_let_list>] : <thf_unitary_formula>
data THFLet =
    TL_THf_Let {tl_thf_let_list         :: THFLetList,
                tl_thf_unitary_formula  :: THFUnitaryFormula}
    deriving Show

-- <thf_let_list> ::= <thf_defined_var> |
--                    <thf_defined_var>,<thf_let_list>
-- THFLetList must not be empty
type THFLetList = [THFDefinedVar]

-- <thf_defined_var> ::= <thf_variable> := <thf_logic_formula> |
--                       (<thf_defined_var>)
data THFDefinedVar =
    TDV_THF_Defined_Var             {tdv_thf_variable         :: THFVariable,
                                     tdv_thf_logic_formula    :: THFLogicFormula}
  | TDV_THF_Defined_Var_Bracketed   THFDefinedVar
    deriving Show

-- <thf_conditional> ::= $itef(<thf_logic_formula>,<thf_logic_formula>,
--                       <thf_logic_formula>)
data THFConditional =
    TC_THF_Conditional {tc_thf_logic_formula_1  :: THFLogicFormula,
                        tc_thf_logic_formula_2  :: THFLogicFormula,
                        tc_thf_logic_formula_3  :: THFLogicFormula}
    deriving Show

-- <thf_sequent> ::= <thf_tuple> <gentzen_arrow> <thf_tuple> |
--                   (<thf_sequent>)
-- <gentzen_arrow> ::= -->
data THFSequent =
    TS_THF_Sequent              {ts_thf_tuple_front :: THFTuple,
                                 ts_thf_tuple_back  :: THFTuple}
  | TS_THF_Sequent_Bracketed    THFSequent
    deriving Show

-- <thf_conn_term> ::= <thf_pair_connective> | <assoc_connective> |
--                     <thf_unary_connective>
data THFConnTerm =
    TCT_THF_Pair_Connective     THFPairConnective
  | TCT_Assoc_Connective        AssocConnective
  | TCT_THF_Unary_Connective    THFUnaryConnective
    deriving Show

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
    deriving Show

-- <thf_pair_connective> ::= <infix_equality> | <infix_inequality> |
--                          <binary_connective>
-- <binary_connective>  ::= <=> | => | <= | <~> | ~<vline> | ~&
data THFPairConnective =
    Infix_Equality          -- =
  | Infix_Inequality        -- !=
  | Equivalent              -- <=>
  | Implication             -- =>
  | IF                      -- <=
  | XOR                     -- <~>
  | NOR                     -- ~|
  | NAND                    -- ~&
    deriving Show

-- <thf_unary_connective> ::= <unary_connective> | !! | ??
-- <unary_connective>   ::= ~
-- http://www.cs.miami.edu/~tptp/TPTP/THF/
data THFUnaryConnective =
    Negation                -- ~
  | PiForAll                -- !!
  | SigmaExists             -- ??
    deriving Show

-- <assoc_connective>   ::= <vline> | &
data AssocConnective =
    OR      -- |
  | AND     -- &
    deriving Show

-- <defined_type>       ::= <atomic_defined_word>
-- <defined_type>       :== $oType | $o | $iType | $i | $tType |
--                          $real | $rat | $int
data DefinedType =
    DT_oType | DT_o    | DT_iType | DT_i
  | DT_tType | DT_real | DT_rat   | DT_int
    deriving Show

-- <defined_plain_formula> ::= <defined_plain_term>
-- <defined_plain_formula> :== <defined_prop> | <defined_pred>(<arguments>)
data DefinedPlainFormula =
    DPF_Defined_Prop    DefinedProp
  | DPF_Defined_Formula {dpf_defined_pred   :: DefinedPred,
                         dpf_arguments      :: Arguments}
    deriving Show

-- <defined_prop>       :== <atomic_defined_word>
-- <defined_prop>       :== $true | $false
data DefinedProp =
    DP_True | DP_False
    deriving Show

-- <defined_pred>       :== <atomic_defined_word>
-- <defined_pred>       :== $equal | $distinct | $itef | $less |
--                          $lesseq | $greater | $greatereq | $evaleq |
--                          $is_int | $is_rat
data DefinedPred =
    DP_equal  | DP_disrinct | DP_itef      | DP_less
  | DP_lesseq | DP_greater  | DP_greatereq | DP_evaleq
  | DP_is_int | DP_is_rat
    deriving Show

-- <term> ::= <function_term> | <variable> | <conditional_term>
-- %----Conditional terms should not be used by THF
data Term =
    T_Function_Term    FunctionTerm
  | T_Variable        Variable
    deriving Show

-- <function_term> ::= <plain_term> | <defined_term> | <system_term>
data FunctionTerm =
    FT_Plain_Term   PlainTerm
  | FT_Defined_Term DefinedTerm
  | FT_System_Term  SystemTerm
    deriving Show

-- <plain_term> ::= <constant> | <functor>(<arguments>)
data PlainTerm =
    PT_Constant     Constant
  | PT_Plain_Term   {pt_functor     :: TPTPFunctor,
                     pt_arguments   :: Arguments}
    deriving Show

-- Constanten besteheb aus einem kleinen Buchstabeun gefolgt von
-- alpfanumerischen Zeichen
-- <constant> ::= <functor>
type Constant = TPTPFunctor

-- <functor>            ::= <atomic_word>
type TPTPFunctor = AtomicWord

-- <defined_term> ::= <defined_atom> | <defined_atomic_term>
data DefinedTerm =
    DT_Defined_Atom         DefinedAtom
  | DT_Defined_Atomic_Term  DefinedAtomicTerm
    deriving Show

-- <defined_atom> ::= <number> | <distinct_object>
data DefinedAtom =
    DA_Number           Number
  | DA_Distinct_Object  DistinctObject
    deriving Show

-- <defined_atomic_term> ::= <defined_plain_term>
type DefinedAtomicTerm = DefinedPlainTerm

-- <defined_plain_term> ::= <defined_constant> | <defined_functor>(<arguments>)
data DefinedPlainTerm =
    DPT_Defined_Constant    DefinedConstant
  | DPT_Defined_Function    {dpt_defined_functor    :: DefinedFunctor,
                             dpt_arguments          :: Arguments}
    deriving Show

-- <defined_constant> ::= <defined_functor>
type DefinedConstant = DefinedFunctor

-- <defined_functor> ::= <atomic_defined_word>
-- <defined_functor> :== $itett | $uminus | $sum | $difference |
--                       $product | $to_int | $to_rat | $to_real
data DefinedFunctor =
    Itett   | Uminus | Sum    | Difference
  | Product | To_int | To_rat | To_real
    deriving Show

-- <system_term> ::= <system_constant> | <system_functor>(<arguments>)
data SystemTerm =
    ST_System_Constant  SystemConstant
  | ST_System_Term      {st_system_functor  :: SystemFunctor,
                         st_arguments       :: Arguments}
    deriving Show

-- <system_constant> ::= <system_functor>
type SystemConstant = SystemFunctor

-- <system_functor>     ::= <atomic_system_word>
type SystemFunctor = AtomicSystemWord

-- variablen bestehen aus einen großen buchstaben gefolgt von
-- alpfanumerischen zeichen
-- <variable>           ::= <upper_word>
type Variable = String

-- <arguments> ::= <term> | <term>,<arguments>
data Arguments =
    A_Term          Term
  | A_Arguments_Rec {a_term         :: Term,
                     a_arguments    :: Arguments}
    deriving Show

-- <principal_symbol>   :== <functor> | <variable>
data PrincipalSymbol =
    PS_Functor  TPTPFunctor
  | PS_Variable Variable
    deriving Show

-- <source>             ::= <general_term>
-- <source>             :== <dag_source> | <internal_source> | <external_source> |
--                          unknown | [<sources>]
-- <internal_source>    :== introduced(<intro_type><optional_info>)
data Source =
    S_Dag_Source        DagSource
  | S_Internal_Source   {is_intro_type      :: IntroType,
                         is_optional_info   :: OptionalInfo}
  | S_External_Source   ExternalSource
  | S_Sources           Sources
  | S_Unknown
    deriving Show

-- <sources>            :== <source> | <source>,<sources>
-- Sources must not be empty
type Sources = [Source]

-- <dag_source>         :== <name> | <inference_record>
-- <inference_record>   :== inference(<inference_rule>,<useful_info>,
--                              [<parent_list>])
-- <inference_rule>     :== <atomic_word>
data DagSource =
    DS_Name             Name
  | DS_Inference_Record {inference_rule :: AtomicWord,
                         useful_info    :: UsefulInfo,
                         parent_list    :: ParentList}
    deriving Show

-- <parent_list>        :== <parent_info> | <parent_info>,<parent_list>
-- ParentList must not be empty
type ParentList = [ParentInfo]

-- <parent_info>        :== <source><parent_details>
-- <parent_details>     :== :<general_list> | <null>
data ParentInfo =
    PI_Parent_Info  {pi_source          :: Source,
                     piparent_detail    :: (Maybe GeneralList)}
    deriving Show

-- <intro_type>         :== definition | axiom_of_choice | tautology | assumption
data IntroType =
   IT_definition | IT_axiom_of_choice | IT_tautology | IT_assumption
   deriving Show

-- <external_source>    :== <file_source> | <theory> | <creator_source>
-- <theory>             :== theory(<theory_name><optional_info>)
-- <creator_source>     :== creator(<creator_name><optional_info>)
-- <creator_name>       :== <atomic_word>
data ExternalSource =
    ES_File_Source      FileSource
  | ES_Theory           {theory_name            :: TheoryName,
                         es_t_optional_info     :: OptionalInfo}
  | ES_Creator_Source   {creator_name           :: AtomicWord,
                         es_cs_optional_info    :: OptionalInfo}
    deriving Show

-- <file_source>        :== file(<file_name><file_info>)
-- <file_info>          :== ,<name> | <null>
data FileSource =
    FS_File {fs_file_name   :: FileName,
             fs_file_info   :: (Maybe Name)}
    deriving Show

-- <theory_name>        :== equality | ac
data TheoryName =
    Equality | Ac
    deriving Show

-- <optional_info>      ::= ,<useful_info> | <null>
data OptionalInfo =
    OI_Useful_Info     UsefulInfo
  | OI_Null
    deriving Show

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
    deriving Show

-- <formula_item>       :== <description_item> | <iquote_item>
-- <description_item>   :== description(<atomic_word>)
-- <iquote_item>        :== iquote(<atomic_word>)
data FormulaItem =
    FI_Description_Item AtomicWord
  | FI_Iquote_Item      AtomicWord
    deriving Show

-- <inference_item>     :== <inference_status> | <assumptions_record> |
--                          <new_symbol_record> | <refutation>
data InferenceItem =
    II_Inference_Status     InferenceStatus
  | II_Assumptions_Record   AssumptionRecord
  | II_New_Symbol_Record    NewSymbolRecord
  | II_Refutation           Refutation
    deriving Show

-- <inference_status>   :== status(<status_value>) | <inference_info>
-- <inference_info>     :== <inference_rule>(<atomic_word>,<general_list>)
-- <inference_rule>     :== <atomic_word>
data InferenceStatus =
    IS_Status           StatusValue
  | IS_Inference_Info   {ii_inference_rule :: AtomicWord,
                         ii_atomic_word    :: AtomicWord,
                         ii_general_List   :: GeneralList}
    deriving Show

-- <status_value>       :== suc | unp | sap | esa | sat | fsa | thm | eqv | tac |
--                          wec | eth | tau | wtc | wth | cax | sca | tca | wca |
--                          cup | csp | ecs | csa | cth | ceq | unc | wcc | ect |
--                          fun | uns | wuc | wct | scc | uca | noc
data StatusValue =
    Suc | Unp | Sap | Esa | Sat | Fsa | Thm | Eqv | Tac
  | Wec | Eth | Tau | Wtc | Wth | Cax | Sca | Tca | Wca
  | Cup | Csp | Ecs | Csa | Cth | Ceq | Unc | Wcc | Ect
  | Fun | Uns | Wuc | Wct | Scc | Uca | Noc
  deriving Show

-- <assumptions_record> :== assumptions([<name_list>])
-- the list must not be empty
type AssumptionRecord = NameList

-- <refutation>         :== refutation(<file_source>)
type Refutation = FileSource

-- <new_symbol_record>  :== new_symbols(<atomic_word>,[<new_symbol_list>])
-- <new_symbol_list>    :== <principal_symbol> |
--                          <principal_symbol>,<new_symbol_list>
data NewSymbolRecord =
    NSR_New_Symbols {atomic_word        :: AtomicWord,
                     new_symbol_list    :: [PrincipalSymbol]}
    deriving Show

-- <formula_selection>  ::= ,[<name_list>] | <null>
-- FS_Name_List must not be empty! For empty FormulaSelections
-- use FS_Null
data FormulaSelection =
    FS_Null
  | FS_Name_List    NameList
    deriving Show

-- <name_list>          ::= <name> | <name>,<name_list>
-- the list must mot be empty
type NameList = [Name]

-- <general_term>       ::= <general_data> | <general_data>:<general_term> |
--                          <general_list>
data GeneralTerm =
    GT_General_Data         GeneralData
  | GT_General_Data_Term    {general_data   :: GeneralData,
                             general_term   :: GeneralTerm}
  | GT_General_List         GeneralList
    deriving Show

-- <general_data>       ::= <atomic_word> | <general_function> |
--                          <variable> | <number> | <distinct_object> |
--                          <formula_data>
-- <general_data>       :== bind(<variable>,<formula_data>)
-- das zweite fehlt noch
data GeneralData =
    GD_Atomic_Word      AtomicWord
  | GD_General_Function GeneralFunction
  | GD_Variable         Variable
  | GD_Number           Number
  | GD_Distinct_Object  DistinctObject
  | GD_Formula_Data     FormulaData
  | GD_Bind             {gd_variable        :: Variable,
                         gd_formula_data    :: FormulaData}
    deriving Show

-- <general_function>   ::= <atomic_word>(<general_terms>)
-- general_terms must not be empty
data GeneralFunction =
    GF_General_Function {atpmic_word    :: AtomicWord,
                         general_terms  :: [GeneralTerm]}
    deriving Show

-- <formula_data>       ::= $thf(<thf_formula>) | $tff(<tff_formula>) |
--                          $fof(<fof_formula>) | $cnf(<cnf_formula>) |
--                          $fot(<term>)
-- only thf is used here
data FormulaData =
    THF_Formula THFFormula
    deriving Show

-- <general_list>       ::= [] | [<general_terms>]
-- <general_terms>      ::= <general_term> | <general_term>,<general_terms>
type GeneralList = [GeneralTerm]

-- <name>               ::= <atomic_word> | <integer>
data Name =
    N_Atomic_Word   AtomicWord
  | N_Integer       String
    deriving Show

-- <atomic_word>        ::= <lower_word> | <single_quoted>
-- <lower_word>         ::- <lower_alpha><alpha_numeric>*
-- <single_quoted>      ::- <single_quote><sq_char><sq_char>*<single_quote>
-- <alpha_numeric>      ::: (<lower_alpha>|<upper_alpha>|<numeric>|[_])
-- <single_quote>       ::: [']
-- <sq_char>            ::: ([\40-\46\50-\133\135-\176]|[\\]['\\])
-- <lower_alpha>        ::: [a-z]
-- <upper_alpha>        ::: [A-Z]
-- <numeric>            ::: [0-9]
type AtomicWord = String

-- <atomic_system_word> ::= <dollar_dollar_word>
-- <dollar_dollar_word> ::- <dollar><dollar><lower_word>
-- <dollar>             ::: [$]
-- <lower_word>         ::- <lower_alpha><alpha_numeric>*
-- <lower_alpha>        ::: [a-z]
-- <upper_alpha>        ::: [A-Z]
-- <alpha_numeric>      ::: (<lower_alpha>|<upper_alpha>|<numeric>|[_])
type AtomicSystemWord = String

-- <number> ::= <integer> | <rational> | <real>
data Number =
    Num_Integer   String
  | Num_Rational  String
  | Num_Real      String
    deriving Show

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
