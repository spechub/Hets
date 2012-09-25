{- |
Module      :  $Header$
Description :  A abstract syntax for the TPTP-THF Syntax
Copyright   :  (c) A. Tsogias, DFKI Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Alexis.Tsogias@dfki.de
Stability   :  provisional
Portability :  portable

A Abstract Syntax for the TPTP-THF Input Syntax v5.1.0.2 taken from
<http://www.cs.miami.edu/~tptp/TPTP/SyntaxBNF.html>
In addition the Syntax for THF0 taken from
<http://www.ags.uni-sb.de/~chris/papers/C25.pdf> P. 15-16
has been added where needed.
-}

module THF.As where

--------------------------------------------------------------------------------
-- Abstract Syntax for THF in general and THF0
-- For Explanation of the data types refer to the comments in ParseTHF
--------------------------------------------------------------------------------
-- Questions:
--      * at the example of <source>: Sould <general_term> be also
--        tried when all ather variations fail?
--------------------------------------------------------------------------------

data TPTP_THF =
    TPTP_THF_Annotated_Formula  { nameAF :: Name
                                , formulaRoleAF :: FormulaRole
                                , thfFormulaAF :: THFFormula
                                , annotationsAF :: Annotations}
  | TPTP_Include                Include
  | TPTP_Comment                Comment
  | TPTP_Defined_Comment        DefinedComment
  | TPTP_System_Comment         SystemComment
  | TPTP_Header                 [Comment]
    deriving (Show, Eq, Ord)

data Comment =
    Comment_Line    String
  | Comment_Block   [String]
    deriving (Show, Eq, Ord)

data DefinedComment =
    Defined_Comment_Line    String
  | Defined_Comment_Block   [String]
    deriving (Show, Eq, Ord)

data SystemComment =
    System_Comment_Line    String
  | System_Comment_Block   [String]
    deriving (Show, Eq, Ord)

data Include =
    I_Include   FileName (Maybe NameList)
    deriving (Show, Eq, Ord)

data Annotations =
    Annotations Source OptionalInfo
  | Null
    deriving (Show, Eq, Ord)

data FormulaRole =
    Axiom | Hypothesis | Definition  | Assumption
  | Lemma | Theorem    | Conjecture  | Negated_Conjecture
  | Plain | Fi_Domain  | Fi_Functors | Fi_Predicates
  | Type  | Unknown
    deriving (Show, Eq, Ord)

data THFFormula =
    TF_THF_Logic_Formula    THFLogicFormula
  | TF_THF_Sequent          THFSequent
  | T0F_THF_Typed_Const     THFTypedConst
    deriving (Show, Eq, Ord)

data THFLogicFormula =
    TLF_THF_Binary_Formula  THFBinaryFormula
  | TLF_THF_Unitary_Formula THFUnitaryFormula
  | TLF_THF_Type_Formula    THFTypeFormula
  | TLF_THF_Sub_Type        THFSubType
    deriving (Show, Eq, Ord)

data THFBinaryFormula =
    TBF_THF_Binary_Pair     THFUnitaryFormula THFPairConnective
                            THFUnitaryFormula
  | TBF_THF_Binary_Tuple    THFBinaryTuple
  | TBF_THF_Binary_Type     THFBinaryType
    deriving (Show, Eq, Ord)

data THFBinaryTuple =
    TBT_THF_Or_Formula      [THFUnitaryFormula]
  | TBT_THF_And_Formula     [THFUnitaryFormula]
  | TBT_THF_Apply_Formula   [THFUnitaryFormula]
    deriving (Show, Eq, Ord)

data THFUnitaryFormula =
    TUF_THF_Quantified_Formula  THFQuantifiedFormula
  | TUF_THF_Unary_Formula       THFUnaryConnective THFLogicFormula
  | TUF_THF_Atom                THFAtom
  | TUF_THF_Tuple               THFTuple
  | TUF_THF_Let                 [THFDefinedVar] THFUnitaryFormula
  | TUF_THF_Conditional         THFLogicFormula THFLogicFormula THFLogicFormula
  | TUF_THF_Logic_Formula_Par   THFLogicFormula
  | T0UF_THF_Abstraction        THFVariableList THFUnitaryFormula
    deriving (Show, Eq, Ord)

data THFQuantifiedFormula =
    TQF_THF_Quantified_Formula  THFQuantifier THFVariableList THFUnitaryFormula
  | T0QF_THF_Quantified_Var     Quantifier THFVariableList THFUnitaryFormula
  | T0QF_THF_Quantified_Novar   THFQuantifier THFUnitaryFormula
    deriving (Show, Eq, Ord)

type THFVariableList = [THFVariable]

data THFVariable =
    TV_THF_Typed_Variable   Variable THFTopLevelType
  | TV_Variable             Variable
    deriving (Show, Eq, Ord)

data THFTypedConst =
    T0TC_Typed_Const            Constant THFTopLevelType
  | T0TC_THF_TypedConst_Par     THFTypedConst
    deriving (Show, Eq, Ord)

data THFTypeFormula =
    TTF_THF_Type_Formula    THFTypeableFormula THFTopLevelType
  | TTF_THF_Typed_Const     Constant THFTopLevelType
    deriving (Show, Eq, Ord)

data THFTypeableFormula =
    TTyF_THF_Atom           THFAtom
  | TTyF_THF_Tuple          THFTuple
  | TTyF_THF_Logic_Formula  THFLogicFormula
    deriving (Show, Eq, Ord)

data THFSubType =
    TST_THF_Sub_Type        Constant Constant
    deriving (Show, Eq, Ord)

data THFTopLevelType =
    TTLT_THF_Logic_Formula  THFLogicFormula
  | T0TLT_Constant          Constant
  | T0TLT_Variable          Variable
  | T0TLT_Defined_Type      DefinedType
  | T0TLT_System_Type       SystemType
  | T0TLT_THF_Binary_Type   THFBinaryType
    deriving (Show, Eq, Ord)

data THFUnitaryType =
    TUT_THF_Unitary_Formula     THFUnitaryFormula
  | T0UT_Constant               Constant
  | T0UT_Variable               Variable
  | T0UT_Defined_Type           DefinedType
  | T0UT_System_Type            SystemType
  | T0UT_THF_Binary_Type_Par    THFBinaryType
    deriving (Show, Eq, Ord)

data THFBinaryType =
    TBT_THF_Mapping_Type        [THFUnitaryType]
  | TBT_THF_Xprod_Type          [THFUnitaryType]
  | TBT_THF_Union_Type          [THFUnitaryType]
  | T0BT_THF_Binary_Type_Par    THFBinaryType
    deriving (Show, Eq, Ord)

data THFAtom =
    TA_Term                     Term
  | TA_THF_Conn_Term            THFConnTerm
  | TA_Defined_Type             DefinedType
  | TA_Defined_Plain_Formula    DefinedPlainFormula
  | TA_System_Type              SystemType
  | TA_System_Atomic_Formula    SystemTerm
  | T0A_Constant                Constant
  | T0A_Defined_Constant        AtomicDefinedWord
  | T0A_System_Constant         AtomicSystemWord
  | T0A_Variable                Variable
    deriving (Show, Eq, Ord)

type THFTuple = [THFUnitaryFormula]

data THFDefinedVar =
    TDV_THF_Defined_Var     THFVariable THFLogicFormula
  | TDV_THF_Defined_Var_Par THFDefinedVar
    deriving (Show, Eq, Ord)

data THFSequent =
    TS_THF_Sequent      THFTuple THFTuple
  | TS_THF_Sequent_Par  THFSequent
    deriving (Show, Eq, Ord)

data THFConnTerm =
    TCT_THF_Pair_Connective     THFPairConnective
  | TCT_Assoc_Connective        AssocConnective
  | TCT_THF_Unary_Connective    THFUnaryConnective
  | T0CT_THF_Quantifier         THFQuantifier
    deriving (Show, Eq, Ord)

data THFQuantifier =
    TQ_ForAll                   -- !
  | TQ_Exists                   -- ?
  | TQ_Lambda_Binder            -- ^
  | TQ_Dependent_Product        -- !>
  | TQ_Dependent_Sum            -- ?*
  | TQ_Indefinite_Description   -- @+
  | TQ_Definite_Description     -- @-
  | T0Q_PiForAll                -- !!
  | T0Q_SigmaExists             -- ??
    deriving (Show, Eq, Ord)

data Quantifier =
    T0Q_ForAll                  -- !
  | T0Q_Exists                  -- ?
    deriving (Show, Eq, Ord)

data THFPairConnective =
    Infix_Equality          -- =
  | Infix_Inequality        -- !=
  | Equivalent              -- <=>
  | Implication             -- =>
  | IF                      -- <=
  | XOR                     -- <~>
  | NOR                     -- ~|
  | NAND                    -- ~&
    deriving (Show, Eq, Ord)

data THFUnaryConnective =
    Negation                -- ~
  | PiForAll                -- !!
  | SigmaExists             -- ??
    deriving (Show, Eq, Ord)

data AssocConnective =
    OR      -- |
  | AND     -- &
    deriving (Show, Eq, Ord)

data DefinedType =
    DT_oType | DT_o    | DT_iType | DT_i
  | DT_tType | DT_real | DT_rat   | DT_int
    deriving (Show, Eq, Ord)

type SystemType = AtomicSystemWord

data DefinedPlainFormula =
    DPF_Defined_Prop    DefinedProp
  | DPF_Defined_Formula DefinedPred Arguments
    deriving (Show, Eq, Ord)

data DefinedProp =
    DP_True | DP_False
    deriving (Show, Eq, Ord)

data DefinedPred =
    Equal  | Disrinct | Itef      | Less
  | Lesseq | Greater  | Greatereq | Evaleq
  | Is_int | Is_rat
    deriving (Show, Eq, Ord)

data Term =
    T_Function_Term     FunctionTerm
  | T_Variable          Variable
    deriving (Show, Eq, Ord)

data FunctionTerm =
    FT_Plain_Term   PlainTerm
  | FT_Defined_Term DefinedTerm
  | FT_System_Term  SystemTerm
    deriving (Show, Eq, Ord)

data PlainTerm =
    PT_Plain_Term   TPTPFunctor Arguments
  | PT_Constant     Constant
    deriving (Show, Eq, Ord)

type Constant = TPTPFunctor

type TPTPFunctor = AtomicWord

data DefinedTerm =
    DT_Defined_Atom         DefinedAtom
  | DT_Defined_Atomic_Term  DefinedPlainTerm
    deriving (Show, Eq, Ord)

data DefinedAtom =
    DA_Number           Number
  | DA_Distinct_Object  DistinctObject
    deriving (Show, Eq, Ord)

data DefinedPlainTerm =
    DPT_Defined_Function    DefinedFunctor Arguments
  | DPT_Defined_Constant    DefinedFunctor
    deriving (Show, Eq, Ord)

data DefinedFunctor =
    Itett   | Uminus | Sum    | Difference
  | Product | To_int | To_rat | To_real
    deriving (Show, Eq, Ord)

data SystemTerm =
    ST_System_Term      SystemFunctor Arguments
  | ST_System_Constant  SystemFunctor
    deriving (Show, Eq, Ord)

type SystemFunctor = AtomicSystemWord

type Variable = String

type Arguments = [Term]

data PrincipalSymbol =
    PS_Functor  TPTPFunctor
  | PS_Variable Variable
    deriving (Show, Eq, Ord)

data Source =
    S_Dag_Source        DagSource
  | S_Internal_Source   IntroType OptionalInfo
  | S_External_Source   ExternalSource
  | S_Sources           [Source]
  | S_Unknown
    deriving (Show, Eq, Ord)

data DagSource =
    DS_Name             Name
  | DS_Inference_Record AtomicWord UsefulInfo [ParentInfo]
    deriving (Show, Eq, Ord)

data ParentInfo =
    PI_Parent_Info  Source (Maybe GeneralList)
    deriving (Show, Eq, Ord)

data IntroType =
   IT_definition | IT_axiom_of_choice | IT_tautology | IT_assumption
   deriving (Show, Eq, Ord)

data ExternalSource =
    ES_File_Source      FileSource
  | ES_Theory           TheoryName OptionalInfo
  | ES_Creator_Source   AtomicWord OptionalInfo
    deriving (Show, Eq, Ord)

data FileSource =
    FS_File FileName (Maybe Name)
    deriving (Show, Eq, Ord)

data TheoryName =
    Equality | Ac
    deriving (Show, Eq, Ord)

type OptionalInfo = (Maybe UsefulInfo)

type UsefulInfo = [InfoItem]

data InfoItem =
    II_Formula_Item     FormulaItem
  | II_Inference_Item   InferenceItem
  | II_General_Function GeneralFunction
    deriving (Show, Eq, Ord)

data FormulaItem =
    FI_Description_Item AtomicWord
  | FI_Iquote_Item      AtomicWord
    deriving (Show, Eq, Ord)

data InferenceItem =
    II_Inference_Status     InferenceStatus
  | II_Assumptions_Record   NameList
  | II_New_Symbol_Record    AtomicWord [PrincipalSymbol]
  | II_Refutation           FileSource
    deriving (Show, Eq, Ord)

data InferenceStatus =
    IS_Status           StatusValue
  | IS_Inference_Info   AtomicWord AtomicWord GeneralList
    deriving (Show, Eq, Ord)

data StatusValue =
    Suc | Unp | Sap | Esa | Sat | Fsa | Thm | Eqv | Tac
  | Wec | Eth | Tau | Wtc | Wth | Cax | Sca | Tca | Wca
  | Cup | Csp | Ecs | Csa | Cth | Ceq | Unc | Wcc | Ect
  | Fun | Uns | Wuc | Wct | Scc | Uca | Noc
  deriving (Show, Eq, Ord)

type NameList = [Name]

data GeneralTerm =
    GT_General_Data         GeneralData
  | GT_General_Data_Term    GeneralData GeneralTerm
  | GT_General_List         GeneralList
    deriving (Show, Eq, Ord)

data GeneralData =
    GD_Atomic_Word      AtomicWord
  | GD_Variable         Variable
  | GD_Number           Number
  | GD_Distinct_Object  DistinctObject
  | GD_Formula_Data     FormulaData
  | GD_Bind             Variable FormulaData
  | GD_General_Function GeneralFunction
    deriving (Show, Eq, Ord)

data GeneralFunction =
    GF_General_Function AtomicWord GeneralTerms
    deriving (Show, Eq, Ord)

data FormulaData =
    THF_Formula THFFormula
    deriving (Show, Eq, Ord)

type GeneralList = GeneralTerms

type GeneralTerms = [GeneralTerm]

data Name =
    N_Atomic_Word           AtomicWord
  | N_Integer               String
  | T0N_Unsigned_Integer    String
    deriving (Show, Eq, Ord)

data AtomicWord =
    A_Lower_Word    LowerWord
  | A_Single_Quoted SingleQuoted
    deriving (Show, Eq, Ord)

type AtomicSystemWord = LowerWord

type AtomicDefinedWord = LowerWord

data Number =
    Num_Integer   String
  | Num_Rational  String
  | Num_Real      String
    deriving (Show, Eq, Ord)

type FileName = SingleQuoted

type SingleQuoted = String

type DistinctObject = String

type LowerWord = String

type UpperWord = String
