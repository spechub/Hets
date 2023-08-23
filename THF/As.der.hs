{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./THF/As.der.hs
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

import Common.Id

import Data.Data

{-! global: GetRange !-}

{- ---------------------------------------------------------------------------
Abstract Syntax for THF in general and THF0
For Explanation of the data types refer to the comments in ParseTHF
------------------------------------------------------------------------------
Questions:
at the example of <source>: Sould <general_term> be also
tried when all ather variations fail?
----------------------------------------------------------------------------- -}

data TPTP_THF =
    TPTP_THF_Annotated_Formula { nameAF :: Name
                                , formulaRoleAF :: FormulaRole
                                , thfFormulaAF :: THFFormula
                                , annotationsAF :: Annotations}
  | TPTP_Include Include
  | TPTP_Comment Comment
  | TPTP_Defined_Comment DefinedComment
  | TPTP_System_Comment SystemComment
  | TPTP_Header [Comment]
    deriving (Show, Eq, Ord, Typeable, Data)

data Comment =
    Comment_Line Token
  | Comment_Block Token
    deriving (Show, Eq, Ord, Typeable, Data)

data DefinedComment =
    Defined_Comment_Line Token
  | Defined_Comment_Block Token
    deriving (Show, Eq, Ord, Typeable, Data)

data SystemComment =
    System_Comment_Line Token
  | System_Comment_Block Token
    deriving (Show, Eq, Ord, Typeable, Data)

data Include =
    I_Include Token (Maybe NameList)
    deriving (Show, Eq, Ord, Typeable, Data)

data Annotations =
    Annotations Source OptionalInfo
  | Null
    deriving (Show, Eq, Ord, Typeable, Data)

data FormulaRole =
    Axiom | Hypothesis | Definition | Assumption
  | Lemma | Theorem | Conjecture | Negated_Conjecture
  | Plain | Fi_Domain | Fi_Functors | Fi_Predicates
  | Type | Unknown
    deriving (Show, Eq, Ord, Typeable, Data)

data THFFormula =
    TF_THF_Logic_Formula THFLogicFormula
  | TF_THF_Sequent THFSequent
  | T0F_THF_Typed_Const THFTypedConst
    deriving (Show, Eq, Ord, Typeable, Data)

data THFLogicFormula =
    TLF_THF_Binary_Formula THFBinaryFormula
  | TLF_THF_Unitary_Formula THFUnitaryFormula
  | TLF_THF_Type_Formula THFTypeFormula
  | TLF_THF_Sub_Type THFSubType
    deriving (Show, Eq, Ord, Typeable, Data)

data THFBinaryFormula =
    TBF_THF_Binary_Pair THFUnitaryFormula THFPairConnective
                            THFUnitaryFormula
  | TBF_THF_Binary_Tuple THFBinaryTuple
  | TBF_THF_Binary_Type THFBinaryType
    deriving (Show, Eq, Ord, Typeable, Data)

data THFBinaryTuple =
    TBT_THF_Or_Formula [THFUnitaryFormula]
  | TBT_THF_And_Formula [THFUnitaryFormula]
  | TBT_THF_Apply_Formula [THFUnitaryFormula]
    deriving (Show, Eq, Ord, Typeable, Data)

data THFUnitaryFormula =
    TUF_THF_Quantified_Formula THFQuantifiedFormula
  | TUF_THF_Unary_Formula THFUnaryConnective THFLogicFormula
  | TUF_THF_Atom THFAtom
  | TUF_THF_Tuple THFTuple
  | TUF_THF_Conditional THFLogicFormula THFLogicFormula THFLogicFormula
  | TUF_THF_Logic_Formula_Par THFLogicFormula
  | T0UF_THF_Abstraction THFVariableList THFUnitaryFormula
    deriving (Show, Eq, Ord, Typeable, Data)

data THFQuantifiedFormula =
    TQF_THF_Quantified_Formula THFQuantifier THFVariableList THFUnitaryFormula
  | T0QF_THF_Quantified_Var Quantifier THFVariableList THFUnitaryFormula
  | T0QF_THF_Quantified_Novar THFQuantifier THFUnitaryFormula
    deriving (Show, Eq, Ord, Typeable, Data)

type THFVariableList = [THFVariable]

data THFVariable =
    TV_THF_Typed_Variable Token THFTopLevelType
  | TV_Variable Token
    deriving (Show, Eq, Ord, Typeable, Data)

data THFTypedConst =
    T0TC_Typed_Const Constant THFTopLevelType
  | T0TC_THF_TypedConst_Par THFTypedConst
    deriving (Show, Eq, Ord, Typeable, Data)

data THFTypeFormula =
    TTF_THF_Type_Formula THFTypeableFormula THFTopLevelType
  | TTF_THF_Typed_Const Constant THFTopLevelType
    deriving (Show, Eq, Ord, Typeable, Data)

data THFTypeableFormula =
    TTyF_THF_Atom THFAtom
  | TTyF_THF_Tuple THFTuple
  | TTyF_THF_Logic_Formula THFLogicFormula
    deriving (Show, Eq, Ord, Typeable, Data)

data THFSubType =
    TST_THF_Sub_Type Constant Constant
    deriving (Show, Eq, Ord, Typeable, Data)

data THFTopLevelType =
    TTLT_THF_Logic_Formula THFLogicFormula
  | T0TLT_Constant Constant
  | T0TLT_Variable Token
  | T0TLT_Defined_Type DefinedType
  | T0TLT_System_Type Token
  | T0TLT_THF_Binary_Type THFBinaryType
    deriving (Show, Eq, Ord, Typeable, Data)

data THFUnitaryType =
    TUT_THF_Unitary_Formula THFUnitaryFormula
  | T0UT_Constant Constant
  | T0UT_Variable Token
  | T0UT_Defined_Type DefinedType
  | T0UT_System_Type Token
  | T0UT_THF_Binary_Type_Par THFBinaryType
    deriving (Show, Eq, Ord, Typeable, Data)

data THFBinaryType =
    TBT_THF_Mapping_Type [THFUnitaryType]
  | TBT_THF_Xprod_Type [THFUnitaryType]
  | TBT_THF_Union_Type [THFUnitaryType]
  | T0BT_THF_Binary_Type_Par THFBinaryType
    deriving (Show, Eq, Ord, Typeable, Data)

data THFAtom =
    TA_Term Term
  | TA_THF_Conn_Term THFConnTerm
  | TA_Defined_Type DefinedType
  | TA_Defined_Plain_Formula DefinedPlainFormula
  | TA_System_Type Token
  | TA_System_Atomic_Formula SystemTerm
  | T0A_Constant Constant
  | T0A_Defined_Constant Token
  | T0A_System_Constant Token
  | T0A_Variable Token
    deriving (Show, Eq, Ord, Typeable, Data)

type THFTuple = [THFLogicFormula]

data THFSequent =
    TS_THF_Sequent THFTuple THFTuple
  | TS_THF_Sequent_Par THFSequent
    deriving (Show, Eq, Ord, Typeable, Data)

data THFConnTerm =
    TCT_THF_Pair_Connective THFPairConnective
  | TCT_Assoc_Connective AssocConnective
  | TCT_THF_Unary_Connective THFUnaryConnective
  | T0CT_THF_Quantifier THFQuantifier
    deriving (Show, Eq, Ord, Typeable, Data)

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
    deriving (Show, Eq, Ord, Typeable, Data)

data Quantifier =
    T0Q_ForAll                  -- !
  | T0Q_Exists                  -- ?
    deriving (Show, Eq, Ord, Typeable, Data)

data THFPairConnective =
    Infix_Equality          -- =
  | Infix_Inequality        -- !=
  | Equivalent              -- <=>
  | Implication             -- =>
  | IF                      -- <=
  | XOR                     -- <~>
  | NOR                     -- ~|
  | NAND                    -- ~&
    deriving (Show, Eq, Ord, Typeable, Data)

data THFUnaryConnective =
    Negation                -- ~
  | PiForAll                -- !!
  | SigmaExists             -- ??
    deriving (Show, Eq, Ord, Typeable, Data)

data AssocConnective =
    OR      -- |
  | AND     -- &
    deriving (Show, Eq, Ord, Typeable, Data)

data DefinedType =
    DT_oType | DT_o | DT_iType | DT_i
  | DT_tType | DT_real | DT_rat | DT_int
    deriving (Show, Eq, Ord, Typeable, Data)

data DefinedPlainFormula =
    DPF_Defined_Prop DefinedProp
  | DPF_Defined_Formula DefinedPred Arguments
    deriving (Show, Eq, Ord, Typeable, Data)

data DefinedProp =
    DP_True | DP_False
    deriving (Show, Eq, Ord, Typeable, Data)

data DefinedPred =
    Disrinct | Less | Lesseq | Greater
  | Greatereq
  | Is_int | Is_rat
    deriving (Show, Eq, Ord, Typeable, Data)

data Term =
    T_Function_Term FunctionTerm
  | T_Variable Token
    deriving (Show, Eq, Ord, Typeable, Data)

data FunctionTerm =
    FT_Plain_Term PlainTerm
  | FT_Defined_Term DefinedTerm
  | FT_System_Term SystemTerm
    deriving (Show, Eq, Ord, Typeable, Data)

data PlainTerm =
    PT_Plain_Term AtomicWord Arguments
  | PT_Constant Constant
    deriving (Show, Eq, Ord, Typeable, Data)

type Constant = AtomicWord

data DefinedTerm =
    DT_Defined_Atom DefinedAtom
  | DT_Defined_Atomic_Term DefinedPlainTerm
    deriving (Show, Eq, Ord, Typeable, Data)

data DefinedAtom =
    DA_Number Number
  | DA_Distinct_Object Token
    deriving (Show, Eq, Ord, Typeable, Data)

data DefinedPlainTerm =
    DPT_Defined_Function DefinedFunctor Arguments
  | DPT_Defined_Constant DefinedFunctor
    deriving (Show, Eq, Ord, Typeable, Data)

data DefinedFunctor =
    UMinus | Sum | Difference | Product |
    Quotient | Quotient_e | Quotient_t | Quotient_f |
    Remainder_e | Remainder_t | Remainder_f |
    Floor | Ceiling | Truncate | Round |
    To_int | To_rat | To_real
    deriving (Show, Eq, Ord, Typeable, Data)

data SystemTerm =
    ST_System_Term Token Arguments
  | ST_System_Constant Token
    deriving (Show, Eq, Ord, Typeable, Data)

type Arguments = [Term]

data PrincipalSymbol =
    PS_Functor AtomicWord
  | PS_Variable Token
    deriving (Show, Eq, Ord, Typeable, Data)

data Source =
    S_Dag_Source DagSource
  | S_Internal_Source IntroType OptionalInfo
  | S_External_Source ExternalSource
  | S_Sources [Source]
  | S_Unknown
    deriving (Show, Eq, Ord, Typeable, Data)

data DagSource =
    DS_Name Name
  | DS_Inference_Record AtomicWord UsefulInfo [ParentInfo]
    deriving (Show, Eq, Ord, Typeable, Data)

data ParentInfo =
    PI_Parent_Info Source (Maybe GeneralList)
    deriving (Show, Eq, Ord, Typeable, Data)

data IntroType =
   IT_definition | IT_axiom_of_choice | IT_tautology | IT_assumption
   deriving (Show, Eq, Ord, Typeable, Data)

data ExternalSource =
    ES_File_Source FileSource
  | ES_Theory TheoryName OptionalInfo
  | ES_Creator_Source AtomicWord OptionalInfo
    deriving (Show, Eq, Ord, Typeable, Data)

data FileSource =
    FS_File Token (Maybe Name)
    deriving (Show, Eq, Ord, Typeable, Data)

data TheoryName =
    Equality | Ac
    deriving (Show, Eq, Ord, Typeable, Data)

type OptionalInfo = (Maybe UsefulInfo)

type UsefulInfo = [InfoItem]

data InfoItem =
    II_Formula_Item FormulaItem
  | II_Inference_Item InferenceItem
  | II_General_Function GeneralFunction
    deriving (Show, Eq, Ord, Typeable, Data)

data FormulaItem =
    FI_Description_Item AtomicWord
  | FI_Iquote_Item AtomicWord
    deriving (Show, Eq, Ord, Typeable, Data)

data InferenceItem =
    II_Inference_Status InferenceStatus
  | II_Assumptions_Record NameList
  | II_New_Symbol_Record AtomicWord [PrincipalSymbol]
  | II_Refutation FileSource
    deriving (Show, Eq, Ord, Typeable, Data)

data InferenceStatus =
    IS_Status StatusValue
  | IS_Inference_Info AtomicWord AtomicWord GeneralList
    deriving (Show, Eq, Ord, Typeable, Data)

data StatusValue =
    Suc | Unp | Sap | Esa | Sat | Fsa | Thm | Eqv | Tac
  | Wec | Eth | Tau | Wtc | Wth | Cax | Sca | Tca | Wca
  | Cup | Csp | Ecs | Csa | Cth | Ceq | Unc | Wcc | Ect
  | Fun | Uns | Wuc | Wct | Scc | Uca | Noc
  deriving (Show, Eq, Ord, Typeable, Data)

type NameList = [Name]

data GeneralTerm =
    GT_General_Data GeneralData
  | GT_General_Data_Term GeneralData GeneralTerm
  | GT_General_List GeneralList
    deriving (Show, Eq, Ord, Typeable, Data)

data GeneralData =
    GD_Atomic_Word AtomicWord
  | GD_Variable Token
  | GD_Number Number
  | GD_Distinct_Object Token
  | GD_Formula_Data FormulaData
  | GD_Bind Token FormulaData
  | GD_General_Function GeneralFunction
    deriving (Show, Eq, Ord, Typeable, Data)

data GeneralFunction =
    GF_General_Function AtomicWord GeneralTerms
    deriving (Show, Eq, Ord, Typeable, Data)

data FormulaData =
    THF_Formula THFFormula
    deriving (Show, Eq, Ord, Typeable, Data)

type GeneralList = GeneralTerms

type GeneralTerms = [GeneralTerm]

data Name =
    N_Atomic_Word AtomicWord
  | N_Integer Token
  | T0N_Unsigned_Integer Token
    deriving (Show, Eq, Ord, Typeable, Data)

data AtomicWord =
    A_Lower_Word Token
  | A_Single_Quoted Token
    deriving (Show, Eq, Ord, Typeable, Data)

data Number =
    Num_Integer Token
  | Num_Rational Token
  | Num_Real Token
    deriving (Show, Eq, Ord, Typeable, Data)
