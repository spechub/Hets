{- |
Module      :  ./TPTP/Pretty.hs
Description :  A pretty printer for the TPTP Syntax v6.4.0.7
Copyright   :  (c) Eugen Kuksa University of Magdeburg 2017
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Eugen Kuksa <kuksa@iks.cs.ovgu.de>
Stability   :  provisional
Portability :  portable

A pretty printer for the TPTP Input Syntax v6.4.0.7 taken from
<http://www.cs.miami.edu/~tptp/TPTP/SyntaxBNF.html>
-}

module TPTP.Pretty (printBasicTheory, printNamedSentence) where

import TPTP.AS
import TPTP.Sign

import Common.AS_Annotation hiding (Name)
import Common.Id (Token)
import Common.Doc hiding (defn)
import Common.DocUtils

import Data.Char (toLower)
import qualified Data.Map as Map
import qualified Data.Set as Set

{- -----------------------------------------------------------------------------
Pretty instances
----------------------------------------------------------------------------- -}

instance Pretty Symbol where
  pretty = printSymbol

instance Pretty Sign where
  pretty = printSign

instance Pretty BASIC_SPEC where
  pretty = printBasicSpec

instance Pretty TPTP where
  pretty = printTPTP

instance Pretty TPTP_input where
  pretty = printTPTP_input

instance Pretty Comment where
  pretty = printComment

instance Pretty DefinedComment where
  pretty = printDefinedComment

instance Pretty SystemComment where
  pretty = printSystemComment

instance Pretty Annotated_formula where
  pretty = printAnnotated_formula

instance Pretty TPI_annotated where
  pretty = printTPI_annotated

instance Pretty THF_annotated where
  pretty = printTHF_annotated

instance Pretty TFX_annotated where
  pretty = printTFX_annotated

instance Pretty TFF_annotated where
  pretty = printTFF_annotated

instance Pretty TCF_annotated where
  pretty = printTCF_annotated

instance Pretty FOF_annotated where
  pretty = printFOF_annotated

instance Pretty CNF_annotated where
  pretty = printCNF_annotated

instance Pretty Annotations where
  pretty = printAnnotations

instance Pretty Formula_role where
  pretty = printFormula_role

instance Pretty THF_formula where
  pretty = printTHF_formula

instance Pretty THF_logic_formula where
  pretty = printTHF_logic_formula

instance Pretty THF_binary_formula where
  pretty = printTHF_binary_formula

instance Pretty THF_binary_pair where
  pretty = printTHF_binary_pair

instance Pretty THF_binary_tuple where
  pretty = printTHF_binary_tuple

instance Pretty THF_unitary_formula where
  pretty = printTHF_unitary_formula

instance Pretty THF_quantified_formula where
  pretty = printTHF_quantified_formula

instance Pretty THF_quantification where
  pretty = printTHF_quantification

instance Pretty THF_variable where
  pretty = printTHF_variable

instance Pretty THF_typed_variable where
  pretty = printTHF_typed_variable

instance Pretty THF_unary_formula where
  pretty = printTHF_unary_formula

instance Pretty THF_atom where
  pretty = printTHF_atom

instance Pretty THF_function where
  pretty = printTHF_function

instance Pretty THF_conn_term where
  pretty = printTHF_conn_term

instance Pretty THF_conditional where
  pretty = printTHF_conditional

instance Pretty THF_let where
  pretty = printTHF_let

instance Pretty THF_let_defns where
  pretty = printTHF_let_defns

instance Pretty THF_let_defn where
  pretty = printTHF_let_defn

instance Pretty THF_let_quantified_defn where
  pretty = printTHF_let_quantified_defn

instance Pretty THF_let_plain_defn where
  pretty = printTHF_let_plain_defn

instance Pretty THF_let_defn_LHS where
  pretty = printTHF_let_defn_LHS

instance Pretty THF_type_formula where
  pretty = printTHF_type_formula

instance Pretty THF_typeable_formula where
  pretty = printTHF_typeable_formula

instance Pretty THF_subtype where
  pretty = printTHF_subtype

instance Pretty THF_top_level_type where
  pretty = printTHF_top_level_type

instance Pretty THF_unitary_type where
  pretty = printTHF_unitary_type

instance Pretty THF_binary_type where
  pretty = printTHF_binary_type

instance Pretty THF_sequent where
  pretty = printTHF_sequent

instance Pretty THF_tuple where
  pretty = printTHF_tuple

instance Pretty TFX_formula where
  pretty = printTFX_formula

instance Pretty TFX_logic_formula where
  pretty = printTFX_logic_formula

instance Pretty TFF_formula where
  pretty = printTFF_formula

instance Pretty TFF_logic_formula where
  pretty = printTFF_logic_formula

instance Pretty TFF_binary_formula where
  pretty = printTFF_binary_formula

instance Pretty TFF_binary_nonassoc where
  pretty = printTFF_binary_nonassoc

instance Pretty TFF_binary_assoc where
  pretty = printTFF_binary_assoc

instance Pretty TFF_unitary_formula where
  pretty = printTFF_unitary_formula

instance Pretty TFF_quantified_formula where
  pretty = printTFF_quantified_formula

instance Pretty TFF_variable where
  pretty = printTFF_variable

instance Pretty TFF_typed_variable where
  pretty = printTFF_typed_variable

instance Pretty TFF_unary_formula where
  pretty = printTFF_unary_formula

instance Pretty TFF_conditional where
  pretty = printTFF_conditional

instance Pretty TFF_let where
  pretty = printTFF_let

instance Pretty TFF_let_term_defns where
  pretty = printTFF_let_term_defns

instance Pretty TFF_let_term_defn where
  pretty = printTFF_let_term_defn

instance Pretty TFF_let_term_binding where
  pretty = printTFF_let_term_binding

instance Pretty TFF_let_formula_defns where
  pretty = printTFF_let_formula_defns

instance Pretty TFF_let_formula_defn where
  pretty = printTFF_let_formula_defn

instance Pretty TFF_let_formula_binding where
  pretty = printTFF_let_formula_binding

instance Pretty TFF_sequent where
  pretty = printTFF_sequent

instance Pretty TFF_formula_tuple where
  pretty = printTFF_formula_tuple

instance Pretty TFF_typed_atom where
  pretty = printTFF_typed_atom

instance Pretty TFF_subtype where
  pretty = printTFF_subtype

instance Pretty TFF_top_level_type where
  pretty = printTFF_top_level_type

instance Pretty TF1_quantified_type where
  pretty = printTF1_quantified_type

instance Pretty TFF_monotype where
  pretty = printTFF_monotype

instance Pretty TFF_unitary_type where
  pretty = printTFF_unitary_type

instance Pretty TFF_atomic_type where
  pretty = printTFF_atomic_type

instance Pretty TFF_mapping_type where
  pretty = printTFF_mapping_type

instance Pretty TFF_xprod_type where
  pretty = printTFF_xprod_type

instance Pretty TCF_formula where
  pretty = printTCF_formula

instance Pretty TCF_logic_formula where
  pretty = printTCF_logic_formula

instance Pretty TCF_quantified_formula where
  pretty = printTCF_quantified_formula

instance Pretty FOF_formula where
  pretty = printFOF_formula

instance Pretty FOF_logic_formula where
  pretty = printFOF_logic_formula

instance Pretty FOF_binary_formula where
  pretty = printFOF_binary_formula

instance Pretty FOF_binary_nonassoc where
  pretty = printFOF_binary_nonassoc

instance Pretty FOF_binary_assoc where
  pretty = printFOF_binary_assoc

instance Pretty FOF_unitary_formula where
  pretty = printFOF_unitary_formula

instance Pretty FOF_quantified_formula where
  pretty = printFOF_quantified_formula

instance Pretty FOF_unary_formula where
  pretty = printFOF_unary_formula

instance Pretty FOF_infix_unary where
  pretty = printFOF_infix_unary

instance Pretty FOF_atomic_formula where
  pretty = printFOF_atomic_formula

instance Pretty FOF_plain_atomic_formula where
  pretty = printFOF_plain_atomic_formula

instance Pretty FOF_defined_atomic_formula where
  pretty = printFOF_defined_atomic_formula

instance Pretty FOF_defined_plain_formula where
  pretty = printFOF_defined_plain_formula

instance Pretty FOF_defined_infix_formula where
  pretty = printFOF_defined_infix_formula

instance Pretty FOF_system_atomic_formula where
  pretty = printFOF_system_atomic_formula

instance Pretty FOF_plain_term where
  pretty = printFOF_plain_term

instance Pretty FOF_defined_term where
  pretty = printFOF_defined_term

instance Pretty FOF_defined_atomic_term where
  pretty = printFOF_defined_atomic_term

instance Pretty FOF_defined_plain_term where
  pretty = printFOF_defined_plain_term

instance Pretty FOF_system_term where
  pretty = printFOF_system_term

instance Pretty FOF_term where
  pretty = printFOF_term

instance Pretty FOF_function_term where
  pretty = printFOF_function_term

instance Pretty TFF_conditional_term where
  pretty = printTFF_conditional_term

instance Pretty TFF_let_term where
  pretty = printTFF_let_term

instance Pretty FOF_sequent where
  pretty = printFOF_sequent

instance Pretty FOF_formula_tuple where
  pretty = printFOF_formula_tuple

instance Pretty CNF_formula where
  pretty = printCNF_formula

instance Pretty Disjunction where
  pretty = printDisjunction

instance Pretty Literal where
  pretty = printLiteral

instance Pretty THF_quantifier where
  pretty = printTHF_quantifier

instance Pretty TH1_quantifier where
  pretty = printTH1_quantifier

instance Pretty TH0_quantifier where
  pretty = printTH0_quantifier

instance Pretty THF_pair_connective where
  pretty = printTHF_pair_connective

instance Pretty THF_unary_connective where
  pretty = printTHF_unary_connective

instance Pretty TH1_unary_connective where
  pretty = printTH1_unary_connective

instance Pretty FOF_quantifier where
  pretty = printFOF_quantifier

instance Pretty Binary_connective where
  pretty = printBinary_connective

instance Pretty Assoc_connective where
  pretty = printAssoc_connective

instance Pretty Unary_connective where
  pretty = printUnary_connective

instance Pretty Defined_type where
  pretty = printDefined_type

instance Pretty Atom where
  pretty = printAtom

instance Pretty Untyped_atom where
  pretty = printUntyped_atom

instance Pretty Defined_proposition where
  pretty = printDefined_proposition

instance Pretty Defined_predicate where
  pretty = printDefined_predicate

instance Pretty Defined_infix_pred where
  pretty = printDefined_infix_pred

instance Pretty Defined_functor where
  pretty = printDefined_functor

instance Pretty Defined_term where
  pretty = printDefined_term

instance Pretty Source where
  pretty = printSource

instance Pretty DAG_source where
  pretty = printDAG_source

instance Pretty Inference_record where
  pretty = printInference_record

instance Pretty Parent_info where
  pretty = printParent_info

instance Pretty Internal_source where
  pretty = printInternal_source

instance Pretty Intro_type where
  pretty = printIntro_type

instance Pretty External_source where
  pretty = printExternal_source

instance Pretty File_source where
  pretty = printFile_source

instance Pretty Theory where
  pretty = printTheory

instance Pretty Theory_name where
  pretty = printTheory_name

instance Pretty Creator_source where
  pretty = printCreator_source

instance Pretty Useful_info where
  pretty = printUseful_info

instance Pretty Info_item where
  pretty = printInfo_item

instance Pretty Formula_item where
  pretty = printFormula_item

instance Pretty Inference_item where
  pretty = printInference_item

instance Pretty Inference_status where
  pretty = printInference_status

instance Pretty Status_value where
  pretty = printStatus_value

instance Pretty Inference_info where
  pretty = printInference_info

instance Pretty New_symbol_record where
  pretty = printNew_symbol_record

instance Pretty Principal_symbol where
  pretty = printPrincipal_symbol

instance Pretty Include where
  pretty = printInclude

instance Pretty General_term where
  pretty = printGeneral_term

instance Pretty General_data where
  pretty = printGeneral_data

instance Pretty General_function where
  pretty = printGeneral_function

instance Pretty Formula_data where
  pretty = printFormula_data

instance Pretty Name where
  pretty = printName

instance Pretty Number where
  pretty = printNumber

{- -----------------------------------------------------------------------------
Logic components
----------------------------------------------------------------------------- -}

-- Print a newline at the end of the document for good style.
printBasicTheory :: (Sign, [Named Sentence]) -> Doc
printBasicTheory (_, l) = vsep (map printNamedSentence l) $+$ text ""

printNamedSentence :: Named Sentence -> Doc
printNamedSentence = printAnnotated_formula . sentence

printSymbol :: Symbol -> Doc
printSymbol = pretty . symbolId

printSign :: Sign -> Doc
printSign s =
  vsep [ text "%{"
       , if Set.null $ constantSet s then empty else
         text "constants: "
           <+> sepByCommas (map pretty $ Set.toList $ constantSet s)
       , if Set.null $ numberSet s then empty else
         text "numbers: "
           <+> sepByCommas (map pretty $ Set.toList $ numberSet s)
       , if Set.null $ propositionSet s then empty else
         text "propositions: "
           <+> sepByCommas (map pretty $ Set.toList $ propositionSet s)
       , if Map.null (tffPredicateMap s) && Map.null (thfPredicateMap s) && Map.null (fofPredicateMap s) then empty else
         text "predicates: "
           <+> vcat (punctuate comma
             (map printTHFType (Map.toList $ thfPredicateMap s)
             ++ map printTFFType (Map.toList $ tffPredicateMap s)
             ++ map printFOFPredicate (Map.toList $ fofPredicateMap s)))
       , if Map.null (fofFunctorMap s) then empty else
         text "functors: "
           <+> vcat (punctuate comma
             (map printFOFFunctor (Map.toList $ fofFunctorMap s)))
       , if Map.null (tffTypeConstantMap s) && Map.null (thfTypeConstantMap s) then empty else
         text "type constants: "
           <+> vcat (punctuate comma
             (map printTHFType (Map.toList $ thfTypeConstantMap s)
             ++ map printTFFType (Map.toList $ tffTypeConstantMap s)))
       , if Map.null (tffTypeFunctorMap s) && Map.null (thfTypeFunctorMap s) then empty else
         text "type functors: "
           <+> vcat (punctuate comma
             (map printTHFType (Map.toList $ thfTypeFunctorMap s)
             ++ map printTFFType (Map.toList $ tffTypeFunctorMap s)))
       , if Map.null (tffSubtypeMap s) && Map.null (thfSubtypeMap s) then empty else
         text "subtypes: "
           <+> vcat (punctuate comma
             (map printTHFSubType (Map.toList $ thfSubtypeMap s)
             ++ map printTFFSubType (Map.toList $ tffSubtypeMap s)))
       , text "}%"]

  where
    printTHFType :: (THFTypeable, THF_top_level_type) -> Doc
    printTHFType (t, tlt) = pretty $ case t of
      THFTypeFormula f -> THFTF_typeable f tlt
      THFTypeConstant c -> THFTF_constant c tlt

    printTFFType :: (Untyped_atom, TFF_top_level_type) -> Doc
    printTFFType (a, tlt) = pretty $ TFFTA_plain a tlt

    printFOFPredicate :: (Predicate, Set.Set Int) -> Doc
    printFOFPredicate (p, arities) = vcat $ punctuate comma $
      map (printFOFPredicateOrFunctor p O) $ Set.toList arities

    printFOFFunctor :: (TPTP_functor, Set.Set Int) -> Doc
    printFOFFunctor (p, arities) = vcat $ punctuate comma $
      map (printFOFPredicateOrFunctor p I) $ Set.toList arities

    printFOFPredicateOrFunctor :: Token -> Defined_type -> Int -> Doc
    printFOFPredicateOrFunctor token typ arity =
      let arguments =
            if arity == 0
            then empty
            else if arity == 1
            then pretty I <+> text ">"
            else parens (sepBy (text "*") $ map pretty $ replicate arity I)
                   <+> text ">"
      in  pretty token <> colon <+> arguments <+> pretty typ

    printTHFSubType :: (THF_atom, THF_atom) -> Doc
    printTHFSubType (a1, a2) = pretty $ THF_subtype a1 a2

    printTFFSubType :: (Untyped_atom, Atom) -> Doc
    printTFFSubType (a1, a2) = pretty $ TFF_subtype a1 a2

printBasicSpec :: BASIC_SPEC -> Doc
printBasicSpec (Basic_spec xs) = vcat $ map pretty xs

{- -----------------------------------------------------------------------------
Files. Empty file is OK
----------------------------------------------------------------------------- -}

-- <TPTP_file>            ::= <TPTP_input>*
printTPTP :: TPTP -> Doc
printTPTP (TPTP tptp_inputs) = vsep $ map pretty tptp_inputs

-- <TPTP_input>           ::= <annotated_formula> | <include>
printTPTP_input :: TPTP_input -> Doc
printTPTP_input x = case x of
  Annotated_formula a -> pretty a
  TPTP_include i -> pretty i
  TPTP_comment c -> pretty c
  TPTP_defined_comment c -> pretty c
  TPTP_system_comment c -> pretty c

{- -----------------------------------------------------------------------------
Comments
----------------------------------------------------------------------------- -}

-- <comment>              ::- <comment_line>|<comment_block>
-- <comment_line>         ::- [%]<printable_char>*
-- <comment_block>        ::: [/][*]<not_star_slash>[*][*]*[/]
printComment :: Comment -> Doc
printComment comment = case comment of
  Comment_line c -> text "%" <+> pretty c
  Comment_block c -> text "/*" <+> pretty c <+> text "*/"

-- %----  <defined_comment>    ::- <def_comment_line>|<def_comment_block>
-- %----  <def_comment_line>   ::: [%]<dollar><printable_char>*
-- %----  <def_comment_block>  ::: [/][*]<dollar><not_star_slash>[*][*]*[/]
printDefinedComment :: DefinedComment -> Doc
printDefinedComment comment = case comment of
  Defined_comment_line c -> text "%$" <+> pretty c
  Defined_comment_block  c -> text "/*$" <+> pretty c <+> text "*/"

-- %----  <system_comment>     ::- <sys_comment_line>|<sys_comment_block>
-- %----  <sys_comment_line>   ::: [%]<dollar><dollar><printable_char>*
-- %----  <sys_comment_block>  ::: [/][*]<dollar><dollar><not_star_slash>[*][*]*[/]
printSystemComment :: SystemComment -> Doc
printSystemComment comment = case comment of
  System_comment_line c -> text "%$$" <+> pretty c
  System_comment_block c -> text "/*$$" <+> pretty c <+> text "*/"


-- %----Formula records
-- <annotated_formula>    ::= <thf_annotated> | <tfx_annotated> | <tff_annotated> |
--                            <tcf_annotated> | <fof_annotated> | <cnf_annotated> |
--                            <tpi_annotated>
printAnnotated_formula :: Annotated_formula -> Doc
printAnnotated_formula x = case x of
  AF_THF_Annotated f -> pretty f
  AF_TFX_Annotated f -> pretty f
  AF_TFF_Annotated f -> pretty f
  AF_TCF_Annotated f -> pretty f
  AF_FOF_Annotated f -> pretty f
  AF_CNF_Annotated f -> pretty f
  AF_TPI_Annotated f -> pretty f

-- <???_annotated> contains the annotations, which are introduced with a comma.
-- <annotations>          ::= ,<source><optional_info> | <null>
printAnnotationsIfAnnotated :: Annotations -> Doc
printAnnotationsIfAnnotated a@(Annotations ma) = case ma of
  Just _ -> comma <+> pretty a
  Nothing -> empty

-- <tpi_annotated>        ::= tpi(<name>,<formula_role>,<tpi_formula><annotations>).
printTPI_annotated :: TPI_annotated -> Doc
printTPI_annotated x = case x of
  TPI_annotated n r f a ->
    text "tpi"
    <> parens (sepByCommas [pretty n, pretty r, pretty f] <> printAnnotationsIfAnnotated a)
    <> text "."

-- <tpi_formula>          ::= <fof_formula>

-- <thf_annotated>        ::= thf(<name>,<formula_role>,<thf_formula>
--                            <annotations>).
printTHF_annotated :: THF_annotated -> Doc
printTHF_annotated x = case x of
  THF_annotated n r f a ->
    text "thf"
    <> parens (sepByCommas [pretty n, pretty r, pretty f] <> printAnnotationsIfAnnotated a)
    <> text "."

-- <tfx_annotated>        ::= tfx(<name>,<formula_role>,<tfx_formula>
--                            <annotations>).
printTFX_annotated :: TFX_annotated -> Doc
printTFX_annotated x = case x of
  TFX_annotated n r f a ->
    text "tfx"
    <> parens (sepByCommas [pretty n, pretty r, pretty f] <> printAnnotationsIfAnnotated a)
    <> text "."

-- <tff_annotated>        ::= tff(<name>,<formula_role>,<tff_formula>
--                            <annotations>).
printTFF_annotated :: TFF_annotated -> Doc
printTFF_annotated x = case x of
  TFF_annotated n r f a ->
    text "tff"
    <> parens (sepByCommas [pretty n, pretty r, pretty f] <> printAnnotationsIfAnnotated a)
    <> text "."

-- <tcf_annotated>        ::= tcf(<name>,<formula_role>,<tcf_formula>
--                            <annotations>).
printTCF_annotated :: TCF_annotated -> Doc
printTCF_annotated x = case x of
  TCF_annotated n r f a ->
    text "tcf"
    <> parens (sepByCommas [pretty n, pretty r, pretty f] <> printAnnotationsIfAnnotated a)
    <> text "."

-- <fof_annotated>        ::= fof(<name>,<formula_role>,<fof_formula>
--                            <annotations>).
printFOF_annotated :: FOF_annotated -> Doc
printFOF_annotated x = case x of
  FOF_annotated n r f a ->
    text "fof"
    <> parens (sepByCommas [pretty n, pretty r, pretty f] <> printAnnotationsIfAnnotated a)
    <> text "."

-- <cnf_annotated>        ::= cnf(<name>,<formula_role>,<cnf_formula>
--                            <annotations>).
printCNF_annotated :: CNF_annotated -> Doc
printCNF_annotated x = case x of
  CNF_annotated n r f a ->
    text "cnf"
    <> parens (sepByCommas [pretty n, pretty r, pretty f]
               <> printAnnotationsIfAnnotated a)
    <> text "."

-- <annotations>          ::= ,<source><optional_info> | <null>
printAnnotations :: Annotations -> Doc
printAnnotations (Annotations mAnno) = case mAnno of
  Nothing -> empty
  Just (source, optionalInfo) ->
    fsep [pretty source, printOptional_info optionalInfo]

-- Types for problems

-- %----Types for problems.
-- <formula_role>         ::= <lower_word>
-- <formula_role>         :== axiom | hypothesis | definition | assumption |
--                            lemma | theorem | corollary | conjecture |
--                            negated_conjecture | plain | type |
--                            fi_domain | fi_functors | fi_predicates | unknown
printFormula_role :: Formula_role -> Doc
printFormula_role x = case x of
  Other_formula_role t -> pretty t
  -- ^ For future updates. Should not be used.
  _ -> text $ map toLower $ show x

-- %----THF formulae.
-- <thf_formula>          ::= <thf_logic_formula> | <thf_sequent>
printTHF_formula :: THF_formula -> Doc
printTHF_formula x = case x of
  THFF_logic f -> pretty f
  THFF_sequent s -> pretty s

-- <thf_logic_formula>    ::= <thf_binary_formula> | <thf_unitary_formula> |
--                            <thf_type_formula> | <thf_subtype>
printTHF_logic_formula :: THF_logic_formula -> Doc
printTHF_logic_formula x = case x of
  THFLF_binary f -> pretty f
  THFLF_unitary f -> pretty f
  THFLF_type f -> pretty f
  THFLF_subtype f -> pretty f

-- <thf_binary_formula>   ::= <thf_binary_pair> | <thf_binary_tuple>
printTHF_binary_formula :: THF_binary_formula -> Doc
printTHF_binary_formula x = case x of
  THFBF_pair a -> pretty a
  THFBF_tuple a -> pretty a

-- %----Only some binary connectives can be written without ()s.
-- %----There's no precedence among binary connectives
-- <thf_binary_pair>      ::= <thf_unitary_formula> <thf_pair_connective>
--                            <thf_unitary_formula>
printTHF_binary_pair :: THF_binary_pair -> Doc
printTHF_binary_pair x = case x of
  THF_binary_pair c f1 f2 -> fsep [pretty f1, pretty c, pretty f2]

-- <thf_binary_tuple>     ::= <thf_or_formula> | <thf_and_formula> |
--                            <thf_apply_formula>
printTHF_binary_tuple :: THF_binary_tuple -> Doc
printTHF_binary_tuple x = case x of
  THFBT_or fs -> printTHF_or_formula fs
  THFBT_and fs -> printTHF_and_formula fs
  THFBT_apply fs -> printTHF_apply_formula fs

-- <thf_or_formula>       ::= <thf_unitary_formula> <vline> <thf_unitary_formula> |
--                            <thf_or_formula> <vline> <thf_unitary_formula>
printTHF_or_formula :: THF_or_formula -> Doc
printTHF_or_formula fs = sepBy vline $ map pretty fs

-- <thf_and_formula>      ::= <thf_unitary_formula> & <thf_unitary_formula> |
--                            <thf_and_formula> & <thf_unitary_formula>
printTHF_and_formula :: THF_or_formula -> Doc
printTHF_and_formula fs = sepBy andD $ map pretty fs

-- <thf_apply_formula>    ::= <thf_unitary_formula> @ <thf_unitary_formula> |
--                            <thf_apply_formula> @ <thf_unitary_formula>
printTHF_apply_formula :: THF_or_formula -> Doc
printTHF_apply_formula fs = sepBy atD $ map pretty fs

-- <thf_unitary_formula>  ::= <thf_quantified_formula> | <thf_unary_formula> |
--                            <thf_atom> | <thf_conditional> | <thf_let> |
--                            <thf_tuple> | (<thf_logic_formula>)
printTHF_unitary_formula :: THF_unitary_formula -> Doc
printTHF_unitary_formula x = case x of
  THFUF_quantified a -> pretty a
  THFUF_unary a -> pretty a
  THFUF_atom a -> pretty a
  THFUF_conditional a -> pretty a
  THFUF_let a -> pretty a
  THFUF_tuple a -> pretty a
  THFUF_logic a -> parens $ pretty a

-- <thf_quantified_formula> ::= <thf_quantification> <thf_unitary_formula>
printTHF_quantified_formula :: THF_quantified_formula -> Doc
printTHF_quantified_formula x = case x of
  THF_quantified_formula q f -> hsep [pretty q, pretty f]

-- <thf_quantification>   ::= <thf_quantifier> [<thf_variable_list>] :
printTHF_quantification :: THF_quantification -> Doc
printTHF_quantification x = case x of
  THF_quantification q vars ->
    hsep [pretty q, brackets (printTHF_variable_list vars) <> colon]

-- <thf_variable_list>    ::= <thf_variable> | <thf_variable>,<thf_variable_list>
printTHF_variable_list :: THF_variable_list -> Doc
printTHF_variable_list vars = sepByCommas $ map pretty vars

-- <thf_variable>         ::= <thf_typed_variable> | <variable>
printTHF_variable :: THF_variable -> Doc
printTHF_variable x = case x of
  THFV_typed a -> pretty a
  THFV_variable a -> pretty a

-- <thf_typed_variable>   ::= <variable> : <thf_top_level_type>
printTHF_typed_variable :: THF_typed_variable -> Doc
printTHF_typed_variable x = case x of
  THF_typed_variable v tlt -> fsep [pretty v <> colon, pretty tlt]

-- <thf_unary_formula>    ::= <thf_unary_connective> (<thf_logic_formula>)
printTHF_unary_formula :: THF_unary_formula -> Doc
printTHF_unary_formula x = case x of
  THF_unary_formula c f -> pretty c <> parens (pretty f)

-- <thf_atom>             ::= <thf_function> | <variable> | <defined_term> |
--                            <thf_conn_term>
printTHF_atom :: THF_atom -> Doc
printTHF_atom x = case x of
  THF_atom_function a -> pretty a
  THF_atom_variable a -> pretty a
  THF_atom_defined a -> pretty a
  THF_atom_conn a -> pretty a

-- <thf_function>         ::= <atom> | <functor>(<thf_arguments>) |
--                            <defined_functor>(<thf_arguments>) |
--                            <system_functor>(<thf_arguments>)
printTHF_function :: THF_function -> Doc
printTHF_function x = case x of
  THFF_atom a -> pretty a
  THFF_functor f args -> pretty f <> parens (printTHF_arguments args)
  THFF_defined f args -> pretty f <> parens (printTHF_arguments args)
  THFF_system f args -> pretty f <> parens (printTHF_arguments args)

-- <thf_conn_term>        ::= <thf_pair_connective> | <assoc_connective> |
--                            <thf_unary_connective>
printTHF_conn_term :: THF_conn_term -> Doc
printTHF_conn_term x = case x of
  THFC_pair a -> pretty a
  THFC_assoc a -> pretty a
  THFC_unary a -> pretty a

-- <thf_conditional>      ::= $ite(<thf_logic_formula>,<thf_logic_formula>,
--                             <thf_logic_formula>)
printTHF_conditional :: THF_conditional -> Doc
printTHF_conditional x = case x of
  THF_conditional f_if f_then f_else ->
    text "$ite"
    <> parens (sepByCommas [pretty f_if, pretty f_then, pretty f_else])

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
printTHF_let :: THF_let -> Doc
printTHF_let x = case x of
  THF_let defns f ->
    text "$let" <> parens (sepByCommas [pretty defns, pretty f])

-- <thf_let_defns>        :== <thf_let_defn> | [<thf_let_defn_list>]
printTHF_let_defns :: THF_let_defns -> Doc
printTHF_let_defns x = case x of
  THFLD_single a -> pretty a
  THFLD_many a -> brackets $ printTHF_let_defn_list a

-- <thf_let_defn_list>    :== <thf_let_defn> | <thf_let_defn>,<thf_let_defn_list>
printTHF_let_defn_list :: THF_let_defn_list -> Doc
printTHF_let_defn_list = sepByCommas . map pretty

-- <thf_let_defn>         :== <thf_let_quantified_defn> | <thf_let_plain_defn>
printTHF_let_defn :: THF_let_defn -> Doc
printTHF_let_defn x = case x of
  THFLD_quantified a -> pretty a
  THFLD_plain a -> pretty a

-- <thf_let_quantified_defn> :== <thf_quantification> (<thf_let_plain_defn>)
printTHF_let_quantified_defn :: THF_let_quantified_defn -> Doc
printTHF_let_quantified_defn x = case x of
  THF_let_quantified_defn q lpd ->
    pretty q <> parens (pretty lpd)

-- <thf_let_plain_defn>   :== <thf_let_defn_LHS> <assignment> <thf_formula>
printTHF_let_plain_defn :: THF_let_plain_defn -> Doc
printTHF_let_plain_defn x = case x of
  THF_let_plain_defn lhs f -> fsep [pretty lhs, assignment, pretty f]

-- <thf_let_defn_LHS>     :== <constant> | <functor>(<fof_arguments>) |
--                            <thf_tuple>
-- %----The <fof_arguments> must all be <variable>s, and the <thf_tuple> may
-- %----contain only <constant>s and <functor>(<fof_arguments>)s
printTHF_let_defn_LHS :: THF_let_defn_LHS -> Doc
printTHF_let_defn_LHS x = case x of
  THFLDL_constant a -> pretty a
  THFLDL_functor f args -> pretty f <> parens (printFOF_arguments args)
  THFLDL_tuple a -> pretty a

-- <thf_arguments>        ::= <thf_formula_list>
printTHF_arguments :: THF_arguments -> Doc
printTHF_arguments x = printTHF_formula_list x

-- <thf_type_formula>     ::= <thf_typeable_formula> : <thf_top_level_type>
-- <thf_type_formula>     :== <constant> : <thf_top_level_type>
printTHF_type_formula :: THF_type_formula -> Doc
printTHF_type_formula x = case x of
  THFTF_typeable f tlt -> fsep [pretty f <> colon, pretty tlt]
  THFTF_constant c tlt -> fsep [pretty c <> colon, pretty tlt]

-- <thf_typeable_formula> ::= <thf_atom> | (<thf_logic_formula>)
printTHF_typeable_formula :: THF_typeable_formula -> Doc
printTHF_typeable_formula x = case x of
  THFTF_atom a -> pretty a
  THFTF_logic a -> parens $ pretty a

-- <thf_subtype>          ::= <thf_atom> <subtype_sign> <thf_atom>
printTHF_subtype :: THF_subtype -> Doc
printTHF_subtype x = case x of
  THF_subtype a1 a2 -> fsep [pretty a1, subtype_sign, pretty a2]


-- %----<thf_top_level_type> appears after ":", where a type is being specified
-- %----for a term or variable. <thf_unitary_type> includes <thf_unitary_formula>,
-- %----so the syntax allows just about any lambda expression with "enough"
-- %----parentheses to serve as a type. The expected use of this flexibility is
-- %----parametric polymorphism in types, expressed with lambda abstraction.
-- %----Mapping is right-associative: o > o > o means o > (o > o).
-- %----Xproduct is left-associative: o * o * o means (o * o) * o.
-- %----Union is left-associative: o + o + o means (o + o) + o.
-- <thf_top_level_type>   ::= <thf_unitary_type> | <thf_mapping_type>
printTHF_top_level_type :: THF_top_level_type -> Doc
printTHF_top_level_type x = case x of
  THFTLT_unitary a -> pretty a
  THFTLT_mapping a -> printTHF_mapping_type a

-- <thf_unitary_type>     ::= <thf_unitary_formula> | (<thf_binary_type>)
printTHF_unitary_type :: THF_unitary_type -> Doc
printTHF_unitary_type x = case x of
  THFUT_unitary a -> pretty a
  THFUT_binary a -> parens $ pretty a

-- Each of these binary types has at least two (!) list entries.
-- <thf_binary_type>      ::= <thf_mapping_type> | <thf_xprod_type> |
--                            <thf_union_type>
printTHF_binary_type :: THF_binary_type -> Doc
printTHF_binary_type x = case x of
  THFBT_mapping a -> printTHF_mapping_type a
  THFBT_xprod a -> printTHF_xprod_type a
  THFBT_union a -> printTHF_union_type a

-- <thf_mapping_type>     ::= <thf_unitary_type> <arrow> <thf_unitary_type> |
--                            <thf_unitary_type> <arrow> <thf_mapping_type>
printTHF_mapping_type :: THF_mapping_type -> Doc
printTHF_mapping_type = sepBy arrow . map pretty

-- <thf_xprod_type>       ::= <thf_unitary_type> <star> <thf_unitary_type> |
--                            <thf_xprod_type> <star> <thf_unitary_type>
printTHF_xprod_type :: THF_xprod_type -> Doc
printTHF_xprod_type = sepBy star . map pretty

-- <thf_union_type>       ::= <thf_unitary_type> <plus> <thf_unitary_type> |
--                            <thf_union_type> <plus> <thf_unitary_type>
printTHF_union_type :: THF_union_type -> Doc
printTHF_union_type = sepBy plus . map pretty

-- %----Sequents using the Gentzen arrow
-- <thf_sequent>          ::= <thf_tuple> <gentzen_arrow> <thf_tuple> |
--                            (<thf_sequent>)
printTHF_sequent :: THF_sequent -> Doc
printTHF_sequent x = case x of
  THFS_plain t1 t2 -> sepBy gentzen_arrow [pretty t1, pretty t2]
  THFS_parens a -> parens $ pretty a

-- <thf_tuple>            ::= [] | [<thf_formula_list>]
printTHF_tuple :: THF_tuple -> Doc
printTHF_tuple x = case x of
  THF_tuple a -> brackets $ printTHF_formula_list a

-- <thf_formula_list>     ::= <thf_logic_formula> |
--                            <thf_logic_formula>,<thf_formula_list>
printTHF_formula_list :: THF_formula_list -> Doc
printTHF_formula_list = sepByCommas . map pretty

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
printTFX_formula :: TFX_formula -> Doc
printTFX_formula x = case x of
  TFXF_logic a -> pretty a
  TFXF_sequent a -> pretty a

-- <tfx_logic_formula>    ::= <thf_logic_formula>
-- % <tfx_logic_formula>    ::= <thf_binary_formula> | <thf_unitary_formula> |
-- %                            <tff_typed_atom> | <tff_subtype>
printTFX_logic_formula :: TFX_logic_formula -> Doc
printTFX_logic_formula x = case x of
  TFXLF_binary a -> pretty a
  TFXLF_unitary a -> pretty a
  TFXLF_typed a -> pretty a
  TFXLF_subtype a -> pretty a

-- %----TFF formulae.
-- <tff_formula>          ::= <tff_logic_formula> | <tff_typed_atom> |
--                            <tff_sequent>
printTFF_formula :: TFF_formula -> Doc
printTFF_formula x = case x of
  TFFF_logic a -> pretty a
  TFFF_atom a -> pretty a
  TFFF_sequent a -> pretty a

-- <tff_logic_formula>    ::= <tff_binary_formula> | <tff_unitary_formula> |
--                            <tff_subtype>
printTFF_logic_formula :: TFF_logic_formula -> Doc
printTFF_logic_formula x = case x of
  TFFLF_binary a -> pretty a
  TFFLF_unitary a -> pretty a
  TFFLF_subtype a -> pretty a

-- <tff_binary_formula>   ::= <tff_binary_nonassoc> | <tff_binary_assoc>
printTFF_binary_formula :: TFF_binary_formula -> Doc
printTFF_binary_formula x = case x of
  TFFBF_nonassoc a -> pretty a
  TFFBF_assoc a -> pretty a

-- <tff_binary_nonassoc>  ::= <tff_unitary_formula> <binary_connective>
--                            <tff_unitary_formula>
printTFF_binary_nonassoc :: TFF_binary_nonassoc -> Doc
printTFF_binary_nonassoc x = case x of
  TFF_binary_nonassoc c f1 f2 -> fsep [pretty f1, pretty c, pretty f2]

-- <tff_binary_assoc>     ::= <tff_or_formula> | <tff_and_formula>
printTFF_binary_assoc :: TFF_binary_assoc -> Doc
printTFF_binary_assoc x = case x of
  TFFBA_or a -> printTFF_or_formula a
  TFFBA_and a -> printTFF_and_formula a

-- <tff_or_formula>       ::= <tff_unitary_formula> <vline> <tff_unitary_formula> |
--                            <tff_or_formula> <vline> <tff_unitary_formula>
printTFF_or_formula :: TFF_or_formula -> Doc
printTFF_or_formula = sepBy vline . map pretty

-- <tff_and_formula>      ::= <tff_unitary_formula> & <tff_unitary_formula> |
--                            <tff_and_formula> & <tff_unitary_formula>
printTFF_and_formula :: TFF_and_formula -> Doc
printTFF_and_formula = sepBy andD . map pretty

-- <tff_unitary_formula>  ::= <tff_quantified_formula> | <tff_unary_formula> |
--                            <tff_atomic_formula> | <tff_conditional> |
--                            <tff_let> | (<tff_logic_formula>)
printTFF_unitary_formula :: TFF_unitary_formula -> Doc
printTFF_unitary_formula x = case x of
  TFFUF_quantified a -> pretty a
  TFFUF_unary a -> pretty a
  TFFUF_atomic a -> pretty a
  TFFUF_conditional a -> pretty a
  TFFUF_let a -> pretty a
  TFFUF_logic a -> parens $ pretty a

-- <tff_quantified_formula> ::= <fof_quantifier> [<tff_variable_list>] :
--                            <tff_unitary_formula>
printTFF_quantified_formula :: TFF_quantified_formula -> Doc
printTFF_quantified_formula x = case x of
  TFF_quantified_formula q vars f ->
    hsep [pretty q, brackets (printTFF_variable_list vars) <> colon, pretty f]

-- <tff_variable_list>    ::= <tff_variable> | <tff_variable>,<tff_variable_list>
printTFF_variable_list :: TFF_variable_list -> Doc
printTFF_variable_list = sepByCommas . map pretty

-- <tff_variable>         ::= <tff_typed_variable> | <variable>
printTFF_variable :: TFF_variable -> Doc
printTFF_variable x = case x of
  TFFV_typed a -> pretty a
  TFFV_variable a -> pretty a

-- <tff_typed_variable>   ::= <variable> : <tff_atomic_type>
printTFF_typed_variable :: TFF_typed_variable -> Doc
printTFF_typed_variable x = case x of
  TFF_typed_variable v t -> fsep [pretty v <> colon, pretty t]

-- <tff_unary_formula>    ::= <unary_connective> <tff_unitary_formula> |
--                            <fof_infix_unary>
printTFF_unary_formula :: TFF_unary_formula -> Doc
printTFF_unary_formula x = case x of
  TFFUF_connective c f -> fsep [pretty c, pretty f]
  TFFUF_infix a -> pretty a

-- <tff_atomic_formula>   ::= <fof_atomic_formula>
-- already has a pretty instance (FOF_atomic_formula)

-- <tff_conditional>      ::= $ite_f(<tff_logic_formula>,<tff_logic_formula>,
--                            <tff_logic_formula>)
printTFF_conditional :: TFF_conditional -> Doc
printTFF_conditional x = case x of
  TFF_conditional f_if f_then f_else ->
    text "$ite_f"
    <> parens (sepByCommas [pretty f_if, pretty f_then, pretty f_else])

-- <tff_let>              ::= $let_tf(<tff_let_term_defns>,<tff_formula>) |
--                            $let_ff(<tff_let_formula_defns>,<tff_formula>)
printTFF_let :: TFF_let -> Doc
printTFF_let x = case x of
  TFF_let_term_defns defns f ->
    text "$let_tf"
    <> parens (sepByCommas [pretty defns, pretty f])
  TFF_let_formula_defns defns f ->
    text "$let_ff"
    <> parens (sepByCommas [pretty defns, pretty f])

-- %----See the commentary for <thf_let>.
-- <tff_let_term_defns>   ::= <tff_let_term_defn> | [<tff_let_term_list>]
printTFF_let_term_defns :: TFF_let_term_defns -> Doc
printTFF_let_term_defns x = case x of
  TFFLTD_single a -> pretty a
  TFFLTD_many a -> brackets $ printTFF_let_term_list a

-- <tff_let_term_list>    ::= <tff_let_term_defn> |
--                            <tff_let_term_defn>,<tff_let_term_list>
printTFF_let_term_list :: TFF_let_term_list -> Doc
printTFF_let_term_list = sepByCommas . map pretty

-- <tff_let_term_defn>    ::= ! [<tff_variable_list>] : <tff_let_term_defn> |
--                            <tff_let_term_binding>
printTFF_let_term_defn :: TFF_let_term_defn -> Doc
printTFF_let_term_defn x = case x of
  TFFLTD_variable vars defn ->
    fsep [ text "!"
         , brackets (printTFF_variable_list vars) <> colon
         , pretty defn
         ]
  TFFLTD_binding a -> pretty a

-- <tff_let_term_binding> ::= <fof_plain_term> = <fof_term> |
--                            (<tff_let_term_binding>)
printTFF_let_term_binding :: TFF_let_term_binding -> Doc
printTFF_let_term_binding x = case x of
  TFFLTB_plain pt t -> fsep [pretty pt, text "=" ,pretty t]
  TFFLTB_binding a -> parens $ pretty a

-- <tff_let_formula_defns> ::= <tff_let_formula_defn> | [<tff_let_formula_list>]
printTFF_let_formula_defns :: TFF_let_formula_defns -> Doc
printTFF_let_formula_defns x = case x of
  TFFLFD_single a -> pretty a
  TFFLFD_many a -> brackets $ printTFF_let_formula_list a

-- <tff_let_formula_list> ::= <tff_let_formula_defn> |
--                            <tff_let_formula_defn>,<tff_let_formula_list>
printTFF_let_formula_list :: TFF_let_formula_list -> Doc
printTFF_let_formula_list = sepByCommas . map pretty

-- <tff_let_formula_defn> ::= ! [<tff_variable_list>] : <tff_let_formula_defn> |
--                            <tff_let_formula_binding>
printTFF_let_formula_defn :: TFF_let_formula_defn -> Doc
printTFF_let_formula_defn x = case x of
  TFFLFD_variable vars defn ->
    fsep [ text "!"
         , brackets (printTFF_variable_list vars) <> colon
         , pretty defn
         ]
  TFFLFD_binding a -> pretty a

-- <tff_let_formula_binding> ::= <fof_plain_atomic_formula> <=>
--                            <tff_unitary_formula> | (<tff_let_formula_binding>)
printTFF_let_formula_binding :: TFF_let_formula_binding -> Doc
printTFF_let_formula_binding x = case x of
  TFFLFB_plain paf uf -> fsep [pretty paf, pretty uf]
  TFFLFB_binding a -> parens $ pretty a

-- <tff_sequent>          ::= <tff_formula_tuple> <gentzen_arrow>
--                            <tff_formula_tuple> | (<tff_sequent>)
printTFF_sequent :: TFF_sequent -> Doc
printTFF_sequent x = case x of
  TFFS_plain t1 t2 -> sepBy gentzen_arrow [pretty t1, pretty t2]
  TFFS_parens a -> parens $ pretty a

-- <tff_formula_tuple>    ::= [] | [<tff_formula_tuple_list>]
printTFF_formula_tuple :: TFF_formula_tuple -> Doc
printTFF_formula_tuple x = case x of
  TFF_formula_tuple a -> brackets $ printTFF_formula_tuple_list a

-- <tff_formula_tuple_list> ::= <tff_logic_formula> |
--                            <tff_logic_formula>,<tff_formula_tuple_list>
printTFF_formula_tuple_list :: TFF_formula_tuple_list -> Doc
printTFF_formula_tuple_list = sepByCommas . map pretty

-- %----<tff_typed_atom> can appear only at top level
-- <tff_typed_atom>       ::= <untyped_atom> : <tff_top_level_type> |
--                            (<tff_typed_atom>)
printTFF_typed_atom :: TFF_typed_atom -> Doc
printTFF_typed_atom x = case x of
  TFFTA_plain ua tlt -> fsep [pretty ua <> colon, pretty tlt]
  TFFTA_parens a -> parens $ pretty a

-- <tff_subtype>          ::= <untyped_atom> <subtype_sign> <atom>
printTFF_subtype :: TFF_subtype -> Doc
printTFF_subtype x = case x of
  TFF_subtype ua a -> fsep [pretty ua, subtype_sign, pretty a]

-- %----See <thf_top_level_type> for commentary.
-- <tff_top_level_type>   ::= <tff_atomic_type> | <tff_mapping_type> |
--                            <tf1_quantified_type> | (<tff_top_level_type>)
printTFF_top_level_type :: TFF_top_level_type -> Doc
printTFF_top_level_type x = case x of
  TFFTLT_atomic a -> pretty a
  TFFTLT_mapping a -> pretty a
  TFFTLT_quantified a -> pretty a
  TFFTLT_parens a -> parens $ pretty a

-- <tf1_quantified_type>  ::= !> [<tff_variable_list>] : <tff_monotype>
printTF1_quantified_type :: TF1_quantified_type -> Doc
printTF1_quantified_type x = case x of
  TF1_quantified_type vars t ->
    fsep [ text "!>"
         , brackets (printTFF_variable_list vars) <> colon
         , pretty t
         ]

-- <tff_monotype>         ::= <tff_atomic_type> | (<tff_mapping_type>)
printTFF_monotype :: TFF_monotype -> Doc
printTFF_monotype x = case x of
  TFFMT_atomic a -> pretty a
  TFFMT_mapping a -> parens $ pretty a

-- <tff_unitary_type>     ::= <tff_atomic_type> | (<tff_xprod_type>)
printTFF_unitary_type :: TFF_unitary_type -> Doc
printTFF_unitary_type x = case x of
  TFFUT_atomic a -> pretty a
  TFFUT_xprod a -> parens $ pretty a

-- <tff_atomic_type>      ::= <type_constant> | <defined_type> |
--                            <type_functor>(<tff_type_arguments>) | <variable>
printTFF_atomic_type :: TFF_atomic_type -> Doc
printTFF_atomic_type x = case x of
  TFFAT_constant a -> pretty a
  TFFAT_defined a -> pretty a
  TFFAT_functor f args -> pretty f <> parens (printTFF_type_arguments args)
  TFFAT_variable a -> pretty a

-- <tff_type_arguments>   ::= <tff_atomic_type> |
--                            <tff_atomic_type>,<tff_type_arguments>
printTFF_type_arguments :: TFF_type_arguments -> Doc
printTFF_type_arguments = sepByCommas . map pretty

-- %----For consistency with <thf_unitary_type> (the analogue in thf),
-- %----<tff_atomic_type> should also allow (<tff_atomic_type>), but that causes
-- %----ambiguity.
-- <tff_mapping_type>     ::= <tff_unitary_type> <arrow> <tff_atomic_type>
printTFF_mapping_type :: TFF_mapping_type -> Doc
printTFF_mapping_type x = case x of
  TFF_mapping_type ut at -> fsep [pretty ut, arrow, pretty at]

-- <tff_xprod_type>       ::= <tff_unitary_type> <star> <tff_atomic_type> |
--                            <tff_xprod_type> <star> <tff_atomic_type>
printTFF_xprod_type :: TFF_xprod_type -> Doc
printTFF_xprod_type x = case x of
  TFF_xprod_type ut ats -> sepBy star $ pretty ut : map pretty ats


-- %----TCF formulae.
-- <tcf_formula>          ::= <tcf_logic_formula> | <tff_typed_atom>
printTCF_formula :: TCF_formula -> Doc
printTCF_formula x = case x of
  TCFF_logic a -> pretty a
  TCFF_atom a -> pretty a

-- <tcf_logic_formula>    ::= <tcf_quantified_formula> | <cnf_formula>
printTCF_logic_formula :: TCF_logic_formula -> Doc
printTCF_logic_formula x = case x of
  TCFLF_quantified a -> pretty a
  TCFLF_cnf a -> pretty a

-- <tcf_quantified_formula> ::= ! [<tff_variable_list>] : <cnf_formula>
printTCF_quantified_formula :: TCF_quantified_formula -> Doc
printTCF_quantified_formula x = case x of
  TCF_quantified vars f ->
    fsep [ text "!"
         , brackets (printTFF_variable_list vars) <> colon
         , pretty f
         ]


-- %----FOF formulae.
-- <fof_formula>          ::= <fof_logic_formula> | <fof_sequent>
printFOF_formula :: FOF_formula -> Doc
printFOF_formula x = case x of
  FOFF_logic a -> pretty a
  FOFF_sequent a -> pretty a

-- <fof_logic_formula>    ::= <fof_binary_formula> | <fof_unitary_formula>
printFOF_logic_formula :: FOF_logic_formula -> Doc
printFOF_logic_formula x = case x of
  FOFLF_binary a -> pretty a
  FOFLF_unitary a -> pretty a

-- %----Future answer variable ideas | <answer_formula>
-- <fof_binary_formula>   ::= <fof_binary_nonassoc> | <fof_binary_assoc>
printFOF_binary_formula :: FOF_binary_formula -> Doc
printFOF_binary_formula x = case x of
  FOFBF_nonassoc a -> pretty a
  FOFBF_assoc a -> pretty a

-- %----Only some binary connectives are associative
-- %----There's no precedence among binary connectives
-- <fof_binary_nonassoc>  ::= <fof_unitary_formula> <binary_connective>
--                            <fof_unitary_formula>
printFOF_binary_nonassoc :: FOF_binary_nonassoc -> Doc
printFOF_binary_nonassoc x = case x of
  FOF_binary_nonassoc c f1 f2 ->
    fsep [pretty f1, pretty c, pretty f2]

-- %----Associative connectives & and | are in <binary_assoc>
-- <fof_binary_assoc>     ::= <fof_or_formula> | <fof_and_formula>
printFOF_binary_assoc :: FOF_binary_assoc -> Doc
printFOF_binary_assoc x = case x of
  FOFBA_or a -> printFOF_or_formula a
  FOFBA_and a -> printFOF_and_formula a

-- <fof_or_formula>       ::= <fof_unitary_formula> <vline> <fof_unitary_formula> |
--                            <fof_or_formula> <vline> <fof_unitary_formula>
printFOF_or_formula :: FOF_or_formula -> Doc
printFOF_or_formula = sepBy vline . map pretty

-- <fof_and_formula>      ::= <fof_unitary_formula> & <fof_unitary_formula> |
--                            <fof_and_formula> & <fof_unitary_formula>
printFOF_and_formula :: FOF_and_formula -> Doc
printFOF_and_formula = sepBy andD . map pretty

-- %----<fof_unitary_formula> are in ()s or do not have a <binary_connective> at
-- %----the top level.
-- <fof_unitary_formula>  ::= <fof_quantified_formula> | <fof_unary_formula> |
--                            <fof_atomic_formula> | (<fof_logic_formula>)
printFOF_unitary_formula :: FOF_unitary_formula -> Doc
printFOF_unitary_formula x = case x of
  FOFUF_quantified a -> pretty a
  FOFUF_unary a -> pretty a
  FOFUF_atomic a -> pretty a
  FOFUF_logic a -> parens $ pretty a

-- <fof_quantified_formula> ::= <fof_quantifier> [<fof_variable_list>] :
--                            <fof_unitary_formula>
printFOF_quantified_formula :: FOF_quantified_formula -> Doc
printFOF_quantified_formula x = case x of
  FOF_quantified_formula q vars f ->
    fsep [ pretty q
         , brackets (printFOF_variable_list vars) <> colon
         , pretty f
         ]

-- <fof_variable_list>    ::= <variable> | <variable>,<fof_variable_list>
printFOF_variable_list :: FOF_variable_list -> Doc
printFOF_variable_list = sepByCommas . map pretty

-- <fof_unary_formula>    ::= <unary_connective> <fof_unitary_formula> |
--                            <fof_infix_unary>
printFOF_unary_formula :: FOF_unary_formula -> Doc
printFOF_unary_formula x = case x of
  FOFUF_connective c f -> fsep [pretty c, pretty f]
  FOFUF_infix a -> pretty a

-- <fof_infix_unary>      ::= <fof_term> <infix_inequality> <fof_term>
printFOF_infix_unary :: FOF_infix_unary -> Doc
printFOF_infix_unary x = case x of
  FOF_infix_unary t1 t2 -> fsep [pretty t1, infix_inequality, pretty t2]

-- <fof_atomic_formula>   ::= <fof_plain_atomic_formula> |
--                            <fof_defined_atomic_formula> |
--                            <fof_system_atomic_formula>
printFOF_atomic_formula :: FOF_atomic_formula -> Doc
printFOF_atomic_formula x = case x of
  FOFAT_plain a -> pretty a
  FOFAT_defined a -> pretty a
  FOFAT_system a -> pretty a

-- <fof_plain_atomic_formula> ::= <fof_plain_term>
-- <fof_plain_atomic_formula> :== <proposition> | <predicate>(<fof_arguments>)
printFOF_plain_atomic_formula :: FOF_plain_atomic_formula -> Doc
printFOF_plain_atomic_formula x = case x of
  FOFPAF_proposition a -> pretty a
  FOFPAF_predicate p args -> pretty p <> parens (printFOF_arguments args)

-- <fof_defined_atomic_formula> ::= <fof_defined_plain_formula> |
--                            <fof_defined_infix_formula>
printFOF_defined_atomic_formula :: FOF_defined_atomic_formula -> Doc
printFOF_defined_atomic_formula x = case x of
  FOFDAF_plain a -> pretty a
  FOFDAF_infix a -> pretty a

-- <fof_defined_plain_formula> ::= <fof_defined_plain_term>
-- <fof_defined_plain_formula> :== <defined_proposition> |
--                            <defined_predicate>(<fof_arguments>)
printFOF_defined_plain_formula :: FOF_defined_plain_formula -> Doc
printFOF_defined_plain_formula x = case x of
  FOFDPF_proposition a -> pretty a
  FOFDPF_predicate p args -> pretty p <> parens (printFOF_arguments args)

-- <fof_defined_infix_formula> ::= <fof_term> <defined_infix_pred> <fof_term>
printFOF_defined_infix_formula :: FOF_defined_infix_formula -> Doc
printFOF_defined_infix_formula x = case x of
  FOF_defined_infix_formula dip t1 t2 -> fsep [pretty t1, pretty dip, pretty t2]

-- %----System terms have system specific interpretations
-- <fof_system_atomic_formula> ::= <fof_system_term>
-- %----<fof_system_atomic_formula>s are used for evaluable predicates that are
-- %----available in particular tools. The predicate names are not controlled
-- %----by the TPTP syntax, so use with due care. The same is true for
-- %----<fof_system_term>s.
printFOF_system_atomic_formula :: FOF_system_atomic_formula -> Doc
printFOF_system_atomic_formula x = case x of
  FOF_system_atomic_formula a -> pretty a

-- %----FOF terms.
-- <fof_plain_term>       ::= <constant> | <functor>(<fof_arguments>)
printFOF_plain_term :: FOF_plain_term -> Doc
printFOF_plain_term x = case x of
  FOFPT_constant a -> pretty a
  FOFPT_functor f args -> pretty f <> parens (printFOF_arguments args)

-- %----Defined terms have TPTP specific interpretations
-- <fof_defined_term>     ::= <defined_term> | <fof_defined_atomic_term>
printFOF_defined_term :: FOF_defined_term -> Doc
printFOF_defined_term x = case x of
  FOFDT_term a -> pretty a
  FOFDT_atomic a -> pretty a

-- <fof_defined_atomic_term>  ::= <fof_defined_plain_term>
-- %----None yet             | <defined_infix_term>
printFOF_defined_atomic_term :: FOF_defined_atomic_term -> Doc
printFOF_defined_atomic_term x = case x of
  FOFDAT_plain a -> pretty a
  -- | FOFDAT_indix a -> pretty a

-- %----None yet <defined_infix_term> ::= <fof_term> <defined_infix_func> <fof_term>
-- data Defined_infix_term = Defined_infix_term Defined_infix_func FOF_term FOF_term
--                           deriving (Show, Ord, Eq, Data, Typeable)

-- %----None yet <defined_infix_func> ::=
-- data Defined_infix_func =

-- <fof_defined_plain_term>   ::= <defined_constant> |
--                            <defined_functor>(<fof_arguments>)
-- %----Add $tuple for tuples, because [<fof_arguments>] doesn't work.
printFOF_defined_plain_term :: FOF_defined_plain_term -> Doc
printFOF_defined_plain_term x = case x of
  FOFDPT_constant a -> pretty a
  FOFDPT_functor f args -> pretty f <> parens (printFOF_arguments args)

-- %----System terms have system specific interpretations
-- <fof_system_term>      ::= <system_constant> | <system_functor>(<fof_arguments>)
printFOF_system_term :: FOF_system_term -> Doc
printFOF_system_term x = case x of
  FOFST_constant a -> pretty a
  FOFST_functor f args -> pretty f <> parens (printFOF_arguments args)

-- %----Arguments recurse back up to terms (this is the FOF world here)
-- <fof_arguments>        ::= <fof_term> | <fof_term>,<fof_arguments>
printFOF_arguments :: FOF_arguments -> Doc
printFOF_arguments = sepByCommas . map pretty

-- %----These are terms used as arguments. Not the entry point for terms because
-- %----<fof_plain_term> is also used as <fof_plain_atomic_formula>
-- <fof_term>             ::= <fof_function_term> | <variable> |
--                            <tff_conditional_term> | <tff_let_term>
printFOF_term :: FOF_term -> Doc
printFOF_term x = case x of
  FOFT_function a -> pretty a
  FOFT_variable a -> pretty a
  FOFT_conditional a -> pretty a
  FOFT_let a -> pretty a

-- %% DAMN THIS JUST WON'T WORK | <tuple_term>
-- %----<tuple_term> is for TFF only, but it's here because it's used in
-- %----<fof_atomic_formula>, which is also used as <tff_atomic_formula>.
-- % <tuple_term>           ::= [] | [<fof_arguments>]
-- <fof_function_term>    ::= <fof_plain_term> | <fof_defined_term> |
--                            <fof_system_term>
printFOF_function_term :: FOF_function_term -> Doc
printFOF_function_term x = case x of
  FOFFT_plain a -> pretty a
  FOFFT_defined a -> pretty a
  FOFFT_system a -> pretty a

-- %----Conditional terms should be used by only TFF.
-- <tff_conditional_term> ::= $ite_t(<tff_logic_formula>,<fof_term>,<fof_term>)
printTFF_conditional_term :: TFF_conditional_term -> Doc
printTFF_conditional_term x = case x of
  TFF_conditional_term f_if t_then t_else ->
    text "$ite_t"
    <> parens (sepByCommas [pretty f_if, pretty t_then, pretty t_else])

-- %----Let terms should be used by only TFF. $let_ft is for use when there is
-- %----a $ite_t in the <fof_term>. See the commentary for $let_tf and $let_ff.
-- <tff_let_term>         ::= $let_ft(<tff_let_formula_defns>,<fof_term>) |
--                            $let_tt(<tff_let_term_defns>,<fof_term>)
printTFF_let_term :: TFF_let_term -> Doc
printTFF_let_term x = case x of
  TFFLT_formula defns t ->
    text "$let_ft" <> parens (sepByCommas [pretty defns, pretty t])
  TFFLT_term defns t ->
    text "$let_tt" <> parens (sepByCommas [pretty defns, pretty t])

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
printFOF_sequent :: FOF_sequent -> Doc
printFOF_sequent x = case x of
  FOFS_plain t1 t2 -> fsep [pretty t1, gentzen_arrow, pretty t2]
  FOFS_parens a -> parens $ pretty a

-- <fof_formula_tuple>    ::= [] | [<fof_formula_tuple_list>]
printFOF_formula_tuple :: FOF_formula_tuple -> Doc
printFOF_formula_tuple x = case x of
  FOF_formula_tuple a -> brackets $ printFOF_formula_tuple_list a

-- <fof_formula_tuple_list> ::= <fof_logic_formula> |
--                            <fof_logic_formula>,<fof_formula_tuple_list>
printFOF_formula_tuple_list :: FOF_formula_tuple_list -> Doc
printFOF_formula_tuple_list = sepByCommas . map pretty


-- %----CNF formulae (variables implicitly universally quantified)
-- <cnf_formula>          ::= <disjunction> | (<disjunction>)
printCNF_formula :: CNF_formula -> Doc
printCNF_formula x = case x of
  CNFF_plain a -> pretty a
  CNFF_parens a -> parens $ pretty a

-- <disjunction>          ::= <literal> | <disjunction> <vline> <literal>
printDisjunction :: Disjunction -> Doc
printDisjunction x = case x of
  Disjunction ls -> sepBy vline $ map pretty ls

-- <literal>              ::= <fof_atomic_formula> | ~ <fof_atomic_formula> |
--                            <fof_infix_unary>
printLiteral :: Literal -> Doc
printLiteral x = case x of
  Lit_atomic a -> pretty a
  Lit_negative a -> text "~" <+> pretty a
  Lit_fof_infix a -> pretty a



-- %----Connectives - THF
-- <thf_quantifier>       ::= <fof_quantifier> | <th0_quantifier> |
--                            <th1_quantifier>
printTHF_quantifier :: THF_quantifier -> Doc
printTHF_quantifier x = case x of
  THFQ_fof a -> pretty a
  THFQ_th0 a -> pretty a
  THFQ_th1 a -> pretty a


-- %----TH0 quantifiers are also available in TH1
-- <th1_quantifier>       ::= !> | ?*
printTH1_quantifier :: TH1_quantifier -> Doc
printTH1_quantifier x = case x of
  TH1_DependentProduct -> text "!>"
  TH1_DependentSum -> text "?*"

-- <th0_quantifier>       ::= ^ | @+ | @-
printTH0_quantifier :: TH0_quantifier -> Doc
printTH0_quantifier x = case x of
  TH0_LambdaBinder -> text "^"
  TH0_IndefiniteDescription -> text "@+"
  TH0_DefiniteDescription -> text "@-"

-- <thf_pair_connective>  ::= <infix_equality> | <infix_inequality> |
--                            <binary_connective> | <assignment>
printTHF_pair_connective :: THF_pair_connective -> Doc
printTHF_pair_connective x = case x of
  THF_infix_equality -> infix_equality
  Infix_inequality -> infix_inequality
  THFPC_binary a -> pretty a
  THF_assignment -> assignment

-- <thf_unary_connective> ::= <unary_connective> | <th1_unary_connective>
printTHF_unary_connective :: THF_unary_connective -> Doc
printTHF_unary_connective x = case x of
  THFUC_unary a -> pretty a
  THFUC_th1 a -> pretty a

-- <th1_unary_connective> ::= !! | ?? | @@+ | @@- | @=
printTH1_unary_connective :: TH1_unary_connective -> Doc
printTH1_unary_connective x = case x of
  TH1_PiForAll -> text "!!"
  TH1_PiSigmaExists -> text "??"
  TH1_PiIndefiniteDescription -> text "@@+"
  TH1_PiDefiniteDescription -> text "@@-"
  TH1_PiEquality -> text "@="


-- %----Connectives - TFF
-- % <tff_pair_connective>  ::= <binary_connective> | <assignment>
-- Note: not used
-- data TFF_pair_connective = TFFPC_binary Binary_connective
--                          | TFFPC_assignment TFF_assignment
--                            deriving (Show, Ord, Eq, Data, Typeable)

-- <subtype_sign>         ::= <less_sign><less_sign>
subtype_sign :: Doc
subtype_sign = less_sign <> less_sign

-- %----Connectives - FOF
-- <fof_quantifier>       ::= ! | ?
printFOF_quantifier :: FOF_quantifier -> Doc
printFOF_quantifier x = case x of
  ForAll -> text "!"
  Exists -> text "?"

-- <binary_connective>    ::= <=> | => | <= | <~> | ~<vline> | ~&
printBinary_connective :: Binary_connective -> Doc
printBinary_connective x = case x of
  Equivalence -> text "<=>"
  Implication -> text "=>"
  ReverseImplication -> text "<="
  XOR -> text "<~>"
  NOR -> text "~|"
  NAND -> text "~&"

-- <assoc_connective>     ::= <vline> | &
printAssoc_connective :: Assoc_connective -> Doc
printAssoc_connective x = case x of
  OR -> text "|"
  AND -> text "&"

-- <unary_connective>     ::= ~
printUnary_connective :: Unary_connective -> Doc
printUnary_connective x = case x of
  NOT -> text "~"


-- %----Types for THF and TFF
-- <type_constant>        ::= <type_functor>
-- already has a pretty instance (Token)

-- <type_functor>         ::= <atomic_word>
-- already has a pretty instance (Token)

-- <defined_type>         ::= <atomic_defined_word>
-- <defined_type>         :== $oType | $o | $iType | $i | $tType |
--                            $real | $rat | $int
printDefined_type :: Defined_type -> Doc
printDefined_type x = case x of
  OType -> text "$oType"
  O -> text "$o"
  IType -> text "$iType"
  I -> text "$i"
  TType -> text "$tType"
  Real -> text "$real"
  Rat -> text "$rat"
  Int -> text "$int"

-- <system_type>          :== <atomic_system_word>
-- Note: not used
-- type System_type = Token

-- %----For all language types
-- <atom>                 ::= <untyped_atom> | <defined_constant>
printAtom :: Atom -> Doc
printAtom x = case x of
  Atom_untyped a -> pretty a
  Atom_constant a -> pretty a

-- <untyped_atom>         ::= <constant> | <system_constant>
printUntyped_atom :: Untyped_atom -> Doc
printUntyped_atom x = case x of
  UA_constant a -> pretty a
  UA_system a -> pretty a

-- Proposition
-- already has a pretty instance (Token)

-- Predicate
-- already has a pretty instance (Token)

-- <defined_proposition>  :== <atomic_defined_word>
-- <defined_proposition>  :== $true | $false
printDefined_proposition :: Defined_proposition -> Doc
printDefined_proposition x = case x of
  TPTP_true -> text "$true"
  TPTP_false -> text "$false"

-- <defined_predicate>    :== <atomic_defined_word>
-- <defined_predicate>    :== $distinct |
--                            $less | $lesseq | $greater | $greatereq |
--                            $is_int | $is_rat |
--                            $box_P | $box_i | $box_int | $box |
--                            $dia_P | $dia_i | $dia_int | $dia
-- %----$distinct means that each of it's constant arguments are pairwise !=. It
-- %----is part of the TFF syntax. It can be used only as a fact, not under any
-- %----connective.
printDefined_predicate :: Defined_predicate -> Doc
printDefined_predicate x = case x of
  Distinct -> text "$distinct"
  Less -> text "$less"
  Lesseq -> text "$lesseq"
  Greater -> text "$greater"
  Greatereq -> text "$greatereq"
  Is_int -> text "$is_int"
  Is_rat -> text "$is_rat"
  Box_P -> text "$box_P"
  Box_i -> text "$box_i"
  Box_int -> text "$box_int"
  Box -> text "$box"
  Dia_P -> text "$dia_P"
  Dia_i -> text "$dia_i"
  Dia_int -> text "$dia_int"
  Dia -> text "$dia"

-- <defined_infix_pred>   ::= <infix_equality> | <assignment>
-- <infix_equality>       ::= =
-- <infix_inequality>     ::= !=
printDefined_infix_pred :: Defined_infix_pred -> Doc
printDefined_infix_pred x = case x of
  Defined_infix_equality -> infix_equality
  Defined_assignment -> assignment

-- <constant>             ::= <functor>
-- already has a pretty instance (Token)

-- <functor>              ::= <atomic_word>
-- already has a pretty instance (Token)

-- <system_constant>      ::= <system_functor>
-- already has a pretty instance (Token)

-- <system_functor>       ::= <atomic_system_word>
-- already has a pretty instance (Token)

-- <defined_constant>     ::= <defined_functor>
-- already has a pretty instance (Token)

-- <defined_functor>      ::= <atomic_defined_word>
-- <defined_functor>      :== $uminus | $sum | $difference | $product |
--                            $quotient | $quotient_e | $quotient_t | $quotient_f |
--                            $remainder_e | $remainder_t | $remainder_f |
--                            $floor | $ceiling | $truncate | $round |
--                            $to_int | $to_rat | $to_real
printDefined_functor :: Defined_functor -> Doc
printDefined_functor x = case x of
  Uminus -> text "$uminus"
  Sum -> text "$sum"
  Difference -> text "$difference"
  Product -> text "$product"
  Quotient -> text "$quotient"
  Quotient_e -> text "$quotient_e"
  Quotient_t -> text "$quotient_t"
  Quotient_f -> text "$quotient_f"
  Remainder_e -> text "$remainder_e"
  Remainder_t -> text "$remainder_t"
  Remainder_f -> text "$remainder_f"
  Floor -> text "$floor"
  Ceiling -> text "$ceiling"
  Truncate -> text "$truncate"
  Round -> text "$round"
  To_int -> text "$to_int"
  To_rat -> text "$to_rat"
  To_real -> text "$to_real"
  DF_atomic_defined_word a -> pretty a

-- <defined_term>         ::= <number> | <distinct_object>
printDefined_term :: Defined_term -> Doc
printDefined_term x = case x of
  DT_number a -> pretty a
  DT_object a -> pretty a

-- <variable>             ::= <upper_word>
-- already has a pretty instance (Token)

-- %----Formula sources
-- <source>               ::= <general_term>
-- <source>               :== <dag_source> | <internal_source> |
--                            <external_source> | unknown | [<sources>]
printSource :: Source -> Doc
printSource x = case x of
  Source_DAG a -> pretty a
  Source_internal a -> pretty a
  Source_external a -> pretty a
  Unknown_source -> text "unknown"
  Source_many a -> brackets $ printSources a

-- %----Alternative sources are recorded like this, thus allowing representation
-- %----of alternative derivations with shared parts.
-- <sources>              :== <source> | <source>,<sources>
printSources :: Sources -> Doc
printSources = sepByCommas . map pretty

-- %----Only a <dag_source> can be a <name>, i.e., derived formulae can be
-- %----identified by a <name> or an <inference_record>
-- <dag_source>           :== <name> | <inference_record>
printDAG_source :: DAG_source -> Doc
printDAG_source x = case x of
  DAGS_name a -> pretty a
  DAGS_record a -> pretty a

-- <inference_record>     :== inference(<inference_rule>,<useful_info>,
--                            <inference_parents>)
printInference_record :: Inference_record -> Doc
printInference_record x = case x of
  Inference_record ir ui ip ->
    text "inference"
    <> parens (sepByCommas [pretty ir, pretty ui, printInference_parents ip])

-- <inference_rule>       :== <atomic_word>
-- %----Examples are          deduction | modus_tollens | modus_ponens | rewrite |
-- %                          resolution | paramodulation | factorization |
-- %                          cnf_conversion | cnf_refutation | ...
printInference_rule :: Inference_rule -> Doc
printInference_rule = pretty

-- %----<inference_parents> can be empty in cases when there is a justification
-- %----for a tautologous theorem. In case when a tautology is introduced as
-- %----a leaf, e.g., for splitting, then use an <internal_source>.
-- <inference_parents>    :== [] | [<parent_list>]
printInference_parents :: Inference_parents -> Doc
printInference_parents = brackets . printParent_list

-- <parent_list>          :== <parent_info> | <parent_info>,<parent_list>
printParent_list :: Parent_list -> Doc
printParent_list = sepByCommas . map pretty

-- <parent_info>          :== <source><parent_details>
printParent_info :: Parent_info -> Doc
printParent_info x = case x of
  Parent_info s d -> fsep [pretty s, printParent_details d]

-- <parent_details>       :== :<general_list> | <null>
printParent_details :: Parent_details -> Doc
printParent_details x = case x of
  Just gl -> printGeneral_list gl
  Nothing -> empty

-- <internal_source>      :== introduced(<intro_type><optional_info>)
printInternal_source :: Internal_source -> Doc
printInternal_source x = case x of
  Internal_source it oi ->
    text "introduced" <> parens (fsep [pretty it, pretty oi])

-- <intro_type>           :== definition | axiom_of_choice | tautology | assumption
-- %----This should be used to record the symbol being defined, or the function
-- %----for the axiom of choice
printIntro_type :: Intro_type -> Doc
printIntro_type x = case x of
  IntroTypeDefinition -> text "definition"
  AxiomOfChoice -> text "axiom_of_choice"
  Tautology -> text "tautology"
  IntroTypeAssumption -> text "assumption"

-- <external_source>      :== <file_source> | <theory> | <creator_source>
printExternal_source :: External_source -> Doc
printExternal_source x = case x of
  ExtSrc_file a -> pretty a
  ExtSrc_theory a -> pretty a
  ExtSrc_creator a -> pretty a

-- <file_source>          :== file(<file_name><file_info>)
printFile_source :: File_source -> Doc
printFile_source x = case x of
  File_source fn fi ->
    text "file" <> parens (fsep [text "'" <> pretty fn <> text "'",
                                 printFile_info fi])

-- <file_info>            :== ,<name> | <null>
printFile_info :: File_info -> Doc
printFile_info x = case x of
  Just n -> fsep [comma, text "'" <> pretty n <> text "'"]
  Nothing -> empty

-- <theory>               :== theory(<theory_name><optional_info>)
printTheory :: Theory -> Doc
printTheory x = case x of
  Theory tn oi -> text "theory" <> parens (fsep [pretty tn, pretty oi])

-- <theory_name>          :== equality | ac
printTheory_name :: Theory_name -> Doc
printTheory_name x = case x of
  TN_equality -> text "equality"
  TN_ac -> text "ac"

-- %----More theory names may be added in the future. The <optional_info> is
-- %----used to store, e.g., which axioms of equality have been implicitly used,
-- %----e.g., theory(equality,[rst]). Standard format still to be decided.
-- <creator_source>       :== creator(<creator_name><optional_info>)
printCreator_source :: Creator_source -> Doc
printCreator_source x = case x of
  Creator_source cn oi ->
    text "creator" <> parens (fsep [printCreator_name cn, pretty oi])

-- <creator_name>         :== <atomic_word>
printCreator_name :: Creator_name -> Doc
printCreator_name = pretty


-- %----Useful info fields
-- <optional_info>        ::= ,<useful_info> | <null>
printOptional_info :: Optional_info -> Doc
printOptional_info x = case x of
  Just ui -> comma <+> pretty ui
  Nothing -> empty

-- <useful_info>          ::= <general_list>
-- <useful_info>          :== [] | [<info_items>]
printUseful_info :: Useful_info -> Doc
printUseful_info x = case x of
  UI_items a -> brackets $ printInfo_items a
  UI_general_list a -> pretty a

-- <info_items>           :== <info_item> | <info_item>,<info_items>
printInfo_items :: Info_items -> Doc
printInfo_items = sepByCommas . map pretty

-- <info_item>            :== <formula_item> | <inference_item> |
--                            <general_function>
printInfo_item :: Info_item -> Doc
printInfo_item x = case x of
  Info_formula a -> pretty a
  Info_inference a -> pretty a
  Info_general a -> pretty a

-- %----Useful info for formula records
-- <formula_item>         :== <description_item> | <iquote_item>
printFormula_item :: Formula_item -> Doc
printFormula_item x = case x of
  FI_description a -> printDescription_item a
  FI_iquote a -> printIquote_item a

-- <description_item>     :== description(<atomic_word>)
printDescription_item :: Description_item -> Doc
printDescription_item a = text "description" <> parens (pretty a)

-- <iquote_item>          :== iquote(<atomic_word>)
-- %----<iquote_item>s are used for recording exactly what the system output about
-- %----the inference step. In the future it is planned to encode this information
-- %----in standardized forms as <parent_details> in each <inference_record>.
-- %----Useful info for inference records
printIquote_item :: Iquote_item -> Doc
printIquote_item a = text "iquote" <> parens (pretty a)

-- <inference_item>       :== <inference_status> | <assumptions_record> |
--                            <new_symbol_record> | <refutation>
printInference_item :: Inference_item -> Doc
printInference_item x = case x of
  Inf_status a -> pretty a
  Inf_assumption a -> printAssumptions_record a
  Inf_symbol a -> pretty a
  Inf_refutation a -> printRefutation a

-- <inference_status>     :== status(<status_value>) | <inference_info>
printInference_status :: Inference_status -> Doc
printInference_status x = case x of
  Inf_value a -> text "status" <> parens (pretty a)
  Inf_info a -> pretty a

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
printStatus_value :: Status_value -> Doc
printStatus_value x = case x of
  SUC -> text "suc"
  UNP -> text "unp"
  SAP -> text "sap"
  ESA -> text "esa"
  SAT -> text "sat"
  FSA -> text "fsa"
  THM -> text "thm"
  EQV -> text "eqv"
  TAC -> text "tac"
  WEC -> text "wec"
  ETH -> text "eth"
  TAU -> text "tau"
  WTC -> text "wtc"
  WTH -> text "wth"
  CAX -> text "cax"
  SCA -> text "sca"
  TCA -> text "tca"
  WCA -> text "wca"
  CUP -> text "cup"
  CSP -> text "csp"
  ECS -> text "ecs"
  CSA -> text "csa"
  CTH -> text "cth"
  CEQ -> text "ceq"
  UNC -> text "unc"
  WCC -> text "wcc"
  ECT -> text "ect"
  FUN -> text "fun"
  UNS -> text "uns"
  WUC -> text "wuc"
  WCT -> text "wct"
  SCC -> text "scc"
  UCA -> text "uca"
  NOC -> text "noc"

-- %----<inference_info> is used to record standard information associated with an
-- %----arbitrary inference rule. The <inference_rule> is the same as the
-- %----<inference_rule> of the <inference_record>. The <atomic_word> indicates
-- %----the information being recorded in the <general_list>. The <atomic_word>
-- %----are (loosely) set by TPTP conventions, and include esplit, sr_split, and
-- %----discharge.
-- <inference_info>       :== <inference_rule>(<atomic_word>,<general_list>)
printInference_info :: Inference_info -> Doc
printInference_info x = case x of
  Inference_info ir aw gl ->
    printInference_rule ir
    <> parens (sepByCommas [pretty aw, printGeneral_list gl])

-- %----An <assumptions_record> lists the names of assumptions upon which this
-- %----inferred formula depends. These must be discharged in a completed proof.
-- <assumptions_record>   :== assumptions([<name_list>])
printAssumptions_record :: Assumptions_record -> Doc
printAssumptions_record x =
  text "assumptions" <> parens (brackets $ printName_list x)

-- %----A <refutation> record names a file in which the inference recorded here
-- %----is recorded as a proof by refutation.
-- <refutation>           :== refutation(<file_source>)
printRefutation :: Refutation -> Doc
printRefutation a = text "refutation" <> parens (printFile_source a)

-- %----A <new_symbol_record> provides information about a newly introduced symbol.
-- <new_symbol_record>    :== new_symbols(<atomic_word>,[<new_symbol_list>])
printNew_symbol_record :: New_symbol_record -> Doc
printNew_symbol_record x = case x of
  New_symbol_record aw nsl ->
    text "new_symbols"
    <> parens (sepByCommas [pretty aw, brackets $ printNew_symbol_list nsl])

-- <new_symbol_list>      :== <principal_symbol> |
--                            <principal_symbol>,<new_symbol_list>
printNew_symbol_list :: New_symbol_list -> Doc
printNew_symbol_list = sepByCommas . map pretty

-- %----Principal symbols are predicates, functions, variables
-- <principal_symbol>   :== <functor> | <variable>
printPrincipal_symbol :: Principal_symbol -> Doc
printPrincipal_symbol x = case x of
  PS_functor a -> pretty a
  PS_variable a -> pretty a

-- %----Include directives
-- <include>              ::= include(<file_name><formula_selection>).
printInclude :: Include -> Doc
printInclude x = case x of
  Include fn fs ->
    text "include" <> parens (fsep [pretty fn, printFormula_selection fs])

-- <formula_selection>    ::= ,[<name_list>] | <null>
printFormula_selection :: Formula_selection -> Doc
printFormula_selection x = case x of
  Just ns -> fsep [comma, brackets $ printName_list ns]
  Nothing -> empty

-- <name_list>            ::= <name> | <name>,<name_list>
printName_list :: Name_list -> Doc
printName_list = sepByCommas . map pretty


-- %----Non-logical data
-- <general_term>         ::= <general_data> | <general_data>:<general_term> |
--                            <general_list>
printGeneral_term :: General_term -> Doc
printGeneral_term x = case x of
  GT_data a -> pretty a
  GT_DataTerm gd gt -> fsep [pretty gd <> colon, pretty gt]
  GT_list a -> printGeneral_list a

-- <general_data>         ::= <atomic_word> | <general_function> |
--                            <variable> | <number> | <distinct_object> |
--                            <formula_data>
printGeneral_data :: General_data -> Doc
printGeneral_data x = case x of
  GD_atomic_word a -> pretty a
  GD_general_function a -> pretty a
  GD_variable a -> pretty a
  GD_number a -> pretty a
  GD_distinct_object a -> pretty a
  GD_formula_data a -> pretty a
-- %----A <general_data> bind() term is used to record a variable binding in an
-- %----inference, as an element of the <parent_details> list.
-- <general_data>         :== bind(<variable>,<formula_data>)
  GD_bind v fd -> text "bind" <> parens (sepByCommas [pretty v, pretty fd])

-- <general_function>     ::= <atomic_word>(<general_terms>)
printGeneral_function :: General_function -> Doc
printGeneral_function x = case x of
  General_function aw gt -> pretty aw <> parens (printGeneral_terms gt)

-- <formula_data>         ::= $thf(<thf_formula>) | $tff(<tff_formula>) |
--                            $fof(<fof_formula>) | $cnf(<cnf_formula>) |
--                            $fot(<fof_term>)
-- only used in inference
printFormula_data :: Formula_data -> Doc
printFormula_data x = case x of
  FD_THF a -> pretty a
  FD_TFF a -> pretty a
  FD_FOF a -> pretty a
  FD_CNF a -> pretty a
  FD_FOT a -> pretty a

-- <general_list>         ::= [] | [<general_terms>]
printGeneral_list :: General_list -> Doc
printGeneral_list = brackets . pretty

-- <general_terms>        ::= <general_term> | <general_term>,<general_terms>
printGeneral_terms :: General_terms -> Doc
printGeneral_terms = sepByCommas . map pretty


-- %----General purpose
-- <name>                 ::= <atomic_word> | <integer>
-- %----Integer names are expected to be unsigned
printName :: Name -> Doc
printName x = case x of
  NameString a -> pretty a
  NameInteger a -> pretty a

-- <atomic_word>          ::= <lower_word> | <single_quoted>
-- already has a pretty instance (Token)

-- <atomic_defined_word>  ::= <dollar_word>
-- already has a pretty instance (Token)

-- <atomic_system_word>   ::= <dollar_dollar_word>
-- already has a pretty instance (Token)

-- <number>               ::= <integer> | <rational> | <real>
printNumber :: Number -> Doc
printNumber x = case x of
  NumInteger a -> text $ show a
  NumRational a -> text $ show a
  NumReal a -> text $ show a


-- <distinct_object>      ::- <double_quote><do_char>*<double_quote>
-- already has a pretty instance (Token)

-- <file_name>            ::= <single_quoted>
-- already has a pretty instance (IRI)

{- -----------------------------------------------------------------------------
Tokens used in syntax
----------------------------------------------------------------------------- -}

-- <gentzen_arrow>        ::= -->
gentzen_arrow :: Doc
gentzen_arrow = text "-->"

-- <assignment>           ::= :=
assignment :: Doc
assignment = text ":="

-- <infix_equality>       ::= =
infix_equality :: Doc
infix_equality = text "="

-- <infix_inequality>     ::= !=
infix_inequality :: Doc
infix_inequality = text "!="

vline :: Doc
vline = text "|"

star :: Doc
star = text "*"

plus :: Doc
plus = text "+"

arrow :: Doc
arrow = text ">"

less_sign :: Doc
less_sign = text "<"

andD :: Doc
andD = text "&"

atD :: Doc
atD = text "@"


{- -----------------------------------------------------------------------------
Tokens used in syntax
----------------------------------------------------------------------------- -}

sepBy :: Doc -> [Doc] -> Doc
sepBy delimiter items = case items of
  [] -> empty
  _ -> fsep $ tail $ concatMap (\ i -> [delimiter, i]) items
