{- |
Module      :  ./THF/ParseTHF.hs
Description :  A Parser for the TPTP-THF Syntax
Copyright   :  (c) Jonathan von Schroeder, DFKI Bremen 2012
               (c) A. Tsogias, DFKI Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Jonathan von Schroeder <jonathan.von_schroeder@dfki.de>
Stability   :  provisional
Portability :  portable

A Parser for the TPTP-THF Input Syntax v5.4.0.0 taken from
<http://www.cs.miami.edu/~tptp/TPTP/SyntaxBNF.html> and THF0
Syntax taken from <http://www.ags.uni-sb.de/~chris/papers/C25.pdf> P. 15-16

Note: The parser prefers a THF0 parse tree over a THF parse tree
Note: We pretend as if tuples were still part of the syntax
-}

module THF.ParseTHF (parseTHF) where

import THF.As

import Text.ParserCombinators.Parsec

import Common.Parsec
import Common.Id (Token (..))
import Common.Lexer (parseToken)
import qualified Control.Monad.Fail as Fail

import Data.Char
import Data.Maybe

{- -----------------------------------------------------------------------------
Parser for the THF  and THF0 Syntax
----------------------------------------------------------------------------- -}

{- THF & THF0:
<TPTP_input>       ::= <annotated_formula> | <include>
<thf_annotated>    ::= thf(<name>,<formula_role>,<thf_formula><annotations>).
Data Type: TPTP_THF -}
parseTHF :: CharParser st [TPTP_THF]
parseTHF = do
    h <- optionMaybe header
    thf <- many ((systemComment <|> definedComment <|> comment <|>
                 include <|> thfAnnotatedFormula) << skipSpaces)
    return $ if isJust h then fromJust h : thf else thf


header :: CharParser st TPTP_THF
header = try (do
    s <- headerSE
    c <- myManyTill (try (commentLine << skipSpaces)) (try headerSE)
    return $ TPTP_Header (s : c))

headerSE :: CharParser st Comment
headerSE = do
    try (char '%' >> notFollowedBy (char '$'))
    c <- parseToken $ many1 $ char '-' << notFollowedBy printableChar
    skipSpaces
    return $ Comment_Line c

{- THF & THF0:
<comment>            ::- <comment_line>|<comment_block>
<comment_line>       ::- [%]<printable_char>*
<comment_block>      ::: [/][*]<not_star_slash>[*][*]*[/]
<not_star_slash>     ::: ([^*]*[*][*]*[^/*])*[^*]* -}
commentLine :: CharParser st Comment
commentLine = do
    try (char '%' >> notFollowedBy (char '$'))
    c <- parseToken $ many printableChar
    return $ Comment_Line c

comment_ :: String -> CharParser st Token
comment_ start = do
    try (string start >> notFollowedBy (char '$'))
    c <- parseToken $ many (noneOf "*/")
    skipMany1 (char '*')
    char '/'
    return c

comment :: CharParser st TPTP_THF
comment = fmap TPTP_Comment commentLine
  <|> do
    c <- comment_ "/*"
    return $ TPTP_Comment (Comment_Block c)

{- THF & THF0:
<defined_comment>    ::- <def_comment_line>|<def_comment_block>
<def_comment_line>   ::: [%]<dollar><printable_char>*
<def_comment_block>  ::: [/][*]<dollar><not_star_slash>[*][*]*[/]
Data Type: DefinedComment -}
definedComment :: CharParser st TPTP_THF
definedComment = do
    try (string "%$" >> notFollowedBy (char '$'))
    c <- parseToken $ many printableChar
    return $ TPTP_Defined_Comment (Defined_Comment_Line c)
  <|> do
    c <- comment_ "/*$"
    return $ TPTP_Defined_Comment (Defined_Comment_Block c)

{- THF & THF0:
<system_comment>     ::- <sys_comment_line>|<sys_comment_block>
<sys_comment_line>   ::: [%]<dollar><dollar><printable_char>*
<sys_comment_block>  ::: [/][*]<dollar><dollar><not_star_slash>[*][*]*[/]
Data Type: SystemComment -}
systemComment :: CharParser st TPTP_THF
systemComment = do
    tryString "%$$"
    c <- parseToken $ many printableChar
    return $ TPTP_System_Comment (System_Comment_Line c)
  <|> do
    c <- comment_ "/*$$"
    return $ TPTP_System_Comment (System_Comment_Block c)

{- THF & THF0:
<include>            ::= include(<file_name><formula_selection>).
<formula_selection>  ::= ,[<name_list>] | <null>
Data Type: Include -}
include :: CharParser st TPTP_THF
include = do
    key $ tryString "include"
    oParentheses
    fn <- fileName
    fs <- formulaSelection
    cParentheses
    char '.'
    return $ TPTP_Include (I_Include fn fs)

thfAnnotatedFormula :: CharParser st TPTP_THF
thfAnnotatedFormula = do
    key $ tryString "thf"
    oParentheses
    n <- name
    comma
    fr <- formulaRole
    comma
    tf <- thfFormula
    a <- annotations
    cParentheses
    char '.'
    return $ TPTP_THF_Annotated_Formula n fr tf a

{- THF & THF0:
<annotations>        ::= ,<source><optional_info> | <null> -}
annotations :: CharParser st Annotations
annotations = do
    comma
    s <- source
    oi <- optionalInfo
    return $ Annotations s oi
  <|> do
    notFollowedBy (char ',')
    return Null

{- THF & THF0:
<formula_role>       ::= <lower_word>
<formula_role>       :== axiom | hypothesis | definition | assumption |
lemma | theorem | conjecture | negated_conjecture |
plain | fi_domain | fi_functors | fi_predicates |
type | unknown -}
formulaRole :: CharParser st FormulaRole
formulaRole = do
    r <- lowerWord
    case show r of
        "axiom" -> return Axiom
        "hypothesis" -> return Hypothesis
        "definition" -> return Definition
        "assumption" -> return Assumption
        "lemma" -> return Lemma
        "theorem" -> return Theorem
        "conjecture" -> return Conjecture
        "negated_conjecture" -> return Negated_Conjecture
        "plain" -> return Plain
        "fi_domain" -> return Fi_Domain
        "fi_functors" -> return Fi_Functors
        "fi_predicates" -> return Fi_Predicates
        "type" -> return Type
        "unknown" -> return Unknown
        s -> Fail.fail ("No such Role: " ++ s)

{- THF
<thf_formula>        ::= <thf_logic_formula> | <thf_sequent>
THF0:
<thf_formula>        ::= <thf_logic_formula> | <thf_typed_const> -}
thfFormula :: CharParser st THFFormula
thfFormula = fmap T0F_THF_Typed_Const thfTypedConst
  <|> fmap TF_THF_Logic_Formula thfLogicFormula
  <|> fmap TF_THF_Sequent thfSequent

{- THF:
<thf_logic_formula>  ::= <thf_binary_formula> | <thf_unitary_formula> |
<thf_type_formula> | <thf_subtype>
THF0:
<thf_logic_formula>   ::= <thf_binary_formula> | <thf_unitary_formula> -}
thfLogicFormula :: CharParser st THFLogicFormula
thfLogicFormula = fmap TLF_THF_Binary_Formula thfBinaryFormula
  <|> fmap TLF_THF_Unitary_Formula thfUnitaryFormula
  -- different position for unitary formula to prefer thf0 parse
  <|> fmap TLF_THF_Type_Formula thfTypeFormula
  <|> fmap TLF_THF_Sub_Type thfSubType

{- THF:
<thf_binary_formula> ::= <thf_binary_pair> | <thf_binary_tuple> |
<thf_binary_type>
<thf_binary_pair>    ::= <thf_unitary_formula> <thf_pair_connective>
<thf_unitary_formula>
THF0:
<thf_binary_formula> ::= <thf_pair_binary> | <thf_tuple_binary>
<thf_pair_binary>    ::= <thf_unitary_formula> <thf_pair_connective>
<thf_unitary_formula>
Note: For THF0
<thf_binary_pair> is used like <thf_pair_binary> and
<thf_binary_tuple> are used like <thf_tuple_binary> -}
thfBinaryFormula :: CharParser st THFBinaryFormula
thfBinaryFormula = fmap TBF_THF_Binary_Tuple thfBinaryTuple
  <|> do
    (uff, pc) <- try $ do
        uff1 <- thfUnitaryFormula
        pc1 <- thfPairConnective
        return (uff1, pc1)
    ufb <- thfUnitaryFormula
    return $ TBF_THF_Binary_Pair uff pc ufb
   <|> fmap TBF_THF_Binary_Type thfBinaryType
   -- different position for binary type to prefer thf0 parse

{- THF:
<thf_binary_tuple>  ::= <thf_or_formula> | <thf_and_formula> |
<thf_apply_formula>
THF0:
<thf_tuple_binary>  ::= <thf_or_formula> | <thf_and_formula> |
<thf_apply_formula>
THF & THF0:
<thf_or_formula>    ::= <thf_unitary_formula> <vline> <thf_unitary_formula> |
<thf_or_formula> <vline> <thf_unitary_formula>
<thf_and_formula>   ::= <thf_unitary_formula> & <thf_unitary_formula> |
thf_and_formula> & <thf_unitary_formula>
<thf_apply_formula> ::= <thf_unitary_formula> @ <thf_unitary_formula> |
<thf_apply_formula> @ <thf_unitary_formula>
<vline>             :== | -}
thfBinaryTuple :: CharParser st THFBinaryTuple
thfBinaryTuple = do -- or
    uff <- try (thfUnitaryFormula << vLine)
    ufb <- sepBy1 thfUnitaryFormula vLine
    return $ TBT_THF_Or_Formula (uff : ufb)
  <|> do -- and
    uff <- try (thfUnitaryFormula << ampersand)
    ufb <- sepBy1 thfUnitaryFormula ampersand
    return $ TBT_THF_And_Formula (uff : ufb)
  <|> do -- apply
    uff <- try (thfUnitaryFormula << at)
    ufb <- sepBy1 thfUnitaryFormula at
    return $ TBT_THF_Apply_Formula (uff : ufb)

formulaWithVariables :: CharParser st (THFVariableList, THFUnitaryFormula)
formulaWithVariables = do
    vl <- brackets thfVariableList
    colon
    uf <- thfUnitaryFormula
    return (vl, uf)

{- THF:
<thf_unitary_formula>    ::= <thf_quantified_formula> | <thf_unary_formula> |
<thf_atom> | <thf_tuple> | <thf_let> |
<thf_conditional> | (<thf_logic_formula>)
note: thf let is currently not well defined and thus ommited
<thf_conditional>        ::= $itef(<thf_logic_formula>,<thf_logic_formula>,
<thf_logic_formula>)
THF0:
<thf_unitary_formula>    ::= <thf_quantified_formula> | <thf_abstraction> |
<thf_unary_formula> | <thf_atom> |
(<thf_logic_formula>)
<thf_abstraction>        ::= <thf_lambda> [<thf_variable_list>] :
<thf_unitary_formula>
<thf_lambda>             ::= ^
THF & THF0:
<thf_unary_formula>      ::= <thf_unary_connective> (<thf_logic_formula>) -}
thfUnitaryFormula :: CharParser st THFUnitaryFormula
thfUnitaryFormula = fmap TUF_THF_Logic_Formula_Par (parentheses thfLogicFormula)
  <|> fmap TUF_THF_Quantified_Formula (try thfQuantifiedFormula)
  <|> do
    keyChar '^'
    (vl, uf) <- formulaWithVariables
    return $ T0UF_THF_Abstraction vl uf {- added this for thf0
  changed positions of parses below to prefer th0 -}
  <|> try thfUnaryFormula
  <|> fmap TUF_THF_Atom thfAtom
  <|> fmap TUF_THF_Tuple thfTuple
  <|> do
    key $ tryString "$itef"
    oParentheses
    lf1 <- thfLogicFormula
    comma
    lf2 <- thfLogicFormula
    comma
    lf3 <- thfLogicFormula
    cParentheses
    return $ TUF_THF_Conditional lf1 lf2 lf3

{- THF:
<thf_quantified_formula> ::= <thf_quantifier> [<thf_variable_list>] :
<thf_unitary_formula>
THF0:
<thf_quantified_formula> ::= <thf_quantified_var> | <thf_quantified_novar>
<thf_quantified_var>     ::= <quantifier> [<thf_variable_list>] :
<thf_unitary_formula>
<thf_quantified_novar>   ::= <thf_quantifier> (<thf_unitary_formula>) -}
thfQuantifiedFormula :: CharParser st THFQuantifiedFormula
thfQuantifiedFormula = do
    q <- quantifier
    (vl, uf) <- formulaWithVariables
    return $ T0QF_THF_Quantified_Var q vl uf -- added this for thf0
  <|> do
    q <- thfQuantifier
    uf <- parentheses thfUnitaryFormula
    return $ T0QF_THF_Quantified_Novar q uf -- added this for thf0
  <|> do
    q <- thfQuantifier
    (vl, uf) <- formulaWithVariables
    return $ TQF_THF_Quantified_Formula q vl uf

{- THF & THF0:
<thf_variable_list>      ::= <thf_variable> |
<thf_variable>,<thf_variable_list> -}
thfVariableList :: CharParser st THFVariableList
thfVariableList = sepBy1 thfVariable comma

{- THF & THF0:
<thf_variable>           ::= <thf_typed_variable> | <variable>
<thf_typed_variable>     ::= <variable> : <thf_top_level_type> -}
thfVariable :: CharParser st THFVariable
thfVariable = do
    v <- try (variable << colon)
    tlt <- thfTopLevelType
    return $ TV_THF_Typed_Variable v tlt
  <|> fmap TV_Variable variable

{- THF0:
<thf_typed_const>        ::= <constant> : <thf_top_level_type> |
(<thf_typed_const>) -}
thfTypedConst :: CharParser st THFTypedConst -- added this for thf0
thfTypedConst = fmap T0TC_THF_TypedConst_Par (parentheses thfTypedConst)
  <|> do
    c <- try (constant << colon)
    tlt <- thfTopLevelType
    return $ T0TC_Typed_Const c tlt

thfUnaryFormula :: CharParser st THFUnitaryFormula
thfUnaryFormula = do
    uc <- thfUnaryConnective
    lf <- parentheses thfLogicFormula
    return $ TUF_THF_Unary_Formula uc lf

{- THF:
<thf_type_formula>       ::= <thf_typeable_formula> : <thf_top_level_type>
<thf_type_formula>       :== <constant> : <thf_top_level_type> -}
thfTypeFormula :: CharParser st THFTypeFormula
thfTypeFormula = do
    tp <- try (thfTypeableFormula << colon)
    tlt <- thfTopLevelType
    return $ TTF_THF_Type_Formula tp tlt
  <|> do
    c <- try (constant << colon)
    tlt <- thfTopLevelType
    return $ TTF_THF_Typed_Const c tlt

{- THF:
<thf_typeable_formula> ::= <thf_atom> | <thf_tuple> | (<thf_logic_formula>) -}
thfTypeableFormula :: CharParser st THFTypeableFormula
thfTypeableFormula = fmap TTyF_THF_Atom thfAtom
  <|> fmap TTyF_THF_Tuple thfTuple
  <|> fmap TTyF_THF_Logic_Formula (parentheses thfLogicFormula)

{- THF:
<thf_subtype> ::= <constant> <subtype_sign> <constant>
<subtype_sign> == << -}
thfSubType :: CharParser st THFSubType
thfSubType = do
    cf <- try (constant << key (string "<<"))
    cb <- constant
    return $ TST_THF_Sub_Type cf cb

{- THF:
<thf_top_level_type> ::= <thf_logic_formula>
THF0:
<thf_top_level_type> ::= <constant> | <variable> | <defined_type> |
<system_type> | <thf_binary_type> -}
thfTopLevelType :: CharParser st THFTopLevelType
thfTopLevelType = fmap T0TLT_THF_Binary_Type thfBinaryType
  <|> fmap T0TLT_Constant constant
  <|> fmap T0TLT_Variable variable
  <|> fmap T0TLT_Defined_Type definedType
  <|> fmap T0TLT_System_Type systemType
  <|> fmap TTLT_THF_Logic_Formula thfLogicFormula
  -- added all except for this for thf0

{- THF:
<thf_unitary_type>   ::= <thf_unitary_formula>
THF0:
<thf_unitary_type>   ::= <constant> | <variable> | <defined_type> |
<system_type> | (<thf_binary_type>) -}
thfUnitaryType :: CharParser st THFUnitaryType
thfUnitaryType = fmap T0UT_Constant constant
  <|> fmap T0UT_Variable variable
  <|> fmap T0UT_Defined_Type definedType
  <|> fmap T0UT_System_Type systemType
  <|> fmap T0UT_THF_Binary_Type_Par (parentheses thfBinaryType)
  <|> fmap TUT_THF_Unitary_Formula thfUnitaryFormula
  -- added all except for this for th0

{- THF:
<thf_binary_type>    ::= <thf_mapping_type> | <thf_xprod_type> |
<thf_union_type>
<thf_xprod_type>     ::= <thf_unitary_type> <star> <thf_unitary_type> |
<thf_xprod_type> <star> <thf_unitary_type>
<star> ::- *
<thf_union_type>     ::= <thf_unitary_type> <plus> <thf_unitary_type> |
<thf_union_type> <plus> <thf_unitary_type>
<plus> ::- +
THF0:
<thf_binary_type>    ::= <thf_mapping_type> | (<thf_binary_type>)
THF & THF0:
<thf_mapping_type>   ::= <thf_unitary_type> <arrow> <thf_unitary_type> |
<thf_unitary_type> <arrow> <thf_mapping_type>
<arrow> ::- > -}
thfBinaryType :: CharParser st THFBinaryType
thfBinaryType = do
    utf <- try (thfUnitaryType << arrow)
    utb <- sepBy1 thfUnitaryType arrow
    return $ TBT_THF_Mapping_Type (utf : utb)
  <|> fmap T0BT_THF_Binary_Type_Par (parentheses thfBinaryType)
  -- added this for thf0
  <|> do -- xprodType
    utf <- try (thfUnitaryType << star)
    utb <- sepBy1 thfUnitaryType star
    return $ TBT_THF_Xprod_Type (utf : utb)
  <|> do -- unionType
    utf <- try (thfUnitaryType << plus)
    utb <- sepBy1 thfUnitaryType plus
    return $ TBT_THF_Union_Type (utf : utb)

{- THF:
<thf_atom>               ::= <term> | <thf_conn_term>
%----<thf_atom> can also be <defined_type> | <defined_plain_formula> |
%----<system_type> | <system_atomic_formula>, but they are syntactically
%----captured by <term>.
<system_atomic_formula>  ::= <system_term>
THF0:
<thf_atom>               ::= <constant> | <defined_constant> |
<system_constant> | <variable> | <thf_conn_term>
<defined_constant>       ::= <atomic_defined_word>
<system_constant>        ::= <atomic_system_word> -}
thfAtom :: CharParser st THFAtom
thfAtom = fmap T0A_Constant constant
  <|> fmap T0A_Defined_Constant atomicDefinedWord
  <|> fmap T0A_System_Constant atomicSystemWord
  <|> fmap T0A_Variable variable
  -- added all above for thf0
  <|> fmap TA_THF_Conn_Term thfConnTerm
  -- changed position to prefer thf0
  <|> fmap TA_Defined_Type definedType
  <|> fmap TA_Defined_Plain_Formula definedPlainFormula
  <|> fmap TA_System_Type systemType
  <|> fmap TA_System_Atomic_Formula systemTerm
  <|> fmap TA_Term term

{- THF:
<thf_tuple> ::= [] | [<thf_tuple_list>]
<thf_tuple_list> ::= <thf_logic_formula> |
<thf_logic_formula>,<thf_tuple_list>
THFTupleList must not be empty -}
thfTuple :: CharParser st THFTuple
thfTuple = try ((oBracket >> cBracket) >> return [])
  <|> brackets (sepBy1 thfLogicFormula comma)

{- THF:
<thf_sequent> ::= <thf_tuple> <gentzen_arrow> <thf_tuple> |
(<thf_sequent>)
<gentzen_arrow> ::= --> -}
thfSequent :: CharParser st THFSequent
thfSequent = fmap TS_THF_Sequent_Par (parentheses thfSequent)
  <|> do
    tf <- try (thfTuple << gentzenArrow)
    tb <- thfTuple
    return $ TS_THF_Sequent tf tb

{- THF:
<thf_conn_term>  ::= <thf_pair_connective> | <assoc_connective> |
<thf_unary_connective>
THF0:
<thf_conn_term>  ::= <thf_quantifier> | <thf_pair_connective> |
<assoc_connective> | <thf_unary_connective> -}
thfConnTerm :: CharParser st THFConnTerm
thfConnTerm = fmap TCT_THF_Pair_Connective thfPairConnective
  <|> fmap TCT_Assoc_Connective assocConnective
  <|> fmap TCT_THF_Unary_Connective thfUnaryConnective
  <|> fmap T0CT_THF_Quantifier thfQuantifier
  -- added for thf0

{- THF:
<thf_quantifier>     ::= <fol_quantifier> | ^ | !> | ?* | @+ | @-
<fol_quantifier>     ::= ! | ?
THF0:
<thf_quantifier>     ::= !! | ?? -}
thfQuantifier :: CharParser st THFQuantifier
thfQuantifier = (key (tryString "!!") >> return T0Q_PiForAll)
  <|> (key (tryString "??") >> return T0Q_SigmaExists)
  -- added all above for thf0
  <|> (keyChar '!' >> return TQ_ForAll)
  <|> (keyChar '?' >> return TQ_Exists)
  <|> (keyChar '^' >> return TQ_Lambda_Binder)
  <|> (key (tryString "!>") >> return TQ_Dependent_Product)
  <|> (key (tryString "?*") >> return TQ_Dependent_Sum)
  <|> (key (tryString "@+") >> return TQ_Indefinite_Description)
  <|> (key (tryString "@-") >> return TQ_Definite_Description)
  <?> "thfQuantifier"

{- THF0:
<quantifier>         ::= ! | ? -}
quantifier :: CharParser st Quantifier
quantifier = (keyChar '!' >> return T0Q_ForAll)
  <|> (keyChar '?' >> return T0Q_Exists)
  <?> "quantifier"

{- THF:
<thf_pair_connective> ::= <infix_equality> | <infix_inequality> |
<binary_connective>
<infix_equality>     ::= =
<infix_inequality>   ::= !=
THF0:
<thf_pair_connective> ::= <defined_infix_pred> | <binary_connective>
<defined_infix_pred> ::= = | !=
THF & THF0:
<binary_connective>  ::= <=> | => | <= | <~> | ~<vline> | ~& -}
thfPairConnective :: CharParser st THFPairConnective
thfPairConnective = (key (tryString "!=") >> return Infix_Inequality)
  <|> (key (tryString "<=>") >> return Equivalent)
  <|> (key (tryString "=>") >> return Implication)
  <|> (key (tryString "<=") >> return IF)
  <|> (key (tryString "<~>") >> return XOR)
  <|> (key (tryString "~|") >> return NOR)
  <|> (key (tryString "~&") >> return NAND)
  <|> (keyChar '=' >> return Infix_Equality)
  <?> "pairConnective"

{- THF:
<thf_unary_connective> ::= <unary_connective> | !! | ??
THF0:
<thf_unary_connective> ::= <unary_connective>
THF & THF0:
<unary_connective>   ::= ~ -}
thfUnaryConnective :: CharParser st THFUnaryConnective
thfUnaryConnective = (keyChar '~' >> return Negation)
  <|> (key (tryString "!!") >> return PiForAll)
  <|> (key (tryString "??") >> return SigmaExists)

{- THF & THF0:
<assoc_connective>   ::= <vline> | & -}
assocConnective :: CharParser st AssocConnective
assocConnective = (keyChar '|' >> return OR)
  <|> (keyChar '&' >> return AND)

{- THF:
<defined_type>       :== $oType | $o | $iType | $i | $tType |
real | $rat | $int
THF0:
<defined_type>       :== $oType | $o | $iType | $i | $tType
THF & THF0:
<defined_type>       ::= <atomic_defined_word> -}
definedType :: CharParser st DefinedType
definedType = do
    adw <- atomicDefinedWord
    case show adw of
        "oType" -> return DT_oType
        "o" -> return DT_o
        "iType" -> return DT_iType
        "i" -> return DT_i
        "tType" -> return DT_tType
        "real" -> return DT_real
        "rat" -> return DT_rat
        "int" -> return DT_int
        s -> Fail.fail ("No such definedType: " ++ s)

{- THF & THF0:
<system_type>        ::= <atomic_system_word> -}
systemType :: CharParser st Token
systemType = atomicSystemWord

{- THF:
<defined_plain_formula> ::= <defined_plain_term>
<defined_plain_formula> :== <defined_prop> | <defined_pred>(<arguments>) -}
definedPlainFormula :: CharParser st DefinedPlainFormula
definedPlainFormula = fmap DPF_Defined_Prop definedProp
  <|> do
    dp <- definedPred
    a <- parentheses arguments
    return $ DPF_Defined_Formula dp a

{- THF & THF0:
<defined_prop>       :== <atomic_defined_word>
<defined_prop>       :== $true | $false -}
definedProp :: CharParser st DefinedProp
definedProp = do
    adw <- atomicDefinedWord
    case show adw of
        "true" -> return DP_True
        "false" -> return DP_False
        s -> Fail.fail ("No such definedProp: " ++ s)

{- THF:
<defined_pred>       :== <atomic_defined_word>
<defined_pred>       :== $distinct |
less | $lesseq | $greater | $greatereq |
is_int | $is_rat -}
definedPred :: CharParser st DefinedPred
definedPred = do
    adw <- atomicDefinedWord
    case show adw of
        "distinct" -> return Disrinct
        "less" -> return Less
        "lesseq" -> return Lesseq
        "greater" -> return Greater
        "greatereq" -> return Greatereq
        "is_int" -> return Is_int
        "is_rat" -> return Is_rat
        s -> Fail.fail ("No such definedPred: " ++ s)

{- THF:
<term> ::= <function_term> | <variable> | <conditional_term>
%----Conditional terms should only be used by TFF and not by THF.
Thus tey are not implemented. -}
term :: CharParser st Term
term = fmap T_Function_Term functionTerm
  <|> fmap T_Variable variable

{- THF:
<function_term> ::= <plain_term> | <defined_term> | <system_term> -}
functionTerm :: CharParser st FunctionTerm
functionTerm = fmap FT_System_Term systemTerm
  <|> fmap FT_Defined_Term definedTerm
  <|> fmap FT_Plain_Term plainTerm

{- THF:
<plain_term> ::= <constant> | <functor>(<arguments>) -}
plainTerm :: CharParser st PlainTerm
plainTerm = try (do
    f <- tptpFunctor
    a <- parentheses arguments
    return $ PT_Plain_Term f a)
  <|> fmap PT_Constant constant

{- THF & THF0:
<constant> ::= <functor> -}
constant :: CharParser st Constant
constant = tptpFunctor

{- THF & THF0:
<functor>  ::= <atomic_word> -}
tptpFunctor :: CharParser st AtomicWord
tptpFunctor = atomicWord

{- THF:
<defined_term> ::= <defined_atom> | <defined_atomic_term>
<defined_atomic_term> ::= <defined_plain_term> -}
definedTerm :: CharParser st DefinedTerm
definedTerm = fmap DT_Defined_Atomic_Term definedPlainTerm
  <|> fmap DT_Defined_Atom definedAtom

{- THF:
<defined_atom> ::= <number> | <distinct_object> -}
definedAtom :: CharParser st DefinedAtom
definedAtom = fmap DA_Number number
  <|> fmap DA_Distinct_Object distinctObject

{- THF:
<defined_plain_term> ::= <defined_constant> | <defined_functor>(<arguments>)
<defined_constant> ::= <defined_functor> -}
definedPlainTerm :: CharParser st DefinedPlainTerm
definedPlainTerm = try (do
    df <- definedFunctor
    a <- parentheses arguments
    return $ DPT_Defined_Function df a)
  <|> fmap DPT_Defined_Constant definedFunctor

{- THF:
<defined_functor> ::= <atomic_defined_word>
<defined_functor> :== $uminus | $sum | $difference | $product |
quotient | $quotient_e | $quotient_t | $quotient_f |
remainder_e | $remainder_t | $remainder_f |
floor | $ceiling | $truncate | $round |
to_int | $to_rat | $to_real -}
definedFunctor :: CharParser st DefinedFunctor
definedFunctor = do
    adw <- atomicDefinedWord
    case show adw of
        "uminus" -> return UMinus
        "sum" -> return Sum
        "difference" -> return Difference
        "product" -> return Product
        "quotient" -> return Quotient
        "quotient_e" -> return Quotient_e
        "quotient_t" -> return Quotient_t
        "quotient_f" -> return Quotient_f
        "floor" -> return Floor
        "ceiling" -> return Ceiling
        "truncate" -> return Truncate
        "round" -> return Round
        "to_int" -> return To_int
        "to_rat" -> return To_rat
        "to_real" -> return To_real
        s -> Fail.fail ("No such definedFunctor: " ++ s)

{- THF:
<system_term>        ::= <system_constant> | <system_functor>(<arguments>)
<system_constant>    ::= <system_functor> -}
systemTerm :: CharParser st SystemTerm
systemTerm = try (do
    sf <- systemFunctor
    a <- parentheses arguments
    return $ ST_System_Term sf a)
  <|> fmap ST_System_Constant systemFunctor

{- THF:
<system_functor>     ::= <atomic_system_word> -}
systemFunctor :: CharParser st Token
systemFunctor = atomicSystemWord

{- THF & THF0:
<variable>           ::= <upper_word> -}
variable :: CharParser st Token
variable = parseToken
  (do
    u <- upper
    an <- many (alphaNum <|> char '_')
    skipAll
    return (u : an)
   <?> "Variable")

{- THF:
<arguments> ::= <term> | <term>,<arguments>
at least one term is neaded -}
arguments :: CharParser st Arguments
arguments = sepBy1 term comma

{- THF & THF0:
<principal_symbol>   :== <functor> | <variable> -}
principalSymbol :: CharParser st PrincipalSymbol
principalSymbol = fmap PS_Functor tptpFunctor
  <|> fmap PS_Variable variable

{- THF & THF0:
<source>           ::= <general_term>
<source>           :== <dag_source> | <internal_source> | <external_source> |
unknown | [<sources>]
<internal_source>  :== introduced(<intro_type><optional_info>)
<sources>          :== <source> | <source>,<sources> -}
source :: CharParser st Source
source = (key (tryString "unknown") >> return S_Unknown)
  <|> fmap S_Dag_Source dagSource
  <|> fmap S_External_Source externalSource
  <|> fmap S_Sources (sepBy1 source comma)
  <|> do -- internal_source
    key $ tryString "introduced"
    oParentheses
    it <- introType
    oi <- optionalInfo
    cParentheses
    return $ S_Internal_Source it oi

{- THF & THF0:
<dag_source>         :== <name> | <inference_record>
<inference_record>   :== inference(<inference_rule>,<useful_info>,
[<parent_list>])
<inference_rule>     :== <atomic_word>
<parent_list>        :== <parent_info> | <parent_info>,<parent_list> -}
dagSource :: CharParser st DagSource
dagSource = do
    key (tryString "inference")
    oParentheses
    ir <- atomicWord
    comma
    ui <- usefulInfo
    comma
    pl <- brackets (sepBy1 parentInfo comma)
    cParentheses
    return (DS_Inference_Record ir ui pl)
  <|> fmap DS_Name name

{- THF & THF0:
<parent_info>        :== <source><parent_details>
<parent_details>     :== :<general_list> | <null> -}
parentInfo :: CharParser st ParentInfo
parentInfo = do
    s <- source
    pd <- parentDetails
    return $ PI_Parent_Info s pd


parentDetails :: CharParser st (Maybe GeneralList)
parentDetails = fmap Just (colon >> generalList)
  <|> (notFollowedBy (char ':') >> return Nothing)

{- THF & THF0:
<intro_type>     :== definition | axiom_of_choice | tautology | assumption -}
introType :: CharParser st IntroType
introType = (key (tryString "definition") >> return IT_definition)
  <|> (key (tryString "axiom_of_choice") >> return IT_axiom_of_choice)
  <|> (key (tryString "tautology") >> return IT_tautology)
  <|> (key (tryString "assumption") >> return IT_assumption)

{- THF & THF0:
<external_source>    :== <file_source> | <theory> | <creator_source>
<theory>             :== theory(<theory_name><optional_info>)
<creator_source>     :== creator(<creator_name><optional_info>)
<creator_name>       :== <atomic_word> -}
externalSource :: CharParser st ExternalSource
externalSource = fmap ES_File_Source fileSource
  <|> do
    key $ tryString "theory"
    oParentheses
    tn <- theoryName
    oi <- optionalInfo
    cParentheses
    return $ ES_Theory tn oi
  <|> do
    key $ tryString "creator"
    oParentheses
    cn <- atomicWord
    oi <- optionalInfo
    cParentheses
    return $ ES_Creator_Source cn oi

{- THF & THF0:
<file_source>        :== file(<file_name><file_info>)
<file_info>          :== ,<name> | <null> -}
fileSource :: CharParser st FileSource
fileSource = do
    key $ tryString "file"
    oParentheses
    fn <- fileName
    fi <- fileInfo
    cParentheses
    return $ FS_File fn fi


fileInfo :: CharParser st (Maybe Name)
fileInfo = fmap Just (comma >> name)
  <|> (notFollowedBy (char ',') >> return Nothing)

{- THF & THF0:
<theory_name>        :== equality | ac -}
theoryName :: CharParser st TheoryName
theoryName = (key (tryString "equality") >> return Equality)
  <|> (key (tryString "ac") >> return Ac)

{- THF & THF0:
<optional_info>      ::= ,<useful_info> | <null> -}
optionalInfo :: CharParser st OptionalInfo
optionalInfo = fmap Just (comma >> usefulInfo)
  <|> (notFollowedBy (char ',') >> return Nothing)

{- THF & THF0:
<useful_info>        ::= <general_list>
<useful_info>        :== [] | [<info_items>]
<info_items>         :== <info_item> | <info_item>,<info_items> -}
usefulInfo :: CharParser st UsefulInfo
usefulInfo = (oBracket >> cBracket >> return [])
  <|> brackets (sepBy1 infoItem comma)

{- THF & THF0:
<info_item>          :== <formula_item> | <inference_item> |
<general_function> -}
infoItem :: CharParser st InfoItem
infoItem = fmap II_Formula_Item formulaItem
  <|> fmap II_Inference_Item inferenceItem
  <|> fmap II_General_Function generalFunction

{- THF & THF0:
<formula_item>       :== <description_item> | <iquote_item>
<description_item>   :== description(<atomic_word>)
<iquote_item>        :== iquote(<atomic_word>) -}
formulaItem :: CharParser st FormulaItem
formulaItem = do
    key $ tryString "description"
    fmap FI_Description_Item (parentheses atomicWord)
  <|> do
    key $ tryString "iquote"
    fmap FI_Iquote_Item (parentheses atomicWord)

{- THF & THF0:
<inference_item>     :== <inference_status> | <assumptions_record> |
<new_symbol_record> | <refutation>
<assumptions_record> :== assumptions([<name_list>])
<refutation>         :== refutation(<file_source>)
<new_symbol_record>  :== new_symbols(<atomic_word>,[<new_symbol_list>])
<new_symbol_list>    :== <principal_symbol> |
<principal_symbol>,<new_symbol_list> -}
inferenceItem :: CharParser st InferenceItem
inferenceItem = fmap II_Inference_Status inferenceStatus
  <|> do
    key $ tryString "assumptions"
    fmap II_Assumptions_Record (parentheses (brackets nameList))
  <|> do
    key $ tryString "new_symbols"
    oParentheses
    aw <- atomicWord
    comma
    nsl <- brackets (sepBy1 principalSymbol comma)
    cParentheses
    return $ II_New_Symbol_Record aw nsl
  <|> do
    key $ tryString "refutation"
    fmap II_Refutation (parentheses fileSource)

{- THF & THF0:
<inference_status>   :== status(<status_value>) | <inference_info>
<inference_info>     :== <inference_rule>(<atomic_word>,<general_list>)
<inference_rule>     :== <atomic_word> -}
inferenceStatus :: CharParser st InferenceStatus
inferenceStatus = do
    key $ tryString "status"
    fmap IS_Status (parentheses statusValue)
  <|> do
    ir <- try (atomicWord << oParentheses)
    aw <- atomicWord
    comma
    gl <- generalList
    cParentheses
    return $ IS_Inference_Info ir aw gl

{- THF & THF0:
<status_value>   :== suc | unp | sap | esa | sat | fsa | thm | eqv | tac |
wec | eth | tau | wtc | wth | cax | sca | tca | wca |
cup | csp | ecs | csa | cth | ceq | unc | wcc | ect |
fun | uns | wuc | wct | scc | uca | noc -}
statusValue :: CharParser st StatusValue
statusValue = choice $ map (\ r -> key (tryString $ showStatusValue r)
                            >> return r) allStatusValues

allStatusValues :: [StatusValue]
allStatusValues =
  [Suc, Unp, Sap, Esa, Sat, Fsa, Thm, Eqv, Tac,
   Wec, Eth, Tau, Wtc, Wth, Cax, Sca, Tca, Wca,
   Cup, Csp, Ecs, Csa, Cth, Ceq, Unc, Wcc, Ect,
   Fun, Uns, Wuc, Wct, Scc, Uca, Noc]

showStatusValue :: StatusValue -> String
showStatusValue = map toLower . show

formulaSelection :: CharParser st (Maybe NameList)
formulaSelection = fmap Just (comma >> brackets nameList)
  <|> (notFollowedBy (char ',') >> return Nothing)

{- THF & THF0:
<name_list>          ::= <name> | <name>,<name_list>
the list must mot be empty -}
nameList :: CharParser st NameList
nameList = sepBy1 name comma

{- THF & THF0:
<general_term>       ::= <general_data> | <general_data>:<general_term> |
<general_list> -}
generalTerm :: CharParser st GeneralTerm
generalTerm = do
    gd <- try (generalData << notFollowedBy (char ':'))
    return $ GT_General_Data gd
  <|> do
    gd <- try (generalData << colon)
    gt <- generalTerm
    return $ GT_General_Data_Term gd gt
  <|> fmap GT_General_List generalList

{- THF & THF0:
<general_data>       ::= <atomic_word> | <general_function> |
<variable> | <number> | <distinct_object> |
<formula_data>
<general_data>       :== bind(<variable>,<formula_data>) -}
generalData :: CharParser st GeneralData
generalData = fmap GD_Variable variable
  <|> fmap GD_Number number
  <|> fmap GD_Distinct_Object distinctObject
  <|> do
    key $ tryString "bind"
    oParentheses
    v <- variable
    comma
    fd <- formulaData
    cParentheses
    return (GD_Bind v fd)
  <|> fmap GD_General_Function generalFunction
  <|> fmap GD_Atomic_Word atomicWord
  <|> fmap GD_Formula_Data formulaData

{- THF & THF0:
<general_function>   ::= <atomic_word>(<general_terms>)
general_terms must not be empty -}
generalFunction :: CharParser st GeneralFunction
generalFunction = do
    aw <- atomicWord
    gts <- parentheses generalTerms
    return $ GF_General_Function aw gts

{- THF & THF0:
<formula_data>       ::= $thf(<thf_formula>) | $tff(<tff_formula>) |
fof(<fof_formula>) | $cnf(<cnf_formula>) |
fot(<term>)
only thf is used here -}
formulaData :: CharParser st FormulaData
formulaData = fmap THF_Formula thfFormula

{- THF & THF0:
<general_list>       ::= [] | [<general_terms>] -}
generalList :: CharParser st GeneralList
generalList = (try (oBracket >> cBracket) >> return [])
  <|> brackets generalTerms

{- THF & THF0:
<general_terms>      ::= <general_term> | <general_term>,<general_terms> -}
generalTerms :: CharParser st [GeneralTerm]
generalTerms = sepBy1 generalTerm comma

{- THF:
<name>               ::= <atomic_word> | <integer>
THF0:
<name>               ::= <atomic_word> | <unsigned_integer> -}
name :: CharParser st Name
name = fmap T0N_Unsigned_Integer (parseToken (unsignedInteger << skipAll))
  -- added for thf0
  <|> fmap N_Integer (integer << skipAll)
  <|> fmap N_Atomic_Word atomicWord

{- THF & THF0:
<atomic_word>        ::= <lower_word> | <single_quoted> -}
atomicWord :: CharParser st AtomicWord
atomicWord = fmap A_Lower_Word lowerWord
  <|> fmap A_Single_Quoted singleQuoted
  <?> "lowerWord or singleQuoted"

{- THF & THF0:
<atomic_defined_word> ::= <dollar_word> -}
atomicDefinedWord :: CharParser st Token
atomicDefinedWord = char '$' >> lowerWord

{- THF & THF0:
<atomic_system_word> ::= <dollar_dollar_word>
<dollar_dollar_word> ::- <dollar><dollar><lower_word>
<dollar>             ::: [$] -}
atomicSystemWord :: CharParser st Token
atomicSystemWord = tryString "$$" >> lowerWord

{- THF & THF0:
<number> ::= <integer> | <rational> | <real>
<real>               ::- (<signed_real>|<unsigned_real>)
<signed_real>        ::- <sign><unsigned_real>
<unsigned_real>      ::- (<decimal_fraction>|<decimal_exponent>)
<rational>           ::- (<signed_rational>|<unsigned_rational>)
<signed_rational>    ::- <sign><unsigned_rational>
<unsigned_rational>  ::- <decimal><slash><positive_decimal>
<integer>            ::- (<signed_integer>|<unsigned_integer>)
<signed_integer>     ::- <sign><unsigned_integer>
<unsigned_integer>   ::- <decimal>
<decimal>            ::- (<zero_numeric>|<positive_decimal>)
<positive_decimal>   ::- <non_zero_numeric><numeric>*
<decimal_exponent>   ::- (<decimal>|<decimal_fraction>)<exponent><decimal>
<decimal_fraction>   ::- <decimal><dot_decimal>
<dot_decimal>        ::- <dot><numeric><numeric>*
<sign>               ::: [+-]
<dot>                ::: [.]
<exponent>           ::: [Ee]
<slash>              ::: [/]
<zero_numeric>       ::: [0]
<non_zero_numeric>   ::: [1-9]
<numeric>            ::: [0-9] -}
number :: CharParser st Number
number = fmap Num_Real (real << skipAll)
  <|> fmap Num_Rational (rational << skipAll)
  <|> fmap Num_Integer (integer << skipAll)

{- THF & THF0:
<file_name>          ::= <single_quoted> -}
fileName :: CharParser st Token
fileName = singleQuoted

{- THF & THF0:
<single_quoted>      ::- <single_quote><sq_char><sq_char>*<single_quote>
<single_quote>       ::: [']
<sq_char>            ::: ([\40-\46\50-\133\135-\176]|[\\]['\\]) -}
singleQuoted :: CharParser st Token
singleQuoted = parseToken $ do
    char '\''
    s <- fmap concat $ many1 (tryString "\\\\" <|> tryString "\\'"
        <|> tryString "\\\'"
        <|> single ( satisfy (\ c -> printable c && notElem c "'\\")))
    keyChar '\''
    return s

{- THF & THF0:
<distinct_object> ::- <double_quote><do_char>*<double_quote>
<do_char> ::: ([\40-\41\43-\133\135-\176]|[\\]["\\])
<double_quote> ::: ["] -}
distinctObject :: CharParser st Token
distinctObject = parseToken $ do
    char '\"'
    s <- fmap concat $ many1 (tryString "\\\\" <|> tryString "\\\""
        <|> single ( satisfy (\ c -> printable c && notElem c "\"\\")))
    keyChar '\"'
    return s

{- THF & THF0:
<lower_word>         ::- <lower_alpha><alpha_numeric>*
<alpha_numeric>      ::: (<lower_alpha>|<upper_alpha>|<numeric>|[_])
<lower_alpha>        ::: [a-z]
<upper_alpha>        ::: [A-Z]
<numeric>            ::: [0-9] -}
lowerWord :: CharParser st Token
lowerWord = parseToken (do
    l <- lower
    an <- many (alphaNum <|> char '_')
    skipAll
    return (l : an)
  <?> "alphanumeric word with leading lowercase letter")

printableChar :: CharParser st Char
printableChar = satisfy printable

printable :: Char -> Bool
printable c = ord c >= 32 && ord c <= 126

-- Numbers
real :: CharParser st Token
real = parseToken (try (do
    s <- oneOf "-+"
    ur <- unsignedReal
    return (s : ur))
  <|> unsignedReal
  <?> "(signed) real")

unsignedReal :: CharParser st String
unsignedReal = do
    de <- try (do
        d <- decimalFractional <|> decimal
        e <- oneOf "Ee"
        return (d ++ [e]))
    ex <- integer
    return (de ++ (show ex))
  <|> decimalFractional
  <?> "unsigned real"

rational :: CharParser st Token
rational = parseToken (try (do
    s <- oneOf "-+"
    ur <- unsignedRational
    return (s : ur))
  <|> unsignedRational
  <?> "(signed) rational")

unsignedRational :: CharParser st String
unsignedRational = do
    d1 <- try (decimal << char '/')
    d2 <- positiveDecimal
    return (d1 ++ "/" ++ d2)

integer :: CharParser st Token
integer = parseToken (try (do
    s <- oneOf "-+"
    ui <- unsignedInteger
    return (s : ui))
  <|> unsignedInteger
  <?> "(signed) integer")

unsignedInteger :: CharParser st String
unsignedInteger = try (decimal << notFollowedBy (oneOf "eE/."))

decimal :: CharParser st String
decimal = do
    char '0'
    notFollowedBy digit
    return "0"
  <|> positiveDecimal
  <?> "single zero or digits"

positiveDecimal :: CharParser st String
positiveDecimal = do
    nz <- satisfy (\ c -> isDigit c && c /= '0')
    d <- many digit
    return (nz : d)
  <?> "positiv decimal"

decimalFractional :: CharParser st String
decimalFractional = do
    dec <- try (decimal << char '.')
    n <- many1 digit
    return (dec ++ "." ++ n)
  <?> "decimal fractional"


{- -----------------------------------------------------------------------------
Some helper functions
----------------------------------------------------------------------------- -}

skipAll :: CharParser st ()
skipAll = skipMany (skipMany1 space <|>
                    forget (comment <|> definedComment <|> systemComment))

skipSpaces :: CharParser st ()
skipSpaces = skipMany space

key :: CharParser st a -> CharParser st ()
key = (>> skipAll)

keyChar :: Char -> CharParser st ()
keyChar = key . char

myManyTill :: CharParser st a -> CharParser st a -> CharParser st [a]
myManyTill p end = do
    e <- end
    return [e]
  <|> do
    x <- p
    xs <- myManyTill p end
    return (x : xs)


{- -----------------------------------------------------------------------------
Different simple symbols
----------------------------------------------------------------------------- -}

vLine :: CharParser st ()
vLine = keyChar '|'

star :: CharParser st ()
star = keyChar '*'

plus :: CharParser st ()
plus = keyChar '+'

arrow :: CharParser st ()
arrow = keyChar '>'

comma :: CharParser st ()
comma = keyChar ','

colon :: CharParser st ()
colon = keyChar ':'

oParentheses :: CharParser st ()
oParentheses = keyChar '('

cParentheses :: CharParser st ()
cParentheses = keyChar ')'

parentheses :: CharParser st a -> CharParser st a
parentheses p = do
    r <- try (oParentheses >> p)
    cParentheses
    return r

oBracket :: CharParser st ()
oBracket = keyChar '['

cBracket :: CharParser st ()
cBracket = keyChar ']'

brackets :: CharParser st a -> CharParser st a
brackets p = do
    r <- try (oBracket >> p)
    cBracket
    return r

ampersand :: CharParser st ()
ampersand = keyChar '&'

at :: CharParser st ()
at = keyChar '@'

gentzenArrow :: CharParser st ()
gentzenArrow = key $ string "-->"
