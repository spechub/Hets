{- |
Module      :  ./TPTP/Parse.hs
Description :  A Parser for the TPTP Syntax v6.4.0.11
Copyright   :  (c) Eugen Kuksa University of Magdeburg 2017
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Eugen Kuksa <kuksa@iks.cs.ovgu.de>
Stability   :  provisional
Portability :  portable

A Parser for the TPTP Input Syntax v6.4.0.11 taken from
<http://www.cs.miami.edu/~tptp/TPTP/SyntaxBNF.html>

References

[1] G. Sutcliffe et al.: The TPTP language grammar in BNF.
    <http://www.cs.miami.edu/~tptp/TPTP/SyntaxBNF.html>

    Note: The implemented version is saved at TPTP/Documents/SyntaxBNF.html

    Note: The names of the data types are aligned with the names of the
    grammar rules at this reference page (modulo case).
-}

module TPTP.Parser ( parseBasicSpec
                   , annotated_formula
                   ) where

import TPTP.AS hiding (name, formulaRole, annotations)
import TPTP.Common

import qualified Common.AnnoState as AnnoState
import qualified Common.AS_Annotation as Annotation
import Common.GlobalAnnotations (PrefixMap)
import Common.Id (Token (..))
import Common.IRI (IRI (..), iriCurie)
import qualified Common.Lexer as Lexer (pToken)
import Common.Parsec

import Control.Monad (liftM)
import Data.Char (isAlphaNum, isSpace, ord)
import Prelude hiding (exp, exponent)
import Text.ParserCombinators.Parsec

{- -----------------------------------------------------------------------------
Debug
----------------------------------------------------------------------------- -}
import Debug.Trace
import Text.Printf


parserInsideTrace :: Monad m => String -> m ()
parserInsideTrace msg = trace msg $ return ()

parserTrace, parserTraceId, parserTraceLineNumber, parserTraceFull :: String -> CharParser st a -> CharParser st a
parserTrace = parserTraceId
parserTraceId _ p = p
parserTraceLineNumber _ p = do
  s <- getParserState
  if 1 == (sourceColumn $ statePos s)
  then trace (show $ sourceLine $ statePos s) $ return ()
  else return ()
  p
parserTraceFull msg p = do
  s <- getParserState
  if debug s
  then do
    let outBefore = takeWhile (\ c -> c /= '\n') $ take width (stateInput s)
    trace (parserMessage s outBefore) $ return ()
    parsed <- p
    s' <- getParserState
    let outAfter = takeConsumed outBefore s s'
    trace (successMessage s s' outBefore outAfter) $ return parsed
  else p
  where
    width = 54 :: Int
    space = 5 :: Int
    parserWidth = 24 :: Int
    parsedWidth = 24 :: Int
    debug s = True --6 == (sourceLine $ statePos s)
    line s = sourceLine $ statePos s
    column s = sourceColumn $ statePos s
    parserMessage s out =  printf ("%3d.%-4d - %" ++ show width ++ "s%" ++ show space ++ "s     %-" ++ show parserWidth ++ "s") (line s) (column s) out "" msg
    successMessage s s' outBefore outAfter = printf ("%3d.%-4d - %" ++ show width ++ "s%" ++ show space ++ "s --> %-" ++ show parserWidth ++ "s  =  %-"++ show parsedWidth ++"s  FROM  %3d.%-4d - %-s") (line s') (column s') "" "" msg outAfter (line s) (column s) outBefore
    takeConsumed :: String -> State s u -> State s u -> String
    takeConsumed outBefore stateBefore stateAfter =
      let consumedLength = sourceColumn (statePos stateAfter) - sourceColumn (statePos stateBefore)
      in take consumedLength outBefore

{- -----------------------------------------------------------------------------
Logic components
----------------------------------------------------------------------------- -}

parseBasicSpec :: PrefixMap -> AnnoState.AParser st BASIC_SPEC
parseBasicSpec _ = parserTrace "parseBasicSpec" (liftM Basic_spec (many1 $ AnnoState.allAnnoParser tptp_file)
  <|> do
    file <- tptp_file
    return $ Basic_spec [Annotation.emptyAnno file]
  )

{- -----------------------------------------------------------------------------
Files. Empty file is OK
----------------------------------------------------------------------------- -}

-- <TPTP_file>            ::= <TPTP_input>*
tptp_file :: CharParser st TPTP
tptp_file = parserTrace "tptp_file" (do
    skip
    inputs <- many1 tptp_input
    return $ TPTP inputs
  <?> "TPTP_file"
  )

-- <TPTP_input>           ::= <annotated_formula> | <include>
tptp_input :: CharParser st TPTP_input
tptp_input = parserTrace "tptp_input" (
  skip >> (liftM Annotated_formula annotated_formula
    <|> liftM TPTP_include include
    <|> liftM TPTP_system_comment system_comment
    <|> liftM TPTP_defined_comment defined_comment
    <|> liftM TPTP_comment comment
    <?> "TPTP_input")
  )

{- -----------------------------------------------------------------------------
Formula records
----------------------------------------------------------------------------- -}

-- <annotated_formula>    ::= <thf_annotated> | <tfx_annotated> | <tff_annotated> |
--                            <tcf_annotated> | <fof_annotated> | <cnf_annotated> |
--                            <tpi_annotated>
annotated_formula :: CharParser st Annotated_formula
annotated_formula = parserTrace "annotated_formula" (
  skip >> (thf_annotated
    <|> tfx_annotated
    <|> tff_annotated
    <|> tcf_annotated
    <|> fof_annotated
    <|> cnf_annotated
    <|> tpi_annotated
    <?> "annotated_formula")
  )

-- <tpi_annotated>        ::= tpi(<name>,<formula_role>,<tpi_formula><annotations>).
tpi_annotated :: CharParser st Annotated_formula
tpi_annotated = parserTrace "tpi_annotated" (formulaAnnotated "tpi" tpi_formula
  (\ n r f a -> AF_TPI_Annotated $ TPI_annotated n r f a)
  )

-- <tpi_formula>          ::= <fof_formula>
tpi_formula :: CharParser st TPI_formula
tpi_formula = parserTrace "tpi_formula" (fof_formula <?> "tpi_formula"
  )

-- <thf_annotated>        ::= thf(<name>,<formula_role>,<thf_formula>
--                            <annotations>).
thf_annotated :: CharParser st Annotated_formula
thf_annotated = parserTrace "thf_annotated" (formulaAnnotated "thf" thf_formula
  (\ n r f a -> AF_THF_Annotated $ THF_annotated n r f a)
  )

-- <tfx_annotated>        ::= tfx(<name>,<formula_role>,<tfx_formula>
--                            <annotations>).
tfx_annotated :: CharParser st Annotated_formula
tfx_annotated = parserTrace "tfx_annotated" (formulaAnnotated "tfx" tfx_formula
  (\ n r f a -> AF_TFX_Annotated $ TFX_annotated n r f a)
  )

-- <tff_annotated>        ::= tff(<name>,<formula_role>,<tff_formula>
--                            <annotations>).
tff_annotated :: CharParser st Annotated_formula
tff_annotated = parserTrace "tff_annotated" (formulaAnnotated "tff" tff_formula
  (\ n r f a -> AF_TFF_Annotated $ TFF_annotated n r f a)
  )

-- <tcf_annotated>        ::= tcf(<name>,<formula_role>,<tcf_formula>
--                            <annotations>).
tcf_annotated :: CharParser st Annotated_formula
tcf_annotated = parserTrace "tcf_annotated" (formulaAnnotated "tcf" tcf_formula
  (\ n r f a -> AF_TCF_Annotated $ TCF_annotated n r f a)
  )

-- <fof_annotated>        ::= fof(<name>,<formula_role>,<fof_formula>
--                            <annotations>).
fof_annotated :: CharParser st Annotated_formula
fof_annotated = parserTrace "fof_annotated" (formulaAnnotated "fof" fof_formula
  (\ n r f a -> AF_FOF_Annotated $ FOF_annotated n r f a)
  )

-- <cnf_annotated>        ::= cnf(<name>,<formula_role>,<cnf_formula>
--                            <annotations>).
cnf_annotated :: CharParser st Annotated_formula
cnf_annotated = parserTrace "cnf_annotated" (formulaAnnotated "cnf" cnf_formula
  (\ n r f a -> AF_CNF_Annotated $ CNF_annotated n r f a)
  )

formulaAnnotated :: String
                 -> CharParser st a
                 -> (Name -> Formula_role -> a -> Annotations -> Annotated_formula)
                 -> CharParser st Annotated_formula
formulaAnnotated keyword formula constructor = do
  strTok keyword
  (n, r, f, a) <- parens (do
    n <- name
    commaT
    r <- formula_role
    commaT
    f <- formula
    a <- annotations
    return (n, r, f, a))
  dotT
  return $ constructor n r f a

-- <annotations>          ::= ,<source><optional_info> | <null>
annotations :: CharParser st Annotations
annotations = parserTrace "annotations" (liftM Annotations annotations' <?> "annotations"
  )
  where
    annotations' = optionMaybe $ do
      commaT
      s <- source
      oi <- optional_info
      return (s, oi)

{- -----------------------------------------------------------------------------
Types for problems.
----------------------------------------------------------------------------- -}

-- %----Types for problems.
-- %----Note: The previous <source_type> from ...
-- %----   <formula_role> ::= <user_role>-<source>
-- %----... is now gone. Parsers may choose to be tolerant of it for backwards
-- %----compatibility.
-- <formula_role>         ::= <lower_word>
-- <formula_role>         :== axiom | hypothesis | definition | assumption |
--                            lemma | theorem | corollary | conjecture |
--                            negated_conjecture | plain | type |
--                            fi_domain | fi_functors | fi_predicates | unknown
formula_role :: CharParser st Formula_role
formula_role = parserTrace "formula_role" (constantsChoice
   [("axiom", Axiom),
    ("hypothesis", Hypothesis),
    ("definition", Definition),
    ("assumption", Assumption),
    ("lemma", Lemma),
    ("theorem", Theorem),
    ("corollary", Corollary),
    ("conjecture", Conjecture),
    ("negated_conjecture", Negated_conjecture),
    ("plain", Plain),
    ("type", Type),
    ("fi_domain", Fi_domain),
    ("fi_functors", Fi_functors),
    ("fi_predicates", Fi_predicates),
    ("unknown", Unknown)]
   <?> "formula_role"
  )



{- -----------------------------------------------------------------------------
THF formulae
----------------------------------------------------------------------------- -}
-- <thf_formula>          ::= <thf_logic_formula> | <thf_sequent>
thf_formula :: CharParser st THF_formula
thf_formula = parserTrace "thf_formula" (liftM THFF_logic thf_logic_formula
  <|> liftM THFF_sequent thf_sequent
  <?> "thf_formula"
  )

-- <thf_logic_formula>    ::= <thf_binary_formula> | <thf_unitary_formula> |
--                            <thf_type_formula> | <thf_subtype>
thf_logic_formula :: CharParser st THF_logic_formula
thf_logic_formula = parserTrace "thf_logic_formula" (
  liftM THFLF_type thf_type_formula
  <|> do
    f <- thf_unitary_formula
    (liftM THFLF_binary (thf_binary_formula f)
      <|> return (THFLF_unitary f))
  <|> liftM THFLF_subtype thf_subtype
  <?> "thf_logic_formula"
  )

-- <thf_binary_formula>   ::= <thf_binary_pair> | <thf_binary_tuple>
thf_binary_formula :: THF_unitary_formula -> CharParser st THF_binary_formula
thf_binary_formula f = parserTrace "thf_binary_formula" (
  liftM THFBF_pair (thf_binary_pair f)
  <|> liftM THFBF_tuple (thf_binary_tuple f)
  <?> "thf_binary_formula"
  )

-- <thf_binary_pair>      ::= <thf_unitary_formula> <thf_pair_connective>
--                            <thf_unitary_formula>
thf_binary_pair :: THF_unitary_formula -> CharParser st THF_binary_pair
thf_binary_pair f1 = parserTrace "thf_binary_pair" (do
    pc <- try thf_pair_connective
    f2 <- thf_unitary_formula
    return $ THF_binary_pair pc f1 f2
  <?> "thf_binary_pair"
  )

-- <thf_binary_tuple>     ::= <thf_or_formula> | <thf_and_formula> |
--                            <thf_apply_formula>
thf_binary_tuple :: THF_unitary_formula -> CharParser st THF_binary_tuple
thf_binary_tuple f = parserTrace "thf_binary_tuple" (
  (liftM THFBT_or (thf_or_formula f)
   <|> liftM THFBT_and (thf_and_formula f)
   <|> liftM THFBT_apply (thf_apply_formula f))
  <?> "thf_binary_tuple"
  )

-- <thf_or_formula>       ::= <thf_unitary_formula> <vline> <thf_unitary_formula> |
--                            <thf_or_formula> <vline> <thf_unitary_formula>
thf_or_formula :: THF_unitary_formula -> CharParser st THF_or_formula
thf_or_formula f = parserTrace "thf_or_formula" (do
    try vline
    fs <- thf_unitary_formula `sepBy1` vline
    return $ f : fs
  <?> "thf_or_formula"
  )

-- <thf_and_formula>      ::= <thf_unitary_formula> & <thf_unitary_formula> |
--                            <thf_and_formula> & <thf_unitary_formula>
thf_and_formula :: THF_unitary_formula -> CharParser st THF_and_formula
thf_and_formula f = parserTrace "thf_and_formula" (do
    try andT
    fs <- thf_unitary_formula `sepBy1` andT
    return $ f : fs
  <?> "thf_and_formula"
  )

-- <thf_apply_formula>    ::= <thf_unitary_formula> @ <thf_unitary_formula> |
--                            <thf_apply_formula> @ <thf_unitary_formula>
thf_apply_formula :: THF_unitary_formula -> CharParser st THF_apply_formula
thf_apply_formula f = parserTrace "thf_apply_formula" (do
    try $ charTok '@'
    fs <- thf_unitary_formula `sepBy1` charTok '@'
    return $ f : fs
  <?> "thf_apply_formula"
  )

-- <thf_unitary_formula>  ::= <thf_quantified_formula> | <thf_unary_formula> |
--                            <thf_atom> | <thf_conditional> | <thf_let> |
--                            <thf_tuple> | (<thf_logic_formula>)
thf_unitary_formula :: CharParser st THF_unitary_formula
thf_unitary_formula = parserTrace "thf_unitary_formula" (
  liftM THFUF_logic (parens thf_logic_formula)
  <|> liftM THFUF_quantified thf_quantified_formula
  <|> liftM THFUF_unary thf_unary_formula
  <|> liftM THFUF_conditional thf_conditional
  <|> liftM THFUF_let thf_let
  <|> liftM THFUF_atom thf_atom
  <|> liftM THFUF_tuple thf_tuple
  <?> "thf_unitary_formula"
  )

-- <thf_quantified_formula> ::= <thf_quantification> <thf_unitary_formula>
thf_quantified_formula :: CharParser st THF_quantified_formula
thf_quantified_formula = parserTrace "thf_quantified_formula" (do
    q <- thf_quantification
    f <- thf_unitary_formula
    return $ THF_quantified_formula q f
  <?> "thf_quantified_formula"
  )

-- <thf_quantification>   ::= <thf_quantifier> [<thf_variable_list>] :
-- %----@ (denoting apply) is left-associative and lambda is right-associative.
-- %----^ [X] : ^ [Y] : f @ g (where f is a <thf_apply_formula> and g is a
-- %----<thf_unitary_formula>) should be parsed as: (^ [X] : (^ [Y] : f)) @ g.
-- %----That is, g is not in the scope of either lambda.
thf_quantification :: CharParser st THF_quantification
thf_quantification = parserTrace "thf_quantification" (do
    q <- try thf_quantifier
    vars <- brackets thf_variable_list
    colonT
    return $ THF_quantification q vars
  <?> "thf_quantification"
  )

-- <thf_variable_list>    ::= <thf_variable> | <thf_variable>,<thf_variable_list>
thf_variable_list :: CharParser st THF_variable_list
thf_variable_list = parserTrace "thf_variable_list" (sepByComma1 thf_variable <?> "thf_variable_list"
  )

-- <thf_variable>         ::= <thf_typed_variable> | <variable>
thf_variable :: CharParser st THF_variable
thf_variable = parserTrace "thf_variable" (liftM THFV_typed thf_typed_variable <|> liftM THFV_variable variable
  <?> "thf_variable"
  )

-- <thf_typed_variable>   ::= <variable> : <thf_top_level_type>
thf_typed_variable :: CharParser st THF_typed_variable
thf_typed_variable = parserTrace "thf_typed_variable" (do
    v <- try (variable << colonT)
    tlt <- thf_top_level_type
    return $ THF_typed_variable v tlt
  <?> "thf_typed_variable"
  )

-- %----Unary connectives bind more tightly than binary. The negated formula
-- %----must be ()ed because a ~ is also a term.
-- <thf_unary_formula>    ::= <thf_unary_connective> (<thf_logic_formula>)
thf_unary_formula :: CharParser st THF_unary_formula
thf_unary_formula = parserTrace "thf_unary_formula" (do
    uc <- try (thf_unary_connective << oParenT)
    arg <- thf_logic_formula << cParenT
    return $ THF_unary_formula uc arg
  <?> "thf_unary_formula"
  )

-- <thf_atom>             ::= <thf_function> | <variable> | <defined_term> |
--                            <thf_conn_term>
thf_atom :: CharParser st THF_atom
thf_atom = parserTrace "thf_atom" (
  liftM THF_atom_function thf_function
  <|> liftM THF_atom_variable variable
  <|> liftM THF_atom_defined defined_term
  <|> liftM THF_atom_conn thf_conn_term
  <?> "thf_atom"
  )

-- <thf_function>         ::= <thf_plain_term> | <thf_defined_term> |
--                            <thf_system_term>
-- <thf_function>         ::= <atom> | <functor>(<thf_arguments>) |
--                            <defined_functor>(<thf_arguments>) |
--                            <system_functor>(<thf_arguments>)
thf_function :: CharParser st THF_function
thf_function = parserTrace "thf_function" (do
    f <- try (functor << oParenT)
    args <- thf_arguments
    return $ THFF_functor f args
  <|> liftM THFF_atom atom
  <|> do
    f <- try (defined_functor << oParenT)
    args <- thf_arguments
    return $ THFF_defined f args
  <|> do
    f <- try (system_functor << oParenT)
    args <- thf_arguments
    return $ THFF_system f args
  <?> "thf_function"
  )

-- <thf_conn_term>        ::= <thf_pair_connective> | <assoc_connective> |
--                            <thf_unary_connective>
thf_conn_term :: CharParser st THF_conn_term
thf_conn_term = parserTrace "thf_conn_term" (
  liftM THFC_pair thf_pair_connective
  <|> liftM THFC_assoc assoc_connective
  <|> liftM THFC_unary thf_unary_connective
  <?> "thf_conn_term"
  )

-- <thf_conditional>      ::= $ite(<thf_logic_formula>,<thf_logic_formula>,
--                             <thf_logic_formula>)
thf_conditional :: CharParser st THF_conditional
thf_conditional = parserTrace "thf_conditional" (do
    try (strTok "$ite" << oParenT)
    lf_if <- thf_logic_formula
    commaT
    lf_then <- thf_logic_formula
    commaT
    lf_else <- thf_logic_formula
    cParenT
    return $ THF_conditional lf_if lf_then lf_else
  <?> "thf_conditional"
  )

-- <thf_let>              ::= $let(<thf_unitary_formula>,<thf_formula>)
-- <thf_let>              :== $let(<thf_let_defns>,<thf_formula>)
thf_let :: CharParser st THF_let
thf_let = parserTrace "thf_let" (do
  try (strTok "$let" << oParenT)
  lds <- thf_let_defns
  commaT
  f <- thf_formula
  return $ THF_let lds f
  <?> "thf_let"
  )

-- <thf_let_defns>        :== <thf_let_defn> | [<thf_let_defn_list>]
thf_let_defns :: CharParser st THF_let_defns
thf_let_defns = parserTrace "thf_let_defns" (
  liftM THFLD_many (brackets thf_let_defn_list)
  <|> liftM THFLD_single thf_let_defn
  <?> "thf_let_defns"
  )

-- <thf_let_defn_list>    :== <thf_let_defn> | <thf_let_defn>,<thf_let_defn_list>
thf_let_defn_list :: CharParser st THF_let_defn_list
thf_let_defn_list = parserTrace "thf_let_defn_list" (
  sepByComma1 thf_let_defn
  <?> "thf_let_defn_list"
  )

-- <thf_let_defn>         :== <thf_let_quantified_defn> | <thf_let_plain_defn>
thf_let_defn :: CharParser st THF_let_defn
thf_let_defn = parserTrace "thf_let_defn" (
  liftM THFLD_quantified thf_let_quantified_defn
  <|> liftM THFLD_plain thf_let_plain_defn
  <?> "thf_let_defn"
  )

-- <thf_let_quantified_defn> :== <thf_quantification> (<thf_let_plain_defn>)
thf_let_quantified_defn :: CharParser st THF_let_quantified_defn
thf_let_quantified_defn = parserTrace "thf_let_quantified_defn" (do
    q <- thf_quantification
    lpd <- parens thf_let_plain_defn
    return $ THF_let_quantified_defn q lpd
  <?> "thf_let_quantified_defn"
  )

-- <thf_let_plain_defn>   :== <thf_let_defn_LHS> <assignment> <thf_formula>
thf_let_plain_defn :: CharParser st THF_let_plain_defn
thf_let_plain_defn = parserTrace "thf_let_plain_defn" (do
    lhs <- thf_let_defn_LHS
    assignment
    f <- thf_formula
    return $ THF_let_plain_defn lhs f
  <?> "thf_let_plain_defn"
  )

-- <thf_let_defn_LHS>     :== <thf_plain_term> | <thf_tuple>
-- <thf_let_defn_LHS>     :== <constant> | <functor>(<fof_arguments>) |
--                            <thf_tuple>
-- %----The <fof_arguments> must all be <variable>s, and the <thf_tuple> may
-- %----contain only <constant>s and <functor>(<fof_arguments>)s
thf_let_defn_LHS :: CharParser st THF_let_defn_LHS
thf_let_defn_LHS = parserTrace "thf_let_defn_LHS" (liftM THFLDL_tuple thf_tuple
  <|> do
    f <- try (functor << oParenT)
    args <- fof_arguments
    if onlyVariables args
    then return $ THFLDL_functor f args
    else fail "thf_let_defn_LHS: The <fof_arguments> must all be <variable>s."
  <|> liftM THFLDL_constant constant
  <?> "thf_let_defn_LHS"
  )
  where
    onlyVariables :: FOF_arguments -> Bool
    onlyVariables = all isVariable

    isVariable :: FOF_term -> Bool
    isVariable t = case t of
      FOFT_variable _ -> True
      _ -> False

-- <thf_arguments>        ::= <thf_formula_list>
thf_arguments :: CharParser st THF_arguments
thf_arguments = parserTrace "thf_arguments" (thf_formula_list <?> "thf_arguments"
  )

-- The thf_type_formula rule is ambiguous in the following.
-- Here, it is split into
-- thf_type_formula_typeable and
-- thf_type_formula_constant
-- <thf_type_formula>     ::= <thf_typeable_formula> : <thf_top_level_type>
-- <thf_type_formula>     :== <constant> : <thf_top_level_type>
thf_type_formula :: CharParser st THF_type_formula
thf_type_formula = parserTrace "thf_type_formula" (thf_type_formula_constant <|> thf_type_formula_typeable
  <?> "thf_type_formula"
  )
  where
    -- <thf_type_formula>     ::= <thf_typeable_formula> : <thf_top_level_type>
    thf_type_formula_typeable :: CharParser st THF_type_formula
    thf_type_formula_typeable = parserTrace "thf_type_formula_typeable" (do
        tf <- try (thf_typeable_formula << colonT)
        tlt <- thf_top_level_type
        return $ THFTF_typeable tf tlt
      <?> "thf_type_formula"
      )

    -- <thf_type_formula>     :== <constant> : <thf_top_level_type>
    thf_type_formula_constant :: CharParser st THF_type_formula
    thf_type_formula_constant = parserTrace "thf_type_formula_constant" (do
        c <- try (constant << colonT)
        tlt <- thf_top_level_type
        return $ THFTF_constant c tlt
      <?> "thf_type_formula"
      )

-- <thf_typeable_formula> ::= <thf_atom> | (<thf_logic_formula>)
thf_typeable_formula :: CharParser st THF_typeable_formula
thf_typeable_formula = parserTrace "thf_typeable_formula" (
  liftM THFTF_logic (parens thf_logic_formula) <|> liftM THFTF_atom (thf_atom)
  <?> "thf_typeable_formula"
  )

-- <thf_subtype>          ::= <thf_atom> <subtype_sign> <thf_atom>
thf_subtype :: CharParser st THF_subtype
thf_subtype = parserTrace "thf_subtype" ((do
  c1 <- try (thf_atom << subtype_sign)
  c2 <- thf_atom
  return $ THF_subtype c1 c2)
  <?> "thf_subtype"
  )


-- %----<thf_top_level_type> appears after ":", where a type is being specified
-- %----for a term or variable. <thf_unitary_type> includes <thf_unitary_formula>,
-- %----so the syntax allows just about any lambda expression with "enough"
-- %----parentheses to serve as a type. The expected use of this flexibility is
-- %----parametric polymorphism in types, expressed with lambda abstraction.
-- %----Mapping is right-associative: o > o > o means o > (o > o).
-- %----Xproduct is left-associative: o * o * o means (o * o) * o.
-- %----Union is left-associative: o + o + o means (o + o) + o.
-- <thf_top_level_type>   ::= <thf_unitary_type> | <thf_mapping_type>
thf_top_level_type :: CharParser st THF_top_level_type
thf_top_level_type = parserTrace "thf_top_level_type" (
  liftM THFTLT_mapping thf_mapping_type
  <|> liftM THFTLT_unitary thf_unitary_type
  <?> "thf_top_level_type"
  )

-- <thf_unitary_type>     ::= <thf_unitary_formula> | (<thf_binary_type>)
thf_unitary_type :: CharParser st THF_unitary_type
thf_unitary_type = parserTrace "thf_unitary_type" (
  liftM THFUT_binary (parens thf_binary_type)
  <|> liftM THFUT_unitary thf_unitary_formula
  <?> "thf_unitary_type"
  )

-- <thf_binary_type>      ::= <thf_mapping_type> | <thf_xprod_type> |
--                            <thf_union_type>
thf_binary_type :: CharParser st THF_binary_type
thf_binary_type = parserTrace "thf_binary_type" (
  liftM THFBT_mapping thf_mapping_type
  <|> liftM THFBT_xprod thf_xprod_type
  <|> liftM THFBT_union thf_union_type
  <?> "thf_binary_type"
  )

-- <thf_mapping_type>     ::= <thf_unitary_type> <arrow> <thf_unitary_type> |
--                            <thf_unitary_type> <arrow> <thf_mapping_type>
thf_mapping_type :: CharParser st THF_mapping_type
thf_mapping_type = parserTrace "thf_mapping_type" (do
    t <- try (thf_unitary_type << arrowT)
    ts <- thf_unitary_type `sepBy1` arrowT
    return $ t : ts
  <?> "thf_mapping_type"
  )

-- <thf_xprod_type>       ::= <thf_unitary_type> <star> <thf_unitary_type> |
--                            <thf_xprod_type> <star> <thf_unitary_type>
thf_xprod_type :: CharParser st THF_xprod_type
thf_xprod_type = parserTrace "thf_xprod_type" (do
    t <- try (thf_unitary_type << starT)
    ts <- thf_unitary_type `sepBy1` starT
    return $ t : ts
  <?> "thf_xprod_type"
  )

-- <thf_union_type>       ::= <thf_unitary_type> <plus> <thf_unitary_type> |
--                            <thf_union_type> <plus> <thf_unitary_type>
thf_union_type :: CharParser st THF_union_type
thf_union_type = parserTrace "thf_union_type" (do
    t <- try (thf_unitary_type << plusT)
    ts <- thf_unitary_type `sepBy1` plusT
    return $ t : ts
  <?> "thf_union_type"
  )

-- <thf_sequent>          ::= <thf_tuple> <gentzen_arrow> <thf_tuple> |
--                            (<thf_sequent>)
thf_sequent :: CharParser st THF_sequent
thf_sequent = parserTrace "thf_sequent" (do
    t1 <- try (thf_tuple << gentzen_arrow)
    t2 <- thf_tuple
    return $ THFS_plain t1 t2
  <|> liftM THFS_parens (parens thf_sequent)
  <?> "thf_sequent"
  )

-- <thf_tuple>            ::= [] | [<thf_formula_list>]
thf_tuple :: CharParser st THF_tuple
thf_tuple = parserTrace "thf_tuple" (
  liftM THF_tuple (emptyBrackets <|> brackets thf_formula_list)
  <?> "thf_tuple"
  )

-- <thf_formula_list>     ::= <thf_logic_formula> |
--                            <thf_logic_formula>,<thf_formula_list>
thf_formula_list :: CharParser st THF_formula_list
thf_formula_list = parserTrace "thf_formula_list" (sepByComma1 thf_logic_formula <?> "thf_formula_list"
  )


-- NOTE: not used
-- %----New material for modal logic semantics, not integrated yet
-- -- <logic_defn_rule>      :== <logic_defn_LHS> <assignment> <logic_defn_RHS>
-- logic_defn_rule :: CharParser st Logic_defn_rule
-- logic_defn_rule = (do
--   lhs <- logic_defn_LHS
--   assignment
--   rhs <- logic_defn_RHS
--   return $ Logic_defn_rule lhs rhs)
--   <?> "logic_defn_rule"
--
-- NOTE: not used
-- -- <logic_defn_LHS>       :== <logic_defn_value> | <thf_top_level_type>  | <name>
-- -- <logic_defn_LHS>       :== $constants | $quantification | $consequence |
-- --                            $modalities
-- logic_defn_LHS :: CharParser st Logic_defn_LHS
-- logic_defn_LHS = (constantsChoice
--   [("$constants", LDLC_constants),
--    ("$quantification", LDLC_quantification),
--    ("$consequence", LDLC_consequence),
--    ("$modalities", LDLC_modalities)])
--   <|> liftM Logic_defn_LHS_value logic_defn_value
--   <|> liftM Logic_defn_LHS_THF_Top_level_type thf_top_level_type
--   <|> liftM Logic_defn_LHS_name name
--   <?> "logic_defn_LHS"
--
-- NOTE: not used
-- -- <logic_defn_RHS>       :== <logic_defn_value> | <thf_unitary_formula>
-- logic_defn_RHS :: CharParser st Logic_defn_RHS
-- logic_defn_RHS = logic_defn_value' <|> thf_unitary_formula'
--   <?> "logic_defn_RHS"
--   where
--     logic_defn_value' = liftM Logic_defn_RHS_value logic_defn_value
--     thf_unitary_formula' =
--       liftM Logic_defn_RNG_THF_Unitary_forumla thf_unitary_formula
--
-- NOTE: not used
-- -- <logic_defn_value>     :== <defined_constant>
-- -- <logic_defn_value>     :== $rigid | $flexible |
--                            -- $constant | $varying | $cumulative | $decreasing |
--                            -- $local | $global |
--                            -- $modal_system_K | $modal_system_T | $modal_system_D |
--                            -- $modal_system_S4 | $modal_system_S5 |
--                            -- $modal_axiom_K | $modal_axiom_T | $modal_axiom_B |
--                            -- $modal_axiom_D | $modal_axiom_4 | $modal_axiom_5
-- logic_defn_value :: CharParser st Logic_defn_value
-- logic_defn_value = constantsChoice
--   [("$rigid", Rigid),
--    ("$flexible", Flexible),
--    ("$constant", Constant),
--    ("$varying", Varying),
--    ("$cumulative", Cumulative),
--    ("$decreasing", Decreasing),
--    ("$local", Local),
--    ("$global", Global),
--    ("$modal_system_K", Modal_system_K),
--    ("$modal_system_T", Modal_system_T),
--    ("$modal_system_D", Modal_system_D),
--    ("$modal_system_S4", Modal_system_S4),
--    ("$modal_system_S5", Modal_system_S5),
--    ("$modal_axiom_K", Modal_axiom_K),
--    ("$modal_axiom_T", Modal_axiom_T),
--    ("$modal_axiom_B", Modal_axiom_B),
--    ("$modal_axiom_D", Modal_axiom_D),
--    ("$modal_axiom_4", Modal_axiom_4),
--    ("$modal_axiom_5", Modal_axiom_5)]
--   <?> "logic_defn_value"
--

{- -----------------------------------------------------------------------------
TFX formulae
----------------------------------------------------------------------------- -}
-- <tfx_formula>          ::= <tfx_logic_formula> | <thf_sequent>
tfx_formula :: CharParser st TFX_formula
tfx_formula = parserTrace "tfx_formula" (
  liftM TFXF_logic tfx_logic_formula
  <|> liftM TFXF_sequent thf_sequent
  <?> "tfx_formula"
  )

-- <tfx_logic_formula>    ::= <thf_logic_formula>
-- % <tfx_logic_formula>    ::= <thf_binary_formula> | <thf_unitary_formula> |
-- %                            <tff_typed_atom> | <tff_subtype>
tfx_logic_formula :: CharParser st TFX_logic_formula
tfx_logic_formula = parserTrace "tfx_logic_formula" (
  liftM TFXLF_unitary thf_unitary_formula
  <|> liftM TFXLF_typed tff_typed_atom
  <|> liftM TFXLF_subtype tff_subtype
  <|> do
    f <- thf_unitary_formula
    liftM TFXLF_binary (thf_binary_formula f)
  <?> "tfx_logic_formula"
  )

{- -----------------------------------------------------------------------------
TFF formulae
----------------------------------------------------------------------------- -}
-- <tff_formula>          ::= <tff_logic_formula> | <tff_typed_atom> |
--                            <tff_sequent>
tff_formula :: CharParser st TFF_formula
tff_formula = parserTrace "tff_formula" (
  liftM TFFF_atom tff_typed_atom
  <|> liftM TFFF_logic tff_logic_formula
  <|> liftM TFFF_sequent tff_sequent
  <?> "tff_formula"
  )

-- <tff_logic_formula>    ::= <tff_binary_formula> | <tff_unitary_formula>
-- <tff_logic_formula>    ::= <tff_binary_formula> | <tff_unitary_formula> |
--                            <tff_subtype>
tff_logic_formula :: CharParser st TFF_logic_formula
tff_logic_formula = parserTrace "tff_logic_formula" (
  liftM TFFLF_subtype tff_subtype
  <|> do
    f <- tff_unitary_formula
    (liftM TFFLF_binary (tff_binary_formula f)
      <|> return (TFFLF_unitary f))
  <?> "tff_logic_formula"
  )

-- <tff_binary_formula>   ::= <tff_binary_nonassoc> | <tff_binary_assoc>
tff_binary_formula :: TFF_unitary_formula -> CharParser st TFF_binary_formula
tff_binary_formula f = parserTrace "tff_binary_formula" (
  liftM TFFBF_nonassoc (tff_binary_nonassoc f)
  <|> liftM TFFBF_assoc (tff_binary_assoc f)
  <?> "tff_binary_formula"
  )

-- <tff_binary_nonassoc>  ::= <tff_unitary_formula> <binary_connective>
--                            <tff_unitary_formula>
tff_binary_nonassoc :: TFF_unitary_formula -> CharParser st TFF_binary_nonassoc
tff_binary_nonassoc f1 = parserTrace "tff_binary_nonassoc" (do
    bc <- try binary_connective
    f2 <- tff_unitary_formula
    return $ TFF_binary_nonassoc bc f1 f2
  <?> "tff_binary_nonassoc"
  )

-- <tff_binary_assoc>     ::= <tff_or_formula> | <tff_and_formula>
tff_binary_assoc :: TFF_unitary_formula -> CharParser st TFF_binary_assoc
tff_binary_assoc f = parserTrace "tff_binary_assoc" (
  liftM TFFBA_or (tff_or_formula f)
  <|> liftM TFFBA_and (tff_and_formula f)
  <?> "tff_binary_assoc"
  )

-- <tff_or_formula>       ::= <tff_unitary_formula> <vline> <tff_unitary_formula> |
--                            <tff_or_formula> <vline> <tff_unitary_formula>
tff_or_formula :: TFF_unitary_formula -> CharParser st TFF_or_formula
tff_or_formula f = parserTrace "tff_or_formula" (do
    try vline
    fs <- tff_unitary_formula `sepBy1` vline
    return $ f : fs
  <?> "tff_or_formula"
  )

-- <tff_and_formula>      ::= <tff_unitary_formula> & <tff_unitary_formula> |
--                            <tff_and_formula> & <tff_unitary_formula>
tff_and_formula :: TFF_unitary_formula -> CharParser st TFF_and_formula
tff_and_formula f = parserTrace "tff_and_formula" (do
    try andT
    fs <- tff_unitary_formula `sepBy1` andT
    return $ f : fs
  <?> "tff_and_formula"
  )

--- <tff_unitary_formula>  ::= <tff_quantified_formula> | <tff_unary_formula> |
---                            <atomic_formula> | <tff_conditional> | <tff_let> |
---                            (<tff_logic_formula>)
-- <tff_unitary_formula>  ::= <tff_quantified_formula> | <tff_unary_formula> |
--                            <tff_atomic_formula> | <tff_conditional> |
--                            <tff_let> | (<tff_logic_formula>)
tff_unitary_formula :: CharParser st TFF_unitary_formula
tff_unitary_formula = parserTrace "tff_unitary_formula" (
  liftM TFFUF_quantified tff_quantified_formula
  <|> liftM TFFUF_unary tff_unary_formula
  <|> liftM TFFUF_atomic tff_atomic_formula
  <|> liftM TFFUF_conditional tff_conditional
  <|> liftM TFFUF_let tff_let
  -- <|> liftM TFFUF_logic (try $ parens tff_logic_formula) -- TODO: remove
  <|> liftM TFFUF_logic (parens tff_logic_formula) -- TODO: add try (above line)
  <?> "tff_unitary_formula"
  )

-- <tff_quantified_formula> ::= <fof_quantifier> [<tff_variable_list>] :
--                            <tff_unitary_formula>
tff_quantified_formula :: CharParser st TFF_quantified_formula
tff_quantified_formula = parserTrace "tff_quantified_formula" (do
    q <- try fof_quantifier
    vars <- brackets tff_variable_list
    colonT
    f <- tff_unitary_formula
    return $ TFF_quantified_formula q vars f
  <?> "tff_quantified_formula"
  )

-- <tff_variable_list>    ::= <tff_variable> | <tff_variable>,<tff_variable_list>
tff_variable_list :: CharParser st TFF_variable_list
tff_variable_list = parserTrace "tff_variable_list" (sepByComma1 tff_variable <?> "tff_variable_list"
  )

-- <tff_variable>         ::= <tff_typed_variable> | <variable>
tff_variable :: CharParser st TFF_variable
tff_variable = parserTrace "tff_variable" (
  liftM TFFV_typed tff_typed_variable
  <|> liftM TFFV_variable variable
  <?> "tff_variable"
  )

-- <tff_typed_variable>   ::= <variable> : <tff_atomic_type>
tff_typed_variable :: CharParser st TFF_typed_variable
tff_typed_variable = parserTrace "tff_typed_variable" (do
    v <- try (variable << colonT)
    at <- tff_atomic_type
    return $ TFF_typed_variable v at
  <?> "tff_typed_variable"
  )

-- <tff_unary_formula>    ::= <unary_connective> <tff_unitary_formula> |
--                            <fof_infix_unary>
tff_unary_formula :: CharParser st TFF_unary_formula
tff_unary_formula = parserTrace "tff_unary_formula" (do
    uc <- try unary_connective
    uf <- tff_unitary_formula
    return $ TFFUF_connective uc uf
  <|> liftM TFFUF_infix fof_infix_unary
  <?> "tff_unary_formula"
  )

-- <tff_atomic_formula>   ::= <fof_atomic_formula>
tff_atomic_formula :: CharParser st TFF_atomic_formula
tff_atomic_formula = parserTrace "tff_atomic_formula" (fof_atomic_formula
  <?> "tff_atomic_formula"
  )

-- <tff_conditional>      ::= $ite_f(<tff_logic_formula>,<tff_logic_formula>,
--                            <tff_logic_formula>)
tff_conditional :: CharParser st TFF_conditional
tff_conditional = parserTrace "tff_conditional" ((do
  strTok "$ite_f"
  parens $ do
    lf_if <- tff_logic_formula
    commaT
    lf_then <- tff_logic_formula
    commaT
    lf_else <- tff_logic_formula
    return $ TFF_conditional lf_if lf_then lf_else)
  <?> "tff_conditional"
  )

-- <tff_let>              ::= $let_tf(<tff_let_term_defns>,<tff_formula>) |
--                            $let_ff(<tff_let_formula_defns>,<tff_formula>)
tff_let :: CharParser st TFF_let
tff_let = parserTrace "tff_let" (do
    strTok "$let_tf"
    parens $ do
      ltds <- tff_let_term_defns
      commaT
      f <- tff_formula
      return $ TFF_let_term_defns ltds f
  <|> do
    strTok "$let_ff"
    parens $ do
      lfds <- tff_let_formula_defns
      commaT
      f <- tff_formula
      return $ TFF_let_formula_defns lfds f
  <?> "tff_let"
  )

-- <tff_let_term_defns>   ::= <tff_let_term_defn> | [<tff_let_term_list>]
tff_let_term_defns :: CharParser st TFF_let_term_defns
tff_let_term_defns = parserTrace "tff_let_term_defns" (
  liftM TFFLTD_single tff_let_term_defn
  <|> liftM TFFLTD_many (brackets tff_let_term_list)
  <?> "tff_let_term_defns"
  )

-- <tff_let_term_list>    ::= <tff_let_term_defn> |
--                            <tff_let_term_defn>,<tff_let_term_list>
tff_let_term_list :: CharParser st TFF_let_term_list
tff_let_term_list = parserTrace "tff_let_term_list" (sepByComma1 tff_let_term_defn
  <?> "tff_let_term_list"
  )

-- <tff_let_term_defn>    ::= ! [<tff_variable_list>] : <tff_let_term_defn> |
--                            <tff_let_term_binding>
tff_let_term_defn :: CharParser st TFF_let_term_defn
tff_let_term_defn = parserTrace "tff_let_term_defn" (do
    charTok '!' >> notFollowedBy (oneOf "!=>")
    vars <- brackets tff_variable_list
    colonT
    ltd <- tff_let_term_defn
    return $ TFFLTD_variable vars ltd
  <|> liftM TFFLTD_binding tff_let_term_binding
  <?> "tff_let_term_defn"
  )

-- <tff_let_term_binding> ::= <fof_plain_term> = <fof_term> |
--                            (<tff_let_term_binding>)
tff_let_term_binding :: CharParser st TFF_let_term_binding
tff_let_term_binding = parserTrace "tff_let_term_binding" (do
    pt <- try (fof_plain_term << charTok '=')
    t <- fof_term
    return $ TFFLTB_plain pt t
  <|> liftM TFFLTB_binding (parens tff_let_term_binding)
  <?> "tff_let_term_binding"
  )
-- <tff_let_formula_defns> ::= <tff_let_formula_defn> | [<tff_let_formula_list>]
-- <tff_let_formula_defns> ::= <tff_let_formula_defn> | [<tff_let_formula_list>]
tff_let_formula_defns :: CharParser st TFF_let_formula_defns
tff_let_formula_defns = parserTrace "tff_let_formula_defns" (
  liftM TFFLFD_single tff_let_formula_defn
  <|> liftM TFFLFD_many (brackets tff_let_formula_list)
  <?> "tff_let_formula_defns"
  )

-- <tff_let_formula_list> ::= <tff_let_formula_defn> |
--                            <tff_let_formula_defn>,<tff_let_formula_list>
tff_let_formula_list :: CharParser st TFF_let_formula_list
tff_let_formula_list = parserTrace "tff_let_formula_list" (sepByComma1 tff_let_formula_defn <?> "tff_let_formula_list"
  )

-- <tff_let_formula_defn> ::= ! [<tff_variable_list>] : <tff_let_formula_defn> |
--                            <tff_let_formula_binding>
tff_let_formula_defn :: CharParser st TFF_let_formula_defn
tff_let_formula_defn = parserTrace "tff_let_formula_defn" (do
    charTok '!' >> notFollowedBy (oneOf "!=>")
    vars <- brackets tff_variable_list
    colonT
    lfd <- tff_let_formula_defn
    return $ TFFLFD_variable vars lfd
  <|> liftM TFFLFD_binding tff_let_formula_binding
  <?> "tff_let_formula_defn"
  )

-- <tff_let_formula_binding> ::= <plain_atomic_formula> <=> <tff_unitary_formula> |
--                            (<tff_let_formula_binding>)
-- <tff_let_formula_binding> ::= <fof_plain_atomic_formula> <=>
--                            <tff_unitary_formula> | (<tff_let_formula_binding>)
tff_let_formula_binding :: CharParser st TFF_let_formula_binding
tff_let_formula_binding = parserTrace "tff_let_formula_binding" (do
    paf <- try (fof_plain_atomic_formula << strTok "<=>")
    uf <- tff_unitary_formula
    return $ TFFLFB_plain paf uf
  <|> liftM TFFLFB_binding (parens tff_let_formula_binding)
  <?> "tff_let_formula_binding"
  )

-- <tff_sequent>          ::= <tff_formula_tuple> <gentzen_arrow>
--                            <tff_formula_tuple> | (<tff_sequent>)
tff_sequent :: CharParser st TFF_sequent
tff_sequent = parserTrace "tff_sequent" (do
    t1 <- try (tff_formula_tuple << gentzen_arrow)
    t2 <- tff_formula_tuple
    return $ TFFS_plain t1 t2
  <|> liftM TFFS_parens (parens tff_sequent)
  <?> "tff_sequent"
  )

-- <tff_formula_tuple>    ::= [] | [<tff_formula_tuple_list>]
tff_formula_tuple :: CharParser st TFF_formula_tuple
tff_formula_tuple = parserTrace "tff_formula_tuple" (
  liftM TFF_formula_tuple (emptyBrackets <|> brackets tff_formula_tuple_list)
  <?> "tff_formula_tuple"
  )

-- <tff_formula_tuple_list> ::= <tff_logic_formula> |
--                            <tff_logic_formula>,<tff_formula_tuple_list>
tff_formula_tuple_list :: CharParser st TFF_formula_tuple_list
tff_formula_tuple_list = parserTrace "tff_formula_tuple_list" (
  sepByComma1 tff_logic_formula
  <?> "tff_formula_tuple_list"
  )

-- <tff_typed_atom>       ::= <untyped_atom> : <tff_top_level_type> |
--                            (<tff_typed_atom>)
tff_typed_atom :: CharParser st TFF_typed_atom
tff_typed_atom = parserTrace "tff_typed_atom" (do
    ua <- try (untyped_atom << colonT)
    tlt <- tff_top_level_type
    return $ TFFTA_plain ua tlt
  <|> liftM TFFTA_parens (try (parens tff_typed_atom)) -- TODO: remove
  -- <|> liftM TFFTA_parens (parens tff_typed_atom) -- TODO: add try (above line)
  <?> "tff_typed_atom"
  )

-- <tff_subtype>          ::= <untyped_atom> <subtype_sign> <atom>
tff_subtype :: CharParser st TFF_subtype
tff_subtype = parserTrace "tff_subtype" (do
    ua <- try (untyped_atom << subtype_sign)
    a <- atom
    return $ TFF_subtype ua a
  <?> "tff_subtype"
  )

-- <tff_top_level_type>   ::= <tff_atomic_type> | <tff_mapping_type> |
--                            <tf1_quantified_type> | (<tff_top_level_type>)
tff_top_level_type :: CharParser st TFF_top_level_type
tff_top_level_type = parserTrace "tff_top_level_type" (
  liftM TFFTLT_mapping tff_mapping_type
  <|> liftM TFFTLT_quantified tf1_quantified_type
  <|> liftM TFFTLT_atomic tff_atomic_type
  -- <|> liftM TFFTLT_parens (try (parens tff_top_level_type)) -- TODO: remove
  <|> liftM TFFTLT_parens (parens tff_top_level_type) -- TODO: add try (above line)
  <?> "tff_top_level_type"
  )

-- <tf1_quantified_type>  ::= !> [<tff_variable_list>] : <tff_monotype>
tf1_quantified_type :: CharParser st TF1_quantified_type
tf1_quantified_type = parserTrace "tf1_quantified_type" (do
    strTok "!>"
    vars <- brackets tff_variable_list
    colonT
    mt <- tff_monotype
    return $ TF1_quantified_type vars mt
  <?> "tf1_quantified_type"
  )

-- <tff_monotype>         ::= <tff_atomic_type> | (<tff_mapping_type>)
tff_monotype :: CharParser st TFF_monotype
tff_monotype = parserTrace "tff_monotype" (
  liftM TFFMT_atomic tff_atomic_type
  <|> liftM TFFMT_mapping (parens tff_mapping_type)
  <?> "tff_monotype"
  )

-- <tff_unitary_type>     ::= <tff_atomic_type> | (<tff_xprod_type>)
tff_unitary_type :: CharParser st TFF_unitary_type
tff_unitary_type = parserTrace "tff_unitary_type" (
  liftM TFFUT_xprod (parens tff_xprod_type)
  <|> liftM TFFUT_atomic tff_atomic_type
  <?> "tff_unitary_type"
  )

-- <tff_atomic_type>      ::= <atomic_word> | <defined_type> |
--                            <atomic_word>(<tff_type_arguments>) | <variable>
-- <tff_atomic_type>      ::= <type_constant> | <defined_type> |
--                            <type_functor>(<tff_type_arguments>) | <variable>
tff_atomic_type :: CharParser st TFF_atomic_type
tff_atomic_type = parserTrace "tff_atomic_type" (
  functor_args
  <|> liftM TFFAT_constant type_constant
  <|> liftM TFFAT_defined defined_type
  <|> liftM TFFAT_variable variable
  <?> "tff_atomic_type"
  )
  where
    functor_args = do
      aw <- try (type_functor << oParenT)
      args <- tff_type_arguments << cParenT
      return $ TFFAT_functor aw args

-- <tff_type_arguments>   ::= <tff_atomic_type> |
--                            <tff_atomic_type>,<tff_type_arguments>
tff_type_arguments :: CharParser st TFF_type_arguments
tff_type_arguments = parserTrace "tff_type_arguments" (
  sepByComma1 tff_atomic_type
  <?> "tff_type_arguments"
  )

-- <tff_mapping_type>     ::= <tff_unitary_type> <arrow> <tff_atomic_type>
tff_mapping_type :: CharParser st TFF_mapping_type
tff_mapping_type = parserTrace "tff_mapping_type" (do
    t1 <- try (tff_unitary_type << arrowT)
    t2 <- tff_atomic_type
    return $ TFF_mapping_type t1 t2
  <?> "tff_mapping_type"
  )

-- <tff_xprod_type>       ::= <tff_unitary_type> <star> <tff_atomic_type> |
--                            <tff_xprod_type> <star> <tff_atomic_type>
tff_xprod_type :: CharParser st TFF_xprod_type
tff_xprod_type = parserTrace "tff_xprod_type" (do
    ut <- try (tff_unitary_type << starT)
    ats <- tff_atomic_type `sepBy1` starT
    return $ TFF_xprod_type ut ats
  <?> "tff_xprod_type"
  )


{- -----------------------------------------------------------------------------
TCF formulae
----------------------------------------------------------------------------- -}

-- <tcf_formula>          ::= <tcf_logic_formula> | <tff_typed_atom>
tcf_formula :: CharParser st TCF_formula
tcf_formula = parserTrace "tcf_formula" (
  liftM TCFF_logic tcf_logic_formula
  <|> liftM TCFF_atom tff_typed_atom
  <?> "tcf_formula"
  )

-- <tcf_logic_formula>    ::= <tcf_quantified_formula> | <cnf_formula>
tcf_logic_formula :: CharParser st TCF_logic_formula
tcf_logic_formula = parserTrace "tcf_logic_formula" (
  liftM TCFLF_quantified tcf_quantified_formula
  <|> liftM TCFLF_cnf cnf_formula
  <?> "tcf_logic_formula"
  )

-- <tcf_quantified_formula> ::= ! [<tff_variable_list>] : <cnf_formula>
tcf_quantified_formula :: CharParser st TCF_quantified_formula
tcf_quantified_formula = parserTrace "tcf_quantified_formula" (do
    charTok '!' >> notFollowedBy (oneOf "!=>")
    vars <- brackets tff_variable_list
    colonT
    f <- cnf_formula
    return $ TCF_quantified vars f
  <?> "tcf_quantified_formula"
  )

{- -----------------------------------------------------------------------------
FOF formulae
----------------------------------------------------------------------------- -}
-- <fof_formula>          ::= <fof_logic_formula> | <fof_sequent>
fof_formula :: CharParser st FOF_formula
fof_formula = parserTrace "fof_formula" (
  liftM FOFF_logic fof_logic_formula
  <|> liftM FOFF_sequent fof_sequent
  <?> "fof_formula"
  )

-- <fof_logic_formula>    ::= <fof_binary_formula> | <fof_unitary_formula>
fof_logic_formula :: CharParser st FOF_logic_formula
fof_logic_formula = parserTrace "fof_logic_formula" (do
    f <- fof_unitary_formula
    (liftM FOFLF_binary (fof_binary_formula f)
      <|> return (FOFLF_unitary f))
  <?> "fof_logic_formula"
  )

-- %----Future answer variable ideas | <answer_formula>
-- <fof_binary_formula>   ::= <fof_binary_nonassoc> | <fof_binary_assoc>
fof_binary_formula :: FOF_unitary_formula -> CharParser st FOF_binary_formula
fof_binary_formula f = parserTrace "fof_binary_formula" (
  liftM FOFBF_nonassoc (fof_binary_nonassoc f)
  <|> liftM FOFBF_assoc (fof_binary_assoc f)
  <?> "fof_binary_formula"
  )

-- %----Only some binary connectives are associative
-- %----There's no precedence among binary connectives
-- <fof_binary_nonassoc>  ::= <fof_unitary_formula> <binary_connective>
--                            <fof_unitary_formula>
fof_binary_nonassoc :: FOF_unitary_formula -> CharParser st FOF_binary_nonassoc
fof_binary_nonassoc f1 = parserTrace "fof_binary_nonassoc" (do
    bc <- try binary_connective
    f2 <- fof_unitary_formula
    return $ FOF_binary_nonassoc bc f1 f2
  <?> "fof_binary_nonassoc"
  )

-- <fof_binary_assoc>     ::= <fof_or_formula> | <fof_and_formula>
fof_binary_assoc :: FOF_unitary_formula -> CharParser st FOF_binary_assoc
fof_binary_assoc f = parserTrace "fof_binary_assoc" (
  liftM FOFBA_or (fof_or_formula f)
  <|> liftM FOFBA_and (fof_and_formula f)
  <?> "fof_binary_assoc"
  )

-- <fof_or_formula>       ::= <fof_unitary_formula> <vline> <fof_unitary_formula> |
--                            <fof_or_formula> <vline> <fof_unitary_formula>
fof_or_formula :: FOF_unitary_formula -> CharParser st FOF_or_formula
fof_or_formula f = parserTrace "fof_or_formula" (do
    try vline
    fs <- fof_unitary_formula `sepBy1` vline
    return $ f : fs
  <?> "fof_or_formula"
  )

-- <fof_and_formula>      ::= <fof_unitary_formula> & <fof_unitary_formula> |
--                            <fof_and_formula> & <fof_unitary_formula>
fof_and_formula :: FOF_unitary_formula -> CharParser st FOF_and_formula
fof_and_formula f = parserTrace "fof_and_formula" (do
    try andT
    fs <- fof_unitary_formula `sepBy1` andT
    return $ f : fs
  <?> "fof_and_formula"
  )

-- %----<fof_unitary_formula> are in ()s or do not have a <binary_connective> at
-- %----the top level.
-- <fof_unitary_formula>  ::= <fof_quantified_formula> | <fof_unary_formula> |
--                            <fof_atomic_formula> | (<fof_logic_formula>)
fof_unitary_formula :: CharParser st FOF_unitary_formula
fof_unitary_formula = parserTrace "fof_unitary_formula" (
  liftM FOFUF_logic (parens fof_logic_formula)
  <|> liftM FOFUF_unary fof_unary_formula
  <|> liftM FOFUF_quantified fof_quantified_formula
  <|> liftM FOFUF_atomic fof_atomic_formula
  <?> "fof_unitary_formula"
  )

-- <fof_quantified_formula> ::= <fof_quantifier> [<fof_variable_list>] :
--                            <fof_unitary_formula>
fof_quantified_formula :: CharParser st FOF_quantified_formula
fof_quantified_formula = parserTrace "fof_quantified_formula" (do
  q <- try fof_quantifier
  vars <- brackets fof_variable_list
  colonT
  f <- fof_unitary_formula
  return $ FOF_quantified_formula q vars f
  )


-- <fof_variable_list>    ::= <variable> | <variable>,<fof_variable_list>
fof_variable_list :: CharParser st FOF_variable_list
fof_variable_list = parserTrace "fof_variable_list" (sepByComma1 variable <?> "fof_variable_list"
  )

-- <fof_unary_formula>    ::= <unary_connective> <fof_unitary_formula> |
--                            <fof_infix_unary>
fof_unary_formula :: CharParser st FOF_unary_formula
fof_unary_formula = parserTrace "fof_unary_formula" (do
    uc <- try unary_connective
    uf <- fof_unitary_formula
    return $ FOFUF_connective uc uf
  <|> liftM FOFUF_infix fof_infix_unary
  <?> "fof_unary_formula"
  )

-- <fof_infix_unary>      ::= <fof_term> <infix_inequality> <fof_term>
fof_infix_unary :: CharParser st FOF_infix_unary
fof_infix_unary = parserTrace "fof_infix_unary" (do
    t1 <- try (fof_term << infix_inequality)
    t2 <- fof_term
    return $ FOF_infix_unary t1 t2
  <?> "fof_infix_unary"
  )

-- <fof_atomic_formula>   ::= <fof_plain_atomic_formula> |
--                            <fof_defined_atomic_formula> |
--                            <fof_system_atomic_formula>
fof_atomic_formula :: CharParser st FOF_atomic_formula
fof_atomic_formula = parserTrace "fof_atomic_formula" (
  liftM FOFAT_defined fof_defined_atomic_formula
  <|> liftM FOFAT_system fof_system_atomic_formula
  <|> liftM FOFAT_plain fof_plain_atomic_formula
  <?> "fof_atomic_formula"
  )

-- <fof_plain_atomic_formula> ::= <fof_plain_term>
-- <fof_plain_atomic_formula> :== <proposition> | <predicate>(<fof_arguments>)
fof_plain_atomic_formula :: CharParser st FOF_plain_atomic_formula
fof_plain_atomic_formula = parserTrace "fof_plain_atomic_formula" (do
    p <- try (predicate << oParenT)
    args <- fof_arguments << cParenT
    return $ FOFPAF_predicate p args
  <|> liftM FOFPAF_proposition proposition
  <?> "fof_plain_atomic_formula"
  )

-- <fof_defined_atomic_formula> ::= <fof_defined_plain_formula> |
--                            <fof_defined_infix_formula>
fof_defined_atomic_formula :: CharParser st FOF_defined_atomic_formula
fof_defined_atomic_formula = parserTrace "fof_defined_atomic_formula" (
  liftM FOFDAF_plain fof_defined_plain_formula
  <|> liftM FOFDAF_infix fof_defined_infix_formula
  <?> "fof_defined_atomic_formula"
  )

-- <fof_defined_plain_formula> ::= <fof_defined_plain_term>
-- <fof_defined_plain_formula> :== <defined_proposition> |
--                            <defined_predicate>(<fof_arguments>)
fof_defined_plain_formula :: CharParser st FOF_defined_plain_formula
fof_defined_plain_formula = parserTrace "fof_defined_plain_formula" (do
    p <- try (defined_predicate << oParenT)
    args <- fof_arguments << cParenT
    return $ FOFDPF_predicate p args
  <|> liftM FOFDPF_proposition defined_proposition
  <?> "fof_defined_plain_formula"
  )

-- <fof_defined_infix_formula> ::= <fof_term> <defined_infix_pred> <fof_term>
fof_defined_infix_formula :: CharParser st FOF_defined_infix_formula
fof_defined_infix_formula = parserTrace "fof_defined_infix_formula" (do
    (t1, i) <- try $ do
      t1 <- fof_term
      i <- defined_infix_pred
      return (t1, i)
    t2 <- fof_term
    return $ FOF_defined_infix_formula i t1 t2
  <?> "fof_defined_infix_formula"
  )

-- %----System terms have system specific interpretations
-- <fof_system_atomic_formula> ::= <fof_system_term>
fof_system_atomic_formula :: CharParser st FOF_system_atomic_formula
fof_system_atomic_formula = parserTrace "fof_system_atomic_formula" (
  liftM FOF_system_atomic_formula fof_system_term
  <?> "fof_system_atomic_formula"
  )

-- <fof_plain_term>       ::= <constant> | <functor>(<fof_arguments>)
fof_plain_term :: CharParser st FOF_plain_term
fof_plain_term = parserTrace "fof_plain_term" (do
    f <- try (functor << oParenT)
    args <- fof_arguments << cParenT
    return $ FOFPT_functor f args
  <|> liftM FOFPT_constant constant
  <?> "fof_plain_term"
  )

-- %----Defined terms have TPTP specific interpretations
-- <fof_defined_term>     ::= <defined_term> | <fof_defined_atomic_term>
fof_defined_term :: CharParser st FOF_defined_term
fof_defined_term = parserTrace "fof_defined_term" (
  liftM FOFDT_term defined_term
  <|> liftM FOFDT_atomic fof_defined_atomic_term
  <?> "fof_defined_term"
  )

-- <fof_defined_atomic_term>  ::= <fof_defined_plain_term>
-- %----None yet             | <defined_infix_term>
fof_defined_atomic_term :: CharParser st FOF_defined_atomic_term
fof_defined_atomic_term = parserTrace "fof_defined_atomic_term" (
  liftM FOFDAT_plain fof_defined_plain_term
  <?> "fof_defined_atomic_term"
  )

-- %----None yet <defined_infix_term> ::= <fof_term> <defined_infix_func> <fof_term>
-- data Defined_infix_term = Defined_infix_term Defined_infix_func FOF_term FOF_term
--                           deriving (Show, Ord, Eq, Data, Typeable)

-- %----None yet <defined_infix_func> ::=
-- data Defined_infix_func =

-- <fof_defined_plain_term>   ::= <defined_constant> |
--                            <defined_functor>(<fof_arguments>)
-- %----Add $tuple for tuples, because [<fof_arguments>] doesn't work.
fof_defined_plain_term :: CharParser st FOF_defined_plain_term
fof_defined_plain_term = parserTrace "fof_defined_plain_term" (do
    f <- try (defined_functor << oParenT)
    args <- fof_arguments << cParenT
    return $ FOFDPT_functor f args
  <|> liftM FOFDPT_constant defined_constant
  <?> "fof_defined_plain_term"
  )

-- %----System terms have system specific interpretations
-- <fof_system_term>      ::= <system_constant> | <system_functor>(<fof_arguments>)
fof_system_term :: CharParser st FOF_system_term
fof_system_term = parserTrace "fof_system_term" (do
    f <- try (system_functor << oParenT)
    args <- fof_arguments << cParenT
    return $ FOFST_functor f args
  <|> liftM FOFST_constant system_constant
  <?> "fof_system_term"
  )

-- %----Arguments recurse back up to terms (this is the FOF world here)
-- <fof_arguments>        ::= <fof_term> | <fof_term>,<fof_arguments>
fof_arguments :: CharParser st FOF_arguments
fof_arguments = parserTrace "fof_arguments" (
  sepByComma1 fof_term
  <?> "fof_arguments"
  )

-- %----These are terms used as arguments. Not the entry point for terms because
-- %----<fof_plain_term> is also used as <fof_plain_atomic_formula>
-- <fof_term>             ::= <fof_function_term> | <variable> |
--                            <tff_conditional_term> | <tff_let_term>
fof_term :: CharParser st FOF_term
fof_term = parserTrace "fof_term" (
  liftM FOFT_let tff_let_term
  <|> liftM FOFT_conditional tff_conditional_term
  <|> liftM FOFT_variable variable
  <|> liftM FOFT_function fof_function_term
  <?> "fof_term"
  )

-- %% DAMN THIS JUST WON'T WORK | <tuple_term>
-- %----<tuple_term> is for TFF only, but it's here because it's used in
-- %----<fof_atomic_formula>, which is also used as <tff_atomic_formula>.
-- % <tuple_term>           ::= [] | [<fof_arguments>]
-- <fof_function_term>    ::= <fof_plain_term> | <fof_defined_term> |
--                            <fof_system_term>
fof_function_term :: CharParser st FOF_function_term
fof_function_term = parserTrace "fof_function_term" (
  liftM FOFFT_system fof_system_term
  <|> liftM FOFFT_defined fof_defined_term
  <|> liftM FOFFT_plain fof_plain_term
  <?> "fof_function_term"
  )

-- %----Conditional terms should be used by only TFF.
-- <tff_conditional_term> ::= $ite_t(<tff_logic_formula>,<fof_term>,<fof_term>)
tff_conditional_term :: CharParser st TFF_conditional_term
tff_conditional_term = parserTrace "tff_conditional_term" (do
    strTok "$ite_t"
    oParenT
    f_if <- tff_logic_formula
    commaT
    t_then <- fof_term
    commaT
    t_else <- fof_term
    cParenT
    return $ TFF_conditional_term f_if t_then t_else
  <?> "tff_conditional_term"
  )

-- %----Let terms should be used by only TFF. $let_ft is for use when there is
-- %----a $ite_t in the <fof_term>. See the commentary for $let_tf and $let_ff.
-- <tff_let_term>         ::= $let_ft(<tff_let_formula_defns>,<fof_term>) |
--                            $let_tt(<tff_let_term_defns>,<fof_term>)
tff_let_term :: CharParser st TFF_let_term
tff_let_term = parserTrace "tff_let_term" (do
    strTok "$let_ft"
    oParenT
    defns <- tff_let_formula_defns
    commaT
    t <- fof_term
    cParenT
    return $ TFFLT_formula defns t
  <|> do
    strTok "$let_tt"
    oParenT
    defns <- tff_let_term_defns
    commaT
    t <- fof_term
    cParenT
    return $ TFFLT_term defns t
  <?> "tff_let_term"
  )


-- %----This section is the FOFX syntax. Not yet in use.
-- % <fof_let>            ::= := [<fof_let_list>] : <fof_unitary_formula>
-- % <fof_let_list>       ::= <fof_defined_var> |
-- %                          <fof_defined_var>,<fof_let_list>
-- % <fof_defined_var>    ::= <variable> := <fof_logic_formula> |
-- %                          <variable> :- <fof_term> | (<fof_defined_var>)
-- %
-- % <fof_conditional>    ::= $ite_f(<fof_logic_formula>,<fof_logic_formula>,
-- %                          <fof_logic_formula>)
-- %
-- % <fof_conditional_term> ::= $ite_t(<fof_logic_formula>,<fof_term>,<fof_term>)

-- <fof_sequent>          ::= <fof_formula_tuple> <gentzen_arrow>
--                            <fof_formula_tuple> | (<fof_sequent>)
fof_sequent :: CharParser st FOF_sequent
fof_sequent = parserTrace "fof_sequent" (do
    ft1 <- try (fof_formula_tuple << gentzen_arrow)
    ft2 <- fof_formula_tuple
    return $ FOFS_plain ft1 ft2
  <|> liftM FOFS_parens (parens fof_sequent)
  <?> "fof_sequent"
  )

-- <fof_formula_tuple>    ::= [] | [<fof_formula_tuple_list>]
fof_formula_tuple :: CharParser st FOF_formula_tuple
fof_formula_tuple = parserTrace "fof_formula_tuple" (
  liftM FOF_formula_tuple (emptyBrackets <|> brackets fof_formula_tuple_list)
  <?> "fof_formula_tuple"
  )

-- <fof_formula_tuple_list> ::= <fof_logic_formula> |
--                            <fof_logic_formula>,<fof_formula_tuple_list>
fof_formula_tuple_list :: CharParser st FOF_formula_tuple_list
fof_formula_tuple_list = parserTrace "fof_formula_tuple_list" (
  sepByComma1 fof_logic_formula
  <?> "fof_formula_tuple_list"
  )

{- -----------------------------------------------------------------------------
CNF formulae (variables implicitly universally quantified)
----------------------------------------------------------------------------- -}
-- <cnf_formula>          ::= <disjunction> | (<disjunction>)
cnf_formula :: CharParser st CNF_formula
cnf_formula = parserTrace "cnf_formula" (
  liftM CNFF_parens (parens disjunction)
  <|> liftM CNFF_plain disjunction
  <?> "cnf_formula"
  )

-- <disjunction>          ::= <literal> | <disjunction> <vline> <literal>
disjunction :: CharParser st Disjunction
disjunction = parserTrace "disjunction" (
  liftM Disjunction (literal `sepBy1` vline)
  <?> "disjunction"
  )

-- <literal>              ::= <fof_atomic_formula> | ~ <fof_atomic_formula> |
--                            <fof_infix_unary>
literal :: CharParser st Literal
literal = parserTrace "literal" (
  liftM Lit_fof_infix fof_infix_unary
  <|> not_fof_atomic_formula
  <|> liftM Lit_atomic fof_atomic_formula
  <?> "literal"
  )
  where
    not_fof_atomic_formula = do
      charTok '~'
      liftM Lit_negative fof_atomic_formula

-- %----Connectives - THF
-- <thf_quantifier>       ::= <fof_quantifier> | <th0_quantifier> |
--                            <th1_quantifier>
thf_quantifier :: CharParser st THF_quantifier
thf_quantifier = parserTrace "thf_quantifier" (
  liftM THFQ_fof fof_quantifier
  <|> liftM THFQ_th0 th0_quantifier
  <|> liftM THFQ_th1 th1_quantifier
  <?> "thf_quantifier"
  )

-- %----TH0 quantifiers are also available in TH1
-- <th1_quantifier>       ::= !> | ?*
th1_quantifier :: CharParser st TH1_quantifier
th1_quantifier = parserTrace "th1_quantifier" (
  (strTok "!>" >> return TH1_DependentProduct)
  <|> (strTok "?*" >> return TH1_DependentSum)
  <?> "th1_quantifier"
  )

-- <th0_quantifier>       ::= ^ | @+ | @-
th0_quantifier :: CharParser st TH0_quantifier
th0_quantifier = parserTrace "th0_quantifier" (
  (strTok "^" >> return TH0_LambdaBinder)
  <|> (strTok "@+" >> return TH0_IndefiniteDescription)
  <|> (strTok "@-" >> return TH0_DefiniteDescription)
  <?> "th0_quantifier"
  )


-- <thf_pair_connective>  ::= <infix_equality> | <infix_inequality> |
--                            <binary_connective> | <assignment>
thf_pair_connective :: CharParser st THF_pair_connective
thf_pair_connective = parserTrace "thf_pair_connective" (
  (infix_equality >> return THF_infix_equality)
  <|> liftM THFPC_binary binary_connective
  <|> (infix_inequality >> return Infix_inequality)
  <|> (assignment >> return THF_assignment)
  <?> "thf_pair_connective"
  )

-- <thf_unary_connective> ::= <unary_connective> | <th1_unary_connective>
thf_unary_connective :: CharParser st THF_unary_connective
thf_unary_connective = parserTrace "thf_unary_connective" (
  liftM THFUC_th1 th1_unary_connective
  <|> liftM THFUC_unary unary_connective
  <?> "thf_unary_connective"
  )

-- <th1_unary_connective> ::= !! | ?? | @@+ | @@- | @=
th1_unary_connective :: CharParser st TH1_unary_connective
th1_unary_connective = parserTrace "th1_unary_connective" (
  (strTok "!!" >> return TH1_PiForAll)
  <|> (strTok "??" >> return TH1_PiSigmaExists)
  <|> (strTok "@@+" >> return TH1_PiIndefiniteDescription)
  <|> (strTok "@@-" >> return TH1_PiDefiniteDescription)
  <|> (strTok "@=" >> return TH1_PiEquality)
  <?> "th1_unary_connective"
  )

-- %----Connectives - THF and TFF
-- <subtype_sign>         ::= <<
subtype_sign :: CharParser st Token
subtype_sign = parserTrace "subtype_sign" (
  strTok "<<" <?> "subtype_sign"
  )

-- %----Connectives - TFF
-- % <tff_pair_connective>  ::= <binary_connective> | <assignment>
-- Note: not used
-- tff_pair_connective :: CharParser st TFF_pair_connective
-- tff_pair_connective = parserTrace "tff_pair_connective" (
--   liftM TFFPC_binary binary_connective
--   <|> liftM TFFPC_assignment tff_assignment
--   <?> "tff_pair_connective"
--   )

-- %----Connectives - FOF
-- <fof_quantifier>       ::= ! | ?
fof_quantifier :: CharParser st FOF_quantifier
fof_quantifier = parserTrace "fof_quantifier" (
  (charTok '!' >> notFollowedBy (oneOf "!=>") >> return ForAll)
  <|> (charTok '?' >> notFollowedBy (oneOf "?*") >> return Exists)
  <?> "fof_quantifier"
  )

-- <binary_connective>    ::= <=> | => | <= | <~> | ~<vline> | ~&
binary_connective :: CharParser st Binary_connective
binary_connective = parserTrace "binary_connective" ((strTok "<=>" >> return Equivalence)
  <|> (strTok "=>" >> return Implication)
  <|> (strTok "<=" >> return ReverseImplication)
  <|> (strTok "<~>" >> return XOR)
  <|> (strTok "~|" >> return NOR)
  <|> (strTok "~&" >> return NAND)
  <?> "binary_connective"
  )

-- <assoc_connective>     ::= <vline> | &
assoc_connective :: CharParser st Assoc_connective
assoc_connective = parserTrace "assoc_connective" (
  (vline >> return OR)
  <|> (andT >> return AND)
  <?> "assoc_connective"
  )

-- <unary_connective>     ::= ~
unary_connective :: CharParser st Unary_connective
unary_connective = parserTrace "unary_connective" (
  (charTok '~' >> return NOT)
  <?> "unary_connective"
  )

-- %----The seqent arrow
-- <gentzen_arrow>        ::= -->
gentzen_arrow :: CharParser st Token
gentzen_arrow = parserTrace "gentzen_arrow" (
  strTok "-->"
  <?> "gentzen_arrow"
  )

-- <assignment>           ::= :=
assignment :: CharParser st Token
assignment = parserTrace "assignment" (
  strTok ":="
  <?> "assignment"
  )

{- -----------------------------------------------------------------------------
Types for THF and TFF
----------------------------------------------------------------------------- -}
-- -<type_constant>        ::= <type_functor>
type_constant :: CharParser st Type_constant
type_constant = parserTrace "type_constant" (
  type_functor
  <?> "type_constant"
  )

-- <type_functor>         ::= <atomic_word>
type_functor :: CharParser st Type_functor
type_functor = parserTrace "type_functor" (
  atomic_word
  <?> "type_functor"
  )

-- <defined_type>         ::= <atomic_defined_word>
-- <defined_type>         :== $oType | $o | $iType | $i | $tType |
--                            $real | $rat | $int
defined_type :: CharParser st Defined_type
defined_type = parserTrace "defined_type" (constantsChoice
  [("$oType", OType),
   ("$o", O),
   ("$iType", IType),
   ("$int", Int),
   ("$i", I),
   ("$tType", TType),
   ("$real", Real),
   ("$rat", Rat)]
  <?> "defined_type"
  )

-- NOTE: unused
-- <system_type>          :== <atomic_system_word>
-- system_type :: CharParser st Token
-- system_type = pToken atomic_system_word <?> "system_type"
--


{- -----------------------------------------------------------------------------
For all language types
----------------------------------------------------------------------------- -}
-- <atom_>                 ::= <untyped_atom> | <defined_constant>
atom :: CharParser st Atom
atom = parserTrace "atom" (
  liftM Atom_constant defined_constant
  <|> liftM Atom_untyped untyped_atom
  <?> "atom"
  )

-- <untyped_atom>         ::= <constant> | <system_constant>
untyped_atom :: CharParser st Untyped_atom
untyped_atom = parserTrace "untyped_atom" (
  liftM UA_system system_constant
  <|> liftM UA_constant constant
  <?> "untyped_atom"
  )

-- <proposition>          :== <predicate>
proposition :: CharParser st Proposition
proposition = parserTrace "proposition" (predicate <?> "proposition"
  )

-- <predicate>            :== <atomic_word>
predicate :: CharParser st Predicate
predicate = parserTrace "predicate" (atomic_word <?> "predicate"
  )

-- <defined_proposition>  :== <atomic_defined_word>
-- <defined_proposition>  :== $true | $false
defined_proposition :: CharParser st Defined_proposition
defined_proposition = parserTrace "defined_prop" (
  constantsChoice [("$true", TPTP_true), ("$false", TPTP_false)]
  <?> "defined_prop"
  )

-- <defined_predicate>    :== <atomic_defined_word>
-- <defined_predicate>    :== $distinct |
--                            $less | $lesseq | $greater | $greatereq |
--                            $is_int | $is_rat |
--                            $box_P | $box_i | $box_int | $box |
--                            $dia_P | $dia_i | $dia_int | $dia
defined_predicate :: CharParser st Defined_predicate
defined_predicate = parserTrace "defined_pred" (constantsChoice
  [("$distinct", Distinct),
   ("$lesseq", Lesseq),
   ("$less", Less),
   ("$greatereq", Greatereq),
   ("$greater", Greater),
   ("$is_int", Is_int),
   ("$is_rat", Is_rat),
   ("$box_P", Box_P),
   ("$box_int", Box_int),
   ("$box_i", Box_i),
   ("$box", Box),
   ("$dia_P", Dia_P),
   ("$dia_int", Dia_int),
   ("$dia_i", Dia_i),
   ("$dia", Dia)]
  <?> "defined_pred"
  )

-- <defined_infix_pred>   ::= <infix_equality> | <assignment>
defined_infix_pred :: CharParser st Defined_infix_pred
defined_infix_pred = parserTrace "defined_infix_pred" (
  (infix_equality >> return Defined_infix_equality)
  <|> (assignment >> return Defined_assignment)
  <?> "defined_infix_pred"
  )

-- <infix_equality>       ::= =
infix_equality :: CharParser st Token
infix_equality = parserTrace "infix_equality" (
  parseIfNot (strTok "=>") (charTok '=')
  <?> "infix_equality"
  )

-- <infix_inequality>     ::= !=
infix_inequality :: CharParser st Token
infix_inequality = parserTrace "infix_inequality" (
  strTok "!="
  <?> "infix_inequality"
  )

-- <constant>             ::= <functor>
constant :: CharParser st Constant
constant = parserTrace "constant" (
  functor
  <?> "constant"
  )

-- <functor>              ::= <atomic_word>
functor :: CharParser st TPTP_functor
functor = parserTrace "functor" (
  atomic_word
  <?> "functor"
  )

-- <system_constant>      ::= <system_functor>
system_constant :: CharParser st System_constant
system_constant = parserTrace "system_constant" (
  system_functor
  <?> "system_constant"
  )

-- <system_functor>       ::= <atomic_system_word>
system_functor :: CharParser st System_functor
system_functor = parserTrace "system_functor" (
  atomic_system_word
  <?> "system_functor"
  )

-- <defined_constant>     ::= <defined_functor>
defined_constant :: CharParser st Defined_constant
defined_constant = parserTrace "defined_constant" (
  defined_functor
  <?> "defined_constant"
  )

-- <defined_functor>      ::= <atomic_defined_word>
-- <defined_functor>      :== $uminus | $sum | $difference | $product |
--                            $quotient | $quotient_e | $quotient_t | $quotient_f |
--                            $remainder_e | $remainder_t | $remainder_f |
--                            $floor | $ceiling | $truncate | $round |
--                            $to_int | $to_rat | $to_real
defined_functor :: CharParser st Defined_functor
defined_functor = parserTrace "defined_functor" (constantsChoice
  [("$uminus", Uminus),
   ("$sum", Sum),
   ("$difference", Difference),
   ("$product", Product),
   ("$quotient_e", Quotient_e),
   ("$quotient_t", Quotient_t),
   ("$quotient_f", Quotient_f),
   ("$quotient", Quotient),
   ("$remainder_e", Remainder_e),
   ("$remainder_t", Remainder_t),
   ("$remainder_f", Remainder_f),
   ("$floor", Floor),
   ("$ceiling", Ceiling),
   ("$truncate", Truncate),
   ("$round", Round),
   ("$to_int", To_int),
   ("$to_rat", To_rat),
   ("$to_real", To_real)]
  <|> liftM DF_atomic_defined_word atomic_defined_word
  <?> "defined_functor"
  )

-- <defined_term>         ::= <defined_atom> | <defined_atomic_term>
-- <defined_term>         ::= <number> | <distinct_object>
defined_term :: CharParser st Defined_term
defined_term = parserTrace "defined_term" (
  liftM DT_number number
  <|> liftM DT_object distinct_object
  <?> "defined_term"
  )

-- <variable>             ::= <upper_word>
variable :: CharParser st Variable
variable = parserTrace "variable" (
  pToken upper_word
  <?> "variable"
  )

{- -----------------------------------------------------------------------------
Formula sources
----------------------------------------------------------------------------- -}
-- <source>               ::= <general_term>
-- <source>               :== <dag_source> | <internal_source> |
--                            <external_source> | unknown | [<sources>]
source :: CharParser st Source
source = parserTrace "source" (
  liftM Source_external external_source
  <|> liftM Source_internal internal_source
  <|> liftM Source_DAG dag_source
  <|> (strTok "unknown" >> return Unknown_source)
  <|> liftM Source_many (brackets sources)
  <?> "source"
  )

-- %----Alternative sources are recorded like this, thus allowing representation
-- %----of alternative derivations with shared parts.
-- <sources>              :== <source> | <source>,<sources>
sources :: CharParser st Sources
sources = parserTrace "sources" (
  sepByComma1 source
  <?> "sources"
  )

-- %----Only a <dag_source> can be a <name>, i.e., derived formulae can be
-- %----identified by a <name> or an <inference_record>
-- <dag_source>           :== <name> | <inference_record>
dag_source :: CharParser st DAG_source
dag_source = parserTrace "dag_source" (
  liftM DAGS_record inference_record
  <|> liftM DAGS_name name
  <?> "dag_source"
  )

-- <inference_record>     :== inference(<inference_rule>,<useful_info>,
--                            <inference_parents>)
inference_record :: CharParser st Inference_record
inference_record = parserTrace "inference_record" (do
    try (strTok "inference" << oParenT)
    ir <- inference_rule
    commaT
    ui <- useful_info
    commaT
    ip <- inference_parents
    cParenT
    return $ Inference_record ir ui ip
  <?> "inference_record"
  )

-- <inference_rule>       :== <atomic_word>
-- %----Examples are          deduction | modus_tollens | modus_ponens | rewrite |
-- %                          resolution | paramodulation | factorization |
-- %                          cnf_conversion | cnf_refutation | ...
inference_rule :: CharParser st Token
inference_rule = parserTrace "inference_rule" (
  atomic_word
  <?> "inference_rule"
  )

-- %----<inference_parents> can be empty in cases when there is a justification
-- %----for a tautologous theorem. In case when a tautology is introduced as
-- %----a leaf, e.g., for splitting, then use an <internal_source>.
-- <inference_parents>    :== [] | [<parent_list>]
inference_parents :: CharParser st Inference_parents
inference_parents = parserTrace "inference_parents" (
  emptyBrackets
  <|> brackets parent_list
  <?> "inference_parents"
  )

-- <parent_list>          :== <parent_info> | <parent_info>,<parent_list>
parent_list :: CharParser st Parent_list
parent_list = parserTrace "parent_list" (
  sepByComma1 parent_info
  <?> "parent_list"
  )

-- <parent_info>          :== <source><parent_details>
parent_info :: CharParser st Parent_info
parent_info = parserTrace "parent_info" (do
    s <- source
    pd <- parent_details
    return $ Parent_info s pd
  <?> "parent_info"
  )

-- <parent_details>       :== :<general_list> | <null>
parent_details :: CharParser st Parent_details
parent_details = parserTrace "parent_details" (do
    colonT
    liftM Just general_list
  <|> return Nothing
  <?> "parent_details"
  )

-- <internal_source>      :== introduced(<intro_type><optional_info>)
internal_source :: CharParser st Internal_source
internal_source = parserTrace "internal_source" (do
    try (strTok "introduced" << oParenT)
    it <- intro_type
    oi <- optional_info
    cParenT
    return $ Internal_source it oi
  <?> "internal_source"
  )

-- <intro_type>           :== definition | axiom_of_choice | tautology | assumption
intro_type :: CharParser st Intro_type
intro_type = parserTrace "intro_type" (
  constantsChoice
    [("definition", IntroTypeDefinition),
     ("axiom_of_choice", AxiomOfChoice),
     ("tautology", Tautology),
     ("assumption", IntroTypeAssumption)]
  <?> "intro_type"
  )

-- <external_source>      :== <file_source> | <theory> | <creator_source>
external_source :: CharParser st External_source
external_source = parserTrace "external_source" (
  liftM ExtSrc_file file_source
  <|> liftM ExtSrc_theory theory
  <|> liftM ExtSrc_creator creator_source
  <?> "external_source"
  )

-- <file_source>          :== file(<file_name><file_info>)
file_source :: CharParser st File_source
file_source = parserTrace "file_source" (do
    try (strTok "file" << oParenT)
    fn <- file_name
    fi <- file_info
    cParenT
    return $ File_source fn fi
  <?> "file_source"
  )

-- <file_info>            :== ,<name> | <null>
file_info :: CharParser st File_info
file_info = parserTrace "file_info" (do
    commaT
    n <- name
    return $ Just n
  <|> return Nothing
  <?> "file_info"
  )

-- <theory>               :== theory(<theory_name><optional_info>)
theory :: CharParser st Theory
theory = parserTrace "theory" (do
    try (strTok "theory" << oParenT)
    tn <- theory_name
    oi <- optional_info
    cParenT
    return $ Theory tn oi
  <?> "theory"
  )

-- <theory_name>          :== equality | ac
theory_name :: CharParser st Theory_name
theory_name = parserTrace "theory_name" (
  (strTok "equality" >> return TN_equality)
  <|> (strTok "ac" >> return TN_ac)
  <?> "theory_name"
  )

-- <creator_source>       :== creator(<creator_name><optional_info>)
creator_source :: CharParser st Creator_source
creator_source = parserTrace "creator_source" (do
    try (strTok "creator" << oParenT)
    cn <- creator_name
    oi <- optional_info
    cParenT
    return $ Creator_source cn oi
  <?> "creator_source"
  )

-- <creator_name>         :== <atomic_word>
creator_name :: CharParser st Token
creator_name = parserTrace "creator_name" (
  atomic_word
  <?> "creator_name"
  )


{- -----------------------------------------------------------------------------
Useful info fields
----------------------------------------------------------------------------- -}
-- <optional_info>        ::= ,<useful_info> | <null>
optional_info :: CharParser st (Maybe Useful_info)
optional_info = parserTrace "optional_info" (
  optionMaybe (charTok ',' >> useful_info)
  <?> "optional_info"
  )

-- <useful_info>          ::= <general_list>
-- <useful_info>          :== [] | [<info_items>]
useful_info :: CharParser st Useful_info
useful_info = parserTrace "useful_info" (
  liftM UI_items (emptyBrackets <|> try (brackets info_items))
  <|> liftM UI_general_list general_list
  <?> "useful_info"
  )

-- <info_items>           :== <info_item> | <info_item>,<info_items>
info_items :: CharParser st Info_items
info_items = parserTrace "info_items" (
  sepByComma1 info_item
  <?> "info_items"
  )

-- <info_item>            :== <formula_item> | <inference_item> |
--                            <general_function>
info_item :: CharParser st Info_item
info_item = parserTrace "info_item" (
  liftM Info_formula formula_item
  <|> liftM Info_inference inference_item
  <|> liftM Info_general general_function
  <?> "info_item"
  )


{- -----------------------------------------------------------------------------
Useful info for formula records
----------------------------------------------------------------------------- -}
-- <formula_item>         :== <description_item> | <iquote_item>
formula_item :: CharParser st Formula_item
formula_item = parserTrace "formula_item" (
  liftM FI_description description_item
  <|> liftM FI_iquote iquote_item
  <?> "formula_item"
  )

-- <description_item>     :== description(<atomic_word>)
description_item :: CharParser st Description_item
description_item = parserTrace "description_item" (do
    try (strTok "description" << oParenT)
    atomic_word << cParenT
  <?> "description_item"
  )

-- <iquote_item>          :== iquote(<atomic_word>)
iquote_item :: CharParser st Iquote_item
iquote_item = parserTrace "iquote_item" (do
    try (strTok "iquote" << oParenT)
    atomic_word << cParenT
  <?> "iquote_item"
  )

-- <inference_item>       :== <inference_status> | <assumptions_record> |
--                            <new_symbol_record> | <refutation>
inference_item :: CharParser st Inference_item
inference_item = parserTrace "inference_item" (
  liftM Inf_status inference_status
  <|> liftM Inf_assumption assumptions_record
  <|> liftM Inf_symbol new_symbol_record
  <|> liftM Inf_refutation refutation
  <?> "inference_item"
  )

-- <inference_status>     :== status(<status_value>) | <inference_info>
inference_status :: CharParser st Inference_status
inference_status = parserTrace "inference_status" (do
    try (strTok "status" << oParenT)
    liftM Inf_value (status_value << cParenT)
  <|> liftM Inf_info inference_info
  <?> "inference_status"
  )

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
status_value :: CharParser st Status_value
status_value = parserTrace "status_value" (
  constantsChoice
    [("suc", SUC), ("unp", UNP), ("sap", SAP), ("esa", ESA), ("sat", SAT),
     ("fsa", FSA), ("thm", THM), ("eqv", EQV), ("tac", TAC),
     ("wec", WEC), ("eth", ETH), ("tau", TAU), ("wtc", WTC), ("wth", WTH),
     ("cax", CAX), ("sca", SCA), ("tca", TCA), ("wca", WCA),
     ("cup", CUP), ("csp", CSP), ("ecs", ECS), ("csa", CSA), ("cth", CTH),
     ("ceq", CEQ), ("unc", UNC), ("wcc", WCC), ("ect", ECT),
     ("fun", FUN), ("uns", UNS), ("wuc", WUC), ("wct", WCT), ("scc", SCC),
     ("uca", UCA), ("noc", NOC)]
  <?> "status_value"
  )

-- %----<inference_info> is used to record standard information associated with an
-- %----arbitrary inference rule. The <inference_rule> is the same as the
-- %----<inference_rule> of the <inference_record>. The <atomic_word> indicates
-- %----the information being recorded in the <general_list>. The <atomic_word>
-- %----are (loosely) set by TPTP conventions, and include esplit, sr_split, and
-- %----discharge.
-- <inference_info>       :== <inference_rule>(<atomic_word>,<general_list>)
inference_info :: CharParser st Inference_info
inference_info = parserTrace "inference_info" (do
    ir <- try (inference_rule << oParenT)
    aw <- atomic_word
    commaT
    gl <- general_list
    cParenT
    return $ Inference_info ir aw gl
  <?> "inference_info"
  )

-- %----An <assumptions_record> lists the names of assumptions upon which this
-- %----inferred formula depends. These must be discharged in a completed proof.
-- <assumptions_record>   :== assumptions([<name_list>])
assumptions_record :: CharParser st Assumptions_record
assumptions_record = parserTrace "assumptions_record" (do
    try (strTok "assumptions" << oParenT)
    brackets name_list << cParenT
  <?> "assumptions_record"
  )

-- %----A <refutation> record names a file in which the inference recorded here
-- %----is recorded as a proof by refutation.
-- <refutation>           :== refutation(<file_source>)
refutation :: CharParser st Refutation
refutation = parserTrace "refutation" (do
    try (strTok "refutation" << oParenT)
    file_source << cParenT
  <?> "refutation"
  )

-- %----A <new_symbol_record> provides information about a newly introduced symbol.
-- <new_symbol_record>    :== new_symbols(<atomic_word>,[<new_symbol_list>])
new_symbol_record :: CharParser st New_symbol_record
new_symbol_record = parserTrace "new_symbol_record" (do
    try (strTok "new_symbols" << oParenT)
    aw <- atomic_word
    nsl <- new_symbol_list
    cParenT
    return $ New_symbol_record aw nsl
  <?> "new_symbol_record"
  )

-- <new_symbol_list>      :== <principal_symbol> |
--                            <principal_symbol>,<new_symbol_list>
new_symbol_list :: CharParser st New_symbol_list
new_symbol_list = parserTrace "new_symbol_list" (
  sepByComma1 principal_symbol
  <?> "new_symbol_list"
  )

-- %----Principal symbols are predicates, functions, variables
-- <principal_symbol>   :== <functor> | <variable>
principal_symbol :: CharParser st Principal_symbol
principal_symbol = parserTrace "principal_symbol" (
  liftM PS_functor functor
  <|> liftM PS_variable variable
  <?> "principal_symbol"
  )

{- -----------------------------------------------------------------------------
Include directives
----------------------------------------------------------------------------- -}
-- <include>              ::= include(<file_name><formula_selection>).
include :: CharParser st Include
include = parserTrace "include" (do
    try (strTok "include" << oParenT)
    fn <- file_name
    fs <- formula_selection
    cParenT
    dotT
    return $ Include fn fs
  <?> "include"
  )

-- <formula_selection>    ::= ,[<name_list>] | <null>
formula_selection :: CharParser st Formula_selection
formula_selection = parserTrace "formula_selection" (
  optionMaybe (commaT >> brackets name_list)
  <?> "formula_selection"
  )

-- <name_list>            ::= <name> | <name>,<name_list>
name_list :: CharParser st Name_list
name_list = parserTrace "name_list" (
  sepByComma1 name
  <?> "name_list"
  )


{- -----------------------------------------------------------------------------
Non-logical data
----------------------------------------------------------------------------- -}
-- <general_term>         ::= <general_data> | <general_data>:<general_term> |
--                            <general_list>
general_term :: CharParser st General_term
general_term = parserTrace "general_term" (do
    gd <- try (general_data << colonT)
    gt <- general_term
    return $ GT_DataTerm gd gt
  <|> liftM GT_data general_data
  <|> liftM GT_list general_list
  <?> "general_term"
  )

-- <general_data>         ::= <atomic_word> | <general_function> |
--                            <variable> | <number> | <distinct_object> |
--                            <formula_data>
-- <general_data>         :== bind(<variable>,<formula_data>)
general_data :: CharParser st General_data
general_data = parserTrace "general_data" (do
    try (strTok "bind" << oParenT)
    v <- variable
    commaT
    fd <- formula_data
    cParenT
    return $ GD_bind v fd
  <|> liftM GD_general_function general_function
  <|> liftM GD_atomic_word atomic_word
  <|> liftM GD_variable variable
  <|> liftM GD_number number
  <|> liftM GD_distinct_object distinct_object
  <|> liftM GD_formula_data formula_data
  <?> "general_data"
  )

-- <general_function>     ::= <atomic_word>(<general_terms>)
general_function :: CharParser st General_function
general_function = parserTrace "general_function" (do
  aw <- try (atomic_word << oParenT)
  fd <- general_terms
  cParenT
  return $ General_function aw fd
  )

-- <formula_data>         ::= $thf(<thf_formula>) | $tff(<tff_formula>) |
--                            $fof(<fof_formula>) | $cnf(<cnf_formula>) |
--                            $fot(<fof_term>)
formula_data :: CharParser st Formula_data
formula_data = parserTrace "formula_data" (
  xxx_data "$thf" FD_THF thf_formula
  <|> xxx_data "$tff" FD_TFF tff_formula
  <|> xxx_data "$fof" FD_FOF fof_formula
  <|> xxx_data "$cnf" FD_CNF cnf_formula
  <|> xxx_data "$fot" FD_FOT fof_term
  <?> "formula_data"
  )
  where
    xxx_data str constructor parser = do
      try (strTok str << oParenT)
      d <- parser
      cParenT
      return $ constructor d

-- <general_list>         ::= [] | [<general_terms>]
general_list :: CharParser st General_list
general_list = parserTrace "general_list" (
  emptyBrackets
  <|> brackets general_terms
  <?> "general_list"
  )

-- <general_terms>        ::= <general_term> | <general_term>,<general_terms>
general_terms :: CharParser st General_terms
general_terms = parserTrace "general_terms" (
  sepByComma1 general_term
  <?> "general_terms"
  )


{- -----------------------------------------------------------------------------
General purpose
----------------------------------------------------------------------------- -}
-- <name>                 ::= <atomic_word> | <integer>
name :: CharParser st Name
name = parserTrace "name" (
  liftM NameString atomic_word
  <|> (liftM NameInteger $ liftM read integer)
  <?> "name"
  )

-- <atomic_word>          ::= <lower_word> | <single_quoted>
-- %----<single_quoted> tokens do not include their outer quotes, therefore the
-- %----<lower_word> <atomic_word> cat and the <single_quoted> <atomic_word> 'cat'
-- %----are the same. Quotes must be removed from a <single_quoted> <atomic_word>
-- %----if doing so produces a <lower_word> <atomic_word>. Note that <numbers>s
-- %----and <variable>s are not <lower_word>s, so '123' and 123, and 'X' and X,
-- %----are different.
atomic_word :: CharParser st Token
atomic_word = parserTrace "atomic_word" (
  pToken lower_word
  <|> do
    s <- single_quoted
    let sNoQuotes = removeQuotes $ tokStr s
    case runParser lower_word () "" sNoQuotes of
      Right _ -> return $ s { tokStr = sNoQuotes }
      Left _ -> return s
  <?> "atomic_word"
  )
  where
    removeQuotes :: String -> String
    removeQuotes = init . tail

-- <atomic_defined_word>  ::= <dollar_word>
atomic_defined_word :: CharParser st Token
atomic_defined_word = parserTrace "atomic_defined_word" (pToken dollar_word
  )


-- <atomic_system_word>   ::= <dollar_dollar_word>
atomic_system_word :: CharParser st Token
atomic_system_word = parserTrace "atomic_system_word" (pToken dollar_dollar_word
  )

-- <number>               ::= <integer> | <rational> | <real>
number :: CharParser st Number
number = parserTrace "number" (
  (liftM NumRational (liftM read rational) << skip)
  <|> (liftM NumReal (liftM read real) << skip)
  <|> (liftM NumInteger (liftM read integer) << skip)
  <?> "number"
  )

-- <file_name>            ::= <single_quoted>
file_name :: CharParser st File_name
file_name = parserTrace "file_name" (
  single_quoted_file_name
  <|> unquoted_file_name
  <?> "file_name"
  )

-- <null>                 ::=


{- -----------------------------------------------------------------------------
Comments
----------------------------------------------------------------------------- -}

-- <comment>              ::- <comment_line>|<comment_block>
comment :: CharParser st Comment
comment = parserTrace "comment" (comment_line <|> comment_block <?> "comment"
  )

-- <comment_line>         ::- [%]<printable_char>*
comment_line :: CharParser st Comment
comment_line = parserTrace "comment_line" (liftM Comment_line (commentLineWith "%" True) <?> "comment_line"
  )

-- <comment_block>        ::: [/][*]<not_star_slash>[*][*]*[/]
comment_block :: CharParser st Comment
comment_block = parserTrace "comment_block" (liftM Comment_block (commentBlockWith "/*" True) <?> "comment_block"
  )

-- %----  <defined_comment>    ::- <def_comment_line>|<def_comment_block>
defined_comment :: CharParser st DefinedComment
defined_comment = parserTrace "defined_comment" (def_comment_line <|> def_comment_block <?> "defined_comment"
  )

-- %----  <def_comment_line>   ::: [%]<dollar><printable_char>*
def_comment_line :: CharParser st DefinedComment
def_comment_line = parserTrace "def_comment_line" (liftM Defined_comment_line (commentLineWith "%$" True)
  <?> "def_comment_line"
  )

-- %----  <def_comment_block>  ::: [/][*]<dollar><not_star_slash>[*][*]*[/]
def_comment_block :: CharParser st DefinedComment
def_comment_block = parserTrace "def_comment_block" (liftM Defined_comment_block (commentBlockWith "/*$" True)
  <?> "def_comment_block"
  )

-- %----  <system_comment>     ::- <sys_comment_line>|<sys_comment_block>
system_comment :: CharParser st SystemComment
system_comment = parserTrace "system_comment" (sys_comment_line <|> sys_comment_block <?> "system_comment"
  )

-- %----  <sys_comment_line>   ::: [%]<dollar><dollar><printable_char>*
sys_comment_line :: CharParser st SystemComment
sys_comment_line = parserTrace "sys_comment_line" (liftM System_comment_line (commentLineWith "%$$" False)
  <?> "sys_comment_line"
  )

-- %----  <sys_comment_block>  ::: [/][*]<dollar><dollar><not_star_slash>[*][*]*[/]
sys_comment_block :: CharParser st SystemComment
sys_comment_block = parserTrace "sys_comment_block" (liftM System_comment_block (commentBlockWith "/*$$" False)
  <?> "sys_comment_block"
  )

commentLineWith :: String -> Bool -> CharParser st Token
commentLineWith beginning restrict = (do
  tryString beginning
  if restrict then notFollowedBy (char '$') else return ()
  -- we use anyChar instead of printable_char for the comments to parse the whole tptp library
  pToken $ manyTill anyChar (char '\n'))
  <?> "commentLineWith"

commentBlockWith :: String -> Bool -> CharParser st Token
commentBlockWith beginning restrict = (do
  tryString beginning
  if restrict then notFollowedBy (char '$') >> return () else return ()
  -- we use anyChar instead of printable_char for the comments to parse the whole tptp library
  pToken $ manyTill anyChar (strTok "*/"))
  <?> "commentBlockWith"

{- -----------------------------------------------------------------------------
Word classes
----------------------------------------------------------------------------- -}

-- <sq_char>            ::: ([\40-\46\50-\133\135-\176]|[\\]['\\])
-- <single_quoted>      ::- <single_quote><sq_char><sq_char>*<single_quote>
-- %---Space and visible characters upto ~, except ' and \
single_quoted :: CharParser st Token
single_quoted = parserTrace "single_quoted" (pToken (do
    char '\''
    s <- fmap concat $ many1 (tryString "\\\\" <|> tryString "\\'"
        <|> single (satisfy (\ c -> printable c && notElem c "'\\")))
    keyChar '\''
    return ( "'" ++ s ++ "'"))
  <?> "single_quoted"
  )

-- For the include, we need the single quoted to be an IRI
single_quoted_file_name :: CharParser st IRI
single_quoted_file_name = parserTrace "single_quoted" (do
    char '\''
    s <- fmap concat $ many1 (tryString "\\\\" <|> tryString "\\'"
        <|> single (satisfy (\ c -> printable c && notElem c "'\\")))
    let s' = escapeTPTPFilePath s
    i <- case parse (iriCurie << eof) "" s' of
      Left err -> fail $ show err
      Right i -> return $ unescapeTPTPFileIRI i
    keyChar '\''
    skip
    return i
  <?> "single_quoted"
  )

unquoted_file_name :: CharParser st IRI
unquoted_file_name = parserTrace "single_quoted" (try (do
    -- a file name is always terminated by a comma or a closing parenthesis
    s <- lookAhead $ try $ manyTill anyChar $ try $ oneOf ",)"
    let s' = escapeTPTPFilePath s
    i <- case parse (iriCurie << eof) "" s' of
      Left err -> fail $ show err
      Right i -> return $ unescapeTPTPFileIRI i
    strTok s
    skip
    return i)
  <?> "single_quoted"
  )

-- <do_char>              ::: ([\40-\41\43-\133\135-\176]|[\\]["\\])
-- <distinct_object>      ::- <double_quote><do_char>*<double_quote>
-- %---Space and visible characters upto ~, except " and \
-- %----<distinct_object>s contain visible characters. \ is the escape character
-- %----for " and \, i.e., \" is not the end of the <distinct_object>.
-- %----<distinct_object>s are different from (but may be equal to) other tokens,
-- %----e.g., "cat" is different from 'cat' and cat. Distinct objects are always
-- %----interpreted as themselves, so if they are different they are unequal,
-- %----e.g., "Apple" != "Microsoft" is implicit.
distinct_object :: CharParser st Token
distinct_object = parserTrace "distinct_object" (pToken (do
    char '"'
    s <- fmap concat $ many (tryString "\\\\" <|> tryString "\\\""
        <|> single (satisfy (\ c -> printable c && notElem c "\"\\")))
    keyChar '"'
    return ("\"" ++ s ++ "\""))
  <?> "distinct_object"
  )


-- -- <dollar_word>          ::- <dollar><lower_word>
dollar_word :: CharParser st String
dollar_word = do
  prefix <- char '$' << notFollowedBy (char '$')
  word <- lower_word
  return (prefix : word)

-- <dollar_dollar_word>   ::- <dollar><dollar><lower_word>
dollar_dollar_word :: CharParser st String
dollar_dollar_word = do
    prefix <- tryString "$$"
    word <- lower_word
    return (prefix ++ word)
  <?> "dollar_dollar_word"

-- <upper_word>           ::- <upper_alpha><alpha_numeric>*
upper_word :: CharParser st String
upper_word = do
    u <- upper
    w <- many alpha_numeric
    return (u : w)
  <?> "upper_word"

-- <lower_word>           ::- <lower_alpha><alpha_numeric>*
lower_word :: CharParser st String
lower_word = do
    l <- lower
    w <- many alpha_numeric
    return (l : w)
  <?> "lower_word"

{- -----------------------------------------------------------------------------
Numbers. Signs are made part of the same token here.
----------------------------------------------------------------------------- -}
-- <real>                 ::- (<signed_real>|<unsigned_real>)
real :: CharParser st String
real = signed_real <|> unsigned_real <?> "real"

-- <signed_real>          ::- <sign><unsigned_real>
signed_real :: CharParser st String
signed_real = try (do
    s <- sign
    r <- unsigned_real
    return (s : r))
  <?> "signed_real"

-- <unsigned_real>        ::- (<decimal_fraction>|<decimal_exponent>)
unsigned_real :: CharParser st String
unsigned_real = decimal_exponent <|> decimal_fraction <?> "unsigned_real"

-- <rational>             ::- (<signed_rational>|<unsigned_rational>)
rational :: CharParser st String
rational = signed_rational <|> unsigned_rational <?> "rational"

-- <signed_rational>      ::- <sign><unsigned_rational>
signed_rational :: CharParser st String
signed_rational = try (do
    s <- sign
    r <- unsigned_rational
    return (s : r))
  <?> "signed_rational"

-- <unsigned_rational>    ::- <decimal><slash><positive_decimal>
unsigned_rational :: CharParser st String
unsigned_rational = do
    d <- try (decimal << char '/')
    p <- positive_decimal
    return (d ++ "/" ++ p)
  <?> "unsigned_rational"

-- <integer>              ::- (<signed_integer>|<unsigned_integer>)
integer  :: CharParser st String
integer = signed_integer <|> unsigned_integer <?> "integer"

-- <signed_integer>       ::- <sign><unsigned_integer>
signed_integer :: CharParser st String
signed_integer = try (do
    s <- sign
    i <- unsigned_integer
    return (s : i))
  <?> "signed_integer"

-- <unsigned_integer>     ::- <decimal>
unsigned_integer :: CharParser st String
unsigned_integer = decimal <?> "unsigned_integer"

-- <decimal>              ::- (<zero_numeric>|<positive_decimal>)
decimal :: CharParser st String
decimal = single (char '0') <|> positive_decimal <?> "decimal"

-- <positive_decimal>     ::- <non_zero_numeric><numeric>*
positive_decimal :: CharParser st String
positive_decimal = try (do
    nzn <- non_zero_numeric
    ns <- many digit
    return (nzn : ns))
  <?> "positive_decimal"

-- <decimal_exponent>     ::- (<decimal>|<decimal_fraction>)<exponent><exp_integer>
decimal_exponent :: CharParser st String
decimal_exponent = try (do
    df <- try (decimal_fraction <|> decimal)
    exp <- single exponent
    exp_int <- exp_integer
    return (df ++ exp ++ exp_int))
  <?> "decimal_exponent"

-- <decimal_fraction>     ::- <decimal><dot_decimal>
decimal_fraction :: CharParser st String
decimal_fraction = try (do
    dec <- decimal
    dd <- dot_decimal
    return (dec ++ dd))
  <?> "decimal_fraction"

-- <dot_decimal>          ::- <dot><numeric><numeric>*
dot_decimal :: CharParser st String
dot_decimal = do
    dot <- char '.'
    num <- many1 digit
    return (dot : num)
  <?> "dot_decimal"

-- <exp_integer>          ::- (<signed_exp_integer>|<unsigned_exp_integer>)
exp_integer :: CharParser st String
exp_integer = signed_exp_integer <|> unsigned_exp_integer <?> "exp_integer"

-- <signed_exp_integer>   ::- <sign><unsigned_exp_integer>
signed_exp_integer :: CharParser st String
signed_exp_integer = try (do
    s <- sign
    d <- unsigned_exp_integer
    return (s : d))
  <?> "signed_exp_integer"

-- <unsigned_exp_integer> ::- <numeric><numeric>*
unsigned_exp_integer :: CharParser st String
unsigned_exp_integer = many1 digit <?> "unsigned_exp_integer"


{- -----------------------------------------------------------------------------
Character classes
----------------------------------------------------------------------------- -}

-- <sign>                 ::: [+-]
sign :: CharParser st Char
sign = oneOf "+-" <?> "sign"

-- <exponent>             ::: [Ee]
exponent :: CharParser st Char
exponent = oneOf "Ee" <?> "exponent"

-- <non_zero_numeric>     ::: [1-9]
non_zero_numeric :: CharParser st Char
non_zero_numeric = satisfy (\ c -> '1' <= c && c <= '9') <?> "non_zero_numeric"

-- <alpha_numeric>        ::: (<lower_alpha>|<upper_alpha>|<numeric>|[_])
alpha_numeric :: CharParser st Char
alpha_numeric = satisfy (\ c -> isAlphaNum c || c == '_') <?> "alpha_numeric"

-- <printable_char>       ::: .
-- %----<printable_char> is any printable ASCII character, codes 32 (space) to 126
-- %----(tilde). <printable_char> does not include tabs, newlines, bells, etc. The
-- %----use of . does not not exclude tab, so this is a bit loose.
printable_char :: CharParser st Char
printable_char = satisfy printable <?> "printable_char"

printable :: Char -> Bool
-- the tab character is an unofficial extension
printable c = (32 <= ord c && ord c <= 126) || c == '\t'

-- NOTE: not used
-- -- <viewable_char>        ::: [.\n]
-- viewable_char :: CharParser st Char
-- viewable_char = satisfy (\ c -> printable c || c == '\n')


vline :: CharParser st Token
vline = charTok '|'

andT :: CharParser st Token
andT = charTok '&'

starT :: CharParser st Token
starT = charTok '*'

plusT :: CharParser st Token
plusT = charTok '+'

arrowT :: CharParser st Token
arrowT = charTok '>'


commaT :: CharParser st Token
commaT = charTok ','

dotT :: CharParser st Token
dotT = charTok '.'

colonT :: CharParser st Token
colonT = charTok ':'

{- -----------------------------------------------------------------------------
Some lexer functions
----------------------------------------------------------------------------- -}
skip :: CharParser st ()
skip = skipMany $ forget (satisfy isSpace)

pToken :: CharParser st String -> CharParser st Token
pToken p = Lexer.pToken p << skip

oBracketT :: CharParser st Token
oBracketT = charTok '['

cBracketT :: CharParser st Token
cBracketT = charTok ']'

brackets :: CharParser st a -> CharParser st a
brackets p = oBracketT >> p << cBracketT

oParenT :: CharParser st Token
oParenT = charTok '('

cParenT :: CharParser st Token
cParenT = charTok ')'

parens :: CharParser st a -> CharParser st a
parens p = oParenT >> p << cParenT

{- -----------------------------------------------------------------------------
Some helper functions
----------------------------------------------------------------------------- -}

strTok :: String -> CharParser st Token
strTok s = parserTrace ("strTok " ++ show s) (pToken $ tryString s
  )

charTok :: Char -> CharParser st Token
charTok c = parserTrace ("charTok " ++ show c) (pToken $ single $ char c
  )

constantsChoice :: [(String, a)] -> CharParser st a
constantsChoice choices = choice $ map constantMapping choices

constantMapping :: (String, a) -> CharParser st a
constantMapping (s, c) = strTok s >> return c

emptyBrackets :: CharParser st [a]
emptyBrackets = try (oBracketT >> return [] << cBracketT)

sepByComma1 :: CharParser st a -> CharParser st [a]
sepByComma1 p = p `sepBy1` strTok ","

-- Looks ahead without consuming input. Fails if @notToFind@ follows.
-- Is only used to optimize performance.
-- Apply it only to very short @notToFind@.
parseIfNot :: Show a => CharParser st a -> CharParser st b -> CharParser st b
parseIfNot notToFind p = lookAhead (notFollowedBy $ try notToFind) >> p

skipAll :: CharParser st ()
skipAll = skipMany (skipMany1 space <|>
                    forget ((comment >> return ()) <|>
                            (defined_comment >> return ()) <|>
                            (system_comment >> return ())))

key :: CharParser st a -> CharParser st ()
key = (>> skipAll)

keyChar :: Char -> CharParser st ()
keyChar = key . char
