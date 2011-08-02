{- |
Module      :  $Header$
Description :  A Parser for the TPTP-THF Syntax
Copyright   :  (c) A. Tsogias, DFKI Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Alexis.Tsogias@dfki.de
Stability   :  provisional
Portability :  portable

A Parser for the TPTP-THF Input Syntax v5.1.0.2 taken from
<http://www.cs.miami.edu/~tptp/TPTP/SyntaxBNF.html>
-}

module THF.ParseTHF (parseTHF) where

import THF.As

import Text.ParserCombinators.Parsec

import Common.Parsec

import Data.Char
import Data.Maybe

--------------------------------------------------------------------------------
-- Parser for the THF Syntax
-- Most methods match those of As.hs
--------------------------------------------------------------------------------

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
    c <- many1 $ char '-' << notFollowedBy printableChar
    skipSpaces
    return $ Comment_Line c

commentLine :: CharParser st Comment
commentLine = do
    try (char '%' >> notFollowedBy (char '$'))
    c <- many printableChar
    return $ Comment_Line c

comment :: CharParser st TPTP_THF
comment = fmap TPTP_Comment commentLine
  <|> do
    try (string "/*" >> notFollowedBy (char '$'))
    c <- many (noneOf "*/")
    skipMany1 (char '*'); char '/'
    return $ TPTP_Comment (Comment_Block (lines c))

definedComment :: CharParser st TPTP_THF
definedComment = do
    try (string "%$" >> notFollowedBy (char '$'))
    c <- many printableChar
    return $ TPTP_Defined_Comment (Defined_Comment_Line c)
  <|> do
    try (string "/*$" >> notFollowedBy (char '$'))
    c <- many (noneOf "*/")
    skipMany1 (char '*'); char '/'
    return $ TPTP_Defined_Comment (Defined_Comment_Block (lines c))

systemComment :: CharParser st TPTP_THF
systemComment = do
    tryString "%$$"
    c <- many printableChar
    return $ TPTP_System_Comment (System_Comment_Line c)
  <|> do
    tryString "/*$$"
    c <- many (noneOf "*/")
    skipMany1 (char '*'); char '/'
    return $ TPTP_System_Comment (System_Comment_Block (lines c))

include :: CharParser st TPTP_THF
include = do
    key $ tryString "include"
    oParentheses
    fn <- fileName
    fs <- formulaSelection
    cParentheses; char '.'
    return $ TPTP_Include (I_Include fn fs)

thfAnnotatedFormula :: CharParser st TPTP_THF
thfAnnotatedFormula = do
    key $ tryString "thf"
    oParentheses
    n <- name; comma
    fr <- formulaRole; comma
    tf <- thfFormula
    a <- annotations
    cParentheses; char '.'
    return $ TPTP_THF_Annotated_Formula n fr tf a

annotations :: CharParser st Annotations
annotations = do
    comma
    s <- source
    oi <- optionalInfo
    return $ Annotations s oi
  <|> do
    notFollowedBy (char ',');
    return Null

formulaRole :: CharParser st FormulaRole
formulaRole = do
    r <- lowerWord
    case r of
        "axiom"                 -> return Axiom
        "hypothesis"            -> return Hypothesis
        "definition"            -> return Definition
        "assumption"            -> return Assumption
        "lemma"                 -> return Lemma
        "theorem"               -> return Theorem
        "conjecture"            -> return Conjecture
        "negated_conjecture"    -> return Negated_Conjecture
        "plain"                 -> return Plain
        "fi_domain"             -> return Fi_Domain
        "fi_functors"           -> return Fi_Functors
        "fi_predicates"         -> return Fi_Predicates
        "type"                  -> return Type
        "unknown"               -> return Unknown
        _                       -> fail ("No such Role: " ++ r)

thfFormula :: CharParser st THFFormula
thfFormula = fmap TF_THF_Logic_Formula thfLogicFormula
  <|> fmap TF_THF_Sequent thfSequent

thfLogicFormula :: CharParser st THFLogicFormula
thfLogicFormula = fmap TLF_THF_Binary_Formula thfBinaryFormula
  <|> fmap TLF_THF_Type_Formula thfTypeFormula
  <|> fmap TLF_THF_Sub_Type thfSubType
  <|> fmap TLF_THF_Unitary_Formula thfUnitaryFormula

thfBinaryFormula :: CharParser st THFBinaryFormula
thfBinaryFormula = fmap TBF_THF_Binary_Type thfBinaryType
  <|> fmap TBF_THF_Binary_Tuple thfBinaryTuple
  <|> do
    (uff, pc) <- try $ do
        uff1 <- thfUnitaryFormula
        pc1 <- thfPairConnective
        return (uff1, pc1)
    ufb <- thfUnitaryFormula
    return $ TBF_THF_Binary_Pair uff pc ufb

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

thfUnitaryFormula :: CharParser st THFUnitaryFormula
thfUnitaryFormula = fmap TUF_THF_Logic_Formula_Par (parentheses thfLogicFormula)
  <|> fmap TUF_THF_Quantified_Formula thfQuantifiedFormula
  <|> thfUnaryFormula
  <|> fmap TUF_THF_Atom thfAtom
  <|> fmap TUF_THF_Tuple thfTuple
  <|> do
    key $ tryString ":="
    ll <- brackets (sepBy1 thfDefinedVar comma); colon
    uf <- thfUnitaryFormula
    return $ TUF_THF_Let ll uf
  <|> do
    key $ tryString "$itef"; oParentheses
    lf1 <- thfLogicFormula; comma
    lf2 <- thfLogicFormula; comma
    lf3 <- thfLogicFormula; cParentheses
    return $ TUF_THF_Conditional lf1 lf2 lf3

thfQuantifiedFormula :: CharParser st THFQuantifiedFormula
thfQuantifiedFormula = do
    q <- thfQuantifier
    vl <- brackets thfVariableList; colon
    uf <- thfUnitaryFormula
    return $ TQF_THF_Quantified_Formula q vl uf

thfVariableList :: CharParser st THFVariableList
thfVariableList = sepBy1 thfVariable comma

thfVariable :: CharParser st THFVariable
thfVariable = do
    v <- try (variable << colon)
    tlt <- thfTopLevelType
    return $ TV_THF_Typed_Variable v tlt
  <|> fmap TV_Variable variable

thfUnaryFormula :: CharParser st THFUnitaryFormula
thfUnaryFormula = do
    uc <- thfUnaryConnective
    lf <- parentheses thfLogicFormula
    return $ TUF_THF_Unary_Formula uc lf

thfTypeFormula :: CharParser st THFTypeFormula
thfTypeFormula = do
    tp <- try (thfTypeableFormula << colon)
    tlt <- thfTopLevelType
    return $ TTF_THF_Type_Formula tp tlt
  <|> do
    c <- try (constant << colon)
    tlt <- thfTopLevelType
    return $ TTF_THF_Typed_Const c tlt

thfTypeableFormula :: CharParser st THFTypeableFormula
thfTypeableFormula = fmap TTyF_THF_Atom thfAtom
  <|> fmap TTyF_THF_Tuple thfTuple
  <|> fmap TTyF_THF_Logic_Formula (parentheses thfLogicFormula)

thfSubType :: CharParser st THFSubType
thfSubType = do
    cf <- try (constant << key (string "<<"))
    cb <- constant
    return $ TST_THF_Sub_Type cf cb

thfTopLevelType :: CharParser st THFTopLevelType
thfTopLevelType = fmap TTLT_THF_Logic_Formula thfLogicFormula

thfUnitaryType :: CharParser st THFUnitaryType
thfUnitaryType = fmap TUT_THF_Unitary_Formula thfUnitaryFormula

thfBinaryType :: CharParser st THFBinaryType
thfBinaryType = do -- mappingType
    utf <- try (thfUnitaryType << arrow)
    utb <- sepBy1 thfUnitaryType arrow
    return $ TBT_THF_Mapping_Type (utf : utb)
  <|> do -- xprodType
    utf <- try (thfUnitaryType << star)
    utb <- sepBy1 thfUnitaryType star
    return $ TBT_THF_Xprod_Type (utf : utb)
  <|> do -- unionType
    utf <- try (thfUnitaryType << plus)
    utb <- sepBy1 thfUnitaryType plus
    return $ TBT_THF_Union_Type (utf : utb)

thfAtom :: CharParser st THFAtom
thfAtom = fmap TA_Defined_Type definedType
  <|> fmap TA_Defined_Plain_Formula definedPlainFormula
  <|> fmap TA_System_Type systemType
  <|> fmap TA_System_Atomic_Formula systemTerm
  <|> fmap TA_Term term
  <|> fmap TA_THF_Conn_Term thfConnTerm

thfTuple :: CharParser st THFTuple
thfTuple = try ((oBracket >> cBracket) >> return [])
  <|> brackets (sepBy1 thfUnitaryFormula comma)

thfDefinedVar :: CharParser st THFDefinedVar
thfDefinedVar = fmap TDV_THF_Defined_Var_Par (parentheses thfDefinedVar)
  <|> do
    v <- try (thfVariable << key ( string ":="))
    lf <- thfLogicFormula
    return $ TDV_THF_Defined_Var v lf

thfSequent :: CharParser st THFSequent
thfSequent = fmap TS_THF_Sequent_Par (parentheses thfSequent)
  <|> do
    tf <- try (thfTuple << gentzenArrow)
    tb <- thfTuple
    return $ TS_THF_Sequent tf tb

thfConnTerm :: CharParser st THFConnTerm
thfConnTerm = fmap TCT_THF_Pair_Connective thfPairConnective
  <|> fmap TCT_Assoc_Connective assocConnective
  <|> fmap TCT_THF_Unary_Connective thfUnaryConnective

thfQuantifier :: CharParser st THFQuantifier
thfQuantifier = (keyChar '!'    >> return TQ_ForAll)
  <|> (keyChar '?'              >> return TQ_Exists)
  <|> (keyChar '^'              >> return TQ_Lambda_Binder)
  <|> (key (tryString "!>")     >> return TQ_Dependent_Product)
  <|> (key (tryString "?*")     >> return TQ_Dependent_Sum)
  <|> (key (tryString "@+")     >> return TQ_Indefinite_Description)
  <|> (key (tryString "@-")     >> return TQ_Definite_Description)
  <?> "quantifier"

thfPairConnective :: CharParser st THFPairConnective
thfPairConnective = (key (tryString "!=")   >> return Infix_Inequality)
  <|> (key (tryString "<=>")    >> return Equivalent)
  <|> (key (tryString "=>")     >> return Implication)
  <|> (key (tryString "<=")     >> return IF)
  <|> (key (tryString "<~>")    >> return XOR)
  <|> (key (tryString "~|")     >> return NOR)
  <|> (key (tryString "~&")     >> return NAND)
  <|> (keyChar '='              >> return Infix_Equality)
  <?> "pairConnective"

thfUnaryConnective :: CharParser st THFUnaryConnective
thfUnaryConnective = (keyChar '~'   >> return Negation)
  <|> (key (tryString "!!")         >> return PiForAll)
  <|> (key (tryString "??")         >> return SigmaExists)

assocConnective :: CharParser st AssocConnective
assocConnective = (keyChar '|'  >> return OR)
  <|> (keyChar '&'              >> return AND)

definedType :: CharParser st DefinedType
definedType = do
    adw <- atomicDefinedWord
    case adw of
        "oType"     -> return DT_oType
        "o"         -> return DT_o
        "iType"     -> return DT_iType
        "i"         -> return DT_i
        "tType"     -> return DT_tType
        "real"      -> return DT_real
        "rat"       -> return DT_rat
        "int"       -> return DT_int
        _           -> fail ("No such definedType: " ++ adw)

systemType :: CharParser st SystemType
systemType = atomicSystemWord

definedPlainFormula :: CharParser st DefinedPlainFormula
definedPlainFormula = fmap DPF_Defined_Prop definedProp
  <|> do
    dp <- definedPred
    a <- parentheses arguments
    return $ DPF_Defined_Formula dp a

definedProp :: CharParser st DefinedProp
definedProp = do
    adw <- atomicDefinedWord
    case adw of
        "true"      -> return DP_True
        "false"     -> return DP_False
        _           -> fail ("No such definedProp: " ++ adw)

definedPred :: CharParser st DefinedPred
definedPred = do
    adw <- atomicDefinedWord
    case adw of
        "equal"         -> return Equal
        "distinct"      -> return Disrinct
        "itef"          -> return Itef
        "less"          -> return Less
        "lesseq"        -> return Lesseq
        "greater"       -> return Greater
        "greatereq"     -> return Greatereq
        "evaleq"        -> return Evaleq
        "is_int"        -> return Is_int
        "is_rat"        -> return Is_rat
        _               -> fail ("No such definedPred: " ++ adw)

term :: CharParser st Term
term = fmap T_Function_Term functionTerm
  <|> fmap T_Variable variable

functionTerm :: CharParser st FunctionTerm
functionTerm = fmap FT_System_Term systemTerm
  <|> fmap FT_Defined_Term definedTerm
  <|> fmap FT_Plain_Term plainTerm

plainTerm :: CharParser st PlainTerm
plainTerm = try (do
    f <- tptpFunctor
    a <- parentheses arguments
    return $ PT_Plain_Term f a)
  <|> fmap PT_Constant constant

constant :: CharParser st Constant
constant = tptpFunctor

tptpFunctor :: CharParser st TPTPFunctor
tptpFunctor = atomicWord

definedTerm :: CharParser st DefinedTerm
definedTerm = fmap DT_Defined_Atomic_Term definedPlainTerm
  <|> fmap DT_Defined_Atom definedAtom

definedAtom :: CharParser st DefinedAtom
definedAtom = fmap DA_Number number
  <|> fmap DA_Distinct_Object distinctObject

definedPlainTerm :: CharParser st DefinedPlainTerm
definedPlainTerm = try (do
    df <- definedFunctor
    a <- parentheses arguments
    return $ DPT_Defined_Function df a)
  <|> fmap DPT_Defined_Constant definedFunctor

definedFunctor :: CharParser st DefinedFunctor
definedFunctor = do
    adw <- atomicDefinedWord
    case adw of
        "itett"         -> return Itett
        "uminus"        -> return Uminus
        "sum"           -> return Sum
        "difference"    -> return Difference
        "product"       -> return Product
        "to_int"        -> return To_int
        "to_rat"        -> return To_rat
        "to_real"       -> return To_real
        _               -> fail ("No such definedFunctor: " ++ adw)

systemTerm :: CharParser st SystemTerm
systemTerm = try (do
    sf <- systemFunctor
    a <- parentheses arguments
    return $ ST_System_Term sf a)
  <|> fmap ST_System_Constant systemFunctor

systemFunctor :: CharParser st SystemFunctor
systemFunctor = atomicSystemWord

variable :: CharParser st Variable
variable = do
    u <- upper
    an <- many alphaNum
    skipAll
    return (u : an)
  <?> "Variable"

arguments :: CharParser st Arguments
arguments = sepBy1 term comma

principalSymbol :: CharParser st PrincipalSymbol
principalSymbol = fmap PS_Functor tptpFunctor
  <|> fmap PS_Variable variable

source :: CharParser st Source
source = (key (tryString "unknown")  >>  return S_Unknown)
  <|> fmap S_Dag_Source dagSource
  <|> fmap S_External_Source externalSource
  <|> fmap S_Sources (sepBy1 source comma)
  <|> do -- internal_source
    key $ tryString "introduced"; oParentheses
    it <- introType
    oi <- optionalInfo; cParentheses
    return $ S_Internal_Source it oi

dagSource :: CharParser st DagSource
dagSource = do
    key (tryString "inference"); oParentheses
    ir <- atomicWord; comma
    ui <- usefulInfo; comma
    pl <- brackets (sepBy1 parentInfo comma)
    cParentheses
    return (DS_Inference_Record ir ui pl)
  <|> fmap DS_Name name

parentInfo :: CharParser st ParentInfo
parentInfo = do
    s <- source
    pd <- parentDetails
    return $ PI_Parent_Info s pd

parentDetails :: CharParser st (Maybe GeneralList)
parentDetails = fmap Just (colon >> generalList)
  <|> (notFollowedBy (char ':') >> return Nothing)

introType :: CharParser st IntroType
introType = (key (tryString "definition")   >> return IT_definition)
  <|> (key (tryString "axiom_of_choice")    >> return IT_axiom_of_choice)
  <|> (key (tryString "tautology")          >> return IT_tautology)
  <|> (key (tryString "assumption")         >> return IT_assumption)

externalSource :: CharParser st ExternalSource
externalSource = fmap ES_File_Source fileSource
  <|> do
    key $ tryString "theory"; oParentheses
    tn <- theoryName
    oi <- optionalInfo; cParentheses
    return $ ES_Theory tn oi
  <|> do
    key $ tryString "creator"; oParentheses
    cn <- atomicWord
    oi <- optionalInfo; cParentheses
    return $ ES_Creator_Source cn oi

fileSource :: CharParser st FileSource
fileSource = do
    key $ tryString "file"; oParentheses
    fn <- fileName
    fi <- fileInfo; cParentheses
    return $ FS_File fn fi

fileInfo :: CharParser st (Maybe Name)
fileInfo = fmap Just (comma >> name)
  <|> (notFollowedBy (char ',') >> return Nothing)

theoryName :: CharParser st TheoryName
theoryName = (key (tryString "equality")  >> return Equality)
  <|> (key (tryString "ac")               >> return Ac)

optionalInfo :: CharParser st OptionalInfo
optionalInfo = fmap Just (comma >> usefulInfo)
  <|> (notFollowedBy (char ',') >> return Nothing)

usefulInfo :: CharParser st UsefulInfo
usefulInfo = (oBracket >> cBracket >> return [])
  <|> brackets (sepBy1 infoItem comma)

infoItem :: CharParser st InfoItem
infoItem = fmap II_Formula_Item formulaItem
  <|> fmap II_Inference_Item inferenceItem
  <|> fmap II_General_Function generalFunction

formulaItem :: CharParser st FormulaItem
formulaItem = do
    key $ tryString "description"
    fmap FI_Description_Item (parentheses atomicWord)
  <|> do
    key $ tryString "iquote"
    fmap FI_Iquote_Item (parentheses atomicWord)

inferenceItem :: CharParser st InferenceItem
inferenceItem = fmap II_Inference_Status inferenceStatus
  <|> do
    key $ tryString "assumptions"
    fmap II_Assumptions_Record (parentheses (brackets nameList))
  <|> do
    key $ tryString "new_symbols"; oParentheses
    aw <- atomicWord; comma
    nsl <- brackets (sepBy1 principalSymbol comma); cParentheses
    return $ II_New_Symbol_Record aw nsl
  <|> do
    key $ tryString "refutation"
    fmap II_Refutation (parentheses fileSource)

inferenceStatus :: CharParser st InferenceStatus
inferenceStatus = do
    key $ tryString "status"
    fmap IS_Status (parentheses statusValue)
  <|> do
    ir <- try (atomicWord << oParentheses)
    aw <- atomicWord; comma
    gl <- generalList; cParentheses
    return $ IS_Inference_Info ir aw gl

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

nameList :: CharParser st NameList
nameList = sepBy1 name comma

generalTerm :: CharParser st GeneralTerm
generalTerm = do
    gd <- try (generalData << notFollowedBy (char ':'))
    return $ GT_General_Data gd
  <|> do
    gd <- try (generalData << colon)
    gt <- generalTerm
    return $ GT_General_Data_Term gd gt
  <|> fmap GT_General_List generalList

generalData :: CharParser st GeneralData
generalData = fmap GD_Variable variable
  <|> fmap GD_Number number
  <|> fmap GD_Distinct_Object distinctObject
  <|> do
    key $ tryString "bind"; oParentheses
    v <- variable; comma
    fd <- formulaData; cParentheses
    return (GD_Bind v fd)
  <|> fmap GD_General_Function generalFunction
  <|> fmap GD_Atomic_Word atomicWord
  <|> fmap GD_Formula_Data formulaData

generalFunction :: CharParser st GeneralFunction
generalFunction = do
    aw <- atomicWord
    gts <- parentheses generalTerms
    return $ GF_General_Function aw gts

formulaData :: CharParser st FormulaData
formulaData = fmap THF_Formula thfFormula

generalList :: CharParser st GeneralList
generalList = (try (oBracket >> cBracket) >> return [])
  <|> brackets generalTerms

generalTerms :: CharParser st [GeneralTerm]
generalTerms = sepBy1 generalTerm comma

name :: CharParser st Name
name = fmap N_Integer (integer << skipAll)
  <|> fmap N_Atomic_Word atomicWord

atomicWord :: CharParser st AtomicWord
atomicWord = fmap A_Lower_Word lowerWord
  <|> fmap A_Single_Quoted singleQuoted
  <?> "lowerWord or singleQuoted"

atomicDefinedWord :: CharParser st String
atomicDefinedWord = char '$' >> lowerWord

atomicSystemWord :: CharParser st AtomicSystemWord
atomicSystemWord = tryString "$$" >> lowerWord

number :: CharParser st Number
number = fmap Num_Real (real << skipAll)
  <|> fmap Num_Rational (rational << skipAll)
  <|> fmap Num_Integer (integer << skipAll)

fileName :: CharParser st FileName
fileName = singleQuoted

singleQuoted :: CharParser st SingleQuoted
singleQuoted = do
    char '\''
    s <- fmap concat $ many1 (tryString "\\\\" <|> tryString "\\'"
        <|> tryString "\\\'"
        <|> single ( satisfy (\ c -> printable c && notElem c ['\'', '\\'])))
    keyChar '\''
    return s

distinctObject :: CharParser st DistinctObject
distinctObject = do
    char '\"'
    s <- fmap concat $ many1 (tryString "\\\\" <|> tryString "\\\""
        <|> single ( satisfy (\ c -> printable c && notElem c ['\'', '\\'])))
    keyChar '\"'
    return s

lowerWord :: CharParser st LowerWord
lowerWord = do
    l <- lower
    an <- many (alphaNum <|> char '_'); skipAll
    return (l : an)
  <?> "alphanumeric word with leading lowercase letter"

printableChar :: CharParser st Char
printableChar = satisfy printable

printable :: Char -> Bool
printable c = ord c >= 32 && ord c <= 126

-- Numbers
real :: CharParser st String
real = try (do
    s <- oneOf "-+"
    ur <- unsignedReal
    return (s : ur))
  <|> unsignedReal
  <?> "(signed) real"

unsignedReal :: CharParser st String
unsignedReal = do
    de <- try (do
        d <- decimalFractional <|> decimal
        e <- oneOf "Ee"
        return (d ++ [e]))
    ex <- decimal
    return (de ++ ex)
  <|> decimalFractional
  <?> "unsigned real"

rational :: CharParser st String
rational = try (do
    s <- oneOf "-+"
    ur <- unsignedRational
    return (s : ur))
  <|> unsignedRational
  <?> "(signed) rational"

unsignedRational :: CharParser st String
unsignedRational = do
    d1 <- try (decimal << char '/')
    d2 <- positiveDecimal
    return (d1 ++ "/" ++ d2)

integer :: CharParser st String
integer = try (do
    s <- oneOf "-+"
    ui <- unsignedInteger
    return (s : ui))
  <|> unsignedInteger
  <?> "(signed) integer"

unsignedInteger :: CharParser st String
unsignedInteger = try ( decimal << notFollowedBy (oneOf "eE/."))

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


--------------------------------------------------------------------------------
-- Some helper functions
--------------------------------------------------------------------------------

skipAll :: CharParser st ()
skipAll = skipMany (skipMany1 space <|>
                    ((comment <|> definedComment <|>
                      systemComment) >> return ()))

skipSpaces :: CharParser st ()
skipSpaces = skipMany space

key :: CharParser st a -> CharParser st ()
key = (>> skipAll)

keyChar :: Char -> CharParser st ()
keyChar = key . char

myManyTill :: CharParser st a -> CharParser st a -> CharParser st [a]
myManyTill p end = do
    e <- end ; return [e]
  <|> do
    x <- p; xs <- myManyTill p end; return (x : xs)


--------------------------------------------------------------------------------
-- Different simple symbols
--------------------------------------------------------------------------------

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
