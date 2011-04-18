{- |
Module      :  $Header$
Description :  A parser for the TPTP-THF Syntax
Copyright   :  (c) A.Tsogias, DFKI Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :
Stability   :
Portability :

A parser for the TPTP-THF Input Syntax v5.1.0.1 taken from
<http://www.cs.miami.edu/~tptp/TPTP/SyntaxBNF.html>
-}

-- bnf no_star_slash ist auch unverständlich

-- siehe 146

module THF.ParseTHF {- (parseTHF) -} where

import Text.ParserCombinators.Parsec
import THF.As
import Common.Parsec

import Char

-- Parser

parseTHF :: Parser [TPTP_THF]
parseTHF = do
    skipSpaces
    thf <- many (comment <|> definedComment     <|> systemComment <|>
                 include <|> thfAnnotatedFormula)
    skipSpaces; eof
    return thf

-- wie verhalten sich comments in comments?
-- die lines sollten damit kein problem haben aber die blocks werden rummeckern
comment :: Parser TPTP_THF
comment = do
    try (char '%' >> notFollowedBy (char '$'))
    c <- many printableChar
    skipSpaces
    return $ TPTP_Comment (Comment_Line c)
  <|> do
    try (string "/*" >> notFollowedBy (char '$'))
    c <- many (noneOf "*/")
    skipMany1 (char '*'); char '/'
    skipSpaces
    return $ TPTP_Comment (Comment_Block (lines c))


definedComment :: Parser TPTP_THF
definedComment = do
    try(string "%$" >> notFollowedBy (char '$'))
    c <- many printableChar
    skipSpaces
    return $ TPTP_Defined_Comment (Defined_Comment_Line c)
  <|> do
    try (string "/*$" >> notFollowedBy (char '$'))
    c <- many (noneOf "*/")
    skipMany1 (char '*'); char '/'
    skipSpaces
    return $ TPTP_Defined_Comment (Defined_Comment_Block (lines c))

systemComment :: Parser TPTP_THF
systemComment = do
    tryString "%$$"
    c <- many printableChar
    skipSpaces
    return $ TPTP_System_Comment (System_Comment_Line c)
  <|> do
    tryString "/*$$"
    c <- many (noneOf "*/")
    skipMany1 (char '*'); char '/'
    skipSpaces
    return $ TPTP_System_Comment (System_Comment_Block (lines c))

include :: Parser TPTP_THF
include = do
    key $ tryString "include"
    oParentheses
    fn <- fileName
    fs <- formulaSelection
    cParentheses; char '.'
    skipSpaces
    return $ TPTP_Include (I_Include fn fs)

thfAnnotatedFormula :: Parser TPTP_THF
thfAnnotatedFormula = do
    key $ tryString "thf"
    oParentheses
    n <- name; comma
    fr <- formulaRole; comma
    tf <- thfFormula
    a <- annotations
    cParentheses; char '.'
    skipSpaces
    return $ TPTP_THF_Annotated_Formula n fr tf a

annotations :: Parser Annotations
annotations = do
    comma
    s <- source
    oi <- optionalInfo
    return $ Annotations s oi
  <|> do
    notFollowedBy (char ',');
    return Null

formulaRole :: Parser FormulaRole
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

thfFormula :: Parser THFFormula
thfFormula = fmap TF_THF_Logic_Formula thfLogicFormula
  <|> fmap TF_THF_Sequent thfSequent

thfLogicFormula :: Parser THFLogicFormula
thfLogicFormula = fmap TLF_THF_Binary_Formula thfBinaryFormula
  <|> fmap TLF_THF_Type_Formula thfTypeFormula
  <|> fmap TLF_THF_Sub_Type thfSubType
  <|> fmap TLF_THF_Unitary_Formula thfUnitaryFormula

thfBinaryFormula :: Parser THFBinaryFormula
thfBinaryFormula = fmap TBF_THF_Binary_Type thfBinaryType
  <|> fmap TBF_THF_Binary_Tuple thfBinaryTuple
  <|> thfBinaryPair


-- hier pack ich sicherheitshalber momentan noch ein try davor
-- ist aber ein TODO
thfBinaryPair :: Parser THFBinaryFormula
thfBinaryPair = try (do
    uff <- thfUnitaryFormula
    pc <- thfPairConnective
    ufb <- thfUnitaryFormula
    return $ TBF_THF_Binary_Pair uff pc ufb)

thfBinaryTuple :: Parser THFBinaryTuple
thfBinaryTuple = do -- or
    uff <- try (thfUnitaryFormula << vLine)
    ufb <- sepBy1 thfUnitaryFormula vLine
    return $ TBT_THF_Or_Formula uff ufb
  <|> do -- and
    uff <- try (thfUnitaryFormula << ampersand)
    ufb <- sepBy1 thfUnitaryFormula ampersand
    return $ TBT_THF_And_Formula uff ufb
  <|> do -- apply
    uff <- try (thfUnitaryFormula << at)
    ufb <- sepBy1 thfUnitaryFormula at
    return $ TBT_THF_Apply_Formula uff ufb

thfUnitaryFormula :: Parser THFUnitaryFormula
thfUnitaryFormula = fmap TUF_THF_Logic_Formula_Par (parentheses thfLogicFormula)
  <|> thfQuantifiedFormula
  <|> thfUnaryFormula
  <|> fmap TUF_THF_Atom thfAtom
  <|> fmap TUF_THF_Tuple thfTuple
  <|> do
    key $ tryString ":="
    ll <- brackets (sepBy1 thfDefinedVar comma)
    colon
    uf <- thfUnitaryFormula
    return $ TUF_THF_Let ll uf
  <|> do
    key $ tryString "$itef"; oParentheses
    lf1 <- thfLogicFormula; comma
    lf2 <- thfLogicFormula; comma
    lf3 <- thfLogicFormula; cParentheses
    return $ TUF_THF_Conditional lf1 lf2 lf3

thfQuantifiedFormula :: Parser THFUnitaryFormula
thfQuantifiedFormula = do
    q <- thfQuantifier
    vl <- brackets (sepBy1 thfVariable comma)
    colon
    uf <- thfUnitaryFormula
    return $ TUF_THF_Quantified_Formula q vl uf

thfVariable :: Parser THFVariable
thfVariable = do
    v <- try (variable << colon)
    tlt <- thfTopLevelType
    return $ TV_THF_Typed_Variable v tlt
  <|> fmap TV_Variable variable

thfUnaryFormula :: Parser THFUnitaryFormula
thfUnaryFormula = do
    uc <- thfUnaryConnective
    lf <- parentheses thfLogicFormula
    return $ TUF_THF_Unary_Formula uc lf

thfTypeFormula :: Parser THFTypeFormula
thfTypeFormula = do
    tp <- try (thfTypeableFormula << colon)
    tlt <- thfTopLevelType
    return $ TTF_THF_Type_Formula tp tlt
  <|> do
    c <- try (constant << colon)
    tlt <- thfTopLevelType
    return $ TTF_THF_Role_Type c tlt

thfTypeableFormula :: Parser THFTypeableFormula
thfTypeableFormula = fmap TTyF_THF_Atom thfAtom
  <|> fmap TTyF_THF_Tuple thfTuple
  <|> fmap TTyF_THF_Logic_Formula (parentheses thfLogicFormula)

thfSubType :: Parser THFSubType
thfSubType = do
    cf <- try (constant << (key $ string "<<"))
    cb <- constant
    return $ TST_THF_Sub_Type cf cb

thfTopLevelType :: Parser THFTopLevelType
thfTopLevelType = thfLogicFormula

thfUnitaryType :: Parser THFUnitaryType
thfUnitaryType = thfUnitaryFormula

thfBinaryType :: Parser THFBinaryType
thfBinaryType = do -- mappingType
    utf <- try (thfUnitaryType << arrow)
    utb <- sepBy1 thfUnitaryType arrow
    return $ TBT_THF_Mapping_Type utf utb
  <|> do -- xprodType
    utf <- try (thfUnitaryType << star)
    utb <- sepBy1 thfUnitaryType star
    return $ TBT_THF_Xprod_Type utf utb
  <|> do -- unionType
    utf <- try (thfUnitaryType << plus)
    utb <- sepBy1 thfUnitaryType plus
    return $ TBT_THF_Union_Type utf utb

thfAtom :: Parser THFAtom
thfAtom = fmap TA_Defined_Type definedType
  <|> fmap TA_Defined_Plain_Formula definedPlainFormula
  <|> fmap TA_System_Type atomicSystemWord
  <|> fmap TA_System_Atomic_Formula systemTerm
  <|> fmap TA_Term term
  <|> fmap TA_THF_Conn_Term thfConnTerm

thfTuple :: Parser THFTuple
thfTuple = (try (oBracket >> cBracket) >> return [])
  <|> brackets (sepBy1 thfUnitaryFormula comma)

thfDefinedVar :: Parser THFDefinedVar
thfDefinedVar = fmap TDV_THF_Defined_Var_Br (parentheses thfDefinedVar)
  <|> do
    v <- try (thfVariable << (key $ string ":="))
    lf <- thfLogicFormula
    return $ TDV_THF_Defined_Var v lf

thfSequent :: Parser THFSequent
thfSequent = fmap TS_THF_Sequent_Bracketed (try (parentheses thfSequent))
  <|> do
    tf <- try (thfTuple << gentzenArrow)
    tb <- thfTuple
    return $ TS_THF_Sequent tf tb

thfConnTerm :: Parser THFConnTerm
thfConnTerm = fmap TCT_THF_Pair_Connective thfPairConnective
  <|> fmap TCT_Assoc_Connective assocConnective
  <|> fmap TCT_THF_Unary_Connective thfUnaryConnective

thfQuantifier :: Parser THFQuantifier
thfQuantifier = (keyChar '!'    >> return ForAll)
  <|> (keyChar '?'            >> return Exists)
  <|> (keyChar '^'            >> return Lambda_Binder)
  <|> (key (tryString "!>")   >> return Dependent_Product)
  <|> (key (tryString "?*")   >> return Dependent_Sum)
  <|> (key (tryString "@+")   >> return Indefinite_Description)
  <|> (key (tryString "@-")   >> return Definite_Description)
  <?> "quantifier"

thfPairConnective :: Parser THFPairConnective
thfPairConnective = (key (tryString "!=")       >> return Infix_Inequality)
  <|> (key (tryString "<=>")      >> return Equivalent)
  <|> (key (tryString "=>")       >> return Implication)
  <|> (key (tryString "<=")       >> return IF)
  <|> (key (tryString "<~>")      >> return XOR)
  <|> (key (tryString "~|")       >> return NOR)
  <|> (key (tryString "~&")       >> return NAND)
  <|> (keyChar '='    >> return Infix_Equality)
  <?> "pairConnective"

thfUnaryConnective :: Parser THFUnaryConnective
thfUnaryConnective = (keyChar '~'   >> return Negation)
  <|> (key (tryString "!!")       >> return PiForAll)
  <|> (key (tryString "??")       >> return SigmaExists)

assocConnective :: Parser AssocConnective
assocConnective = (keyChar '|'  >> return OR)
  <|> (keyChar '&'            >> return AND)

definedType :: Parser DefinedType
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

definedPlainFormula :: Parser DefinedPlainFormula
definedPlainFormula = fmap DPF_Defined_Prop definedProp
  <|> do
    dp <- definedPred
    a <- parentheses arguments
    return $ DPF_Defined_Formula dp a

definedProp :: Parser DefinedProp
definedProp = do
    adw <- atomicDefinedWord
    case adw of
        "true"      -> return DP_True
        "false"     -> return DP_False
        _           -> fail ("No such definedProp: " ++ adw)

definedPred :: Parser DefinedPred
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

term :: Parser Term
term = fmap T_Function_Term functionTerm
  <|> fmap T_Variable variable

functionTerm :: Parser FunctionTerm
functionTerm = fmap FT_System_Term systemTerm
  <|> fmap FT_Defined_Term definedTerm
  <|> fmap FT_Plain_Term plainTerm

plainTerm :: Parser PlainTerm
plainTerm = try (do
    f <- tptpFunctor
    a <- parentheses arguments
    return $ PT_Plain_Term f a)
  <|> fmap PT_Constant constant

constant :: Parser Constant
constant = tptpFunctor

tptpFunctor :: Parser TPTPFunctor
tptpFunctor = atomicWord

definedTerm :: Parser DefinedTerm
definedTerm = fmap DT_Defined_Atomic_Term definedPlainTerm
  <|> fmap DT_Defined_Atom definedAtom

definedAtom :: Parser DefinedAtom
definedAtom = fmap DA_Number number
  <|> fmap DA_Distinct_Object distinctObject

definedPlainTerm :: Parser DefinedPlainTerm
definedPlainTerm = try (do
    df <- definedFunctor
    a <- parentheses arguments
    return $ DPT_Defined_Function df a)
  <|> fmap DPT_Defined_Constant definedFunctor

definedFunctor :: Parser DefinedFunctor
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

systemTerm :: Parser SystemTerm
systemTerm = try (do
    sf <- systemFunctor
    a <- parentheses arguments
    return $ ST_System_Term sf a)
  <|> fmap ST_System_Constant systemFunctor

systemFunctor :: Parser SystemFunctor
systemFunctor = atomicSystemWord

variable :: Parser Variable
variable = do
    u <- upper
    an <- many alphaNum
    skipAll
    return (u : an)
  <?> "Variable"

arguments :: Parser Arguments
arguments = sepBy1 term comma

principalSymbol :: Parser PrincipalSymbol
principalSymbol = fmap PS_Functor tptpFunctor
  <|> fmap PS_Variable variable

source :: Parser Source
source = ((key $ tryString "unknown")  >>  return S_Unknown)
  <|> fmap S_Dag_Source dagSource
  <|> fmap S_External_Source externalSource
  <|> fmap S_Sources (sepBy1 source comma)
  <|> do -- internal_source
    key $ tryString "introduced"; oParentheses
    it <- introType
    oi <- optionalInfo; cParentheses
    return $ S_Internal_Source it oi

dagSource :: Parser DagSource
dagSource = do
    key (tryString "inference")
    oParentheses
    ir <- atomicWord; comma
    ui <- usefulInfo; comma
    pl <- brackets (sepBy1 parentInfo comma)
    cParentheses
    return (DS_Inference_Record ir ui pl)
  <|> fmap DS_Name name

parentInfo :: Parser ParentInfo
parentInfo = do
    s <- source
    pd <- parentDetails
    return $ PI_Parent_Info s pd

parentDetails :: Parser (Maybe GeneralList)
parentDetails = fmap Just (colon >> generalList)
  <|> (notFollowedBy (char ':') >> return Nothing)

introType :: Parser IntroType
introType = (key (tryString "definition")   >> return IT_definition)
  <|> (key (tryString "axiom_of_choice")    >> return IT_axiom_of_choice)
  <|> (key (tryString "tautology")          >> return IT_tautology)
  <|> (key (tryString "assumption")         >> return IT_assumption)

externalSource :: Parser ExternalSource
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

fileSource :: Parser FileSource
fileSource = do
    key $ tryString "file"; oParentheses
    fn <- fileName
    fi <- fileInfo; cParentheses
    return $ FS_File fn fi

fileInfo :: Parser (Maybe Name)
fileInfo = fmap Just (comma >> name)
  <|> (notFollowedBy (char ',') >> return Nothing)

theoryName :: Parser TheoryName
theoryName = ((key $ tryString "equality")  >> return Equality)
  <|> ((key $ tryString "ac")               >> return Ac)

optionalInfo :: Parser OptionalInfo
optionalInfo = fmap Just (comma >> usefulInfo)
  <|> (notFollowedBy (char ',') >> return Nothing)

usefulInfo :: Parser UsefulInfo
usefulInfo = (oBracket >> cBracket >> return [])
  <|> brackets (sepBy1 infoItem comma)

infoItem :: Parser InfoItem
infoItem = fmap II_Formula_Item formulaItem
  <|> fmap II_Inference_Item inferenceItem
  <|> fmap II_General_Function generalFunction

formulaItem :: Parser FormulaItem
formulaItem = do
    key $ tryString "description"
    fmap FI_Description_Item (parentheses atomicWord)
  <|> do
    key $ tryString "iquote"
    fmap FI_Iquote_Item (parentheses atomicWord)

inferenceItem :: Parser InferenceItem
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

inferenceStatus :: Parser InferenceStatus
inferenceStatus = do
    key $ tryString "status"
    fmap IS_Status (parentheses statusValue)
  <|> do
    ir <- try (atomicWord << oParentheses)
    aw <- atomicWord; comma
    gl <- generalList; cParentheses
    return $ IS_Inference_Info ir aw gl

statusValue :: Parser StatusValue
statusValue = choice $ map (\r -> key (tryString $ showStatusValue r)
                            >> return r) allStatusValues

allStatusValues :: [StatusValue]
allStatusValues =
  [Suc, Unp, Sap, Esa, Sat, Fsa, Thm, Eqv, Tac,
   Wec, Eth, Tau, Wtc, Wth, Cax, Sca, Tca, Wca,
   Cup, Csp, Ecs, Csa, Cth, Ceq, Unc, Wcc, Ect,
   Fun, Uns, Wuc, Wct, Scc, Uca, Noc]

showStatusValue :: StatusValue -> String
showStatusValue = map toLower . show

formulaSelection :: Parser (Maybe NameList)
formulaSelection = fmap Just (comma >> brackets nameList)
  <|> (notFollowedBy (char ',') >> return Nothing)

nameList :: Parser NameList
nameList = sepBy1 name comma

generalTerm :: Parser GeneralTerm
generalTerm = do
    gd <- try (generalData << notFollowedBy (char ':'))
    return $ GT_General_Data gd
  <|> do
    gd <- try (generalData << colon)
    gt <- generalTerm
    return $ GT_General_Data_Term gd gt
  <|> fmap GT_General_List generalList

generalData :: Parser GeneralData
generalData = fmap GD_Atomic_Word atomicWord
  <|> fmap GD_General_Function generalFunction
  <|> fmap GD_Variable variable
  <|> fmap GD_Number number
  <|> fmap GD_Distinct_Object distinctObject
  <|> fmap GD_Formula_Data formulaData
  <|> do
    key $ tryString "bind"; oParentheses
    v <- variable; comma
    fd <- formulaData; cParentheses
    return (GD_Bind v fd)

generalFunction :: Parser GeneralFunction
generalFunction = do
    aw <- atomicWord
    gts <- parentheses generalTerms
    return $ GF_General_Function aw gts

formulaData :: Parser FormulaData
formulaData = fmap THF_Formula thfFormula

generalList :: Parser GeneralList
generalList = (try (oBracket >> cBracket) >> return [])
  <|> brackets generalTerms

generalTerms :: Parser [GeneralTerm]
generalTerms = sepBy1 generalTerm comma

name :: Parser Name
name = fmap N_Integer (integer << skipAll)
  <|> fmap N_Atomic_Word atomicWord

atomicWord :: Parser AtomicWord
atomicWord = fmap A_Lower_Word lowerWord
  <|> fmap A_Single_Quoted singleQuoted
  <?> "lowerWord or singleQuoted"

atomicDefinedWord :: Parser String
atomicDefinedWord = char '$' >> lowerWord

atomicSystemWord :: Parser AtomicSystemWord
atomicSystemWord = tryString "$$" >> lowerWord

number :: Parser Number
number = fmap Num_Real (real << skipAll)
  <|> fmap Num_Rational (rational << skipAll)
  <|> fmap Num_Integer (integer << skipAll)

fileName :: Parser FileName
fileName = singleQuoted

singleQuoted :: Parser SingleQuoted
singleQuoted = do
    char '\''
    s <- fmap concat $ many1 (tryString "\\\\" <|> tryString "\\'"
        <|> tryString "\\\'"
        <|> (single $ satisfy (\c -> printable c && c /= '\'' && c /= '\\')))
    keyChar '\''
    return s

distinctObject :: Parser DistinctObject
distinctObject = do
    char '\"'
    s <- fmap concat $ many1 (tryString "\\\\" <|> tryString "\\\""
        <|> (single $ satisfy (\c -> printable c && c /= '\"' && c /= '\\')))
    keyChar '\"'
    return s

lowerWord :: Parser LowerWord
lowerWord = do
    l <- lower
    an <- many (alphaNum <|> (char '_'))
    skipAll
    return (l : an)
  <?> "alphanumeric word with leading lowercase letter"

printableChar :: Parser Char
printableChar = satisfy printable

printable :: Char -> Bool
printable c = (ord c) >= 32 && (ord c) <= 126

-- Numbers
real :: Parser String
real = try (do
    s <- oneOf "-+"
    ur <- unsignedReal
    return (s : ur))
  <|> unsignedReal
  <?> "(signed) real"

unsignedReal :: Parser String
unsignedReal = do
    de <- try (do
        d <- (decimalFractional <|> decimal)
        e <- oneOf "Ee"
        return (d ++ [e]))
    ex <- decimal
    return (de ++ ex)
  <|> decimalFractional
  <?> "unsigned real"

rational :: Parser String
rational = try (do
    s <- oneOf "-+"
    ur <- unsignedRational
    return (s : ur))
  <|> unsignedRational
  <?> "(signed) rational"

unsignedRational :: Parser String
unsignedRational = do
    d1 <- try (decimal << char '/')
    d2 <- positiveDecimal
    return (d1 ++ "/" ++ d2)

integer :: Parser String
integer = try (do
    s <- oneOf "-+"
    ui <- decimal
    notFollowedBy (oneOf "eE/.")
    return (s : ui))
  <|> (decimal << notFollowedBy (oneOf "eE/."))
  <?> "(signed) integer"

decimal :: Parser String
decimal = do
    char '0'
    notFollowedBy digit
    return "0"
  <|> positiveDecimal
  <?> "single zero or digits"

positiveDecimal :: Parser String
positiveDecimal = do
    nz <- satisfy (\c -> isDigit c && c /= '0')
    d <- many digit
    return (nz : d)
  <?> "positiv decimal"

decimalFractional :: Parser String
decimalFractional = do
    dec <- try (decimal << char '.')
    n <- many1 digit
    return (dec ++ "." ++ n)
  <?> "decimal fractional"

-- some helper functions

skipAll :: Parser ()
skipAll = skipMany ((skipMany1 space) <|>
                    ((comment <|> definedComment <|>
                      systemComment)
                     >> return ()))

skipSpaces :: Parser ()
skipSpaces = skipMany space

key :: Parser a -> Parser ()
key = (>> skipAll)

keyChar :: Char -> Parser ()
keyChar = key . char

-- symbols

vLine :: Parser ()
vLine = keyChar '|'

star :: Parser ()
star = keyChar '*'

plus :: Parser ()
plus = keyChar '+'

arrow :: Parser ()
arrow = keyChar '>'

comma :: Parser ()
comma = keyChar ','

colon :: Parser ()
colon = keyChar ':'

oParentheses :: Parser ()
oParentheses = keyChar '('

cParentheses :: Parser ()
cParentheses = keyChar ')'

parentheses :: Parser a -> Parser a
parentheses p = do
    oParentheses
    r <- p
    cParentheses
    return r

oBracket :: Parser ()
oBracket = keyChar '['

cBracket :: Parser ()
cBracket = keyChar ']'

brackets :: Parser a -> Parser a
brackets p = do
    oBracket
    r <- p
    cBracket
    return r

ampersand :: Parser ()
ampersand = keyChar '&'

at :: Parser ()
at = keyChar '@'

gentzenArrow :: Parser ()
gentzenArrow = key $ string "-->"
