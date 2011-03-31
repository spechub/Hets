{- |
Module      :  $Header$
Description :  A abstract syntax for the TPTP-THF Syntax
Copyright   :  (c) A.Tsogias, DFKI Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :
Stability   :
Portability :

A parser for the TPTP-THF Input Syntax v5.1.0.1 taken from
<http://www.cs.miami.edu/~tptp/TPTP/SyntaxBNF.html>
-}


-- bnf no_star_slash ist auch unverständlich
-- siehe newSymbolRecord und seine spezifikation. sollen ( als keychars behandelt werden?
-- nochmal generell soll <wort(> als ein token gelten oder dürfen vor der
-- klammer noch leerzeichen sein?


module THF.ParseTHF (parseTHF) where

import Text.ParserCombinators.Parsec
import THF.As

import Common.Parsec

import Data.Ratio
import Char

-- Parser

-- run is just a method for testing parseTHF
run :: IO ()
run = case (parse parseTHF "" "           \n       \n  \n %$$hallo    \n\n /*$$ vsdfgvsdou \n seld \n***/ \n /*$   skjfg   \n\n   */\n  %$ lkdjfbhasdf  \n") of
    Left err -> do{ putStr "parse error at "
                  ; print err
                  }
    Right x -> print x


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
comment = try (do
    skipSpaces
    char '%'; notFollowedBy (char '$')
    c <- many printableChar
    skipSpaces
    return $ TPTP_Comment (Comment_Line c))
    <|> try (do
    skipSpaces
    char '/'; char '*'; notFollowedBy (char '$')
    c <- many (noneOf "*/")
    skipMany1 (char '*'); char '/'
    skipSpaces
    return $ TPTP_Comment (Comment_Block (lines c)))


definedComment :: Parser TPTP_THF
definedComment = try (do
    skipSpaces
    char '%'; char '$'; notFollowedBy (char '$')
    c <- many printableChar
    skipSpaces
    return $ TPTP_Defined_Comment (Defined_Comment_Line c))
    <|> try (do
    skipSpaces
    char '/'; char '*'; char '$'; notFollowedBy (char '$')
    c <- many (noneOf "*/")
    skipMany1 (char '*'); char '/'
    skipSpaces
    return $ TPTP_Defined_Comment (Defined_Comment_Block (lines c)))

systemComment :: Parser TPTP_THF
systemComment = try (do
    skipSpaces
    char '%'; char '$'; char '$'
    c <- many printableChar
    skipSpaces
    return $ TPTP_System_Comment (System_Comment_Line c))
    <|> try (do
    skipSpaces
    char '/'; char '*'; char '$'; char '$'
    c <- many (noneOf "*/")
    skipMany1 (char '*'); char '/'
    skipSpaces
    return $ TPTP_System_Comment (System_Comment_Block (lines c)))

include :: Parser TPTP_THF
include = try (do
    skipSpaces
    key $ string "include("
    fn <- fileName
    fs <- formulaSelection
    string ")."
    return $ TPTP_Include (I_Include fn fs))

thfAnnotatedFormula :: Parser TPTP_THF
thfAnnotatedFormula = try (do
    skipSpaces
    key $ string "thf("
    n <- name; comma
    fr <- formulaRole; comma
    tf <- thfFormula
    a <- annotations
    string ")."
    return $ TPTP_THF_Annotated_Formula n fr tf a)

annotations :: Parser Annotations
annotations = try (do
    comma
    s <- source
    oi <- optionalInfo
    return $ Annotations s oi)
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
thfFormula = try (thfLogicFormula   >>= (return . TF_THF_Logic_Formula))
    <|> (thfSequent                 >>= (return . TF_THF_Sequent))

thfLogicFormula :: Parser THFLogicFormula
thfLogicFormula = try (thfUnitaryFormula    >>= (return . TLF_THF_Unitary_Formula))
    <|> try(thfTypeFormula                  >>= (return . TLF_THF_Type_Formula))
    <|> try (thfBinaryFormula               >>= (return . TLF_THF_Binary_Formula))
    <|> (thfSubType                         >>= (return . TLF_THF_Sub_Type))

thfBinaryFormula :: Parser THFBinaryFormula
thfBinaryFormula = try (thfBinaryPair   >>= (return . TBF_THF_Binary_Pair))
    <|> try (thfBinaryTuple             >>= (return . TBF_THF_Binary_Tuple))
    <|> (thfBinaryType                  >>= (return . TBF_THF_Binary_Type))

thfBinaryPair :: Parser THFBinaryPair
thfBinaryPair = do
    uff <- thfUnitaryFormula
    pc <- thfPairConnective
    ufb <- thfUnitaryFormula
    return $ TBP_THF_Binary_Pair uff pc ufb

thfBinaryTuple :: Parser THFBinaryTuple
thfBinaryTuple = try (thfOrFormula  >>= (return . TBT_THF_Or_Formula))
    <|> try (thfAndFormula          >>= (return . TBT_THF_And_Formula))
    <|> (thfApplyFormula            >>= (return . TBT_THF_Apply_Formula))

thfOrFormula :: Parser THFOrFormula
thfOrFormula = try (do
    uff <- thfUnitaryFormula
    vLine
    ufb <- thfUnitaryFormula
    return $ TOF_THF_Or_Formula uff ufb)
    <|> do
    tof <- thfOrFormula
    vLine
    uf <- thfUnitaryFormula
    return $ TOF_THF_Or_Formula_Il tof uf

thfAndFormula :: Parser THFAndFormula
thfAndFormula = try (do
    uff <- thfUnitaryFormula
    ampersand
    ufb <- thfUnitaryFormula
    return $ TAF_THF_And_Formula uff ufb)
    <|> do
    af <- thfAndFormula
    ampersand
    uf <- thfUnitaryFormula
    return $ TAF_THF_And_Formula_Il af uf

thfApplyFormula :: Parser THFApplyFormula
thfApplyFormula = try (do
    uff <- thfUnitaryFormula
    at
    ufb <- thfUnitaryFormula
    return $ TApF_THF_Apply_Formula uff ufb)
    <|> do
    af <- thfApplyFormula
    at
    uf <- thfUnitaryFormula
    return $ TApF_THF_Apply_Formula_Il af uf

thfUnitaryFormula :: Parser THFUnitaryFormula
thfUnitaryFormula = try (do
        oParentheses
        lf <- thfLogicFormula
        cParentheses
        return $ TUF_THF_Logic_Formula lf)
    <|> try (thfQuantifiedFormula   >>= (return . TUF_THF_Quantified_Formula))
    <|> try (thfUnaryFormula        >>= (return . TUF_THF_Unary_Formula))
    <|> try (thfAtom                >>= (return . TUF_THF_atom))
    <|> try (thfTuple               >>= (return . TUF_THF_Tuple))
    <|> try (thfLet                 >>= (return . TUF_THF_Let))
    <|> (thfConditional             >>= (return . TUF_THF_Conditional))

thfQuantifiedFormula :: Parser THFQuantifiedFormula
thfQuantifiedFormula = do
    q <- thfQuantifier
    oBracket
    vl <- thfVariableList
    cBracket; colon
    uf <- thfUnitaryFormula
    return $ TQF_THF_Quantified_Formula q vl uf

thfVariableList :: Parser THFVariableList
thfVariableList = try (do
    v <- thfVariable
    notFollowedBy (char ',')
    return [v])
    <|> do
    v <- thfVariable
    comma
    vl <-thfVariableList
    return (v : vl)

thfVariable :: Parser THFVariable
thfVariable = try (thfTypedVariable >>= (return . TV_THF_Typed_Variable))
    <|> (variable                   >>= (return . TV_Variable))

thfTypedVariable :: Parser THFTypedVariable
thfTypedVariable = do
    v <- variable
    colon
    tlt <- thfTopLevelType
    return $ TTV_THF_Typed_Variable v tlt

thfUnaryFormula :: Parser THFUnaryFormula
thfUnaryFormula = do
    uc <- thfUnaryConnective
    oParentheses
    lf <- thfLogicFormula
    cParentheses
    return $ TUnF_THF_Unary_Formula uc lf

thfTypeFormula :: Parser THFTypeFormula
thfTypeFormula = try (do
    tp <- thfTypeableFormula
    colon
    tlt <- thfTopLevelType
    return $ TTF_THF_Type_Formula tp tlt)
    <|> do
    c <- constant
    colon
    tlt <- thfTopLevelType
    return $ TTF_THF_Role_Type c tlt

thfTypeableFormula :: Parser THFTypeableFormula
thfTypeableFormula = try (thfAtom   >>= (return . TTyF_THF_Atom))
    <|> try (thfTuple               >>= (return . TTyF_THF_Tuple))
    <|> (thfLogicFormula            >>= (return . TTyF_THF_Logic_Formula))

thfSubType :: Parser THFSubType
thfSubType = do
    cf <- constant
    key $ string "<<"
    cb <- constant
    return $ TST_THF_Sub_Type cf cb

thfTopLevelType :: Parser THFTopLevelType
thfTopLevelType = thfLogicFormula

thfUnitaryType :: Parser THFUnitaryType
thfUnitaryType = thfUnitaryFormula

thfBinaryType :: Parser THFBinaryType
thfBinaryType = try (thfMappingType >>= (return . TBT_THF_Mapping_Type))
    <|> try (thfXprodType           >>= (return . TBT_THF_Xprod_Type))
    <|> (thfUnionType               >>= (return . TBT_THF_Union_Type))

thfMappingType :: Parser THFMappingType
thfMappingType = try (do
    utf <- thfUnitaryType
    arrow
    utb <- thfUnitaryType
    return $ TMT_THF_Mapping_Type utf utb)
    <|> do
    ut <- thfUnitaryType
    arrow
    mt <- thfMappingType
    return $ TMT_THF_Mapping_Type_Il ut mt

thfXprodType :: Parser THFXprodType
thfXprodType = try (do
    utf <- thfUnitaryType
    star
    utb <- thfUnitaryType
    return $ TXT_THF_Xprod_Type utf utb)
    <|> do
    xt <- thfXprodType
    star
    ut <- thfUnitaryType
    return $ TXT_THF_Xprod_Type_Il xt ut

thfUnionType :: Parser THFUnionType
thfUnionType = try (do
    utf <- thfUnitaryType
    plus
    utb <- thfUnitaryType
    return $ TUT_THF_Union_Type utf utb)
    <|> do
    unt <- thfUnionType
    plus
    ut <- thfUnitaryType
    return $ TUT_THF_Union_Type_Il unt ut

thfAtom :: Parser THFAtom
thfAtom = try (definedType          >>= (return . TA_Defined_Type))
    <|> try (definedPlainFormula    >>= (return . TA_Defined_Plain_Formula))
    <|> try (atomicSystemWord       >>= (return . TA_System_Type))
    <|> try (systemTerm             >>= (return . TA_System_Atomic_Formula))
    <|> try (term                   >>= (return . TA_Term))
    <|> (thfConnTerm                >>= (return . TA_THF_Conn_Term))

thfTuple :: Parser THFTuple
thfTuple = try (do
    oBracket; cBracket
    return [])
    <|> do
    oBracket
    tl <- thfTupleList
    cBracket
    return tl

thfTupleList :: Parser [THFUnitaryFormula]
thfTupleList = try (do
    uf <- thfUnitaryFormula
    notFollowedBy (char ',')
    return [uf])
    <|> do
    uf <- thfUnitaryFormula
    comma
    tl <- thfTupleList
    return (uf : tl)

thfLet :: Parser THFLet
thfLet = do
    key $ string ":="
    oBracket
    ll <- thfLetList
    cBracket; colon
    uf <- thfUnitaryFormula
    return $ TL_THf_Let ll uf

thfLetList :: Parser THFLetList
thfLetList = try (do
    dv <- thfDefinedVar
    notFollowedBy (char ',')
    return [dv])
    <|> do
    dv <- thfDefinedVar
    comma
    ll <-thfLetList
    return (dv : ll)

thfDefinedVar :: Parser THFDefinedVar
thfDefinedVar = try (do
    oParentheses
    dv <- thfDefinedVar
    cParentheses
    return $ TDV_THF_Defined_Var_Bracketed dv)
    <|> do
    v <- thfVariable
    key $ string ":="
    lf <- thfLogicFormula
    return $ TDV_THF_Defined_Var v lf

thfConditional :: Parser THFConditional
thfConditional = do
    key $ string "$itef("
    lf1 <- thfLogicFormula
    comma
    lf2 <- thfLogicFormula
    comma
    lf3 <- thfLogicFormula
    cParentheses
    return $ TC_THF_Conditional lf1 lf2 lf3

thfSequent :: Parser THFSequent
thfSequent = try (do
    tf <- thfTuple
    gentzenArrow
    tb <- thfTuple
    return $ TS_THF_Sequent tf tb)
    <|> do
    oParentheses
    ts <- thfSequent
    cParentheses
    return $ TS_THF_Sequent_Bracketed ts

thfConnTerm :: Parser THFConnTerm
thfConnTerm = try (thfPairConnective    >>= (return . TCT_THF_Pair_Connective))
    <|> try (assocConnective            >>= (return . TCT_Assoc_Connective))
    <|> (thfUnaryConnective             >>= (return . TCT_THF_Unary_Connective))

thfQuantifier :: Parser THFQuantifier
thfQuantifier = try ((keyChar '!')  >> (return ForAll))
    <|> try ((keyChar '?')          >> (return Exists))
    <|> try ((keyChar '^')          >> (return Lambda_Binder))
    <|> try ((key $ string "!>")    >> (return Dependent_Product))
    <|> try ((key $ string "?*")    >> (return Dependent_Sum))
    <|> try ((key $ string "@+")    >> (return Indefinite_Description))
    <|> ((key $ string "@-")        >> (return Definite_Description))

thfPairConnective :: Parser THFPairConnective
thfPairConnective = try ((keyChar '=')  >> (return Infix_Equality))
    <|> try ((key $ string "!=")        >> (return Infix_Inequality))
    <|> try ((key $ string "<=>")       >> (return Equivalent))
    <|> try ((key $ string "=>")        >> (return Implication))
    <|> try ((key $ string "<=")        >> (return IF))
    <|> try ((key $ string "<~>")       >> (return XOR))
    <|> try ((key $ string "~|")        >> (return NOR))
    <|> ((key $ string "~&")            >> (return NAND))

thfUnaryConnective :: Parser THFUnaryConnective
thfUnaryConnective = try (keyChar '~'   >> return Negation)
    <|> try (key (string "!!")          >> return PiForAll)
    <|> (key (string "??")              >> return SigmaExists)

assocConnective :: Parser AssocConnective
assocConnective = try (keyChar '|'  >> return OR)
    <|> (keyChar '&'                >> return AND)

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
definedPlainFormula = try (definedProp >>= (return . DPF_Defined_Prop))
    <|> do
    dp <- definedPred
    oParentheses
    a <- arguments
    cParentheses
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
        "equal"         -> return DP_equal
        "distinct"      -> return DP_disrinct
        "itef"          -> return DP_itef
        "less"          -> return DP_less
        "lesseq"        -> return DP_lesseq
        "greater"       -> return DP_greater
        "greatereq"     -> return DP_greatereq
        "evaleq"        -> return DP_evaleq
        "is_int"        -> return DP_is_int
        "is_rat"        -> return DP_is_rat
        _               -> fail ("No such definedPred: " ++ adw)

term :: Parser Term
term = try (functionTerm    >>= (return . T_Function_Term))
    <|> (variable           >>= (return . T_Variable))

functionTerm :: Parser FunctionTerm
functionTerm = try (systemTerm  >>= (return . FT_System_Term))
    <|> try (definedTerm        >>= (return . FT_Defined_Term))
    <|> (plainTerm              >>= (return . FT_Plain_Term))

plainTerm :: Parser PlainTerm
plainTerm = try (do
    f <- tptpFunctor
    oParentheses
    a <- arguments
    cParentheses
    return $ PT_Plain_Term f a)
    <|> (constant >>= (return . PT_Constant))

constant :: Parser Constant
constant = tptpFunctor

tptpFunctor :: Parser TPTPFunctor
tptpFunctor = atomicWord

definedTerm :: Parser DefinedTerm
definedTerm = try (definedAtomicTerm    >>= (return . DT_Defined_Atomic_Term))
    <|> (definedAtom                    >>= (return . DT_Defined_Atom))

definedAtom :: Parser DefinedAtom
definedAtom = try (number   >>= (return . DA_Number))
    <|> (distinctObject     >>= (return . DA_Distinct_Object))

definedAtomicTerm :: Parser DefinedAtomicTerm
definedAtomicTerm = definedPlainTerm

definedPlainTerm :: Parser DefinedPlainTerm
definedPlainTerm = try (do
    df <- definedFunctor
    oParentheses
    a <- arguments
    cParentheses
    return $ DPT_Defined_Function df a)
    <|> (definedConstant >>= (return . DPT_Defined_Constant))

definedConstant :: Parser DefinedConstant
definedConstant = definedFunctor

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
    oParentheses
    a <- arguments
    cParentheses
    return $ ST_System_Term sf a)
    <|> (systemConstant >>= (return . ST_System_Constant))

systemConstant :: Parser SystemConstant
systemConstant = systemFunctor

systemFunctor :: Parser SystemFunctor
systemFunctor = atomicSystemWord

variable :: Parser Variable
variable = do
    u <- upper
    an <- many alphaNum
    skipAll
    return (u : an)
    <?> "alphanumeric word with leading uppercase letter"

arguments :: Parser Arguments
arguments = try (do
    t <- term
    notFollowedBy (char ',')
    return $ A_Term t)
    <|> (do
    t <- term
    comma
    a <- arguments
    return $ A_Arguments_Rec t a)

principalSymbol :: Parser PrincipalSymbol
principalSymbol = try (tptpFunctor  >>= (return . PS_Functor))
    <|> (variable                   >>= (return . PS_Variable))

source :: Parser Source
source = try ((key $ string "unknown")  >>  (return S_Unknown))
    <|> try (dagSource                  >>= (return . S_Dag_Source))
    <|> try (externalSource             >>= (return . S_External_Source))
    <|> try (sources                    >>= (return . S_Sources))
    <|> do -- internal_source
    key (string "introduced(")
    it <- introType
    oi <- optionalInfo
    return (S_Internal_Source it oi)

sources :: Parser Sources
sources = try (do
    s <- source;
    notFollowedBy (char ',')
    return [s])
    <|> do
    s <- source;
    comma
    ss <- sources
    return (s : ss)

dagSource :: Parser DagSource
dagSource = try (do
    n <- name
    return $ DS_Name n)
    <|> do
    key (string "inference(")
    ir <- atomicWord; comma
    ui <- usefulInfo; comma
    oBracket
    pl <- parentList
    cBracket
    cParentheses
    return (DS_Inference_Record ir ui pl)

parentList :: Parser ParentList
parentList = try (do
    pi <- parentInfo
    notFollowedBy (char ',')
    return [pi])
    <|> do
    pi <- parentInfo
    comma
    pl <- parentList
    return (pi : pl)

parentInfo :: Parser ParentInfo
parentInfo = do
    s <- source
    pd <- parentDetails
    return $ PI_Parent_Info s pd

parentDetails :: Parser (Maybe GeneralList)
parentDetails = try (do
    colon
    gl <- generalList
    return $ Just gl)
    <|> do
    notFollowedBy (char ',')
    return Nothing

introType :: Parser IntroType
introType = try ((key $ string "definition")    >> (return IT_definition))
    <|> try ((key $ string "axiom_of_choice")   >> (return IT_axiom_of_choice))
    <|> try ((key $ string "tautology")         >> (return IT_tautology))
    <|> ((key $ string "assumption")            >> (return IT_assumption))

externalSource :: Parser ExternalSource
externalSource = try (do
    fs <- fileSource
    return $ ES_File_Source fs) -- das gleiche in kuerzer: try (fileSource >>= (return . ES_File_Source))
    <|> try (do
    key $ string "theory("
    tn <- theoryName
    oi <- optionalInfo
    cParentheses
    return $ ES_Theory tn oi)
    <|> do
    key $ string "creator("
    cn <- atomicWord
    oi <- optionalInfo
    cParentheses
    return $ ES_Creator_Source cn oi

fileSource :: Parser FileSource
fileSource = do
    key $ string "file("
    fn <- fileName
    fi <- fileInfo
    cParentheses
    return $ FS_File fn fi

fileInfo :: Parser (Maybe Name)
fileInfo = try (do
    comma
    n <- name
    return $ Just n)
    <|> do
    notFollowedBy (char ',')
    return Nothing

theoryName :: Parser TheoryName
theoryName = try (do
    key $ string "equality"
    return Equality)
    <|> do
    key $ string "ac"
    return Ac

optionalInfo :: Parser OptionalInfo
optionalInfo = try (do
    comma
    ui <- usefulInfo
    return $ OI_Useful_Info ui)
    <|> do
    notFollowedBy (char ',')
    return OI_Null

usefulInfo :: Parser UsefulInfo
usefulInfo = try (do
    oBracket; cBracket
    return [])
    <|> do
    oBracket
    iis <- infoItems
    cBracket
    return iis

infoItems :: Parser [InfoItem]
infoItems = try (do
    ii <- infoItem
    notFollowedBy (char ',')
    return [ii])
    <|> do
    ii <- infoItem
    comma
    iis <- infoItems
    return (ii : iis)

infoItem :: Parser InfoItem
infoItem = try (formulaItem >>= (return . II_Formula_Item))
    <|> try(inferenceItem   >>= (return . II_Inference_Item))
    <|> (generalFunction    >>= (return . II_General_Function))

formulaItem :: Parser FormulaItem
formulaItem = try (do
    key $ string "description("
    aw <- atomicWord
    cParentheses
    return $ FI_Description_Item aw)
    <|> do
    key $ string "iquote("
    aw <- atomicWord
    cParentheses
    return $ FI_Iquote_Item aw

inferenceItem :: Parser InferenceItem
inferenceItem = try (inferenceStatus    >>= (return . II_Inference_Status))
    <|> try (assumptionRecord           >>= (return . II_Assumptions_Record))
    <|> try (newSymbolRecord            >>= (return . II_New_Symbol_Record))
    <|> (refutation                     >>= (return . II_Refutation))

inferenceStatus :: Parser InferenceStatus
inferenceStatus = try (do
    string "status("
    s <- statusValue
    cParentheses
    return $ IS_Status s)
    <|> do
    ir <- atomicWord
    oParentheses
    aw <- atomicWord
    comma
    gl <- generalList
    cParentheses
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

assumptionRecord :: Parser AssumptionRecord
assumptionRecord = do
    key $ string "assumptions("
    oBracket
    nl <- nameList
    cBracket; cParentheses
    return nl

refutation :: Parser Refutation
refutation = do
    key $ string "refutation("
    fs <- fileSource
    cParentheses
    return fs

newSymbolRecord :: Parser NewSymbolRecord
newSymbolRecord = do
    key $ string "new_symbols("
    aw <- atomicWord
    comma; oBracket
    nsl <- newSymbolList
    cBracket; cParentheses
    return $ NSR_New_Symbols aw nsl

newSymbolList :: Parser [PrincipalSymbol]
newSymbolList = try (do
    ps <- principalSymbol
    notFollowedBy (char ',')
    return [ps])
    <|> do
    ps <- principalSymbol
    comma
    nsl <- newSymbolList
    return (ps : nsl)

formulaSelection :: Parser FormulaSelection
formulaSelection = try (do
    comma; oBracket
    n <- nameList
    cBracket
    return (FS_Name_List n))
    <|> do
    notFollowedBy (char ',')
    return FS_Null

nameList :: Parser NameList
nameList = try (do
    n <- name
    comma
    nl <- nameList
    return (n : nl))
    <|> do
    n <- name
    notFollowedBy (char ',')
    return [n]

generalTerm :: Parser GeneralTerm
generalTerm = try (do
    gd <- generalData
    notFollowedBy (char ':')
    return $ GT_General_Data gd)
    <|> try (do
    gd <- generalData
    colon
    gt <- generalTerm
    return $ GT_General_Data_Term gd gt)
    <|> do
    gl <- generalList
    return $ GT_General_List gl

generalData :: Parser GeneralData
generalData = try (atomicWord   >>= (return . GD_Atomic_Word))
    <|> try (generalFunction    >>= (return . GD_General_Function))
    <|> try (variable           >>= (return . GD_Variable))
    <|> try (number             >>= (return . GD_Number))
    <|> try (distinctObject     >>= (return . GD_Distinct_Object))
    <|> try (formulaData        >>= (return . GD_Formula_Data))
    <|> do
    key $ string "bind("
    v <- variable
    comma
    fd <- formulaData
    cParentheses
    return (GD_Bind v fd)

generalFunction :: Parser GeneralFunction
generalFunction = do
    aw <- atomicWord
    oParentheses
    gts <- generalTerms
    cParentheses
    return $ GF_General_Function aw gts

formulaData :: Parser FormulaData
formulaData = thfFormula >>= (return .THF_Formula)

generalList :: Parser GeneralList
generalList = try (do
    oBracket; cBracket
    return [])
    <|> do
    oBracket
    gt <- generalTerms
    cBracket
    return gt

generalTerms :: Parser [GeneralTerm]
generalTerms = try (do
    gt <- generalTerm
    notFollowedBy (char ',')
    return [gt])
    <|> do
    gt <- generalTerm
    comma
    gts <- generalTerms
    return (gt : gts)

name :: Parser Name
name = try (do
    aw <- atomicWord
    return (N_Atomic_Word aw))
    <|> do
    i <- integer
    skipAll
    return (N_Integer i)

atomicWord :: Parser AtomicWord
atomicWord = try (lowerWord)
    <|> singleQuoted
    <?> "lowerWord or singleQuoted"

atomicDefinedWord :: Parser String
atomicDefinedWord = do
    char '$'
    lw <- lowerWord
    return lw

atomicSystemWord :: Parser AtomicSystemWord
atomicSystemWord = do
    string "$$"
    lw <- lowerWord
    return lw

number :: Parser Number
number = try (do
    r <- real; skipAll
    return $ Num_Real r)
    <|> try (do
    r <- rational; skipAll
    return $ Num_Rational r)
    <|> do
    i <- integer; skipAll
    return $ Num_Integer i

fileName :: Parser FileName
fileName = singleQuoted

singleQuoted :: Parser String
singleQuoted = do
    char '\''
    s <- fmap concat $ many1 (tryString "\\\\" <|> tryString "\\\'" <|> (single $ satisfy (\c -> printable c && c /= '\'' && c /= '\\')))
    keyChar '\''
    return s

distinctObject :: Parser DistinctObject
distinctObject = do
    char '\"'
    s <- fmap concat $ many1 (tryString "\\\\" <|> tryString "\\\"" <|> (single $ satisfy (\c -> printable c && c /= '\"' && c /= '\\')))
    keyChar '\"'
    return s

lowerWord :: Parser String
lowerWord = do
    l <- lower
    an <- many alphaNum
    skipAll
    return (l : an)
    <?> "alphanumeric word with leading lowercase letter"

printableChar :: Parser Char
printableChar = satisfy printable

printable :: Char -> Bool
printable c = (ord c) >= 32 && (ord c) <= 126

-- Numbers
real :: Parser String
real = try (signedReal)
    <|> unsignedReal
    <?> "(signed) real"

signedReal :: Parser String
signedReal = do
    s <- oneOf "-+"
    ur <- unsignedReal
    return (s : ur)
    <?> "signed real"

unsignedReal :: Parser String
unsignedReal =
    try (do
    df <- decimalFractional;
    notFollowedBy (oneOf "Ee")
    return df)
    <|> do
    d <- ((try decimalFractional) <|> decimal)
    e <- oneOf "Ee"
    ex <- decimal
    return (d ++ ([e]) ++ ex)
    <?> "unsigned real"

rational :: Parser String
rational = do
    s <- oneOf "-+"
    ur <- unsignedRational
    return (s : ur)
    <|> do
    ur <- unsignedRational
    return ur
    <?> "(signed) rational"

unsignedRational :: Parser String
unsignedRational = do
    d1 <- decimal
    s <- char '/'
    d2 <- positiveDecimal
    return (d1 ++ [s] ++ d2)

integer :: Parser String
integer = do
    s <- oneOf "-+"
    ui <- decimal
    return (s : ui)
    <|> do
    i <- decimal
    return i
    <?> "(signed) integer"

decimal :: Parser String
decimal = try (do
    char '0'; notFollowedBy digit
    return "0")
    <|> positiveDecimal
    <?> "single zero or digits"

positiveDecimal :: Parser String
positiveDecimal = do
    nz <- satisfy (\c -> isDigit c && c /= '0')
    d <- many digit
    return (nz : d)
    <?> "positiv decimal"

decimalFractional :: Parser String
decimalFractional =
    let toDouble a b = a + foldr (\c d -> c + d / 10) 0 (0 : b)
    in do
        dec <- decimal
        dot <- char '.'
        n <- many1 digit
        return (dec ++ [dot] ++ n)
       <?> "decimal fractional"

-- some helper functions

skipAll :: Parser ()
skipAll = skipMany ((skipMany1 space) <|> ((definedComment <|>
                    comment    <|> systemComment) >> return ()))

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

oBracket :: Parser ()
oBracket = keyChar '['

cBracket :: Parser ()
cBracket = keyChar ']'

ampersand :: Parser ()
ampersand = keyChar '&'

at :: Parser ()
at = keyChar '@'

gentzenArrow :: Parser ()
gentzenArrow = key $ string "-->"

-- test

test :: String -> IO ()
test s = case (parse formulaRole "" s) of
    Left err -> do{ putStr "parse error at "
                  ; print err
                  }
    Right x -> print x

filetest :: IO ()
filetest = do
    f <- readFile "Test/testfile.p"
    case (parse parseTHF "" f) of
        Left err -> do{ putStr "parse error at "
                    ; print err
                    }
        Right x -> print x

parentheses :: Parser a -> Parser a
parentheses p = do
    oParentheses
    r <- p
    cParentheses
    return r
