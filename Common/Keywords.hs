{- |
Module      :  ./Common/Keywords.hs
Description :  String constants for CASL keywords to be used for parsing
  and printing
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2003
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

String constants for keywords to be used for parsing and printing

- all identifiers are mixed case (i.e. the keyword followed by  a capital S)

- see <http://www.cofi.info/Documents/CASL/Summary/> from 25 March 2001,
  C.4 Lexical Syntax
-}

module Common.Keywords where

-- * context dependend keywords

-- | sub sort indicator
lessS :: String
lessS = "<"

-- | modifier for 'existsS'
exMark :: String
exMark = "!"

-- | modifier for 'funS' or 'colonS'
quMark :: String
quMark = "?"

-- * type constructors

-- | total function arrow
funS :: String
funS = "->"

-- | partial function arrow
pFun :: String
pFun = funS ++ quMark

-- | ascii product type sign
prodS :: String
prodS = "*"

-- | alternative latin1 product type sign
timesS :: String
timesS = "\215"

-- * symbol keywords

-- | the colon sign
colonS :: String
colonS = ":"

equiS :: String
equiS = "<->"

-- | the dot sign (ascii)
dotS :: String
dotS = "."

-- | the alternative latin1 centered dot sign
cDot :: String
cDot = "\183"

-- | the vertical bar
barS :: String
barS = "|"

-- | arrow started with a bar
mapsTo :: String
mapsTo = "|->"

-- | two colons and an equal sign
defnS :: String
defnS = "::="

-- | a colon with a question mark
colonQuMark :: String
colonQuMark = colonS ++ quMark

-- | the exists keyword with an exclamation mark
existsUnique :: String
existsUnique = existsS ++ exMark

-- * comment keywords

-- | one percent sign
percentS :: String
percentS = "%"

-- | two percent signs (for line comments)
percents :: String
percents = percentS ++ percentS

-- * formula symbols

-- | implication arrow (equal and greater)
implS :: String
implS = "=>"

-- | equivalent sign
equivS :: String
equivS = "<=>"

-- | the alternative latin1 negation sign for not
negS :: String
negS = "\172"

-- | logical and using slashes
lAnd :: String
lAnd = "/\\"

-- | logical or using slashes
lOr :: String
lOr = "\\/"

-- * further HasCASL key signs

-- | assign sign (colon and equal)
assignS :: String
assignS = ":="

-- | minus sign (for variance)
minusS :: String
minusS = "-"

-- | plus sign (for variance)
plusS :: String
plusS = "+"

-- | total continuous function arrow
contFun :: String
contFun = minusS ++ funS

-- | partial continuous function arrow
pContFun :: String
pContFun = minusS ++ pFun

-- | lambda sign (backslash)
lamS :: String
lamS = "\\"

-- | at sign (for as pattern)
asP :: String
asP = "@"

-- | Here sign
hereP :: String
hereP = "Here"

-- | Bind sign
bindP :: String
bindP = "Bind"


-- | assign sign in monad notation
rightArrow :: String
rightArrow = "<-"

-- * further HasCASL keywords

-- | the new keyword fun ('funS' is already defined differently)
functS :: String
functS = "fun"

-- * CoCasl key signs

-- | the diamond sign (less and greater)
diamondS :: String
diamondS = "<>"

-- | the greater sign
greaterS :: String
greaterS = ">"


maxInclusiveS :: String
maxInclusiveS = "maxInclusive"

maxExclusiveS :: String
maxExclusiveS = "maxExclusive"

-- * OWL key signs

minInclusiveS :: String
minInclusiveS = "minInclusive"


minExclusiveS :: String
minExclusiveS = "minExclusive"


lessEq :: String
lessEq = "<="

greaterEq :: String
greaterEq = ">="

-- * CspCasl key signs

-- | Prefix processes
prefix_procS :: String
prefix_procS = "->"

-- | sequential process operator
sequentialS :: String
sequentialS = ";"

-- | interleaving parallel operator
interleavingS :: String
interleavingS = "|||"

-- | synchronous parallel operator
synchronousS :: String
synchronousS = "||"

-- | Open generalised parallel
genpar_openS :: String
genpar_openS = "[|"

-- | Close generalised parallel
genpar_closeS :: String
genpar_closeS = "|]"

-- | Open alpabetised parallel
alpar_openS :: String
alpar_openS = "["

-- | Separator in alpabetised parallel
alpar_sepS :: String
alpar_sepS = "||"

-- | Close alpabetised parallel
alpar_closeS :: String
alpar_closeS = "]"

-- | External choice
external_choiceS :: String
external_choiceS = "[]"

-- | Internal choice
internal_choiceS :: String
internal_choiceS = "|~|"

-- | Hiding (process)
hiding_procS :: String
hiding_procS = "\\"

-- | Open a renaming (process)
ren_proc_openS :: String
ren_proc_openS = "[["

-- | Close a renaming (process)
ren_proc_closeS :: String
ren_proc_closeS = "]]"

-- * logic definition symbols

newlogicS :: String
newlogicS = "newlogic"

metaS :: String
metaS = "meta"

foundationS :: String
foundationS = "foundation"

syntaxS :: String
syntaxS = "syntax"

patternsS :: String
patternsS = "patterns"

modelsS :: String
modelsS = "models"

proofsS :: String
proofsS = "proofs"

newcomorphismS :: String
newcomorphismS = "newcomorphism"

sourceS :: String
sourceS = "source"

targetS :: String
targetS = "target"

-- * DOL keywords

alignArityBackwardS :: String
alignArityBackwardS = "align-arity-backward"

alignArityForwardS :: String
alignArityForwardS = "align-arity-forward"

alignmentS :: String
alignmentS = "alignment"

combineS :: String
combineS = "combine"

excludingS :: String
excludingS = "excluding"

entailmentS :: String
entailmentS = "entailment"

entailsS :: String
entailsS = "entails"

forS :: String
forS = "for"

interpretationS :: String
interpretationS = "interpretation"

moduleS :: String
moduleS = "module"

ontologyS :: String
ontologyS = "ontology"

networkS :: String
networkS = "network"

relationS :: String
relationS = "relation"

serializationS :: String
serializationS = "serialization"

-- * frameworks

lfS :: String
lfS = "LF"

isabelleS :: String
isabelleS = "Isabelle"

maudeS :: String
maudeS = "Maude"

-- * MMT symbols

sigDelimS :: String
sigDelimS = ".."

structDelimS :: String
structDelimS = "/"

-- * Twelf conventions

-- non breaking space
whiteChars :: String
whiteChars = "\n\r\t\v\f \160"

-- special characters permitted in a Twelf symbol name
twelfSymChars :: String
twelfSymChars = "_-+*/<=>@^"

-- special characters permitted in a Twelf declaration
twelfDeclChars :: String
twelfDeclChars = twelfSymChars ++ ":{}[]()"

-- special characters permitted in a Twelf declaration of multiple symbols
twelfMultDeclChars :: String
twelfMultDeclChars = twelfDeclChars ++ ","

-- * letter keywords taken from Keywords.txt

andS :: String
andS = "and"

archS :: String
archS = "arch"

asS :: String
asS = "as"

assocS :: String
assocS = "assoc"

axiomS :: String
axiomS = "axiom"

behaviourallyS :: String
behaviourallyS = "behaviourally"

caseS :: String
caseS = "case"

classS :: String
classS = "class"

closedS :: String
closedS = "closed"

closedworldS :: String
closedworldS = "closed-world"

cofreeS :: String
cofreeS = "cofree"

cogeneratedS :: String
cogeneratedS = "cogenerated"

commS :: String
commS = "comm"

cotypeS :: String
cotypeS = "cotype"

dataS :: String
dataS = "data"

defS :: String
defS = "def"

derivingS :: String
derivingS = "deriving"

displayS :: String
displayS = "display"

doS :: String
doS = "do"

elseS :: String
elseS = "else"

emptyS :: String
emptyS = "empty"

endS :: String
endS = "end"

equivalenceS :: String
equivalenceS = "equivalence"

esortS :: String
esortS = "esort"

etypeS :: String
etypeS = "etype"

existsS :: String
existsS = "exists"

extractS :: String
extractS = "extract"

falseS :: String
falseS = "false"

fitS :: String
fitS = "fit"

flexibleS :: String
flexibleS = "flexible"

floatingS :: String
floatingS = "floating"

forallS :: String
forallS = "forall"

forgetS :: String
forgetS = "forget"

freeS :: String
freeS = "free"

fromS :: String
fromS = "from"

generatedS :: String
generatedS = "generated"

getS :: String
getS = "get"

givenS :: String
givenS = "given"

hideS :: String
hideS = "hide"

keepS :: String
keepS = "keep"

approximateS :: String
approximateS = "approximate"

idemS :: String
idemS = "idem"

ifS :: String
ifS = "if"

inS :: String
inS = "in"

instanceS :: String
instanceS = "instance"

internalS :: String
internalS = "internal"

intersectS :: String
intersectS = "intersect"

lambdaS :: String
lambdaS = "lambda"

left_assocS :: String
left_assocS = "left_assoc"

letS :: String
letS = "let"

libraryS :: String
libraryS = "library"

listS :: String
listS = "list"

localS :: String
localS = "local"

logicS :: String
logicS = "logic"

minimizeS :: String
minimizeS = "minimize"

modalitiesS :: String
modalitiesS = "modalities"

modalityS :: String
modalityS = "modality"


notS :: String
notS = "not"

numberS :: String
numberS = "number"

ofS :: String
ofS = "of"

opS :: String
opS = "op"

precS :: String
precS = "prec"

predS :: String
predS = "pred"

prefixS :: String
prefixS = "prefix"

programS :: String
programS = "program"

propS :: String
propS = "prop"

refinedS :: String
refinedS = "refined"

refinementS :: String
refinementS = "refinement"

rejectS :: String
rejectS = "reject"

removeS :: String
removeS = "remove"

resultS :: String
resultS = "result"

revealS :: String
revealS = "reveal"

right_assocS :: String
right_assocS = "right_assoc"

rigidS :: String
rigidS = "rigid"

sS :: String
sS = "s"

selectS :: String
selectS = "select"

sortS :: String
sortS = "sort"

specS :: String
specS = "spec"

stringS :: String
stringS = "string"

structS :: String
structS = "struct"

termS :: String
termS = "term"

thenS :: String
thenS = "then"

toS :: String
toS = "to"

trueS :: String
trueS = "true"

typeS :: String
typeS = "type"

unitS :: String
unitS = "unit"

varS :: String
varS = "var"

varsS :: String
varsS = "vars"

versionS :: String
versionS = "version"

viaS :: String
viaS = "via"

viewS :: String
viewS = "view"

whenS :: String
whenS = "when"

whereS :: String
whereS = "where"

withS :: String
withS = "with"

withinS :: String
withinS = "within"
