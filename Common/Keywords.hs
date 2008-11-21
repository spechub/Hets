{- |
Module      :  $Header$
Description :  String constants for CASL keywords to be used for parsing
  and printing
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2003
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

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

-- * letter keywords taken form Keywords.txt

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

esortS :: String
esortS = "esort"

etypeS :: String
etypeS = "etype"

existsS :: String
existsS = "exists"

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

programS :: String
programS = "program"

propS :: String
propS = "prop"

refinedS :: String
refinedS = "refined"

refinementS :: String
refinementS = "refinement"

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

sortS :: String
sortS = "sort"

specS :: String
specS = "spec"

stringS :: String
stringS = "string"

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
