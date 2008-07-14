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

left_assocS, right_assocS, precS, displayS, numberS, stringS, listS,
  floatingS :: String
left_assocS = "left_assoc"
right_assocS = "right_assoc"
precS = "prec"
displayS = "display"
numberS = "number"
stringS = "string"
listS = "list"
floatingS = "floating"

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

internalS, classS, programS, instanceS, caseS, ofS, letS, derivingS :: String
classS = "class"
programS = "program"
instanceS = "instance"
caseS = "case"
ofS = "of"
letS = "let"
derivingS = "deriving"
internalS = "internal"

whereS :: String
whereS = "where"

-- | for monad notation
doS :: String
doS = "do"

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

-- * Modal CASL keywords
modalityS, modalitiesS, flexibleS, rigidS, termS, emptyS :: String
modalityS = "modality"
modalitiesS = init modalityS ++ "ies"
flexibleS = "flexible"
rigidS = "rigid"
termS = "term"
emptyS = "empty"

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





-- * standard lower case letter keywords
withinS,
  withS,
  viewS,
  versionS,
  unitS,
  typeS,
  cotypeS,
  toS,
  thenS,
  specS,
  sortS,
  revealS,
  resultS,
  localS,
  logicS,
  libraryS,
  lambdaS,
  inS,
  idemS,
  hideS,
  givenS,
  getS,
  generatedS,
  cogeneratedS,
  fromS,
  cofreeS,
  freeS,
  fitS,
  forallS,
  existsS,
  esortS,
  etypeS,
  endS,
  commS,
  closedS,
  opS,
  predS,
  varS,
  sS,
  axiomS,
  assocS,
  asS,
  archS,
  andS,
  whenS,
  trueS,
  notS,
  ifS,
  falseS,
  elseS,
  defS,
  propS :: String

defS = "def"
elseS = "else"
falseS = "false"
ifS = "if"
notS = "not"
trueS = "true"
whenS = "when"

andS = "and"
archS = "arch"
asS = "as"
assocS = "assoc"
axiomS = "axiom"
sS = "s"
varS = "var"
predS = "pred"
opS = "op"
closedS = "closed"
commS = "comm"
endS = "end"
esortS = "esort"
etypeS = "etype"
existsS = "exists"
forallS = "forall"
fitS = "fit"
freeS = "free"
cofreeS = "cofree"
fromS = "from"
generatedS = "generated"
cogeneratedS = "cogenerated"
getS = "get"
givenS = "given"
hideS = "hide"
idemS = "idem"
inS = "in"
lambdaS = "lambda"
libraryS = "library"
localS = "local"
logicS = "logic" -- new keyword
resultS = "result"
revealS = "reveal"
sortS = "sort"
specS = "spec"
thenS = "then"
toS = "to"
typeS = "type"
cotypeS = "cotype"
unitS = "unit"
versionS = "version"
viewS = "view"
withS = "with"
withinS = "within"
propS = "prop"

refinementS, refinedS, behaviourallyS :: String
refinementS = "refinement"
refinedS = "refined"
behaviourallyS = "behaviourally"

viaS, dataS :: String
viaS = "via"
dataS = "data"
