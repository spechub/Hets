
{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2003
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable
    
String constants for CASL keywords to be used for parsing and printing

- all identifiers are mixed case (i.e. the keyword followed by  a capital S)

- see <http://www.cofi.info/Documents/CASL/Summary/> from 25 March 2001, 
  C.4 Lexical Syntax
-}


module Common.Keywords where

-- * context dependend keywords

-- | sub sort indicator
lessS :: String
lessS  = "<"

-- | modifier for 'funS' or 'colonS'
exMark :: String
exMark  = "!" 

-- | modifier for 'existsS'
quMark :: String 
quMark  = "?"  

-- ** type constructors
timesS,
  prodS,
  funS :: String
funS  = "->"
prodS  = "*"
timesS  = "\215"

-- ** modal operators
diamondS :: String
diamondS = "<>"

-- | mind @[]@ also as (non-symbol) term
boxS :: String
boxS = "[]"  

-- * symbol keywords 
defnS,
  mapsTo,
  barS,
  cDot,
  dotS,
  colonS :: String 
colonS  = ":"
dotS  = "."
cDot  = "\183"
barS  = "|"
mapsTo  = "|->"
defnS  = "::="

-- ** equality symbols

-- | mind spacing i.e. in @e =e= e@
exEqual :: String
exEqual  = "=e="  

-- | also a definition indicator
equalS :: String
equalS  = "="

-- ** formula symbols
lOr,
  lAnd,
  negS,
  equivS,
  implS :: String
implS  = "=>"
equivS  = "<=>"
negS  = "\172"
lAnd  = "/\\"    
lOr  = "\\/"

-- * lower case letter keywords
withinS,
  withS,
  viewS,
  versionS,
  unitS,
  typeS,
  toS,
  thenS,
  specS,
  sortS,
  revealS,
  resultS,
  propS,
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
  fromS,
  cofreeS,
  freeS,
  fitS,
  forallS,
  existsS,
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
  defS :: String

defS  = "def"
elseS  = "else"
falseS  = "false"
ifS  = "if"
notS  = "not"
trueS  = "true"
whenS  = "when"

andS  = "and"
archS  = "arch"
asS  = "as"
assocS  = "assoc"
axiomS  = "axiom"
sS  = "s" 
varS  = "var"
predS  = "pred"
opS  = "op"
closedS  = "closed"
commS  = "comm"
endS  = "end"
existsS  = "exists"
forallS  = "forall"
fitS  = "fit"
freeS  = "free"
cofreeS  = "cofree"
fromS  = "from"
generatedS  = "generated"
getS  = "get"
givenS  = "given" 
hideS  = "hide"
idemS  = "idem"
inS  = "in"
lambdaS  = "lambda"
libraryS  = "library"
localS  = "local"
logicS = "logic" -- new keyword
propS = "prop"
resultS  = "result"
revealS  = "reveal" 
sortS  = "sort"
specS  = "spec"
thenS  = "then"
toS  = "to"
typeS  = "type"
unitS  = "unit"
versionS  = "version"
viewS  = "view"
withS  = "with"
withinS  = "within"
