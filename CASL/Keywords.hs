
{- HetCATS/CASL/Keywords.hs
   $Id$
   Authors: Christian Maeder
   Year:    2002
   
   string constants for CASL keywords to be used for parsing and printing
   all exported identifiers are mixed case (usually keyword plus capital S)

   http://www.cofi.info/Documents/CASL/Summary/
   from 25 March 2001
   C.4 Lexical Syntax
-}

module Keywords where

-- ----------------------------------------------
-- casl special strings 
-- ----------------------------------------------

exMark = "!" -- in "exists!"
quMark = "?"
funS = "->"
prodS = "*"
timesS = "\215"
lessS = "<"
colonS = ":"

-- ----------------------------------------------
-- casl keywords
-- ----------------------------------------------

dotS = "."
cDot = "\183"
barS = "|"
mapsTo = "|->"
defnS = "::="
casl_reserved_ops = [colonS, colonS++quMark, defnS, dotS, cDot, barS, mapsTo]

equalS = "="
exEqual = "=e="  -- unusual keyword 
implS = "=>"
equivS = "<=>"
negS = "\172"
lAnd = "/\\"   -- logical and/or
lOr = "\\/"

-- these signs are legal in terms, but illegal in declarations
formula_ops = [equalS, implS, equivS, lOr, lAnd, negS] 

defS = "def"
elseS = "else"
falseS = "false"
ifS = "if"
notS = "not"
trueS = "true"
whenS = "when"

-- these words are legal in terms, but illegal in declarations
formula_words = [defS, elseS, ifS, whenS, falseS, notS, trueS]

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
existsS = "exists"
forallS = "forall"
fitS = "fit"
freeS = "free"
fromS = "from"
generatedS = "generated"
getS = "get"
givenS = "given" 
hideS = "hide"
idemS = "idem"
inS = "in"
lambdaS = "lambda"
libraryS = "library"
localS = "local"
resultS = "result"
revealS = "reveal" 
sortS = "sort"
specS = "spec"
thenS = "then"
toS = "to"
typeS = "type"
unitS = "unit"
versionS = "version"
viewS = "view"
withS = "with"
withinS = "within"

-- letter keywords
casl_reserved_words =
    [andS, archS, asS, assocS, axiomS, axiomS ++ sS, closedS, commS, endS, 
    existsS, fitS, forallS, freeS, fromS, generatedS, getS, givenS,
    hideS, idemS, inS, lambdaS, libraryS, localS, 
    opS, opS ++ sS, predS, predS ++ sS, resultS, revealS, sortS, 
    sortS ++ sS, specS, thenS, toS, typeS, typeS ++ sS, 
    unitS, unitS ++ sS, varS, varS ++ sS, versionS, viewS, withS, withinS]

oBracketS = "["
cBracketS = "]"
oBraceS = "{"
cBraceS = "}"
oParenS = "("
cParenS = ")"
commaS = ","
semiS = ";"
