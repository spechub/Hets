{- |
Module      :  $Header$
Description :  String constants for CASL keywords to be used for parsing
  and printing
Copyright   :  Dominik Dietrich, DFKI Bremen 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Dominik.Dietrich@dfki.de
Stability   :  provisional
Portability :  portable

String constants for keywords to be used for parsing and reduce expressions

-}

module Reduce.Keywords where

-- commands

algebraicS :: String
algebraicS = "algebraic"

antisymmetricS :: String
antisymmetricS = "antisymmetric"

arrayS :: String
arrayS = "array"

clearS :: String 
clearS = "clear"

byeS :: String
byeS = "bye"

clearrulesS :: String
clearrulesS = "clearrules"

commentS :: String
commentS = "comment"

contS :: String
contS = "cont"

decomposeS :: String
decomposeS = "decompose"

defineS :: String
defineS = "define"

dependS :: String
dependS = "depends"

displayS :: String
displayS = "display"

edS :: String
edS = "ed"

editdefS :: String
editdefS = "editdef"

endS :: String
endS = "end"

evenS :: String
evenS = "even"

factorS :: String
factorS = "factor"

forS :: String
forS = "for"

forallS :: String
forallS = "forall"

foreachS :: String
foreachS = "foreach"

goS :: String
goS = "go"

gotoS :: String
gotoS = "goto"

ifS :: String
ifS = "if"

inS :: String
inS = "in"

indexS :: String
indexS = "index"

infixS :: String
infixS = "infix"

inputS :: String
inputS = "input"

integerS :: String
integerS = "integer"

korderS :: String
korderS = "korder"

letS :: String
letS = "let"

linearS :: String
linearS = "linear"

lispS :: String
lispS = "lisp"

listargpS :: String
listargpS = "lispargp"

loadS :: String
loadS = "load"

loadpackageS :: String
loadpackageS = "loadpackage"

massS :: String
massS = "mass"

matchS :: String
matchS = "match"

matrixS :: String
matrixS = "matrix"

mshellS :: String
mshellS = "mshell"

nodependS :: String
nodependS = "nodepend"

noncomS :: String
noncomS = "nocom"

nonzeroS :: String
nonzeroS = "nonzero"

nospurS :: String
nospurS = "nospur"

oddS :: String
oddS = "odd"

offS :: String
offS = "off"

onS :: String
onS = "on"

operatorS :: String
operatorS = "operator"

orderS :: String
orderS = "order"

outS :: String
outS = "out"

pauseS :: String
pauseS = "pause"

precedenceS :: String
precedenceS = "precedence"

printprecisionS :: String
printprecisionS = "printprecision"

procedureS :: String
procedureS ="procedure"

quitS :: String
quitS = "quit"

realS :: String
realS = "real"

remfacS :: String
remfacS = "remfac"

remindS :: String
remindS = "remind"

retryS :: String
retryS = "retry"

returnS :: String
returnS = "return"

saveasS :: String
saveasS = "saveas"

scalarS :: String
scalarS = "scalar"

setmodS :: String
setmodS = "setmod"

shareS :: String
shareS = "share"

showtimeS :: String
showtimeS = "showtime"

shutS :: String
shutS = "shut"

spurS :: String
spurS = "spur"

symbolicS :: String
symbolicS = "symbolic"

symmetricS :: String
symmetricS = "symmetric"

vecdimS :: String
vecdimS = "vecdim"

vectorS :: String
vectorS = "vector"

wheightS :: String
wheightS = "wheight"

writeS :: String
writeS = "write"

wtlevelS :: String
wtlevelS = "wtlevel"

commandKeywords :: [String]
commandKeywords = [algebraicS, antisymmetricS, arrayS, byeS, clearS, clearrulesS, commentS, contS, decomposeS, defineS, dependS, displayS, edS, editdefS, endS, evenS, factorS, forS, forallS, foreachS, goS, gotoS, ifS, inS, indexS, infixS, inputS, integerS, korderS, letS, linearS, lispS, listargpS, loadS, loadpackageS, massS, matchS, matrixS, mshellS, nodependS, noncomS, nonzeroS, nospurS, oddS, offS, onS, operatorS, orderS, outS, pauseS, precedenceS, printprecisionS, procedureS, quitS, realS, remfacS, remindS, retryS, returnS, saveasS, scalarS, setmodS, shareS, showtimeS, shutS, spurS, symbolicS, symmetricS, vecdimS, vectorS, wheightS, writeS, wtlevelS]

-- boolean operators

evenpS :: String
evenpS = "even"

fixpS :: String
fixpS = "fixp"

freeofS :: String
freeofS = "freeof"

numberpS :: String
numberpS = "numperp"

ordpS :: String
ordpS = "ordp"

primepS :: String
primepS = "primep"

booleanKeywords :: [String]
booleanKeywords = [evenpS, fixpS, freeofS, numberpS, ordpS, primepS]


-- infix operators
sym_assignS :: String
sym_assignS = ":="

sym_equalS :: String
sym_equalS = "="


sym_lessS :: String
sym_lessS = "<"

sym_greaterS :: String
sym_greaterS = ">"

sym_geqS :: String
sym_geqS = ">="

sym_leqS :: String
sym_leqS = "<="

sym_plusS :: String
sym_plusS = "+"

sym_minusS :: String
sym_minusS = "-"

sym_expS :: String 
sym_expS = "^"

sym_divS :: String
sym_divS = "/"

sym_expmulS :: String
sym_expmulS = "**"

orS :: String
orS = "or"

andS :: String
andS = "and"

memberS :: String
memberS = "member"

memqS :: String
memqS = "memq"

equalS :: String
equalS = "equal"

neqS :: String
neqS = "neq"

eqS :: String 
eqS = "eq"

geqS :: String
geqS = "geq"

greaterpS :: String
greaterpS = "greaterp"

leqS :: String
leqS = "leq"

lesspS :: String
lesspS = "lessp"

plusS :: String
plusS = "plus"

differenceS :: String
differenceS = "difference"

minusS :: String
minusS = "minus"

timesS :: String
timesS = "times"

quotientS :: String
quotientS = "quotient"

exptS :: String
exptS = "expt"

consS :: String
consS = "cons"


infixKeywords :: [String]
infixKeywords = [sym_assignS, sym_equalS, sym_lessS, sym_greaterS, sym_geqS, sym_leqS, sym_plusS, sym_minusS, sym_expS, sym_divS, sym_expmulS, sym_expS, orS, andS, memberS, memqS, equalS, neqS, eqS, geqS, greaterpS, leqS, lesspS, plusS, differenceS, minusS, timesS, quotientS, exptS, consS]


-- numerical operators
absS :: String
absS = "abs"

acosS :: String
acosS = "acos"

acoshS :: String
acoshS = "acosh"

acothS :: String
acothS = "actoh"

acscS :: String
acscS = "acsc"

acschS :: String
acschS = "acsch"

asecS :: String
asecS = "asec"

asechS :: String
asechS = "asech"

asinS :: String
asinS = "asin"

asinhS :: String
asinhS = "asinh"

atanS :: String
atanS = "atan"

atanhS :: String
atanhS = "atanh"

atan2S :: String
atan2S = "atan2"

cosS :: String
cosS = "cos"

coshS :: String
coshS = "cosh"

cotS :: String
cotS = "cot"

cothS :: String
cothS = "coth"

cscS :: String
cscS = "csc"

cschS :: String
cschS = "csch"

expS :: String
expS = "exp"

factorialS :: String
factorialS = "factorial"

fixS :: String
fixS = "fix"

floorS :: String
floorS = "floor"

hypotS :: String
hypotS = "hypot"

lnS :: String
lnS = "ln"

logS :: String
logS = "log"

logbS :: String
logbS = "logb"

log10S :: String
log10S = "log10"

nextprimeS ::String
nextprimeS = "nextprime"

roundS :: String
roundS = "round"

secS :: String
secS = "sec"

sechS :: String
sechS = "sech"

sinS :: String
sinS = "sin"

sinhS :: String
sinhS = "sinh"

sqrtS :: String
sqrtS = "sqrt"

tanS :: String
tanS = "tan"

tanhS :: String
tanhS = "tanh"

numericalKeywords :: [String]
numericalKeywords = [absS, acosS, acoshS, acothS, acscS, acschS, asecS, asechS, asinS, asinhS, atanS, atanhS, atan2S, cosS, coshS, cotS, cothS, cscS, cschS, expS, factorialS, fixS, floorS, hypotS, lnS, logS, logbS, log10S, nextprimeS, roundS, secS, sechS, sinS, sinhS, sqrtS, tanS, tanhS]


-- prefix operators
appendS :: String 
appendS = "append"

arglengthS :: String 
arglengthS =" arglenght"

ceilingS :: String 
ceilingS = "ceiling"

coeffS :: String 
coeffS = "coeff"

coeffnS :: String 
coeffnS = "coeffn"

cofactorS :: String 
cofactorS = "cofactor"

conjS :: String 
conjS = "conj"

degS :: String 
degS = "deg"

denS :: String 
denS = "den"

detS :: String 
detS = "det"

defS :: String 
defS = "def"

dilogS :: String 
dilogS = "dilog"

eiS :: String 
eiS = "ei"

epsS :: String 
epsS = "eps"

erfS :: String 
erfS = "erf"

factorizeS :: String 
factorizeS = "factorize"

firstS :: String 
firstS = "first"

gcdS :: String 
gcdS = "gcd"


gS :: String 
gS = "g"

impartS :: String 
impartS = "impart"

intS :: String 
intS = "int"

interpolS :: String 
interpolS = "interpol"

lcmS :: String 
lcmS = "lcm"

lcofS :: String 
lcofS = "lcof"

lengthS :: String 
lengthS = "length"

lhsS :: String 
lhsS = "lhs"

linelengthS :: String
linelengthS = "linelength"

lltermS :: String 
lltermS = "llterm"

mainvarS :: String 
mainvarS = "mainvar"

matS :: String 
matS = "mat"

mateigenS :: String 
mateigenS = "mateigen"

maxS :: String 
maxS = "max"

minS :: String 
minS = "min"

mkidS :: String 
mkidS = "mkid"

nullspaceS :: String 
nullspaceS = "nullspace"

numS :: String 
numS = "num"

partS :: String 
partS = "part"

pfS :: String 
pfS = "pf"

precisionS :: String 
precisionS = "precision"

prodS :: String 
prodS = "prod"

randomS :: String 
randomS = "random"

randomnewseedS :: String 
randomnewseedS = "randomnewseed"

rankS :: String 
rankS = "rank"

rederrS :: String 
rederrS = "rederr"

reductS :: String 
reductS = "reduct"

remainderS :: String 
remainderS = "remainder"

repartS :: String 
repartS = "repart"

restS :: String 
restS = "rest"

resultantS :: String 
resultantS = "resultant"

reverseS :: String 
reverseS = "reverse"

rhsS :: String 
rhsS = "rhs"

secondS :: String 
secondS = "second"

setS :: String 
setS = "set"

showrulesS :: String 
showrulesS = "showrules"

signS :: String 
signS = "sign"

solveS :: String 
solveS = "solve"

structrS :: String 
structrS = "structr"

subS :: String 
subS = "sub"

sumS :: String 
sumS = "sum"

thirdS :: String 
thirdS = "third"

tpS :: String 
tpS = "tp"

traceS :: String 
traceS = "trace"

varnameS :: String
varnameS = "varname"

prefixKeywords :: [String]
prefixKeywords = [appendS, arglengthS, ceilingS, coeffS, coeffnS, cofactorS, conjS, degS, denS, detS, defS, dilogS, eiS, epsS, erfS, factorizeS, firstS, gcdS, gS, impartS, intS, interpolS, lcmS, lcofS, lengthS, lhsS, linelengthS, lltermS, mainvarS, matS, mateigenS, maxS, minS, mkidS, nullspaceS, numS, partS, pfS, precisionS, prodS, randomS, randomnewseedS, rankS, rederrS, reductS, remainderS, repartS, restS, resultantS, reverseS, rhsS, secondS, setS, showrulesS, signS, solveS, structrS, subS, sumS, thirdS, tpS, traceS, varnameS] 



-- reserved variables
cardnoS :: String
cardnoS = "cardno"

eS :: String
eS = "e"

evalmodeS :: String
evalmodeS = "evalmode"

fortwidthS :: String
fortwidthS = "fortwidth"

highpowS :: String
highpowS = "highpow"

iS :: String
iS = "i"

infinityS :: String
infinityS = "infinity"

kexlamS :: String
kexlamS = "k!*"

lowpowS :: String
lowpowS = "lowpow"

nilS :: String
nilS = "nil"

piS :: String
piS = "pi"

rootmultS :: String
rootmultS = "rootmult"

tS :: String
tS = "t"

varKeywords :: [String]
varKeywords = [cardnoS, eS, evalmodeS, fortwidthS, highpowS, iS, infinityS, kexlamS, lowpowS, nilS, piS, rootmultS, tS]


-- switches

adjprecS :: String 
adjprecS = "adjprec"

algintS :: String 
algintS = "algint"

allbranchS :: String 
allbranchS = "allbranch"

allfacS :: String 
allfacS = "allfac"

balancemodS :: String 
balancemodS = "balancemod"

bfspaceS :: String 
bfspaceS = "bfspace"

combineexptS :: String 
combineexptS = "comineexpt"

defnS :: String 
defnS = "defn"

demoS :: String 
demoS = "demo"

divS :: String 
divS = "div"

echoS :: String 
echoS = "echo"

errcontS :: String 
errcontS = "errcont"

evallhseqpS :: String 
evallhseqpS = "evallhseqp"


expandlogsS :: String 
expandlogsS = "expandlogs" 

ezgcdS :: String 
ezgcdS = "ezgcd"

fortS :: String 
fortS = "fort"

fullrootsS :: String 
fullrootsS = "fullroots"

ifactorS :: String 
ifactorS = "ifactor"


intstrS :: String 
intstrS = "intstr"


listS :: String 
listS = "list"

listargsS :: String 
listargsS = "listargs"

mcdS :: String 
mcdS = "mcd"

modularS :: String 
modularS = "modular"

msgS :: String 
msgS = "msg"

multiplicitiesS :: String 
multiplicitiesS = "multiplicities"

natS :: String 
natS = "nat"

neroS :: String 
neroS = "nero"

nosplitS :: String 
nosplitS = "nosplit"

outputS :: String 
outputS = "output"

periodS :: String 
periodS = "period"

preciseS :: String 
preciseS = "precise"

pretS :: String 
pretS = "pret"

priS :: String 
priS = "pri"

ratS :: String 
ratS = "rat"

ratargS :: String 
ratargS = "ratargs"

rationalS :: String 
rationalS = "rational"

rationalizeS :: String 
rationalizeS = "rationalize"

ratrpiS :: String 
ratrpiS = "ratrpi"

revpriS :: String 
revpriS = "repvpri"

rlisp88S :: String 
rlisp88S = "rlisp88"

roundallS :: String 
roundallS = "roundall"

roundbdS :: String 
roundbdS = "roundbd"

roundedS :: String 
roundedS = "rounded"

savestructrS :: String 
savestructrS = "savestructr"

solvesingularS :: String 
solvesingularS = "solvesingular"

timeS :: String 
timeS = "times"

traS ::String 
traS = "tra"

trfacS :: String 
trfacS = "trafac"

trigformS :: String 
trigformS = "trigform"


trintS :: String
trintS = "trint"

switchKeywords :: [String]
switchKeywords = [adjprecS, algintS, allbranchS, allfacS, balancemodS, bfspaceS, combineexptS, defnS, demoS, divS, echoS, errcontS, evallhseqpS, expS, expandlogsS, ezgcdS, factorS, fortS, fullrootsS, gcdS, ifactorS, intS, intstrS, lcmS, listS, listargsS, mcdS, modularS, msgS, multiplicitiesS, natS, neroS, nosplitS, outputS, periodS, preciseS, pretS, priS, ratS, ratargS, rationalS, rationalizeS, ratrpiS, revpriS, rlisp88S, roundallS, roundbdS, roundedS, savestructrS, solvesingularS, timeS, traS, trfacS, trigformS, trintS]



-- others
beginS :: String
beginS = "begin"

doS :: String
doS = "do"

exprS :: String
exprS = "expr"

fexprS :: String
fexprS = "fexpr"

lambdaS :: String
lambdaS = "lambda"

macroS :: String
macroS = "macro"

productS :: String
productS = "product"

repeatS :: String
repeatS = "repeat"

smacroS :: String
smacroS = "scmacro"

untilS :: String
untilS = "until"

whenS :: String
whenS = "when"

whileS :: String
whileS = "while"

wsS :: String 
wsS = "ws"

otherKeywords :: [String]
otherKeywords = [beginS, doS, exprS, fexprS, inputS, lambdaS, lispS, macroS, productS, repeatS, smacroS, sumS, untilS, whenS, whileS, wsS]


-- 
allKeywords :: [String]
allKeywords = commandKeywords ++ booleanKeywords ++ infixKeywords ++ numericalKeywords ++ prefixKeywords ++ varKeywords ++ switchKeywords ++ otherKeywords