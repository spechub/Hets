{- |
Module      :  $Header$
Description :  constants for Isabelle terms
Copyright   :  (c) Sonja Groening, Christian Maeder, Uni Bremen 2004-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

constants for Isabelle
-}

-- possibly differentiate between HOL and HOLCF

module Isabelle.IsaConsts where

import Isabelle.IsaSign
import Data.List

-- | a topological sort with a @uses@ predicate
quickSort :: (a -> a -> Bool) -> [a] -> [a]
quickSort f ls = case ls of
  [] -> []
  a : as -> let (xs, ys) = partition (f a) as in
    quickSort f xs ++ a : quickSort f ys

-- **** STRINGS ------------------------------------------------

-- * boolean constants
cTrue :: String
cTrue = "True"

cFalse :: String
cFalse = "False"

-- | Not string
cNot :: String
cNot = "Not"

-- * quantor strings
allS, exS, ex1S :: String
allS = "ALL"
exS = "EX"
ex1S = "EX!"

-- * Strings of binary ops

conj :: String
conj = "op &"

disj :: String
disj = "op |"

impl :: String
impl = "op -->"

eq :: String
eq = "op ="

plusS :: String
plusS = "op +"

minusS :: String
minusS = "op -"

timesS :: String
timesS = "op *"

divS :: String
divS = "op div"

modS :: String
modS = "op mod"

consS :: String
consS = "op #"

lconsS :: String
lconsS = "op ###"

compS :: String
compS = "comp"

-- | lower case pair
pairC :: String
pairC = "pair"

-- * some stuff for Isabelle

pcpoS :: String
pcpoS = "pcpo"

prodS, sProdS, funS, cFunS, lFunS, sSumS, lProdS, lSumS :: TName
prodS = "*"    -- this is printed as it is!
lProdS = "lprod" -- "***"
sProdS = "**"
funS = "=>"
cFunS = "->"
lFunS = "-->"
sSumS = "++"
lSumS = "either"

-- * some stuff for HasCASL

aptS :: String
aptS = "apt"

appS :: String
appS = "app"

pAppS :: String
pAppS = "pApp"

defOpS :: String
defOpS = "defOp"

-- | Some string
someS :: String
someS = "Some"

-- * strings for HOLCF lifting functions

lliftbinS :: String
lliftbinS = "lliftbin"

fliftbinS :: String
fliftbinS = "fliftbin"

flift2S :: String
flift2S = "flift2"


-- **** CLASSES & SORTS ---------------------------------------

-- * Predifined CLASSES

pcpo :: IsaClass
pcpo = IsaClass pcpoS

isaTerm :: IsaClass
isaTerm = IsaClass "type"

-- * predefined SORTS

holType :: Sort
holType = [isaTerm]

dom :: Sort
dom = [pcpo]

sortT :: Continuity -> Sort
sortT a = case a of
  NotCont -> holType
  IsCont _ -> dom

--------------------- POLY TYPES --------------------------------------

listT :: Continuity -> Typ -> Typ
listT a t = case a of
   IsCont _ -> Type "llist" (sortT a) [t]
   NotCont -> Type "list" (sortT a) [t]

charT :: Continuity -> Typ
charT a = case a of
  IsCont _ -> Type "charT" (sortT a) []
  NotCont  -> Type "char" (sortT a) []

ratT :: Continuity -> Typ
ratT a = case a of
  IsCont _ -> Type "ratT" (sortT a) []
  NotCont  -> Type "rat" (sortT a) []

fracT :: Continuity -> Typ
fracT a = Type "fracT" (sortT a) []

integerT :: Continuity -> Typ
integerT a = case a of
   IsCont _ -> Type "integerT" (sortT a) []
   NotCont  -> Type "int" (sortT a) []

boolT :: Continuity -> Typ
boolT a = case a of
   IsCont _ -> Type "lBool" (sortT a) []
   NotCont -> Type "bool" (sortT a) []

orderingT :: Continuity -> Typ
orderingT a = case a of
   IsCont _ -> Type "lOrdering" (sortT a) []
   NotCont -> Type "sOrdering" (sortT a) []

intT :: Continuity -> Typ
intT a = case a of
   IsCont _ -> Type "intT" (sortT a) []
   NotCont  -> Type "int" (sortT a) []

prodT :: Continuity -> Typ -> Typ -> Typ
prodT a t1 t2 = case a of
   IsCont _ -> mkContProduct t1 t2
   NotCont  -> prodType t1 t2

funT :: Continuity -> Typ -> Typ -> Typ
funT c a b = case c of
   IsCont _ -> mkContFun a b
   NotCont  -> mkFunType a b

curryFunT :: Continuity -> [Typ] -> Typ -> Typ
curryFunT c ls x = case c of
   IsCont _ -> mkCurryContFun ls x
   NotCont  -> mkCurryFunType ls x

-- **** predefinded HOL TYPES ----------------------------------

noTypeT :: Typ
noTypeT = Type "dummy" holType []

noType :: DTyp
noType = Hide noTypeT NA Nothing

noTypeC :: DTyp
noTypeC = Hide noTypeT TCon Nothing

hideNN :: Typ -> DTyp
hideNN t = Hide t NA Nothing

hideCN :: Typ -> DTyp
hideCN t = Hide t TCon Nothing

dispNN :: Typ -> DTyp
dispNN t = Disp t NA Nothing

dispMN :: Typ -> DTyp
dispMN t = Disp t TMet Nothing

boolType :: Typ
boolType = boolT NotCont

mkListType :: Typ -> Typ
mkListType t = Type "list" holType [t]

mkOptionType :: Typ -> Typ
mkOptionType t = Type "option" holType [t]

prodType :: Typ -> Typ -> Typ
prodType t1 t2 = Type prodS holType [t1,t2]

mkFunType :: Typ -> Typ -> Typ
mkFunType s t = Type funS holType [s,t] -- was "-->" before

{-handy for multiple args: [T1,...,Tn]--->T gives T1-->(T2--> ... -->T)-}
mkCurryFunType :: [Typ] -> Typ -> Typ
mkCurryFunType = flip $ foldr mkFunType -- was "--->" before

-- **** predefinded HOLCF TYPES --------------------------------------

voidDom :: Typ
voidDom = Type "void" dom []

{- should this be included (as primitive)? -}
flatDom :: Typ
flatDom = Type "flat" dom []

tLift :: Typ -> Typ
tLift t = Type "lift" dom [t]

{- sort is ok? -}
mkContFun :: Typ -> Typ -> Typ
mkContFun t1 t2 = Type lFunS dom [t1,t2]

mkStrictProduct :: Typ -> Typ -> Typ
mkStrictProduct t1 t2 = Type sProdS dom [t1,t2]

mkContProduct :: Typ -> Typ -> Typ
mkContProduct t1 t2 = Type lProdS dom [t1,t2]

{-handy for multiple args: [T1,...,Tn]--->T gives T1-->(T2--> ... -->T)-}
mkCurryContFun :: [Typ] -> Typ -> Typ
mkCurryContFun = flip $ foldr mkContFun -- was "--->" before

mkStrictSum :: Typ -> Typ -> Typ
mkStrictSum t1 t2 = Type lSumS dom [t1,t2]


-- **** TERM FORMATION -------------------------------------------

-- | 1000
maxPrio :: Int
maxPrio = 1000

-- | 10
lowPrio :: Int
lowPrio = 10

-- | 2
isaEqPrio :: Int
isaEqPrio = 2 -- left assoc

-- | construct constants and variables
mkConstVD :: String -> Typ -> Term
mkConstVD s t = Const (mkVName s) $ hideNN t

mkConstV :: String -> DTyp -> Term
mkConstV s t = Const (mkVName s) t

mkConstD :: VName -> Typ -> Term
mkConstD s t = Const s $ hideNN t

mkConst :: VName -> DTyp -> Term
mkConst s t = Const s t

mkFree :: String -> Term
mkFree s = Free $ mkVName s

-- | construct a constant with no type
con :: VName -> Term
con s = mkConst s noType

conC :: VName -> Term
conC s = mkConst s noTypeC

conDouble :: String -> Term
conDouble = con . mkVName

conDoubleC :: String -> Term
conDoubleC = conC . mkVName

-- | apply VName operator to two term
binVNameAppl :: VName -> Term -> Term -> Term
binVNameAppl v t1 t2 = termAppl (termAppl (con v) t1) t2

-- * TERM CONSTRUCTORS
-- | binary junctors
binConj, binDisj, binImpl, binEqv, binEq :: Term -> Term -> Term
binConj = binVNameAppl conjV
binDisj = binVNameAppl disjV
binImpl = binVNameAppl implV
binEq = binVNameAppl eqV
binEqv = binEq

-- | HOL function application
termAppl :: Term -> Term -> Term
termAppl t1 t2 = App t1 t2 NotCont


-- **** Poly terms for HOL-HOLCF ----------------------------------

andPT :: Continuity -> Term
andPT a = case a of
  NotCont -> con conjV
  IsCont _ -> conDouble "andH"

orPT :: Continuity -> Term
orPT a = case a of
  NotCont -> con disjV
  IsCont _ -> conDouble "orH"

notPT :: Continuity -> Term
notPT a = case a of
  NotCont -> con notV
  IsCont _ -> conDouble "notH"

bottomPT :: Continuity -> Term
bottomPT a = conDouble $ case a of
  NotCont -> "arbitrary"
  IsCont _ -> "UU"

nilPT :: Continuity -> Term
nilPT a = conDoubleC $ case a of
  NotCont -> "[]"
  IsCont _ -> "lNil"

consPT :: Continuity -> Term
consPT a = case a of
  NotCont -> conC consV
  IsCont True  -> conDouble "llCons"
  IsCont False -> conC lconsV

truePT :: Continuity -> Term
truePT a = conDoubleC $ case a of
   NotCont -> "True"
   IsCont _ -> "TRUE"

falsePT :: Continuity -> Term
falsePT a = conDoubleC $ case a of
   NotCont -> "False"
   IsCont _ -> "FALSE"

headPT :: Continuity -> Term
headPT a = conDouble $ case a of
   NotCont -> "hd"
   IsCont _ -> "llHd"

tailPT :: Continuity -> Term
tailPT a = conDouble $ case a of
   NotCont -> "tl"
   IsCont _ -> "llTl"

unitPT :: Continuity -> Term
unitPT a = case a of
   NotCont -> conDouble "()"
   IsCont _ -> termAppl (conDouble "Def") (conDouble "()")

fstPT :: Continuity -> Term
fstPT a = case a of
              NotCont -> conDoubleC "fst"
              IsCont True -> conDouble "llfst"
              IsCont False  -> conDoubleC "lfst"

sndPT :: Continuity -> Term
sndPT a = case a of
              NotCont -> conDoubleC "snd"
              IsCont True -> conDouble "llsnd"
              IsCont False  -> conDoubleC "lsnd"

pairPT :: Continuity -> Term
pairPT a = case a of
     NotCont      ->  conDoubleC "pair"
     IsCont True  ->  conDouble  "llpair"
     IsCont False ->  conDoubleC "lpair"

nothingPT :: Continuity -> Term
nothingPT a = conDouble $ if a == NotCont
                then "None" else "lNothing"

justPT :: Continuity -> Term
justPT a = case a of
             NotCont -> conDouble "Some"
             IsCont True -> conDouble "llJust"
             IsCont False -> conDoubleC "lJust"

leftPT :: Continuity -> Term
leftPT a = case a of
             NotCont -> conDouble "left"
             IsCont True -> conDouble "llLeft"
             IsCont False -> conDoubleC "lLeft"

rightPT :: Continuity -> Term
rightPT a = case a of
             NotCont -> conDouble "right"
             IsCont True -> conDouble "llRight"
             IsCont False -> conDoubleC "lRight"

compPT :: Term
compPT = conDouble "compH"

eqPT :: Term
eqPT = conDouble "eqH"

neqPT :: Term
neqPT = conDouble "neqH"

eqTPT :: Typ -> Term
eqTPT t = mkConstVD "eqH" t

neqTPT :: Typ -> Term
neqTPT t = mkConstVD "neqH" t

-- **** TERMS ---------------------------------------------------

-- * Boolean constants

true :: Term
true = mkConstVD cTrue boolType

false :: Term
false = mkConstVD cFalse boolType

-- * UNTYPED terms

-- | defOp constant
defOp :: Term
defOp = conDouble defOpS

-- | Not constant
notOp :: Term
notOp = con notV

-- | some constant
conSome :: Term
conSome = conDouble someS

-- * HOLCF

liftString :: Term
liftString = conDouble "liftList"

lpairTerm :: Term
lpairTerm = conDoubleC "lpair"

-- **** VNAMES -------------------------------------------------

-- | Not VName
notV :: VName
notV = VName cNot $ Just $ AltSyntax "~/ _" [40] 40

-- * VNames of binary operators

conjV :: VName
conjV = VName conj $ Just $ AltSyntax "(_ &/ _)"   [36, 35] 35

disjV :: VName
disjV = VName disj $ Just $ AltSyntax "(_ |/ _)"   [31, 30] 30

implV :: VName
implV = VName impl $ Just $ AltSyntax "(_ -->/ _)" [26, 25] 25

eqV :: VName
eqV   = VName eq   $ Just $ AltSyntax "(_ =/ _)"   [50, 51] 50

plusV :: VName
plusV = VName plusS $ Just $ AltSyntax "(_ +/ _)" [65, 66] 65

minusV :: VName
minusV = VName minusS $ Just $ AltSyntax "(_ -/ _)" [65, 66] 65

divV :: VName
divV = VName divS $ Just $ AltSyntax "(_ div/ _)" [70, 71] 70

modV :: VName
modV = VName modS $ Just $ AltSyntax "(_ mod/ _)" [70, 71] 70

timesV :: VName
timesV = VName timesS $ Just $ AltSyntax "(_ */ _)" [70, 71] 70

consV :: VName
consV = VName consS $ Just $ AltSyntax "(_ #/ _)" [66, 65] 65

lconsV :: VName
lconsV = VName lconsS $ Just $ AltSyntax "(_ ###/ _)" [66, 65] 65

compV :: VName
compV = VName compS $ Just $ AltSyntax "(_ o/ _)" [55, 56] 55


-- **** keywords in theory files from the Isar Reference Manual 2005

endS :: String
endS = "end"

headerS :: String
headerS = "header"

theoryS :: String
theoryS = "theory"

importsS :: String
importsS = "imports"

usesS :: String
usesS = "uses"

beginS :: String
beginS = "begin"

contextS :: String
contextS = "context"

axiomsS :: String
axiomsS = "axioms"

defsS :: String
defsS = "defs"

oopsS :: String
oopsS = "oops"

mlS :: String
mlS = "ML"

andS :: String
andS = "and"

lemmasS :: String
lemmasS = "lemmas"

lemmaS :: String
lemmaS = "lemma"

corollaryS :: String
corollaryS = "corollary"

refuteS :: String
refuteS = "refute"

theoremsS :: String
theoremsS = "theorems"

theoremS :: String
theoremS = "theorem"

axclassS :: String
axclassS = "axclass"

classesS :: String
classesS = "classes"

instanceS :: String
instanceS = "instance"

typedeclS :: String
typedeclS = "typedecl"

typesS :: String
typesS = "types"

constsS :: String
constsS = "consts"

structureS :: String
structureS = "structure"

constdefsS :: String
constdefsS = "constdefs"

domainS :: String
domainS = "domain"

datatypeS :: String
datatypeS = "datatype"

fixrecS :: String
fixrecS = "fixrec"

primrecS :: String
primrecS = "primrec"

declareS :: String
declareS = "declare"

simpS :: String
simpS = "simp"

applyS :: String
applyS = "apply"

backS :: String
backS = "back"

deferS :: String
deferS = "defer"

preferS :: String
preferS = "prefer"

byS :: String
byS = "by"

doneS :: String
doneS = "done"

sorryS :: String
sorryS = "sorry"

autoS :: String
autoS = "auto"

usingS :: String
usingS = "using"

dotDot :: String
dotDot = ".."

markups :: [String]
markups =
    [ "--", "chapter" , "section", "subsection", "subsubsection", "text"
    , "text_raw", "sect", "subsect", "subsubsect", "txt", "txt_raw"]

-- | toplevel keys that are currently ignored
ignoredKeys :: [String]
ignoredKeys =
    [ domainS, oopsS, refuteS, fixrecS, primrecS, declareS, usingS, dotDot
    , "sorry", "done", "by", "proof", "apply", "qed"
    , "classrel", "defaultsort", "nonterminls", "arities"
    , "syntax", "no_syntax", "translations"
    , "global", "local", "hide", "use", "setup", "method_setup"
    , "ML_command", "ML_setup", "oracle"
    , "fix", "assume", "presume", "def", "note", "then", "from", "with"
    , "have", "show", "hence", "thus", "shows", "."
--    , "rule", "iprover","OF", "of", "where", "assumption", "this", "-"
    , "let", "is", "next", "apply_end", "defer", "prefer", "back"
    , "pr", "thm", "prf", "term", "prop", "typ", "full_prf"
    , "undo", "redo", "kill", "thms_containing", "thms_deps"
    , "cd", "pwd", "use_thy", "use_thy_only", "update_thy"
    , "update_thy_only"
    , "display_drafts", "in", "locale" -- "intro_classes"
    , "fixes", "constrains", "assumes", "defines", "notes", "includes"
    , "interpretation", "interpret", "obtain", "also", "finally"
    , "moreover", "ultimately" -- "trans", "sym", "symmetric"
    , "case", "judgment", "typedef", "morphisms", "record", "rep_datatype"
    , "recdef", "recdef_tc", "specification","ax_specification"
    , "inductive", "coinductive", "inductive_cases", "codatatype"
    , "code_module", "code_library", "consts_code", "types_code" ]
    ++ map (++ "_translation")
       [ "parse_ast", "parse", "print", "print_ast", "typed_print"
       , "token" ]
    ++ map ("print_" ++)
       [ "commands", "syntax", "methods", "attributes", "theorems"
       , "tcset"
       , "facts", "binds", "drafts", "locale", "locales", "interps"
       , "trans_rules", "simp_set", "claset", "cases", "induct_rules" ]

-- | toplevel keywords currently recognized by IsaParse
usedTopKeys :: [String]
usedTopKeys = markups ++
    [ importsS, usesS, beginS, contextS, mlS, axiomsS, defsS, constsS
    , constdefsS, lemmasS, theoremsS, lemmaS, corollaryS, theoremS
    , datatypeS
    , classesS, axclassS, instanceS, typesS, typedeclS, endS ]

-- | all Isabelle keywords
isaKeywords :: [String]
isaKeywords = "::" : andS : theoryS : map (:[]) ":=<|"
              ++ usedTopKeys ++ ignoredKeys
