{- |
Module      :  $Header$
Copyright   :  (c) Sonja Groening, Christian Maeder, Uni Bremen 2004-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

constants for Isabelle
-}

-- possibly differentiate between HOL and HOLCF

module Isabelle.IsaConsts where

import Isabelle.IsaSign

-- * predefined sorts

holType :: Sort
holType = [IsaClass "hol_type"]

isaTerm :: IsaClass
isaTerm = IsaClass "type"

pcpoS :: String
pcpoS = "pcpo"

pcpo :: IsaClass
pcpo = IsaClass pcpoS

dom :: Sort
dom = [pcpo]

-- * predefinded types

noType :: Typ
noType = Type "dummy" holType []

boolType :: Typ
boolType = Type "bool" holType []

intType :: Typ
intType = Type "int" holType []

mkOptionType :: Typ -> Typ
mkOptionType t = Type "option" holType [t]

prodType :: Typ -> Typ -> Typ
prodType t1 t2 = Type prodS holType [t1,t2]

mkFunType :: Typ -> Typ -> Typ
mkFunType s t = Type funS holType [s,t] -- was "-->" before

{-handy for multiple args: [T1,...,Tn]--->T  gives  T1-->(T2--> ... -->T)-}
mkCurryFunType :: [Typ] -> Typ -> Typ
mkCurryFunType = flip $ foldr mkFunType -- was "--->" before

voidDom :: Typ
voidDom = Type "void" dom []

{- should this be included (as primitive)? -}
flatDom :: Typ
flatDom = Type "flat" dom []

{- sort is ok? -}
mkContFun :: Typ -> Typ -> Typ
mkContFun t1 t2 = Type cFunS dom [t1,t2]

mkStrictProduct :: Typ -> Typ -> Typ
mkStrictProduct t1 t2 = Type sProdS dom [t1,t2]

mkContProduct :: Typ -> Typ -> Typ
mkContProduct t1 t2 = Type prodS dom [t1,t2]

{-handy for multiple args: [T1,...,Tn]--->T  gives  T1-->(T2--> ... -->T)-}
mkCurryContFun :: [Typ] -> Typ -> Typ
mkCurryContFun = flip $ foldr mkContFun -- was "--->" before

mkStrictSum :: Typ -> Typ -> Typ
mkStrictSum t1 t2 = Type sSumS dom [t1,t2]

prodS, sProdS, funS, cFunS, sSumS :: TName
prodS = "*"    -- this is printed as it is!
sProdS = "**"
funS = "=>"
cFunS = "->"
sSumS = "++"

-- * functions for term formation

-- | 1000
maxPrio :: Int
maxPrio = 1000

-- | 10
lowPrio :: Int
lowPrio = 10

-- | 2
isaEqPrio :: Int
isaEqPrio = 2 -- left assoc

-- | function application
termAppl :: Term -> Term -> Term
termAppl t1 t2 = MixfixApp t1 [t2] NotCont

-- | function application to a list of arguments
termMixfixAppl :: Term -> [Term] -> Term
termMixfixAppl t1 t2 = MixfixApp t1 t2 NotCont

-- | apply binary operation to arguments
binConst :: String -> Term -> Term -> Term
binConst s t1 t2 = MixfixApp (conDouble s) [t1,t2] NotCont

-- | construct a constant with no type
con :: VName -> Term
con s = Const s noType

conDouble :: String -> Term
conDouble = con . mkVName

-- * some stuff for HasCASL

-- | Some string
someS :: String
someS = "Some"

-- | Some term
conSomeT :: Typ -> Term
conSomeT t = Const (mkVName someS) t

-- | some constant with no type
conSome :: Term
conSome = conDouble someS

aptS :: String
aptS = "apt"

appS :: String
appS = "app"

pAppS :: String
pAppS = "pApp"

defOpS :: String
defOpS = "defOp"

fliftbinS :: String
fliftbinS = "fliftbin"

-- | defOp constant
defOp :: Term
defOp = conDouble defOpS

-- | Not string
cNot :: String
cNot = "Not"

-- | Not VName
notV :: VName
notV = VName cNot $ Just $ AltSyntax "~/ _" [40] 40

-- | Not constant
notOp :: Term
notOp = con notV

-- * quantor strings

allS, exS, ex1S :: String
allS = "ALL"
exS = "EX"
ex1S = "EX!"

-- * Strings and VNames of binary ops

conj :: String
conj = "op &"

disj :: String
disj = "op |"

impl :: String
impl = "op -->"

eq :: String
eq = "op ="

conjV :: VName
conjV = VName conj $ Just $ AltSyntax "(_ &/ _)"   [36, 35] 35

disjV :: VName
disjV = VName disj $ Just $ AltSyntax "(_ |/ _)"   [31, 30] 30

implV :: VName
implV = VName impl $ Just $ AltSyntax "(_ -->/ _)" [26, 25] 25

eqV :: VName
eqV   = VName eq   $ Just $ AltSyntax "(_ =/ _)"   [50, 51] 50

plusS :: String
plusS = "op +"

minusS :: String
minusS = "op -"

timesS :: String
timesS = "op *"

consS :: String
consS = "Cons"

plusV :: VName
plusV = VName plusS $ Just $ AltSyntax "(_ +/ _)"   [65, 66] 65

minusV :: VName
minusV = VName minusS $ Just $ AltSyntax "(_ -/ _)" [65, 66] 65

timesV :: VName
timesV = VName timesS $ Just $ AltSyntax "(_ */ _)" [70, 71] 70

consV :: VName
consV = VName consS $ Just $ AltSyntax "(_ #/ _)" [66, 65] 65

-- | apply VName operator to two term
binVNameAppl :: VName -> Term -> Term -> Term
binVNameAppl v t1 t2 = MixfixApp (con v) [t1,t2] NotCont

-- * binary junctors
binConj, binDisj, binImpl, binEqv, binEq :: Term -> Term -> Term
binConj = binVNameAppl conjV
binDisj = binVNameAppl disjV
binImpl = binVNameAppl implV
binEq   = binVNameAppl eqV
binEqv = binEq

-- * boolean constants

cTrue :: String
cTrue = "True"

cFalse :: String
cFalse = "False"

true :: Term
true = Const (mkVName cTrue) boolType

false :: Term
false = Const (mkVName cFalse) boolType

-- | lower case pair
pairC :: String
pairC = "pair"

-- | upper case pair
isaPair :: String
isaPair = "Pair"

-- * keywords in theory files from the Isar Reference Manual 2005

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

domainS :: String
domainS = "domain"

datatypeS :: String
datatypeS = "datatype"

fixrecS :: String
fixrecS = "fixrec"

primrecS :: String
primrecS = "primrec"

simpS :: String
simpS = "simp"

markups :: [String]
markups =
    [ "--", "chapter" , "section", "subsection", "subsubsection", "text"
    , "text_raw", "sect", "subsect", "subsubsect", "txt", "txt_raw"]

-- | toplevel keys that are currently ignored
ignoredKeys :: [String]
ignoredKeys =
    [ domainS, oopsS, refuteS, fixrecS, primrecS
    , "sorry", "done", "by", "proof", "apply", "qed"
    , "classrel", "defaultsort", "nonterminls", "arities"
    , "constdefs", "syntax", "no_syntax", "translations"
    , "global", "local", "hide", "use", "setup", "method_setup"
    , "ML_command", "ML_setup", "oracle"
    , "fix", "assume", "presume", "def", "note", "then", "from", "with"
    , "using", "have", "show", "hence", "thus", "shows", ".", ".."
--    , "rule", "iprover","OF", "of", "where", "assumption", "this", "-"
    , "let", "is", "next", "apply_end", "defer", "prefer", "back", "declare"
    , "pr", "thm", "prf", "term", "prop", "typ", "full_prf"
    , "undo", "redo", "kill", "thms_containing", "thms_deps"
    , "cd", "pwd", "use_thy", "use_thy_only", "update_thy", "update_thy_only"
    , "display_drafts", "in", "locale" -- "intro_classes"
    , "fixes", "constrains", "assumes", "defines", "notes", "includes"
    , "interpretation", "interpret", "obtain", "also", "finally"
    , "moreover", "ultimately" -- "trans", "sym", "symmetric"
    , "case", "judgment", "typedef", "morphisms", "record", "rep_datatype"
    , "recdef", "recdef_tc", "specification","ax_specification"
    , "inductive", "coinductive", "inductive_cases", "codatatype"
    , "code_module", "code_library", "consts_code", "types_code" ]
    ++ map (++ "_translation")
       [ "parse_ast", "parse", "print", "print_ast", "typed_print", "token" ]
    ++ map ("print_" ++)
       [ "commands", "syntax", "methods", "attributes", "theorems", "tcset"
       , "facts", "binds", "drafts", "locale", "locales", "interps"
       , "trans_rules", "simp_set", "claset", "cases", "induct_rules" ]

-- | toplevel keywords currently recognized by IsaParse
usedTopKeys :: [String]
usedTopKeys = markups ++
    [ importsS, usesS, beginS, contextS, mlS, axiomsS, defsS, constsS
    , lemmasS, theoremsS, lemmaS, corollaryS, theoremS, datatypeS
    , classesS, axclassS, instanceS, typesS, typedeclS, endS ]

-- | all Isabelle keywords
isaKeywords :: [String]
isaKeywords = "::" : andS : theoryS : map (:[]) ":=<|"
              ++ usedTopKeys ++ ignoredKeys
