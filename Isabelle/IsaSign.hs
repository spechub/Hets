{- |
Module      :  $Header$
Copyright   :  (c) University of Cambridge, Cambridge, England
               adaption (c) Till Mossakowski, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

   Data structures for Isabelle sigantures and theories.
   Adapted from Isabelle.
-}

module Isabelle.IsaSign where

import qualified Common.Lib.Map as Map
import Common.Id
import Common.PrettyPrint
import Common.Lib.Pretty

bracketize :: Bool -> String -> String
bracketize b s = if b then "("++s++")" else s

---------------- from src/Pure/Syntax/syntax.ML -------------------

type Syntax = () -- leave this for later

-------------------- from src/Pure/term.ML ------------------------

{-Indexnames can be quickly renamed by adding an offset to the integer part,
  for resolution.-}
type Indexname = (String,Int)

{- Types are classified by sorts. -}
type Class = String;
type Sort  = [Class]

{- The sorts attached to TFrees and TVars specify the sort of that variable -}
data Typ = Type (String,[Typ])
             | TFree (String, Sort)
             -- TVar  (Indexname, Sort)
           deriving (Eq, Ord)

instance Show Typ where
  show = showTyp 1000

showTyp _ (Type (t,[])) = t
showTyp pri (Type ("fun",[s,t])) = 
  bracketize (pri<=10) (showTyp 10 s ++ "=>" ++ showTyp 11 t)
showTyp pri (Type (t,args)) = "("++concat (map ((" "++).show) args)++")"++t
showTyp pri (TFree (v,_)) = v

infix -->
infix --->

dummyT :: Typ
dummyT = Type("dummy",[])

boolType :: Typ
boolType = Type("bool",[])

mkOptionType :: Typ -> Typ
mkOptionType t = Type("option",[t])

mkProductType :: Typ -> Typ -> Typ
mkProductType t1 t2 = Type ("*",[t1,t2])

s --> t = Type("fun",[s,t])

{-handy for multiple args: [T1,...,Tn]--->T  gives  T1-->(T2--> ... -->T)-}
(--->) = flip $ foldr (-->)

{-Terms.  Bound variables are indicated by depth number.
  Free variables, (scheme) variables and constants have names.
  An term is "closed" if every bound variable of level "lev"
  is enclosed by at least "lev" abstractions.

  It is possible to create meaningless terms containing loose bound vars
  or type mismatches.  But such terms are not allowed in rules. -}


data Term =
        Const (String, Typ)
      | Free  (String, Typ)
      -- | Var   (Indexname, Typ)
      -- | Bound Int
      | Abs   (Term, Typ, Term)
      | App Term  Term
      deriving (Eq, Ord)

instance Show Term where
  show = showTerm 1000

showTerm :: Int -> Term -> String
showTerm pri (Const (c,_)) = c
showTerm pri (Free (v,_)) = v
showTerm pri (Abs (v,_,t)) = "%"++showTerm pri v++" . "++showTerm pri t
showTerm pri (Abs (v,_,t)) = "%"++showTerm pri v++" . "++showTerm pri t
showTerm pri (Const ("All",_) `App` Abs (v,ty,t)) = 
  bracketize (pri<=10) ("! "++showTerm pri v++" :: "++show ty++" . "++showTerm pri t)
showTerm pri (Const ("Ex",_) `App` Abs (v,_,t)) = 
  bracketize (pri<=10) ( "? "++showTerm pri v++" . "++showTerm pri t)
showTerm pri (Const ("Ex1",_) `App` Abs (v,_,t)) = 
  bracketize (pri<=10) ( "?! "++showTerm pri v++" . "++showTerm pri t)
showTerm pri (t1 `App` t2) = 
  bracketize (pri<=10) (showTerm 11 t1 ++ " " ++ showTerm 10 t2)


data Sentence = Sentence { senTerm :: Term
                           }
instance Eq Sentence where
  s1 == s2 = senTerm s1 == senTerm s2

instance Ord Sentence where
  compare s1 s2 = compare (senTerm s1) (senTerm s2)

instance Show Sentence where
  show s = show (senTerm s)

instance PrettyPrint Sentence where
    printText0 _ = ptext . show

instance PrintLaTeX Sentence where
    printLatex0 = printText0


-------------------- from src/Pure/sorts.ML ------------------------

{-- type classes and sorts --}

{-
  Classes denote (possibly empty) collections of types that are
  partially ordered by class inclusion. They are represented
  symbolically by strings.

  Sorts are intersections of finitely many classes. They are
  represented by lists of classes.  Normal forms of sorts are sorted
  lists of minimal classes (wrt. current class inclusion).

  (already defined in Pure/term.ML)
-}


{- sort signature information -}

{-
  classrel:
    table representing the proper subclass relation; entries (c, cs)
    represent the superclasses cs of c;

  arities:
    table of association lists of all type arities; (t, ars) means
    that type constructor t has the arities ars; an element (c, Ss) of
    ars represents the arity t::(Ss)c;
-}

type Classrel = Map.Map String [Class]
type Arities = Map.Map String [(Class, [Sort])]


-------------------- from src/Pure/type.ML ------------------------

data TypeSig =
  TySg {
    classes:: [Class],
    classrel:: Classrel,
    defaultSort:: Sort,
    tycons:: Map.Map String Int,
    log_types:: [String],
    univ_witness:: Maybe (Typ,  Sort),
    abbrs:: Map.Map String ([String],Typ),
    arities:: Arities }
   deriving (Eq)

emptyTypeSig :: TypeSig
emptyTypeSig = TySg {
    classes = [],
    classrel = Map.empty,
    defaultSort = [],
    tycons = Map.empty,
    log_types = [],
    univ_witness = Nothing,
    abbrs = Map.empty,
    arities = Map.empty }

instance Show TypeSig where
  show tysig =
    if Map.isEmpty (tycons tysig) then ""
     else Map.foldWithKey showTycon "" (tycons tysig) 
     where showTycon t arity rest =
             "typedecl "++
             (if arity>0 then "("++concat (map ((" 'a"++).show) [1..arity])++")"
               else "") 
            ++ show t
            ++"\n"++rest

-------------------- from src/Pure/sign.ML ------------------------

data Sign = Sign { baseSig :: String, -- like Pure, HOL, Main etc.
                   tsig :: TypeSig,
                   constTab :: Map.Map String Typ,
                   dataTypeTab :: [[(Typ,[(String,[Typ])])]],
                   syn :: Syntax
                 }
             deriving (Eq)

emptySign :: Sign
emptySign = Sign { baseSig = "Pure",
                   tsig = emptyTypeSig,
                   constTab = Map.empty,
                   dataTypeTab = [],
                   syn = () }

instance Show Sign where
  show sig =
    baseSig sig ++":\n"++
    shows (tsig sig) (showDataTypeDefs (dataTypeTab sig))
      ++ (showsConstTab (constTab sig))
    where
    showsConstTab tab =
     if Map.isEmpty tab then ""
      else "consts\n" ++ Map.foldWithKey showConst "" tab
    showConst c t rest = show c ++ " :: " ++ "\"" ++ show t ++ "\"\n" ++ rest
    showDataTypeDefs dtDefs = concat $ map showDataTypeDef dtDefs
    showDataTypeDef [] = ""
    showDataTypeDef (dt:dts) = 
       "datatype " ++ showDataType dt
       ++ (concat $ map (("and "++) . showDataType) dts)
    showDataType (t,op:ops) =
       show t ++ " = " ++ showOp op 
       ++ (concat $ map ((" | "++) . showOp) ops)
    showOp (opname,args) =
       opname ++ (concat $ map (((" ")++) . show) args)


instance PrettyPrint Sign where
    printText0 _ = ptext . show

instance PrintLaTeX Sign where
    printLatex0 = printText0
