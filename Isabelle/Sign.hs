module Isabelle.Sign where

import qualified Common.Lib.Map as Map
import Common.Id

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
             -- | TVar  (Indexname, Sort)

instance Show Typ where
  show = showTyp 1000

showTyp pri (Type ("fun",[s,t])) = 
  bracketize (pri<=10) (showTyp 10 s ++ "=>" ++ showTyp 11 t)
showTyp pri (Type (t,args)) = "("++concat (map ((" "++).show) args)++")"++t
showTyp pri (TFree (v,_)) = v

infix -->
infix --->

s --> t = Type("fun",[s,t])

{-handy for multiple args: [T1,...,Tn]--->T  gives  T1-->(T2--> ... -->T)-}
(--->) = foldr (-->)

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
      | Abs   (String, Typ, Term)
      | App Term  Term

instance Show Term where
  show = showTerm 1000

showTerm :: Int -> Term -> String
showTerm pri (Const (c,_)) = c
showTerm pri (Free (v,_)) = v
showTerm pri (Abs (v,_,t)) = "%"++v++" . "++show t
showTerm pri (Abs (v,_,t)) = "%"++v++" . "++show t
showTerm pri (Const ("All",_) `App` Abs (v,_,t)) = "!"++v++" . "++show t
showTerm pri (Const ("Ex",_) `App` Abs (v,_,t)) = "?"++v++" . "++show t
showTerm pri (Const ("Ex1",_) `App` Abs (v,_,t)) = "?!"++v++" . "++show t
showTerm pri (t1 `App` t2) = 
  bracketize (pri<=10) (showTerm 11 t1 ++ " " ++ showTerm 10 t2)


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

type Classrel = Map.Map Id [Class]
type Arities = Map.Map Id [(Class, [Sort])]


-------------------- from src/Pure/type.ML ------------------------

data TypeSig =
  TySg {
    classes:: [Class],
    classrel:: Classrel,
    defaultSort:: Sort,
    tycons:: Map.Map Id Int,
    log_types:: [String],
    univ_witness:: Maybe (Typ,  Sort),
    abbrs:: Map.Map Id ([String],Typ),
    arities:: Arities }

instance Show TypeSig where
  show tysig =
    if Map.isEmpty (tycons tysig) then ""
     else "types\n" ++ Map.foldWithKey showTycon "" (tycons tysig) 
     where showTycon t arity rest =
             "  "++
             (if arity>0 then "("++concat (map ((" 'a"++).show) [1..arity])++")"
               else "") 
            ++ show t
            ++"\n"++rest

-------------------- from src/Pure/sign.ML ------------------------

data Sign = Sign { baseSig :: String, -- like Pure, HOL etc.
                   tsig :: TypeSig,
                   constTab :: Map.Map Id Typ,
                   syn :: Syntax
                 }

instance Show Sign where
  show sig =
    baseSig sig ++":\n"++
    shows (tsig sig) 
      (showsConstTab (constTab sig))
    where
    showsConstTab tab =
     if Map.isEmpty tab then ""
      else "consts\n" ++ Map.foldWithKey showConst "" tab
    showConst c t rest = show c ++ " :: " ++ "\"" ++ show t ++ "\"" ++ rest