{- |
Module      :  $Header$
Copyright   :  (c) University of Cambridge, Cambridge, England
               adaption (c) Till Mossakowski, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

   Printing functions for Isabelle logic.
-}
{-
  todo: brackets in (? x . p x) ==> q
-}

module Isabelle.IsaPrint where

import Isabelle.IsaSign
import Common.PrettyPrint
import Common.Lib.Pretty
import qualified Common.Lib.Map as Map

------------------- Printing functions -------------------

instance Show Sentence where
  show s = show (senTerm s)

instance PrintLaTeX Sentence where
    printLatex0 = printText0

instance PrettyPrint Sentence where
    printText0 _ = text . show

instance Show Typ where
  show = showTyp 1000

showTyp :: Integer -> Typ -> String
showTyp pri (Type "typeAppl" _ [s,t]) =
  if withTFrees t then showTyp pri t ++ sp ++ showTyp pri s
    else showTyp pri s ++ sp ++ showTyp pri t
  where withTFrees tv =
          case tv of
            TFree _ _ -> True
            Type _ _ ts -> and (map withTFrees ts)
            _      -> False
showTyp pri (Type "fun" _ [s,t]) = 
  bracketize (pri<=10) (showTyp 10 s ++ " => " ++ showTyp 11 t)
showTyp pri (Type "*" _ [s,t]) =
  lb ++ showTyp pri s ++ " * " ++ showTyp pri t ++ rb
showTyp _ (Type name _ args) = 
  case args of
    []     -> name
    arg:[] -> show arg ++ sp ++ name
    _      -> let (tyVars,types) = foldl split ([],[]) args
              in  
                lb ++ concat (map ((sp++) . show) tyVars) ++
                      concat (map ((sp++) . show) types) ++ rb ++ name
              where split (tv,ty) t = case t of 
                                        TFree _ _ -> (tv++[t],ty)
                                        _       -> (tv,ty++[t])
showTyp _ (TFree v _) = "\'" ++ v
showTyp _ (TVar (v,_) _) = "?\'" ++ v

instance Show TypeSig where
  show tysig =
    if Map.isEmpty (tycons tysig) then em
      else Map.foldWithKey showTycon em (tycons tysig) 
    where showTycon t arity rest =
            "typedecl "++
            (if arity>0 then lb++concat (map ((" 'a"++).show) [1..arity])++rb
             else em) ++ show t  ++"\n"++rest

instance Show Term where
  show = showTerm -- outerShowTerm   -- back to showTerm, because meta !! causes problems with show ?thesis

showTerm :: Term -> String
showTerm (Const c _ _) = c
showTerm (Free v _ _) = v
showTerm (Abs v _ t _) = lb++"% "++showTerm v++" . "++showTerm t++rb
showTerm (App (Const "All" _ _) (Abs v ty t _) _) = 
  showQuant "!" v ty t
showTerm (App (Const "Ex" _ _) (Abs v ty t _) _) = 
  showQuant "?" v ty t
showTerm (App (Const "Ex1" _ _) (Abs v ty t _) _) = 
  showQuant "?!" v ty t
showTerm (Case term alts _) =
  let sAlts = map showCaseAlt alts
  in 
   lb ++ "case" ++ sp ++ showTerm term ++ sp ++ "of" 
      ++ sp ++ head sAlts
      ++ concat (map ((++) ("\n" ++ sp ++ sp ++ sp ++ "|" ++ sp)) 
                                                    (tail sAlts)) ++ rb
-- Just t1 `App` t2 left
showTerm (If t1 t2 t3 _) = 
    lb ++ "if" ++ sp ++ showTerm t1 ++ sp ++ "then" ++ sp 
           ++ showTerm t2 ++ sp ++ "else" ++ sp ++ showTerm t3 ++ rb
showTerm (Let pts t _) = lb ++ "let" ++ sp ++ showPat False (head pts) 
                                ++ concat (map (showPat True) (tail pts))
                                ++ sp ++ "in" ++ sp ++ showTerm t ++ rb
showTerm t = showPTree (toPrecTree t)


showPat :: Bool -> (Term, Term) -> String
showPat b (pat, term) = 
  let s = sp ++ showTerm pat ++ sp ++ "=" ++ sp ++ lb ++ showTerm term ++ rb
  in
    if b then ";" ++ s
      else s


showCaseAlt :: (Term, Term) -> String
showCaseAlt (pat, term) =
-- trace ("Pat: " ++ show pat ++ "\n Term: " ++ show term ++ "\n")
  showTerm pat ++ sp ++ "=>" ++ sp ++ showTerm term

showQuant :: String -> Term -> Typ -> Term -> String
showQuant s var typ term =
  (s++sp++showTerm var++" :: "++show typ++" . "++showTerm term)

outerShowTerm :: Term -> String
outerShowTerm (App (Const "All" _ _) (Abs v ty t _) _) = 
  outerShowQuant "!!" v ty t
outerShowTerm (App (App (Const "op -->" _ _) t1 _) t2 _) =
  showTerm t1 ++ " ==> " ++ outerShowTerm1 t2
outerShowTerm t = showTerm t

outerShowTerm1 :: Term -> String
outerShowTerm1 (App (App (Const "op -->" _ _) t1 _) t2 _) =
  showTerm t1 ++ " ==> " ++ outerShowTerm1 t2
outerShowTerm1 t = showTerm t

outerShowQuant :: String -> Term -> Typ -> Term -> String
outerShowQuant s var typ term =
  (s++sp++showTerm var++" :: "++show typ++" . "++outerShowTerm term)


{-   
   For nearly perfect parenthesis - they only appear when needed - 
   a formula/term is broken open in following pieces:
                            (logical) connector
                           /                   \
                          /                     \
                formula's lhs               formula's rhs

   Every connector is annotated with its precedence, every 'unbreakable'
   formula gets the lowest precedence.
-}

-- term annotated with precedence
data PrecTerm = PrecTerm Term Precedence deriving (Show)
type Precedence = Int

{- Precedences (descending): __ __ (Isabelle's term application),
                             application of HasCASL ops, <=>, =, /\, \/, => 
   Associativity:  =  -- left
                   => -- right
                   /\ -- right
                   \/ -- right
-}

data PrecTermTree = Node PrecTerm [PrecTermTree]

isaAppPrec :: Term -> PrecTerm
isaAppPrec t = PrecTerm t 0

appPrec :: Term -> PrecTerm
appPrec t = PrecTerm t 5

eqvPrec :: Term -> PrecTerm
eqvPrec t = PrecTerm t 7

eqPrec :: Term -> PrecTerm
eqPrec t = PrecTerm t 10

andPrec :: Term -> PrecTerm
andPrec t = PrecTerm t 20

orPrec :: Term -> PrecTerm
orPrec t = PrecTerm t 30

implPrec :: Term -> PrecTerm
implPrec t = PrecTerm t 40

noPrec :: Term -> PrecTerm
noPrec t = PrecTerm t (-10)

toPrecTree :: Term -> PrecTermTree
toPrecTree trm =
  case trm of
    App c1@(Const "All" _ _) a2@(Abs _ _ _ _) _-> 
       Node (isaAppPrec (Const "QUANT" noType isaTerm)) 
            [toPrecTree c1, toPrecTree a2]
    App c1@(Const "Ex" t1 c) a2@(Abs _ _ _ _) _ -> 
       Node (isaAppPrec (Const "QUANT" noType isaTerm)) 
            [toPrecTree c1, toPrecTree a2]
    App c1@(Const "Ex1" t1 c) a2@(Abs _ _ _ _) _ -> 
       Node (isaAppPrec (Const "QUANT" noType isaTerm)) 
            [toPrecTree c1, toPrecTree a2]
    App t1 t2 _ -> 
      case t1 of 
        App t@(Const "op <=>" _ _) t3 _ 
          -> Node (eqvPrec t)
                  [toPrecTree t3, toPrecTree t2] 
        App t@(Const "op =" _ _) t3 _
          -> Node (eqPrec t)
                  [toPrecTree t3, toPrecTree t2] 
        App t@(Const "op &" _ _) t3 _ 
          -> Node (andPrec t)
                  [toPrecTree t3, toPrecTree t2] 
        App t@(Const "op |" _ _) t3 _ 
          -> Node (orPrec t)
                  [toPrecTree t3, toPrecTree t2] 
        App t@(Const "op -->" _ _) t3 _ 
          -> Node (implPrec t)
                  [toPrecTree t3, toPrecTree t2] 
        App t@(Const _ _ _) t3 _ 
          -> Node (appPrec t)
                  [toPrecTree t3, toPrecTree t2] 
        _ -> Node (isaAppPrec (Const "DUMMY" noType isaTerm)) 
               [toPrecTree t1, toPrecTree t2] 
    _ -> Node (noPrec trm) []


-- instance Show PrecTermTree where
--    show = showPTree

data Assoc = LeftAs | NoAs | RightAs

showPTree :: PrecTermTree -> String
showPTree (Node (PrecTerm term _) []) = showTerm term
showPTree (Node (PrecTerm term pre) annos) = 
  let leftChild = head annos
      rightChild = last annos
   in
     case term of
       Const "op =" _ _   -> infixP pre "=" LeftAs leftChild rightChild
       Const "op &" _ _   -> infixP pre "&" RightAs leftChild rightChild
       Const "op |" _ _   -> infixP pre "|" RightAs leftChild rightChild
       Const "op -->" _ _ -> infixP pre "-->" RightAs leftChild rightChild
       Const "DUMMY" _ _  -> simpleInfix pre leftChild rightChild
       Const "Pair" _ _   -> pair leftChild rightChild
       Const "QUANT"_ _   -> quant leftChild rightChild
       Const c _ _        -> prefixP pre c leftChild rightChild
       _                  -> showTerm term


{- Logical connectors: For readability and by habit they are written 
   at an infix position.
   If the precedence of one side is weaker (here: higher number) than the 
   connector's one it is bracketed. Otherwise not. 
-}
infixP :: Precedence -> String -> Assoc -> PrecTermTree -> PrecTermTree -> String
infixP pAdult stAdult assoc leftChild rightChild 
    | (pAdult < prLeftCld) && (pAdult < prRightCld) = both
    | pAdult < prLeftCld = 
        case assoc of 
          LeftAs  -> if pAdult == prRightCld then both else left
          RightAs -> left
          NoAs    -> left
    | pAdult < prRightCld = 
        case assoc of
          LeftAs  -> right
          RightAs -> if pAdult == prLeftCld then both else right
          NoAs    -> right
    | (pAdult == prLeftCld) && (pAdult == prRightCld) = 
        case assoc of
          LeftAs  -> right
          RightAs -> left
          NoAs    -> no
    | pAdult == prLeftCld = 
        case assoc of
          LeftAs  -> no
          RightAs -> left
          NoAs    -> no
    | pAdult == prRightCld =
        case assoc of
          LeftAs  -> right
          RightAs -> no
          NoAs    -> no
    | otherwise = no
  where prLeftCld = pr leftChild
        prRightCld = pr rightChild
        stLeftCld = showPTree leftChild
        stRightCld = showPTree rightChild
        left = lb++ stLeftCld ++rb++sp++ stAdult ++sp++ stRightCld
        both = lb++ stLeftCld ++rb++sp++ stAdult ++sp++lb++ stRightCld ++rb
        right = stLeftCld ++sp++ stAdult ++sp++lb++ stRightCld ++rb
        no =  stLeftCld ++sp++ stAdult ++sp++ stRightCld


{- Application of (HasCASL-)operations with two arguments. 
   Both arguments are usually bracketed, except single ones.
-}
prefixP :: Precedence -> String -> PrecTermTree -> PrecTermTree -> String
prefixP pAdult stAdult leftChild rightChild 
    | (pAdult <= prLeftCld) && (pAdult <= prRightCld) =
          stAdult ++
              sp++lb++ stLeftCld ++rb++
                  sp++lb++ stRightCld ++rb
    | pAdult <= prLeftCld = 
          stAdult ++
              sp++lb++ stLeftCld ++rb++
                  sp++ stRightCld
    | pAdult <= prRightCld = 
          stAdult ++
              sp++ stLeftCld ++
                  sp++lb++ stRightCld ++rb
    | otherwise =  stAdult ++
                       sp++ stLeftCld ++
                           sp++ stRightCld
  where prLeftCld = pr leftChild
        prRightCld = pr rightChild
        stLeftCld = showPTree leftChild
        stRightCld = showPTree rightChild

{- Isabelle application: An operation/a datatype-constructor is applied 
   to one argument. The whole expression is always bracketed.
-}
simpleInfix :: Precedence -> PrecTermTree -> PrecTermTree -> String
simpleInfix pAdult leftChild rightChild 
    | (pAdult < prLeftCld) && (pAdult < prRightCld) = 
          lbb++ stLeftCld ++rb++
                sp++lb++ stRightCld ++rbb
    | pAdult < prLeftCld = 
          lbb++ stLeftCld ++rb++
                sp++ stRightCld ++rb
    | pAdult < prRightCld = 
          lb++ stLeftCld ++sp++
               lb++ stRightCld ++rbb
    | otherwise = lb++ stLeftCld ++sp++
                       stRightCld ++rb
  where prLeftCld = pr leftChild
        prRightCld = pr rightChild
        stLeftCld = showPTree leftChild
        stRightCld = showPTree rightChild


{- Quantification _in_ Formulas
-}
quant :: PrecTermTree -> PrecTermTree -> String
quant (Node (PrecTerm (Const"All"_ _) _) []) 
          (Node (PrecTerm (Abs v ty t _) _) []) = 
              lb++showQuant "!"  v ty t++rb
quant (Node (PrecTerm (Const"Ex"_ _) _) []) 
          (Node (PrecTerm (Abs v ty t _) _) [])  = 
              lb++showQuant "?"  v ty t++rb
quant (Node (PrecTerm (Const"Ex1"_ _) _) []) 
          (Node (PrecTerm (Abs v ty t _) _) []) = 
              lb++showQuant "?!"  v ty t++rb
quant _ _ = error "[Isabelle.IsaPrint] Wrong quantification!?"


pr :: PrecTermTree -> Precedence
pr (Node (PrecTerm _ p) _) = p

-- Prints: (p1, p2)
pair :: PrecTermTree -> PrecTermTree -> String
pair leftChild rightChild = lb++showPTree leftChild++", "++
                                showPTree rightChild++rb

-- Not, =, and, or, -->: Absteigende Prio, alle rechtsassoz (ausser Not)

--sT t = trace ("[sT] "++st t++"\n") (showTerm 1000 t)

-- st (Const (c,_)) =  "Const ("++c++")"
-- st (Free (v,_)) = "Free ("++v++")"
-- st (Abs (v,_,t)) = "%"++showTerm v++" . "++showTerm t
-- st (Const ("All",_) `App` Abs (v,ty,t)) = 
--    ("! "++showTerm v++" :: "++show ty++" . "++showTerm t)
-- st (Const ("Ex",_) `App` Abs (v,_,t)) = 
--    ( "? "++showTerm v++" . "++showTerm t)
-- st (Const ("Ex1",_) `App` Abs (v,_,t)) = 
--    ( "?! "++showTerm v++" . "++showTerm t)
-- st (t1 `App` t2) = "App(["++st t1++"],["++st t2++"])"


instance Show Sign where
  show sig =
    baseSig sig ++":\n\n"++
    shows (tsig sig) (showDataTypeDefs (dataTypeTab sig))
      ++ (showsConstTab (constTab sig))
    where
    showsConstTab tab =
     if Map.isEmpty tab then ""
      else "\nconsts\n" ++ Map.foldWithKey showConst "" tab
    showConst c t rest = show c ++ " :: " ++ "\"" ++ show t 
                                ++ "\"" ++ showDecl c ++ "\n" ++ rest
    showDecl c = sp ++ sp ++ sp ++ "( \"" ++ c ++ "\" )"
    showDataTypeDefs dtDefs = concat $ map showDataTypeDef dtDefs
    showDataTypeDef [] = ""
    showDataTypeDef (dt:dts) = 
       "datatype " ++ showDataType dt
       ++ (concat $ map (("and "++) . showDataType) dts) ++ "\n"
    showDataType (_,[]) = error "IsaPrint.showDataType"
    showDataType (t,op:ops) =
       show t ++ " = " ++ showOp op 
       ++ (concat $ map ((" | "++) . showOp) ops)
    showOp (opname,args) =
       opname ++ (concat $ map ((sp ++) . showArg) args)
    showArg arg = case arg of
                    TFree _ _-> show arg
                    _      -> "\"" ++ show arg ++ "\""


instance PrettyPrint Sign where
    printText0 _ = text . show

instance PrintLaTeX Sign where
    printLatex0 = printText0



em :: String
em = ""

sp :: String
sp = " "

rb :: String
rb = ")"

rbb :: String
rbb = rb++rb

lb :: String
lb = "("

lbb :: String
lbb = lb++lb


bracketize :: Bool -> String -> String
bracketize b s = if b then lb++s++rb else s
