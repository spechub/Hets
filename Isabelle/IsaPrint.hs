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
  properly construct docs
-}

module Isabelle.IsaPrint where

import Isabelle.IsaSign
import Isabelle.IsaConsts
import Common.PrettyPrint
import Common.Lib.Pretty
import Data.Char
import qualified Common.Lib.Map as Map

------------------- Printing functions -------------------

instance PrettyPrint IsaClass where
     printText0 _ (IsaClass c _) = parens $ text c

instance PrintLaTeX Sentence where
  printLatex0 = printText0

instance PrettyPrint Sentence where
    printText0 _ = text . showTerm . senTerm

instance PrettyPrint Typ where
  printText0 _ = text . showTyp 1000

showTyp :: Integer -> Typ -> String
showTyp pri (Type str _ _ [s,t]) 
  | str == typeApplS = 
     if withTFrees t then showTyp pri t ++ sp ++ showTyp pri s
        else showTyp pri s ++ sp ++ showTyp pri t
  | str == funS =
       bracketize (pri<=10) (showTyp 10 s ++ " => " ++ showTyp 11 t)
  | str == prodS = 
       lb ++ showTyp pri s ++ " * " ++ showTyp pri t ++ rb
            where withTFrees tv =
                      case tv of
                              TFree _ _ -> True
                              Type _ _ _ ts -> and (map withTFrees ts)
                              _      -> False
showTyp _ (Type name _ _ args) = 
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

instance PrettyPrint TypeSig where
  printText0 _ tysig =
    if Map.isEmpty (arities tysig) then empty
      else text $ Map.foldWithKey showTycon "" (arities tysig) 
    where showTycon t arity' rest = 
              let arity = if null arity' then
                          error "IsaPrint.printText0 (TypeSig)" 
                                else length (snd $ head arity') in 
            "typedecl "++
            (if arity>0 then lb++concat (map ((" 'a"++).show) [1..arity])++rb
             else "") ++ show t  ++"\n"++rest

instance PrettyPrint Term where
  printText0 _ = text . showTerm -- outerShowTerm   
  -- back to showTerm, because meta !! causes problems with show ?thesis

showQuantStr :: String -> String
showQuantStr s | s == allS = "!"
               | s == exS  = "?"
               | s == ex1S = "?!"
               | otherwise = error "IsaPrint.showQuantStr"

showTerm :: Term -> String
showTerm (Const c _ _) = c
showTerm (Free v _ _) = v
showTerm (Abs v _ t _) = lb++"% "++showTerm v++" . "++showTerm t++rb
showTerm (App (Const q _ _) (Abs v ty t _) _) | q `elem` [allS, exS, ex1S] =
  showQuant (showQuantStr q) v ty t
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
  (s++sp++showTerm var++" :: "++showTyp 1000 typ++" . "++showTerm term)

outerShowTerm :: Term -> String
outerShowTerm (App (Const q _ _) (Abs v ty t _) _) | q == allS = 
  outerShowQuant "!!" v ty t
outerShowTerm (App (App (Const o _ _) t1 _) t2 _) | o == impl =
  showTerm t1 ++ " ==> " ++ outerShowTerm1 t2
outerShowTerm t = showTerm t

outerShowTerm1 :: Term -> String
outerShowTerm1 t@(App (App (Const o _ _) _ _) _ _) | o == impl =
  outerShowTerm t
outerShowTerm1 t = showTerm t

outerShowQuant :: String -> Term -> Typ -> Term -> String
outerShowQuant s var typ term =
  (s++sp++showTerm var++" :: "++showTyp 1000 typ++" . "++outerShowTerm term)


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

quantS :: String
quantS = "QUANT" 

dummyS :: String
dummyS = "Dummy" 

binFunct :: String -> Term -> PrecTerm
binFunct s | s == eqv  = eqvPrec
           | s == eq   = eqPrec
           | s == conj = andPrec
           | s == disj = orPrec
           | s == impl = implPrec
           | otherwise = appPrec

toPrecTree :: Term -> PrecTermTree
toPrecTree trm =
  case trm of
    App c1@(Const q _ _) a2@(Abs _ _ _ _) _ | q `elem` [allS, exS, ex1S] -> 
       Node (isaAppPrec $ con quantS) [toPrecTree c1, toPrecTree a2]
    App (App t@(Const o _ _) t3 _) t2 _ ->
      Node (binFunct o t) [toPrecTree t3, toPrecTree t2]
    App t1 t2 _ -> Node (isaAppPrec $ con dummyS) 
                   [toPrecTree t1, toPrecTree t2] 
    _ -> Node (noPrec trm) []

data Assoc = LeftAs | NoAs | RightAs

showPTree :: PrecTermTree -> String
showPTree (Node (PrecTerm term _) []) = showTerm term
showPTree (Node (PrecTerm term pre) annos) = 
  let leftChild = head annos
      rightChild = last annos
   in
     case term of
       Const c _ _ | c == eq -> infixP pre "=" LeftAs leftChild rightChild
                   | c `elem` [conj, disj, impl] ->
                        infixP pre (drop 3 c) RightAs leftChild rightChild
                   | c == dummyS  -> simpleInfix pre leftChild rightChild
                   | c == isaPair -> pair leftChild rightChild
                   | c == quantS  -> quant leftChild rightChild
                   | otherwise    -> prefixP pre c leftChild rightChild
       _ -> showTerm term

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
quant (Node (PrecTerm (Const q _ _) _) []) 
          (Node (PrecTerm (Abs v ty t _) _) []) = 
              lb++showQuant (showQuantStr q)  v ty t++rb
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


instance PrettyPrint Sign where
  printText0 ga sig = text
    (baseSig sig) <> colon $$
    printText0 ga (tsig sig) $$
    showDataTypeDefs (dataTypeTab sig) $$
    showsConstTab (constTab sig) $$
    showCaseLemmata (dataTypeTab sig)
    where
    showsConstTab tab =
     if Map.isEmpty tab then empty
      else text("consts") $$ Map.foldWithKey showConst empty tab
    showConst c t rest = text (show c ++ " :: " ++ "\"" ++ showTyp 1000 t 
                                ++ "\"" ++ showDecl c) $$ rest
    showDecl c = sp ++ sp ++ sp ++ "( \"" ++ c ++ "\" )"
    showDataTypeDefs dtDefs = vcat $ map (text . showDataTypeDef) dtDefs
    showDataTypeDef [] = ""
    showDataTypeDef (dt:dts) = 
       "datatype " ++ showDataType dt
       ++ (concat $ map (("and "++) . showDataType) dts) ++ "\n"
    showDataType (_,[]) = error "IsaPrint.showDataType"
    showDataType (t,op:ops) =
       showTyp 1000 t ++ " = " ++ showOp op 
       ++ (concat $ map ((" | "++) . showOp) ops)
    showOp (opname,args) =
       opname ++ (concat $ map ((sp ++) . showArg) args)
    showArg arg = case arg of
                    TFree _ _ -> showTyp 1000 arg
                    _         -> "\"" ++ showTyp 1000 arg ++ "\""
    showCaseLemmata dtDefs = text (concat $ map showCaseLemmata1 dtDefs)
    showCaseLemmata1 dts = concat $ map showCaseLemma dts
    showCaseLemma (_, []) = ""
    showCaseLemma (tyCons, (c:cons)) = 
      let cs = "case a of" ++ sp
          sc b = showCons b c ++ (concat $ map (("   | " ++) . (showCons b)) cons)
          clSome = sc True
          cl = sc False
          showCons b (cName, args) =
            let pat = cName ++ (concat $ map ((sp ++) . showArg) args) 
                            ++ sp ++ "=>" ++ sp 
                term = showCaseTerm cName args
            in
               if b then pat ++ "Some" ++ sp ++ lb ++ term ++ rb ++ "\n"
                 else pat ++ term ++ "\n"
          showCaseTerm name args = if null name then sa 
                                     else [toLower (head name)] ++ sa
            where sa = (concat $ map ((sp ++) . showArg) args)
          showArg (TFree [] _) = "varName"
          showArg (TFree (n:ns) _) = [toLower n] ++ ns
          showArg (TVar ([], _) _) = "varName"
          showArg (TVar ((n:ns), _) _) = [toLower n] ++ ns
          showArg (Type [] _ _ _) = "varName"
          showArg (Type m@(n:ns) _ _ s) = 
            if m == "typeAppl" || m == "fun" || m == "*"  then concat $ map showArg s
              else [toLower n] ++ ns
          showName (TFree v _) = v
          showName (TVar (v, _) _)  = v
          showName (Type n _ _ _) = n
          proof = "apply (case_tac a)\napply (auto)\ndone\n"
      in
        "lemma" ++ sp ++ "case_" ++ showName tyCons ++ "_SomeProm" ++ sp
                ++ "[simp]:\"" ++ sp ++ lb ++ cs ++ clSome ++ rb ++ sp
                ++ "=\n" ++ "Some" ++ sp ++ lb ++ cs ++ cl ++ rb ++ "\"\n"
                ++ proof


-- datatype Bool = True | False

-- lemma case_Type {typeId = "Bool", typeArgKind = [], typeResultKind = [], typeArgs = []}_SomeProm [simp]:"(case a ofTrue  => Some( true
-- )   |False  => Some( false
-- )) =
-- Some (case a ofTrue  => true
--    |False  => false
-- )"

-- type DataTypeTab = [DataTypeTabEntry]
-- type DataTypeTabEntry = [(Typ,[DataTypeAlt])] -- (type,[constructors])
-- type DataTypeAlt = (String,[Typ])



-- instance PrettyPrint Sign where
--     printText0 _ = ptext . show

instance PrintLaTeX Sign where
    printLatex0 = printText0

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
