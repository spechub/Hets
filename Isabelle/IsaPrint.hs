{-# OPTIONS -fallow-overlapping-instances #-}
{- |
Module      :  $Header$
Copyright   :  (c) University of Cambridge, Cambridge, England
               adaption (c) Till Mossakowski, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  non-portable(overlapping-instances)

   Printing functions for Isabelle logic.
-}
{-
  todo: brackets in (? x . p x) ==> q
-}

module Isabelle.IsaPrint where

import Common.Id 
import Common.PrettyPrint
import Common.Lib.Pretty
import qualified Common.Lib.Map as Map

import Isabelle.IsaSign

import Data.Char
import Data.Tree

import Debug.Trace



------------------- Id translation functions -------------------

showIsa :: Id -> String
showIsa = transString . flip showPretty em

showIsaSid :: SIMPLE_ID -> String
showIsaSid = transString . flip showPretty em

-- disambiguation of overloaded ids
showIsaI :: Id -> Int -> String
showIsaI ident i = showIsa ident ++ "_" ++ show i



------------------- Printing functions -------------------

instance Show Sentence where
  show s = show (senTerm s)

instance PrintLaTeX Sentence where
    printLatex0 = printText0

instance PrettyPrint Sentence where
    printText0 _ = ptext . show

instance Show Typ where
  show = showTyp 1000

showTyp :: Integer -> Typ -> String
showTyp pri (Type ("typeAppl",[s,t])) =
  case t of
    TVar _ -> showTyp pri t ++ sp ++ showTyp pri s
    _      -> showTyp pri s ++ sp ++ showTyp pri t
showTyp pri (Type ("fun",[s,t])) = 
  bracketize (pri<=10) (showTyp 10 s ++ " => " ++ showTyp 11 t)
showTyp pri (Type ("*",[s,t])) =
  showTyp pri s ++ " * " ++ showTyp pri t
showTyp _ (Type (name,args)) = 
  case args of
    []     -> name
    arg:[] -> show arg ++ sp ++ name
    _      -> let (tyVars,types) = foldl split ([],[]) args
              in  
                rb ++ concat (map ((sp++) . show) tyVars) ++
                                concat (map ((sp++) . show) types) ++ lb ++ name
              where split (tv,ty) t = case t of 
                            TVar _ -> (tv++[t],ty)
                            _      -> (tv,ty++[t])
showTyp _ (TFree (v,_)) = v
showTyp _ (TVar ((v,_),_)) = "\'" ++ v

instance Show TypeSig where
  show tysig =
    if Map.isEmpty (tycons tysig) then em
     else Map.foldWithKey showTycon em (tycons tysig) 
     where showTycon t arity rest =
            "typedecl "++
             (if arity>0 then rb++concat (map ((" 'a"++).show) [1..arity])++lb
               else em)
            ++ show t
            ++"\n"++rest

instance Show Term where
  show = outerShowTerm

showTerm :: Term -> String
showTerm (Const (c,_)) = c
showTerm (Free (v,_)) = v
showTerm (Abs (v,_,t)) = rb++"% "++showTerm v++" . "++showTerm t++lb
showTerm (Const ("All",_) `App` Abs (v,ty,t)) = 
  showQuant "!" v ty t
showTerm (Const ("Ex",_) `App` Abs (v,ty,t)) = 
  showQuant "?" v ty t
showTerm (Const ("Ex1",_) `App` Abs (v,ty,t)) = 
  showQuant "?!" v ty t
-- At this point is just t1 `App` t2 left
showTerm t = show(toPrecTree t)

showQuant :: String -> Term -> Typ -> Term -> String
showQuant s var typ term =
  (s++sp++showTerm var++" :: "++show typ++" . "++showTerm term)

outerShowTerm :: Term -> String
outerShowTerm (Const ("All",_) `App` Abs (v,ty,t)) = 
  outerShowQuant "!!" v ty t
outerShowTerm (Const ("op -->",_) `App` t1 `App` t2) =
  showTerm t1 ++ " ==> " ++ outerShowTerm1 t2
outerShowTerm t = showTerm t

outerShowTerm1 :: Term -> String
outerShowTerm1 (Const ("op -->",_) `App` t1 `App` t2) =
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
                             application of HasCASL ops, <=>, /\, \/, => -}

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

toPrecTree :: Term -> Tree PrecTerm
toPrecTree t =
-- trace ("[sT] "++st t++"\n") (
  case t of
    (Const("All",t1) `App` Abs(v,ty,t2)) -> 
       Node (isaAppPrec (Const ("QUANT", dummyT))) 
            [toPrecTree (Const("All",t1)), toPrecTree (Abs(v,ty,t2))]
    (Const("Ex",t1) `App` Abs(v,ty,t2)) -> 
       Node (isaAppPrec (Const ("QUANT", dummyT))) 
            [toPrecTree (Const("All",t1)), toPrecTree (Abs(v,ty,t2))]
    (Const("Ex1",t1) `App` Abs(v,ty,t2)) -> 
       Node (isaAppPrec (Const ("QUANT", dummyT))) 
            [toPrecTree (Const("All",t1)), toPrecTree (Abs(v,ty,t2))]    
    (t1 `App` t2) -> 
      case t1 of 
        Const ("op <=>", typ) `App` t3 
          -> Node (eqvPrec (Const ("op =",typ))) 
                  [toPrecTree t3, toPrecTree t2] 
        Const ("op =", typ) `App` t3 
          -> Node (eqPrec (Const ("op =",typ))) 
                  [toPrecTree t3, toPrecTree t2] 
        Const ("op &", typ) `App` t3 
          -> Node (andPrec (Const ("op &",typ))) 
                  [toPrecTree t3, toPrecTree t2] 
        Const ("op |", typ) `App` t3 
          -> Node (orPrec (Const ("op |",typ))) 
                  [toPrecTree t3, toPrecTree t2] 
        Const ("op -->", typ) `App` t3 
          -> Node (implPrec (Const ("op -->",typ)))
                  [toPrecTree t3, toPrecTree t2] 
        Const (c, typ) `App` t3 
          -> Node (appPrec (Const (c, typ))) 
                  [toPrecTree t3, toPrecTree t2] 
        _ -> Node (isaAppPrec (Const ("DUMMY", dummyT))) 
               [toPrecTree t1, toPrecTree t2] 
    _ -> Node (noPrec t) []
-- )

instance Show (Tree PrecTerm) where
  show = showPTree

showPTree :: Tree PrecTerm -> String
showPTree (Node (PrecTerm term _) []) = showTerm term
showPTree (Node (PrecTerm term pre) annos) = 
-- trace ("[showPTree] "++st term++"\n    Prec: "++show pre++"\n")
  let leftChild = head annos
      rightChild = last annos
   in
    case term of
      Const ("op =", _)   -> infixP pre "=" leftChild rightChild
      Const ("op &", _)   -> infixP pre "&" leftChild rightChild
      Const ("op |", _)   -> infixP pre "|" leftChild rightChild
      Const ("op -->", _) -> infixP pre "-->" leftChild rightChild
      Const ("DUMMY", _)  -> simpleInfix pre leftChild rightChild
      Const ("Pair", _)   -> pair leftChild rightChild
      Const ("QUANT",_)   -> quant leftChild rightChild
      Const (c, _)        -> prefixP pre c leftChild rightChild
      _                   -> showTerm term


{- Logical connectors: For readability and by habit they are written 
   at an infix position.
   If the precedence of one side is weaker (here: higher number) than the 
   connector's one it is bracketed. Otherwise not. 
-}
infixP :: Precedence -> String -> Tree PrecTerm -> Tree PrecTerm -> String
infixP pAdult stAdult leftChild rightChild 
    | (pAdult < prLeftCld) && (pAdult < prRightCld) = 
          rb++ stLeftCld ++lb++
              sp++ stAdult ++sp++
                   rb++ stRightCld ++lb
    | pAdult < prLeftCld = 
          rb++ stLeftCld ++lb++
              sp++ stAdult ++sp++
                   stRightCld
    | pAdult < prRightCld = 
          stLeftCld ++
              sp++ stAdult ++sp++
                   rb++ stRightCld ++lb
    | otherwise = stLeftCld ++
                      sp++ stAdult ++sp++
                           stRightCld
  where prLeftCld = pr leftChild
        prRightCld = pr rightChild
        stLeftCld = showPTree leftChild
        stRightCld = showPTree rightChild


{- Application of (HasCASL-)operations with two arguments. 
   Both arguments are usually bracketed, except single ones.
-}
prefixP :: Precedence -> String -> Tree PrecTerm -> Tree PrecTerm -> String
prefixP pAdult stAdult leftChild rightChild 
    | (pAdult <= prLeftCld) && (pAdult <= prRightCld) =
          stAdult ++
              sp++rb++ stLeftCld ++lb++
                  sp++rb++ stRightCld ++lb
    | pAdult <= prLeftCld = 
          stAdult ++
              sp++rb++ stLeftCld ++lb++
                  sp++ stRightCld
    | pAdult <= prRightCld = 
          stAdult ++
              sp++ stLeftCld ++
                  sp++rb++ stRightCld ++lb
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
simpleInfix :: Precedence -> Tree PrecTerm -> Tree PrecTerm -> String
simpleInfix pAdult leftChild rightChild 
    | (pAdult < prLeftCld) && (pAdult < prRightCld) = 
          rbb++ stLeftCld ++lb++
                sp++rb++ stRightCld ++lbb
    | pAdult < prLeftCld = 
          rbb++ stLeftCld ++lb++
                sp++ stRightCld ++lb
    | pAdult < prRightCld = 
          rb++ stLeftCld ++sp++
               rb++ stRightCld ++lbb
    | otherwise = rb++ stLeftCld ++sp++
                       stRightCld ++lb
  where prLeftCld = pr leftChild
        prRightCld = pr rightChild
        stLeftCld = showPTree leftChild
        stRightCld = showPTree rightChild


{- Quantification _in_ Formulas
-}
quant :: Tree PrecTerm -> Tree PrecTerm -> String
quant (Node (PrecTerm (Const("All",_)) _) []) (Node (PrecTerm (Abs(v,ty,t)) _) []) = 
  rb++showQuant "!"  v ty t++lb
quant (Node (PrecTerm (Const("Ex",_)) _) []) (Node (PrecTerm (Abs(v,ty,t)) _) [])  = 
  rb++showQuant "?"  v ty t++lb
quant (Node (PrecTerm (Const("Ex1",_)) _) []) (Node (PrecTerm (Abs(v,ty,t)) _) []) = 
  rb++showQuant "?!"  v ty t++lb
quant _ _ = error "[Isabelle.IsaPrint] Wrong quantification!?"


pr :: Tree PrecTerm -> Precedence
pr (Node (PrecTerm _ p) _) = p

-- Prints: (p1, p2)
pair :: Tree PrecTerm -> Tree PrecTerm -> String
pair leftChild rightChild = rb++showPTree leftChild++", "++
                                showPTree rightChild++lb

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
       ++ (concat $ map (("and "++) . showDataType) dts) ++ "\n"
    showDataType (t,op:ops) =
       show t ++ " = " ++ showOp op 
       ++ (concat $ map ((" | "++) . showOp) ops)
    showOp (opname,args) =
       opname ++ (concat $ map ((sp ++) . showArg) args)
    showArg arg = case arg of
                    TVar _ -> show arg
                    _      -> "\"" ++ show arg ++ "\""

instance PrettyPrint Sign where
    printText0 _ = ptext . show

instance PrintLaTeX Sign where
    printLatex0 = printText0



em :: String
em = ""

sp :: String
sp = " "

rb :: String
rb = "("

rbb :: String
rbb = rb++rb

lb :: String
lb = ")"

lbb :: String
lbb = lb++lb


bracketize :: Bool -> String -> String
bracketize b s = if b then rb++s++lb else s

isIsaChar :: Char -> Bool
isIsaChar c = (isAlphaNum c && isAscii c) || c `elem` "_'"

replaceChar1 :: Char -> String
replaceChar1 c | isIsaChar c = [c] 
               | otherwise = replaceChar c++"__"

transString :: String -> String
transString "" = "X"
transString (c:s) = 
   if isInf (c:s) then (concat $ map replaceChar1 (cut (c:s)))
   else ((if isAlpha c && isAscii c then [c] 
          else 'X':replaceChar1 c) ++ (concat $ map replaceChar1 s))

isInf :: String -> Bool
isInf s = has2Under s && has2Under (reverse s)

has2Under :: String -> Bool
has2Under (fs:sn:_) = fs == '_' && sn == '_'
has2Under _ = False

cut :: String -> String
cut = reverse . tail . tail . reverse . tail . tail

-- Replacement of special characters

replaceChar :: Char -> String
replaceChar '\t' = "_"
replaceChar '\n' = "_"
replaceChar '\r' = "_"
replaceChar ' ' = "_"
replaceChar '!' = "Exclam"
replaceChar '\"' = "_"
replaceChar '#' = "Sharp"
replaceChar '$' = "Dollar"
replaceChar '%' = "Percent"
replaceChar '&' = "Amp"
replaceChar '(' = "OBra"
replaceChar ')' = "CBra"
replaceChar '*' = "x"
replaceChar '+' = "Plus"
replaceChar ',' = "Comma"
replaceChar '-' = "Minus"
replaceChar '.' = "Dot"
replaceChar '/' = "Div"
replaceChar ':' = "Colon"
replaceChar ';' = "Semi"
replaceChar '<' = "Lt"
replaceChar '=' = "Eq"
replaceChar '>' = "Gt"
replaceChar '?' = "Q"
replaceChar '@' = "At"
replaceChar '[' = "_"
replaceChar '\\' = "Back"
replaceChar ']' = "_"
replaceChar '^' = "Hat"
replaceChar '`' = "'"
replaceChar '{' = "Cur"
replaceChar '|' = "Bar"
replaceChar '}' = "Ruc"
replaceChar '~' = "Tilde"
replaceChar '\128' = "A1"
replaceChar '\129' = "A2"
replaceChar '\130' = "A3"
replaceChar '\131' = "A4"
replaceChar '\132' = "A5"
replaceChar '\133' = "A6"
replaceChar '\134' = "AE"
replaceChar '\135' = "C"
replaceChar '\136' = "E1"
replaceChar '\137' = "E2"
replaceChar '\138' = "E3"
replaceChar '\139' = "E4"
replaceChar '\140' = "I1"
replaceChar '\141' = "I2"
replaceChar '\142' = "I3"
replaceChar '\143' = "I4"
replaceChar '\144' = "D1"
replaceChar '\145' = "N1"
replaceChar '\146' = "O1"
replaceChar '\147' = "O2"
replaceChar '\148' = "O3"
replaceChar '\149' = "O4"
replaceChar '\150' = "O5"
replaceChar '\151' = "x"
replaceChar '\152' = "O"
replaceChar '\153' = "U1"
replaceChar '\154' = "U2"
replaceChar '\155' = "U3"
replaceChar '\156' = "U4"
replaceChar '\157' = "Y"
replaceChar '\158' = "F"
replaceChar '\159' = "ss"
replaceChar '\160' = "_"
replaceChar '¡' = "SpanishExclam"
replaceChar '¢' = "c"
replaceChar '£' = "Lb"
replaceChar '¤' = "o"
replaceChar '¥' = "Yen"
replaceChar '¦' = "Bar1"
replaceChar '§' = "Paragraph"
replaceChar '¨' = "\""
replaceChar '©' = "Copyright"
replaceChar 'ª' = "a1"
replaceChar '«' = "\""
replaceChar '¬' = "not"
replaceChar '­' = "Minus1"
replaceChar '®' = "Regmark"
replaceChar '¯' = "_"
replaceChar '°' = "Degree"
replaceChar '±' = "Plusminus"
replaceChar '²' = "2"
replaceChar '³' = "3"
replaceChar '´' = "'"
replaceChar 'µ' = "Mu"
replaceChar '¶' = "q"
replaceChar '·' = "Dot"
replaceChar '¸' = "'"
replaceChar '¹' = "1"
replaceChar 'º' = "2"
replaceChar '»' = "\""
replaceChar '¼' = "Quarter"
replaceChar '½' = "Half"
replaceChar '¾' = "Threequarter"
replaceChar '¿' = "Q"
replaceChar 'À' = "A7"
replaceChar 'Á' = "A8"
replaceChar 'Â' = "A9"
replaceChar 'Ã' = "A10"
replaceChar 'Ä' = "A11"
replaceChar 'Å' = "A12"
replaceChar 'Æ' = "AE2"
replaceChar 'Ç' = "C2"
replaceChar 'È' = "E5"
replaceChar 'É' = "E6"
replaceChar 'Ê' = "E7"
replaceChar 'Ë' = "E8"
replaceChar 'Ì' = "I5"
replaceChar 'Í' = "I6"
replaceChar 'Î' = "I7"
replaceChar 'Ï' = "I8"
replaceChar 'Ð' = "D2"
replaceChar 'Ñ' = "N2"
replaceChar 'Ò' = "O6"
replaceChar 'Ó' = "O7"
replaceChar 'Ô' = "O8"
replaceChar 'Õ' = "O9"
replaceChar 'Ö' = "O10"
replaceChar '×' = "xx"
replaceChar 'Ø' = "011"
replaceChar 'Ù' = "U5"
replaceChar 'Ú' = "U6"
replaceChar 'Û' = "U7"
replaceChar 'Ü' = "U8"
replaceChar 'Ý' = "Y"
replaceChar 'Þ' = "F"
replaceChar 'ß' = "ss"
replaceChar 'à' = "a2"
replaceChar 'á' = "a3"
replaceChar 'â' = "a4"
replaceChar 'ã' = "a5"
replaceChar 'ä' = "a6"
replaceChar 'å' = "a7"
replaceChar 'æ' = "ae"
replaceChar 'ç' = "c"
replaceChar 'è' = "e1"
replaceChar 'é' = "e2"
replaceChar 'ê' = "e3"
replaceChar 'ë' = "e4"
replaceChar 'ì' = "i1"
replaceChar 'í' = "i2"
replaceChar 'î' = "i3"
replaceChar 'ï' = "i4"
replaceChar 'ð' = "d"
replaceChar 'ñ' = "n"
replaceChar 'ò' = "o1"
replaceChar 'ó' = "o2"
replaceChar 'ô' = "o3"
replaceChar 'õ' = "o4"
replaceChar 'ö' = "o5"
replaceChar '÷' = "Div1"
replaceChar 'ø' = "o6"
replaceChar 'ù' = "u1"
replaceChar 'ú' = "u2"
replaceChar 'û' = "u3"
replaceChar 'ü' = "u4"
replaceChar 'ý' = "y5"
replaceChar 'þ' = "f"
replaceChar 'ÿ' = "y"
replaceChar  _ = "_"


