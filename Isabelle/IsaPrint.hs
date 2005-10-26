{- |
Module      :  $Header$
Copyright   :  (c) University of Cambridge, Cambridge, England
               adaption (c) Till Mossakowski, Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
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
import Common.Lib.Pretty
import Common.PrettyPrint
import Common.PPUtils
import qualified Common.Lib.Map as Map

import Data.Char
import Data.List
------------------- Printing functions -------------------

showBaseSig :: BaseSig -> String
showBaseSig = reverse . drop 4 . reverse . show

instance PrettyPrint BaseSig where
     printText0 _ s = text $ showBaseSig s

instance PrettyPrint IsaClass where
     printText0 _ (IsaClass c) = parens $ text c

instance PrintLaTeX Sentence where
  printLatex0 = printText0

{- test for sentence translation -}
instance PrettyPrint Sentence where
      printText0 _ = text . showTerm . senTerm

instance PrettyPrint Typ where
  printText0 _ = printTyp Null

printClass :: IsaClass -> Doc
printClass (IsaClass x) = text x

printSort :: Sort -> Doc
printSort l = case l of 
    [c] -> printClass c 
    _ -> braces . hsep . punctuate comma $ map printClass l

data SynFlag = Unquoted | Quoted | Null 

printTyp :: SynFlag -> Typ -> Doc
printTyp a = fst . printType a

printType :: SynFlag -> Typ -> (Doc, Int)
printType a t = case t of 
 (TFree v s) -> (let d = text $ if isPrefixOf "\'" v || isPrefixOf "?\'" v 
                                then v  else '\'' : v 
                 in if null s then d else case a of
   Unquoted -> d <> text "::" <> printSort s
   Quoted -> d <> text "::" <> doubleQuotes (printSort s)
   Null -> d, 1000)
 (TVar iv s) -> printType a $ TFree ("?\'" ++ unindexed iv) s
 (Type name _ args) -> case args of 
   [t1, t2] | elem name [prodS, sProdS, funS, cFunS, sSumS] -> 
       printTypeOp a name t1 t2
   _  -> ((case args of
           [] -> empty
           [arg] -> let (d, i) = printType a arg in
                      if i < 1000 then parens d else d
           _ -> parens $ hsep $ punctuate comma $ 
                       map (fst . printType a) args)
          <+> text name, 1000)

printTypeOp :: SynFlag -> TName -> Typ -> Typ -> (Doc, Int)
printTypeOp x name r1 r2 = 
    let (d1, i1) = printType x r1
        (d2, i2) = printType x r2
        (l, r) = Map.findWithDefault (0 :: Int, 0 :: Int) 
                    name $ Map.fromList 
                    [ (funS, (1,0))
                    , (cFunS, (1,0))
                    , (sSumS, (11, 10))
                    , (prodS, (21, 20))
                    , (sProdS, (21, 20))
                    ]
        d3 = if i1 < l then parens d1 else d1
        d4 = if i2 < r then parens d2 else d2
    in (d3 <+> text name <+> d4, r)

instance PrettyPrint TypeSig where
  printText0 ga tysig = printText0 ga $ arities tysig

instance PrettyPrint Term where
  printText0 _ = text . showTerm -- outerShowTerm   
  -- back to showTerm, because meta !! causes problems with show ?thesis

typedVars2st :: (a -> String) -> (b -> String) -> [(a,b)] -> String
typedVars2st f g ls = concat [" (" ++ (f x) ++ "::" ++ (g y) ++ ")" 
                              | (x,y) <- ls]

showTypedVars :: [(Term,Typ)] -> String
showTypedVars = typedVars2st showTerm (show . parens . printTyp Unquoted)

showQuantStr :: String -> String
showQuantStr s | s == allS = "!"
               | s == exS  = "?"
               | s == ex1S = "?!"
               | otherwise = error "IsaPrint.showQuantStr"

showTerm :: Term -> String
showTerm (Const (VName {new=c}) _) = c
showTerm (Free  (VName {new=v}) _) = v

showTerm (Tuplex ls c) = case c of
   IsCont -> "< " ++ (showTupleArgs ls) ++ ">" 
 -- the extra space takes care of a minor Isabelle bug
   NotCont -> "(" ++ (showTupleArgs ls) ++ ")" 
 where 
   showTupleArgs xs = case xs of 
     [] -> []
     [a] -> showTerm a
     a:as -> case a of
      (Free _ t) -> showTerm a ++ "::" ++ show (printTyp Null t) 
                    ++ "," ++ showTupleArgs as
      _ -> showTerm a ++ "," ++ showTupleArgs as

showTerm (Abs v y t l) 
  | y == noType = lb ++ (case l of 
    NotCont -> "%"
    IsCont -> "LAM ") ++ showTerm v ++ ". " ++ showTerm t ++ rb
  | True = lb ++ (case l of 
    NotCont -> "%"
    IsCont -> "LAM ") ++ (case v of 
      (Free _ w) -> showTerm v ++ "::" 
       ++ show (printTyp Null w)
      _ -> showTerm v) ++ ". " ++ showTerm t ++ rb

-- showTerm (App (Const q _) (Abs v ty t _) _) | q `elem` [allS, exS, ex1S] =
--   showQuant (showQuantStr q) v ty t
-- showTerm t@(Const c _) = showPTree (toPrecTree t) 
showTerm (Paren t) = showTerm t 
showTerm (Fix t) = lb++"fix"++"$"++(showTerm t)++rb
showTerm t@(App _ _ NotCont) = showPTree (toPrecTree t)
showTerm t@(MixfixApp _ _ NotCont) = showPTree (toPrecTree t)
showTerm (App t1 t2 IsCont) = lb++(showTerm t1)++"$"++(showTerm t2)++rb
showTerm Bottom = "UU"

showTerm (IsaEq t1 t2) = lb ++ (showTerm t1) ++ sp ++ "==" 
                         ++ sp ++ (showTerm t2) ++ rb
showTerm (Case term alts) =
  let sAlts = map showCaseAlt alts
  in lb ++ "case" ++ sp ++ showTerm term ++ sp ++ "of" 
         ++ sp ++ head sAlts
         ++ concat (map ((++) ("\n" ++ sp ++ sp ++ sp ++ "|" ++ sp)) 
                                                    (tail sAlts)) ++ rb

showTerm (If t1 t2 t3 c) = case c of
  NotCont -> 
    lb ++ "if" ++ sp ++ showTerm t1 ++ sp ++ "then" ++ sp 
           ++ showTerm t2 ++ sp ++ "else" ++ sp ++ showTerm t3 ++ rb
  IsCont -> 
    lb ++ "If" ++ sp ++ showTerm t1 ++ sp ++ "then" ++ sp 
           ++ showTerm t2 ++ sp ++ "else" ++ sp ++ showTerm t3 ++ sp ++ "fi" ++ rb

showTerm (Let pts t) = lb ++ "let" ++ sp ++ showPat False (head pts) 
                                ++ concat (map (showPat True) (tail pts))
                                ++ sp ++ "in" ++ sp ++ showTerm t ++ rb
showTerm t = error $ "Isa.showTerm: " ++ show t 

showPat :: Bool -> (Term, Term) -> String
showPat b (pat, term) = 
  let s = sp ++ showTerm pat ++ sp ++ "=" ++ sp ++ showTerm term
  in-- showTerm (Const c _) = c

    if b then ";" ++ s
      else s

showCaseAlt :: (Term, Term) -> String
showCaseAlt (pat, term) =
  showPattern pat ++ sp ++ "=>" ++ sp ++ showTerm term

showPattern :: Term -> String
showPattern t = showTerm t

showQuant :: String -> Term -> Typ -> Term -> String
showQuant s var typ term =
   s++sp++ showTerm var ++" :: "++ show (printTyp Null typ) ++ " . "
        ++ showTerm term

outerShowTerm :: Term -> String
outerShowTerm (App (Const (VName {new=q}) _) (Abs v ty t _) _) | q == allS = 
  outerShowQuant "!!" v ty t 
outerShowTerm (App (App (Const (VName {new=o}) _) t1 _) t2 _) | o == impl = 
  showTerm t1 ++ " ==> " ++ outerShowTerm1 t2
outerShowTerm t = showTerm t

outerShowTerm1 :: Term -> String
outerShowTerm1 t@(App (App (Const (VName {new=o}) _) _ _) _ _) | o == impl = outerShowTerm t
outerShowTerm1 t = showTerm t

outerShowQuant :: String -> Term -> Typ -> Term -> String
outerShowQuant s var typ term =
  s++sp++ showTerm var ++" :: "++ show (printTyp Null typ) ++ " . "
   ++ outerShowTerm term 


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

capplPrec :: Term -> PrecTerm
capplPrec t = PrecTerm t 999

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
--           | s == cappl = capplPrec
           | otherwise = appPrec

toPrecTree :: Term -> PrecTermTree
toPrecTree trm =
  case trm of
    App c1@(Const vn _) a2@(Abs _ _ _ _) _ 
        | new vn `elem` [allS, exS, ex1S] -> 
            Node (isaAppPrec $ conDouble quantS) [toPrecTree c1, toPrecTree a2]
    App (App t@(Const vn _) t3 NotCont) t2 NotCont ->
        Node (binFunct (new vn) t) [toPrecTree t3, toPrecTree t2]
    App t1 t2 NotCont -> Node (isaAppPrec $ conDouble dummyS) 
                   [toPrecTree t1, toPrecTree t2] 
    MixfixApp t@(Const (VName {new=n,orig=o}) v) (t2:t3) NotCont ->
	if length t3 == 1 then
	   Node (binFunct n t) [toPrecTree t2, toPrecTree (head t3)]
	else
	   let (_, tl) = getParts ' ' $ tail $ tail o in
		Node (binFunct n t) 
                         [toPrecTree t2, 
			  toPrecTree $ MixfixApp 
                          (Const (VName {new=n,orig=tl}) v) t3 NotCont]
    _ -> Node (noPrec trm) []


twoUs :: Char -> Char -> Bool
twoUs c x = c == '_' && x == '_'

getParts :: Char -> String -> (String, String)
getParts _ "" = ("", "")
getParts c (x : xs) = 
    if twoUs c x then ("" , c : x : xs)
    else let (hd, tl) = getParts x xs in (x : hd, tl)

hasDoubleULines::Char->String->Bool
hasDoubleULines _ [] = False
hasDoubleULines c (x : xs) = 
    twoUs c x || hasDoubleULines x xs

rmDoubleULines:: Char -> String -> String
rmDoubleULines _ [] = []
rmDoubleULines '_' ('_':xs) = rmDoubleULines '_' xs
rmDoubleULines c (x:xs) = if twoUs c x then rmDoubleULines '_' xs
                          else x : rmDoubleULines x xs

data Assoc = LeftAs | NoAs | RightAs

showPTree :: PrecTermTree -> String
showPTree (Node (PrecTerm term _) []) = showTerm term
showPTree (Node (PrecTerm term pre) annos) =  
  let [leftChild, rightChild] = annos
   in case term of {
         Const (VName {orig=c}) _
	       | c == eq -> infixP pre "=" LeftAs leftChild rightChild
	       | c == "op +" -> infixP pre "+" LeftAs leftChild rightChild
	       | c == "op -" -> infixP pre "-" LeftAs leftChild rightChild
	       | c == "op *" -> infixP pre "*" LeftAs leftChild rightChild
	       | c == "(op ##)" -> infixP pre "##" RightAs leftChild rightChild
--	        | c1 == cappl -> infixP pre "$" LeftAs leftChild rightChild
	       | c `elem` [conj, disj, impl] ->
                   infixP pre (drop 3 c) RightAs leftChild rightChild
	       | c == dummyS  -> simpleInfix pre leftChild rightChild
	       | c == isaPair -> pair leftChild rightChild
	       | c == quantS  -> quant leftChild rightChild
{-	       | hasDoubleULines ' ' c -> 
	               infixP pre 
			      (takeWhile (/='_') (dropWhile (=='_') c)) 
			      RightAs leftChild rightChild
-- this does not work for __::__-->__ in Graph.casl
-} 
	       | otherwise    -> prefixP pre c leftChild rightChild;
      _ -> showTerm term}

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
quant (Node (PrecTerm (Const (VName {new=q}) _) _) []) 
          (Node (PrecTerm (Abs v ty t _) _) []) = 
              lb++showQuant (showQuantStr q) v ty t++rb
quant _ _ = error "[Isabelle.IsaPrint] Wrong quantification!?"

listEnum :: [a] -> [(a,Int)]
listEnum l = case l of
 [] -> []
 a:as -> (a,length (a:as)):(listEnum as)

pr :: PrecTermTree -> Precedence
pr (Node (PrecTerm _ p) _) = p

-- Prints: (p1, p2)
pair :: PrecTermTree -> PrecTermTree -> String
pair leftChild rightChild = lb++showPTree leftChild++", "++
                                showPTree rightChild++rb

-- instances for Classrel and Arities, in alternative to TSig
instance PrettyPrint Classrel where
 printText0 _ s = Map.foldWithKey showTyconClass empty s 
   where 
   showTyconClass t cl rest = case cl of 
     Nothing -> rest
     Just x -> text "axclass" <+> text (classId t) <+> text "<" <+> 
       (if null x  then text "pcpo" else printSort x) $$ rest

instance PrettyPrint Arities where
 printText0 _ s = if Map.null s then empty  
      else Map.foldWithKey showInstances empty s 
   where 
   showInstances t cl rest =
     (vcat $ map (showInstance t) cl) $$ rest
   showInstance t xs = 
     (text "instance") <+> (text $ show t) <+> text "::" 
                           <+> showInstArgs (snd xs)  
        <+> text (classId $ fst xs) $$ text "by intro_classes"
   showInstArgs ys = case ys of 
     [] -> empty
     _ : _ -> parens $ showInstArgsR ys
   showInstArgsR ys = hsep $ punctuate comma $ map
                (doubleQuotes . printSort . snd) ys

printTypeDecls :: Sign -> Doc
printTypeDecls sig =  
    Map.foldWithKey (showTycon sig) empty $ arities $ tsig sig

showTycon :: Sign -> TName -> [(a, [b])] -> Doc -> Doc
showTycon sig t arity' rest = 
              let arity = if null arity' then
                          error "IsaPrint.printText0 (TypeSig)" 
                                else length (snd $ head arity') in 
            if dtyp sig t then empty else  
            text "typedecl" <+> 
            (if arity > 0 
             then parens $ hsep (map (text . ("'a"++) . show) [1..arity])
             else empty) <+> text t $$ rest 

dtyp :: Sign -> TName -> Bool
dtyp sig t = elem t $ 
         concat [map (typeId . fst) x | x <- domainTab sig ++ dataTypeTab sig]

instance PrettyPrint Sign where
  printText0 ga sig = printText0 ga
    (baseSig sig) <> colon $++$
    printTypeDecls sig $++$
    printText0 ga (classrel $ tsig sig) $++$
    showDataTypeDefs (dataTypeTab sig) $++$
    showDomainDefs (domainTab sig) $++$
    showsConstTab (constTab sig) $++$     
    (if showLemmas sig then showCaseLemmata (dataTypeTab sig) else empty) $++$
                                   -- this may prints an "o"
    printText0 ga (tsig sig) 
    where

    showsConstTab tab =  
     if Map.null tab then empty
      else text "consts" $$ Map.foldWithKey showConst empty tab

    showConst vn t rest =
	      text (new vn) <+> text "::" <+> 
               doubleQuotes (printTyp Unquoted t)
               -- <+> text(showAlt c2) 
	       $$ rest
	   
    --show only this alternative-versions where __ is in the string
    --because only this ones change something
    --maybe it's better to find and remove __ in one step
    showAlt::String->String
    showAlt str = "(\""++(rmDoubleULines ' ' str)++"\")"
    --if (hasDoubleULines ' ' str) then "(\""++(rmDoubleULines ' ' str)++"\")" else ""
		  			 							  
    showDataTypeDefs dtDefs = vcat $ map showDataTypeDef dtDefs
    showDataTypeDef [] = empty
    showDataTypeDef (dt:dts) = 
       (text "datatype") <+> (showDataType dt)
       <+> (vcat $ map ((text ("\n"++"and") <+>) . showDataType) dts) <> text "\n"
    showDataType (_,[]) = error "IsaPrint.showDataType"
    showDataType (t,op:ops) =
       printTyp Quoted t <+> text "=" <+> (showOp op) 
       <+> (hsep $ map ((text "|" <+>) . showOp) ops)
    showDomainDefs dtDefs = vcat $ map showDomainDef dtDefs
    showDomainDef [] = empty
    showDomainDef (dt:dts) =
       (text "domain") <+> (showDomain dt) 
       <+> (vcat $ map ((text ("\n"++"and") <+>) . showDomain) dts) <> text "\n"
    showDomain (_,[]) = error "IsaPrint.showDomain"
    showDomain (t,op:ops) =
       printTyp Quoted t <+> text "=" <+> (showDOp op)
       <+> (hsep $ map ((text "|" <+>) . showDOp) ops)
    showDOp ((VName {new=opname}),args) =
       text opname <+> hsep [parens (text (opname ++ "_" ++ show n)
           <> text "::" <+> showOpArg x) | (x,n) <- listEnum args]
    showOp ((VName {new=opname}),args) =
       text opname <+> hsep (map showOpArg args)
    showOpArg arg = case arg of
                    TFree _ _ -> printTyp Null arg
                    _         -> doubleQuotes $ printTyp Null arg
    showCaseLemmata dtDefs = text (concat $ map showCaseLemmata1 dtDefs)
    showCaseLemmata1 dts = concat $ map showCaseLemma dts
    showCaseLemma (_, []) = ""
    showCaseLemma (tyCons, (c:cons)) = 
      let cs = "case caseVar of" ++ sp
          sc b = showCons b c ++ (concat $ map (("   | " ++) 
                                                . (showCons b)) cons)
          clSome = sc True
          cl = sc False
          showCons b ((VName {new=cName}), args) =
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
          showArg (TVar v s) = showArg (TFree (unindexed v) s)
          showArg (Type [] _ _) = "varName"
          showArg (Type m@(n:ns) _ s) = 
            if m == "typeAppl" || m == "fun" || m == "*"  then concat $ map showArg s
              else [toLower n] ++ ns
          showName (TFree v _) = v
          showName (TVar v _) = unindexed v
          showName (Type n _ _) = n
          proof = "apply (case_tac caseVar)\napply (auto)\ndone\n"
      in
        "lemma" ++ sp ++ "case_" ++ showName tyCons ++ "_SomeProm" ++ sp
                ++ "[simp]:\"" ++ sp ++ lb ++ cs ++ clSome ++ rb ++ sp
                ++ "=\n" ++ "Some" ++ sp ++ lb ++ cs ++ cl ++ rb ++ "\"\n"
                ++ proof

quote_underscores :: String -> String
quote_underscores [] = []
quote_underscores ('_':'_':rest) = '_':quote_underscores rest
quote_underscores ('_':rest) = '\'':'_':quote_underscores rest
quote_underscores (c:rest) = c:quote_underscores rest


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
