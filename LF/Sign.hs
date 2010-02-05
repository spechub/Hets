{- |
Module      :  $Header$
Description :  Definition of signatures for the Edinburgh 
               Logical Framework
Copyright   :  (c) Kristina Sojakova, DFKI Bremen 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  k.sojakova@jacobs-university.de
Stability   :  experimental
Portability :  portable
-}

module LF.Sign where

import Common.Id
import Common.Doc
import Common.DocUtils
import qualified Data.Set as Set
import qualified Data.Map as Map

type NAME = Token
type DECL = ([NAME],EXP)

-- LF expressions
data EXP = Type
         | Var NAME
         | Appl EXP [EXP]
         | Func [EXP] EXP
         | Pi [DECL] EXP
         | Lamb [DECL] EXP
           deriving (Show, Ord)

-- signatures for LF
data Sign = Sign [DECL]
            deriving (Show, Ord, Eq)

-- the empty signature
emptySig :: Sign
emptySig = Sign []

-- adds a symbol declaration to the signature
addSymbolDecl :: DECL -> Sign -> Sign
addSymbolDecl d (Sign ds) = Sign (ds ++ [d])

-- get the set of defined symbols
getSymbols :: Sign -> Set.Set NAME
getSymbols (Sign ds) = Set.fromList $ concatMap fst ds

-- pretty printing
instance Pretty Sign where
   pretty = printSig
instance Pretty EXP where
   pretty = printExp

printSig :: Sign -> Doc
printSig (Sign []) = text "EmptySig"
printSig (Sign ds) = vcat $ map printDecl ds

printDecl :: DECL -> Doc
printDecl (ns,e) = printNames ns <+> colon <+> pretty e

printDecls :: [DECL] -> Doc
printDecls xs = fsep $ punctuate comma $ map printDecl xs

printNames :: [NAME] -> Doc
printNames = ppWithCommas

printExp :: EXP -> Doc
printExp Type = text "type"
printExp (Var n) = pretty n
printExp (Appl e es) = 
  let f = printExpWithPrec (precAppl + 1) e
      as = map (printExpWithPrec precAppl) es
      in fsep (f:as)
printExp (Func es e) = 
  let as = map (printExpWithPrec precFunc) es
      val = printExpWithPrec (precFunc + 1) e
      in fsep $ prepPunctuate (text "-> ") (as ++ [val])
printExp (Pi ds e) = text "{" <> printDecls ds <> text "{" <> pretty e
printExp (Lamb ds e) = text "[" <> printDecls ds <> text "]" <> pretty e

printExpWithPrec :: Int -> EXP -> Doc
printExpWithPrec i e = 
  if prec e >= i
     then parens $ printExp e
     else printExp e

prec :: EXP -> Int
prec Type = 0
prec Var {} = 0
prec Appl {} = 1
prec Func {} = 2
prec Pi {} = 3
prec Lamb {} = 3 

precFunc, precAppl :: Int
precFunc = 2
precAppl = 1

{- converts the expression into a form where each construct takes
   exactly one argument -}
recForm :: EXP -> EXP
recForm Type = Type
recForm (Var n) = Var n
recForm (Appl f []) = recForm f
recForm (Appl f as) = Appl (recForm $ Appl f $ init as) $ [recForm $ last as]
recForm (Func [] a) = recForm a
recForm (Func (t:ts) a) = Func [recForm t] $ recForm $ Func ts a
recForm (Pi [] t) = recForm t
recForm (Pi (([],_):ds) a) = recForm $ Pi ds a
recForm (Pi (((n:ns),t):ds) a) =
  Pi [([n],recForm t)] $ recForm $ Pi ((ns,t):ds) a
recForm (Lamb [] t) = recForm t
recForm (Lamb (([],_):ds) a) = recForm $ Lamb ds a
recForm (Lamb (((n:ns),t):ds) a) =
  Lamb [([n],recForm t)] $ recForm $ Lamb ((ns,t):ds) a

{- modifies the given name until it is different from each of the names
   in the input set -}
getNewName :: NAME -> Set.Set NAME -> NAME
getNewName var names = getNewNameH var names (tokStr var) 0

getNewNameH :: NAME -> Set.Set NAME -> String -> Int -> Token
getNewNameH var names root i =
  if (Set.notMember var names)
     then var
     else let newVar = Token (root ++ (show i)) nullRange
              in getNewNameH newVar names root $ i+1

-- returns a set of unbound identifiers used within an expression
getFreeVars :: EXP -> Set.Set NAME
getFreeVars e = getFreeVarsH $ recForm e

getFreeVarsH :: EXP -> Set.Set NAME
getFreeVarsH Type = Set.empty
getFreeVarsH (Var x) = Set.singleton x
getFreeVarsH (Appl f [a]) =
  Set.union (getFreeVarsH f) (getFreeVarsH a)
getFreeVarsH (Func [t] v) =  
  Set.union (getFreeVarsH t) (getFreeVarsH v)
getFreeVarsH (Pi [([n],t)] a) =
  Set.delete n $ Set.union (getFreeVarsH t) (getFreeVarsH a)
getFreeVarsH (Lamb [([n],t)] a) =
  Set.delete n $ Set.union (getFreeVarsH t) (getFreeVarsH a)
getFreeVarsH _ = Set.empty

{- substitutions and renamings: the first argument specifies the desired
   term/identifier substitutions and the second the set of identifiers which
   cannot be used as new variable names -}
translate :: Map.Map NAME EXP -> Set.Set NAME -> EXP -> EXP
translate m s e = 
  let s1 = Set.unions $ map getFreeVars $ Map.elems m
      in translateH m (Set.union s s1) (recForm e)

translateH :: Map.Map NAME EXP -> Set.Set NAME -> EXP -> EXP
translateH _ _ Type = Type
translateH m _ (Var n) = Map.findWithDefault (Var n) n m
translateH m s (Appl f [a]) = Appl (translate m s f) [translate m s a]
translateH m s (Func ts t) = Func (map (translate m s) ts) (translate m s t)
translateH m s (Pi [([x],t)] a) = 
  let t1 = translate m s t
      x1 = getNewName x s
      a1 = translate (Map.insert x (Var x1) m) (Set.insert x1 s) a
      in Pi [([x1],t1)] a1
translateH m s (Lamb [([x],t)] a) = 
  let t1 = translate m s t
      x1 = getNewName x s
      a1 = translate (Map.insert x (Var x1) m) (Set.insert x1 s) a
      in Lamb [([x1],t1)] a1
translateH _ _ t = t

-- equality
instance Eq EXP where
    e1 == e2 = eq (recForm e1) (recForm e2)

eq :: EXP -> EXP -> Bool
eq Type Type = True
eq (Var x1) (Var x2) = x1 == x2
eq (Appl f1 [a1]) (Appl f2 [a2]) = and [f1 == f2, a1 == a2]
eq (Func [t1] s1) (Func [t2] s2) = and [t1 == t2, s1 == s2]
eq (Pi [([n1],t1)] s1) (Pi [([n2],t2)] s2) =
  let syms1 = Set.delete n1 $ getFreeVars s1
      syms2 = Set.delete n2 $ getFreeVars s2
      v = getNewName n1 $ Set.union syms1 syms2
      type1 = translate (Map.singleton n1 (Var v)) syms1 s1
      type2 = translate (Map.singleton n2 (Var v)) syms2 s2
      in and [t1 == t2, type1 == type2]
eq _ _ = False
