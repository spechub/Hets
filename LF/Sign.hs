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

module LF.Sign
       ( Var
       , NAME
       , MODULE
       , BASE
       , Symbol (..)
       , EXP (..)
       , DECL
       , DEF (..)
       , Sign (..)
       , emptySig
       , addDef
       , getAllSyms
       , getDeclaredSyms
       , getDefinedSyms
       , getLocalSyms
       , isConstant
       , isDeclaredSym
       , isDefinedSym
       , isLocalSym
       , getSymType
       , getSymValue
       , recForm
       , printSymbol
       , printExp
       ) where

import Common.Doc
import Common.DocUtils
import Data.Maybe
import qualified Data.List as List
import qualified Data.Set as Set
import qualified Data.Map as Map

type Var = String
type NAME = String
type MODULE = String
type BASE = String

data Symbol = Symbol
            { symBase :: BASE
            , symModule :: MODULE
            , symName :: NAME
            } deriving (Eq, Ord, Show)

data EXP = Type
         | Var Var
         | Const Symbol
         | Appl EXP [EXP]
         | Func [EXP] EXP
         | Pi [DECL] EXP
         | Lamb [DECL] EXP
           deriving (Ord, Show)

type DECL = (Var,EXP)

data DEF = Def
         { getSym :: Symbol
         , getType :: EXP
         , getValue :: Maybe EXP
         } deriving (Eq, Ord, Show)

data Sign = Sign
          { sigBase :: BASE
          , sigModule :: MODULE
          , getDefs :: [DEF]
          }
          deriving (Show, Ord, Eq)

emptySig :: Sign
emptySig = Sign "" "" []

addDef :: DEF -> Sign -> Sign
addDef d (Sign b m ds) = Sign b m $ ds ++ [d]

-- get the set of all symbols
getAllSyms :: Sign -> Set.Set Symbol
getAllSyms (Sign _ _ ds) = Set.fromList $ map getSym ds

-- checks if the symbol is defined or declared in the signature
isConstant :: Symbol -> Sign -> Bool
isConstant s sig = Set.member s $ getAllSyms sig

-- get the set of declared symbols
getDeclaredSyms :: Sign -> Set.Set Symbol
getDeclaredSyms (Sign _ _ ds) =
  Set.fromList $ map getSym $ filter (\ d -> isNothing $ getValue d) ds

-- checks if the symbol is declared in the signature
isDeclaredSym :: Symbol -> Sign -> Bool
isDeclaredSym s sig = Set.member s $ getDeclaredSyms sig

-- get the set of declared symbols
getDefinedSyms :: Sign -> Set.Set Symbol
getDefinedSyms (Sign _ _ ds) =
  Set.fromList $ map getSym $ filter (\ d -> isJust $ getValue d) ds

-- checks if the symbol is defined in the signature
isDefinedSym :: Symbol -> Sign -> Bool
isDefinedSym s sig = Set.member s $ getDefinedSyms sig

-- get the set of symbols not included from other signatures
getLocalSyms :: Sign -> Set.Set Symbol
getLocalSyms sig = Set.filter (\ s -> isLocalSym s sig) $ getAllSyms sig

-- checks if the symbol is local to the signature
isLocalSym :: Symbol -> Sign -> Bool
isLocalSym s sig =
  and [sigBase sig == symBase s, sigModule sig == symModule s]

-- returns the type/kind for the given symbol
getSymType :: Symbol -> Sign -> Maybe EXP
getSymType sym sig =
  let res = List.find (\ d -> getSym d == sym) $ getDefs sig
      in case res of
              Nothing -> Nothing
              Just (Def _ t _) -> Just t

-- returns the value for the given symbol, if it exists
getSymValue :: Symbol -> Sign -> Maybe EXP
getSymValue sym sig =
  let res = List.find (\ d -> getSym d == sym) $ getDefs sig
      in case res of
              Nothing -> Nothing
              Just (Def _ _ v) -> v

-- pretty printing
instance Pretty Sign where
   pretty = printSig

printSig :: Sign -> Doc
printSig sig = vcat $ map (printDef sig) $ getDefs sig

printDef :: Sign -> DEF -> Doc
printDef sig (Def s t v) =
  fsep
   [ printSymbol sig s
   , text "::" <+> printExp sig t
   , case v of
          Nothing -> empty
          Just val -> text "=" <+> printExp sig val
   ]

printSymbol :: Sign -> Symbol -> Doc
printSymbol sig s =
  if (isLocalSym s sig)
     then text $ symName s
     else text (symModule s) <> dot <> text (symName s)

printExp :: Sign -> EXP -> Doc
printExp _ Type = text "type"
printExp sig (Const s) = printSymbol sig s
printExp _ (Var n) = text n
printExp sig (Appl e es) =
  let f = printExpWithPrec sig (precAppl + 1) e
      as = map (printExpWithPrec sig precAppl) es
      in hsep (f:as)
printExp sig (Func es e) =
  let as = map (printExpWithPrec sig precFunc) es
      val = printExpWithPrec sig (precFunc + 1) e
      in hsep $ punctuate (text "-> ") (as ++ [val])
printExp sig (Pi ds e) = sep [text "{" <> printDecls sig ds <> text "}", printExp sig e]
printExp sig (Lamb ds e) = sep [text "[" <> printDecls sig ds <> text "]", printExp sig e]

printExpWithPrec :: Sign -> Int -> EXP -> Doc
printExpWithPrec sig i e =
  if prec e >= i
     then parens $ printExp sig e
     else printExp sig e

prec :: EXP -> Int
prec Type = 0
prec Const {} = 0
prec Var {} = 0
prec Appl {} = 1
prec Func {} = 2
prec Pi {} = 3
prec Lamb {} = 3

precFunc, precAppl :: Int
precFunc = 2
precAppl = 1

printDecls :: Sign -> [DECL] -> Doc
printDecls sig xs = hsep $ punctuate comma $ map (printDecl sig) xs

printDecl :: Sign -> DECL -> Doc
printDecl sig (n,e) = text n <+> colon <+> printExp sig e

{- converts the expression into a form where each construct takes
   exactly one argument -}
recForm :: EXP -> EXP
recForm (Appl f []) = recForm f
recForm (Appl f as) = Appl (recForm $ Appl f $ init as) $ [recForm $ last as]
recForm (Func [] a) = recForm a
recForm (Func (t:ts) a) = Func [recForm t] $ recForm $ Func ts a
recForm (Pi [] t) = recForm t
recForm (Pi ((n,t):ds) a) =
  Pi [(n,recForm t)] $ recForm $ Pi ds a
recForm (Lamb [] t) = recForm t
recForm (Lamb ((n,t):ds) a) =
  Lamb [(n,recForm t)] $ recForm $ Lamb ds a
recForm t = t

{- modifies the given name until it is different from each of the names
   in the input set -}
getNewName :: Var -> Set.Set Var -> Var
getNewName var names = getNewNameH var names var 0

getNewNameH :: Var -> Set.Set Var -> Var -> Int -> Var
getNewNameH var names root i =
  if (Set.notMember var names)
     then var
     else let newVar = root ++ (show i)
              in getNewNameH newVar names root $ i+1

-- returns a set of free Variables used within an expression
getFreeVars :: EXP -> Set.Set Var
getFreeVars e = getFreeVarsH $ recForm e

getFreeVarsH :: EXP -> Set.Set Var
getFreeVarsH Type = Set.empty
getFreeVarsH (Const _) = Set.empty
getFreeVarsH (Var x) = Set.singleton x
getFreeVarsH (Appl f [a]) =
  Set.union (getFreeVarsH f) (getFreeVarsH a)
getFreeVarsH (Func [t] v) =
  Set.union (getFreeVarsH t) (getFreeVarsH v)
getFreeVarsH (Pi [(n,t)] a) =
  Set.delete n $ Set.union (getFreeVarsH t) (getFreeVarsH a)
getFreeVarsH (Lamb [(n,t)] a) =
  Set.delete n $ Set.union (getFreeVarsH t) (getFreeVarsH a)
getFreeVarsH _ = Set.empty

{- Variable renamings:
   - the first argument specifies the desired Variable renamings
   - the second argument specifies the set of Variables which cannot
     be used as new Variable names -}
rename :: Map.Map Var Var -> Set.Set Var -> EXP -> EXP
rename m s e = renameH m s (recForm e)

renameH :: Map.Map Var Var -> Set.Set Var -> EXP -> EXP
renameH _ _ Type = Type
renameH _ _ (Const n) = Const n
renameH m _ (Var n) = Var $ Map.findWithDefault n n m
renameH m s (Appl f [a]) = Appl (rename m s f) [rename m s a]
renameH m s (Func [t] u) = Func [rename m s t] (rename m s u)
renameH m s (Pi [(x,t)] a) =
  let t1 = rename m s t
      x1 = getNewName x s
      a1 = rename (Map.insert x x1 m) (Set.insert x1 s) a
      in Pi [(x1,t1)] a1
renameH m s (Lamb [(x,t)] a) =
  let t1 = rename m s t
      x1 = getNewName x s
      a1 = rename (Map.insert x x1 m) (Set.insert x1 s) a
      in Lamb [(x1,t1)] a1
renameH _ _ t = t

-- equality
instance Eq EXP where
    e1 == e2 = eq (recForm e1) (recForm e2)

eq :: EXP -> EXP -> Bool
eq Type Type = True
eq (Const x1) (Const x2) = x1 == x2
eq (Var x1) (Var x2) = x1 == x2
eq (Appl f1 [a1]) (Appl f2 [a2]) = and [f1 == f2, a1 == a2]
eq (Func [t1] s1) (Func [t2] s2) = and [t1 == t2, s1 == s2]
eq (Pi [(n1,t1)] s1) (Pi [(n2,t2)] s2) =
  let vars = Set.delete n1 $ getFreeVars s1
      vars1 = Set.delete n2 $ getFreeVars s2
      in if (vars1 /= vars)
            then False
            else let s3 = rename (Map.singleton n2 n1) (Set.insert n1 vars) s2
                 in and [t1 == t2, s1 == s3]
eq (Lamb [(n1,t1)] s1) (Lamb [(n2,t2)] s2) =
  let vars = Set.delete n1 $ getFreeVars s1
      vars1 = Set.delete n2 $ getFreeVars s2
      in if (vars1 /= vars)
            then False
            else let s3 = rename (Map.singleton n2 n1) (Set.insert n1 vars) s2
                 in and [t1 == t2, s1 == s3]
eq _ _ = False
