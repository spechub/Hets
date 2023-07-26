{- |
Module      :  $Id$
Copyright   :  (c) DFKI GmbH
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

utilities for writing new rules.
-}

module RuleUtils where

import Prelude hiding ((<>))
import Text.PrettyPrint.HughesPJ
import DataP (Statement (..), Data (..), Type (..), Class,
              Body (..), Constructor)

-- Rule Declarations

type Tag = String
type Rule = (Tag, Data -> Doc)
type RuleDef = (Tag, Data -> Doc, String, String, Maybe String)

rArrow :: Doc
rArrow = text "->"

lArrow :: Doc
lArrow = text "<-"

prettyType :: Type -> Doc
prettyType (Arrow x y) = parens (prettyType x <+> text "->" <+> prettyType y)
prettyType (List x) = brackets (prettyType x)
prettyType (Tuple xs) = tuple (map prettyType xs)
prettyType (Var s) = text s
prettyType (Con s) = text s
prettyType (LApply t ts) = prettyType t <+> hsep (map prettyType ts)

-- New Pretty Printers ---------------

texts :: [String] -> [Doc]
texts = map text

block, parenList, bracketList :: [Doc] -> Doc
block = nest 4 . vcat
parenList = parens . fsep . sepWith comma
bracketList = brackets . fsep . sepWith comma

-- for bulding m1 >> m2 >> m3, f . g . h, etc
sepWith :: Doc -> [Doc] -> [Doc]
sepWith _ [] = []
sepWith _ [x] = [x]
sepWith a (x : xs) = (x <> a) : sepWith a xs

-- optional combinator, applys fn if arg is non-[]
opt :: [a] -> ([a] -> Doc) -> Doc
opt [] _ = empty
opt a f = f a

-- equivalent of `opt' for singleton lists
opt1 :: [a] -> ([a] -> Doc) -> (a -> Doc) -> Doc
opt1 [] _ _ = empty
opt1 [x] _ g = g x
opt1 a f _ = f a

-- new simple docs
commentLine :: Doc -> Doc
commentLine x = text "--" <+> x -- useful for warnings / error messages

commentBlock :: Doc -> Doc
commentBlock x = text "{-" <+> x <+> text "-}"

-- - Utility Functions -------------------------------------------------------

-- Instances


-- instance header, handling class constraints etc.
simpleInstance :: Class -> Data -> Doc
simpleInstance s d = hsep [text "instance"
                , opt1 constr (\ x -> parenList x <+> text "=>")
                       ( \ x -> x <+> text "=>")
                , text s
                , opt1 (texts (name d : vars d)) parenSpace id]
   where
   constr = map (\ v -> text "Ord" <+> text v)
            (concatMap getSetVars . concatMap types $ body d)
       ++ map (\ (c, v) -> text c <+> text v) (constraints d)
       ++ map (\ x -> text s <+> text x) (vars d)
   parenSpace = parens . hsep

getSetVars :: Type -> [String]
getSetVars ty = case ty of
   LApply (Con "Set.Set") [Var v] -> [v]
   _ -> []

{- instanceSkeleton handles most instance declarations, where instance
functions are not related to one another.  A member function is generated
using a (IFunction,Doc) pair.  The IFunction is applied to each body of the
type, creating a block of pattern - matching cases. Default cases can be
given using the Doc in the pair.  If a default case is not required, set
Doc to 'empty' -}

type IFunction = Body -> Doc -- instance function

instanceSkeleton :: Class -> [(IFunction, Doc)] -> Data -> Doc
instanceSkeleton s ii d = (simpleInstance s d <+> text "where")
                                $$ block functions
        where
        functions = concatMap f ii
        f (i, dflt) = map i (body d) ++ [dflt]

-- little variable name generator, generates unique names a - z
varNames :: [a] -> [Doc]
varNames l = zipWith (const char) l ['a' .. 'z']

-- variant generating aa' - aZ'
varNames' :: [a] -> [Doc]
varNames' = map (<> char '\'') . varNames

-- pattern matching a constructor and args
pattern :: Constructor -> [a] -> Doc
pattern c l = parens $ fsep (text c : varNames l)

pattern_ :: Constructor -> [a] -> Doc
pattern_ c l = parens $ fsep (text c : replicate (length l) (text "_"))

pattern' :: Constructor -> [a] -> Doc
pattern' c l = parens $ fsep (text c : varNames' l)

-- test that a datatype has at least one record constructor
hasRecord :: Data -> Bool
hasRecord d = statement d == DataStmt
                && any (not . null . labels) (body d)

tuple :: [Doc] -> Doc
tuple xs = parens $ hcat (punctuate (char ',') xs)
