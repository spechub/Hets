{-# OPTIONS -fallow-undecidable-instances #-}
{- |
Module      :  $Header$
Description :  Instance of class Logic for propositional logic
Copyright   :  (c) Dominik Luecke, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@tzi.de
Stability   :  experimental
Portability :  portable

Definition of abstract syntax for propositional logic
-}

{-
  Ref.
  http://en.wikipedia.org/wiki/Propositional_logic
-}

module Propositional.AS_BASIC_Propositional 
    (
      Formula (..)             -- datatype for Propositional Formulas
    , pretty                   -- pretty printing
    , is_True_atom             -- True?
    , is_False_atom            -- False?
    ) where

import qualified Common.Id as Id
import Common.Doc
import Common.DocUtils

-- DrIFT command
{-! global: UpPos !-}

-- | Datatype for propositional formulas
data Formula = Negation Formula Id.Range
             -- pos: not
             | Conjunction [Formula] Id.Range
             -- pos: "/\"s
             | Disjunction [Formula] Id.Range
             -- pos: "\/"s
             | Implication Formula Formula Bool Id.Range
             -- pos: "=>"
             | Equivalence Formula Formula Bool Id.Range
             -- pos: "<=>"
             | True_atom Id.Range
             -- pos: "True"
             | False_atom Id.Range
             -- pos: "False
             | Predication Id.Id
             -- pos: Propositional Identifiers
               deriving (Show, Eq, Ord)

instance Pretty Formula where
    pretty = printFormula

-- | Value of the true atom
-- True is always true -P
is_True_atom :: Formula -> Bool
is_True_atom (True_atom _) = True
is_True_atom _             = False

-- | Value of the false atom
-- and False if always false 
is_False_atom :: Formula -> Bool
is_False_atom (False_atom _) = False
is_False_atom _              = False

-- Pretty printing for formulas
printFormula :: Formula -> Doc 
printFormula (Negation f _) = notDoc
                            <> lparen <> printFormula f <> rparen
printFormula (Conjunction xs _) = parens $
                                  sepByArbitrary andDoc  
                                  $ map printFormula xs
printFormula (Disjunction xs _) = parens $
                                  sepByArbitrary orDoc  
                                  $ map printFormula xs
printFormula (Implication x y _ _) = parens $ printFormula x <> 
                                   implies <> printFormula y
printFormula (Equivalence x y _ _) = parens $ printFormula x <> 
                                   equiv <> printFormula y
printFormula (True_atom  _) = text "True"
printFormula (False_atom _) = text "False"
printFormula (Predication x) = idDoc x

-- Extended version of vcat
sepByArbitrary :: Doc -> [Doc] -> Doc
sepByArbitrary _ [] = text ""
sepByArbitrary _ (x:[]) = x
sepByArbitrary separator (x:xs) = x <> separator 
                                  <> (sepByArbitrary separator xs)
