{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances #-}
{- |
Module      :  $Header$
Description :  Class for logical frameworks
Copyright   :  (c) Kristina Sojakova, DFKI Bremen 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  k.sojakova@jacobs-university.de
Stability   :  experimental
Portability :  portable
-}

module Framework.LogicFram where

import Logic.Logic

class Logic lid sublogics basic_spec sentence
            symb_items symb_map_items sign
            morphism symbol raw_symbol proof_tree
      => LogicFram lid sublogics basic_spec sentence
            symb_items symb_map_items sign
            morphism symbol raw_symbol proof_tree
      where
      -- | the base signature
      baseSig :: lid -> sign
      {- | generation of the object logic instances
           second argument is object logic name -}
      writeLogic :: lid -> String -> String
