{- |
Module      :  $Header$
Description :  Symbols of common logic
Copyright   :  (c) Karl Luc, DFKI Bremen 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  kluc@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

Definition of symbols for common logic
-}

module CommonLogic.Symbol where

import qualified Common.Id as Id
import Common.Doc
import Common.DocUtils

--
newtype Symbol = Symbol {symName :: Id.Id}
                 deriving (Show, Eq, Ord)

instance Id.GetRange Symbol where 
    getRange = Id.getRange . symName

instance Pretty Symbol where
    pretty = printSymbol

printSymbol :: Symbol -> Doc
printSymbol x = pretty $ symName x

