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

module CommonLogic.Symbol (
        Symbol (..) 
       ,printSymbol
       ,symOf
       ,getSymbolMap
       ,getSymbolName
       ,symbolToRaw
       ,idToRaw
       ,matches
       ,addSymbToSign
       )
       where

import qualified Common.Id as Id
import Common.Doc
import Common.DocUtils
import Common.Result
import qualified Data.Set as Set
import qualified Data.Map as Map

import qualified CommonLogic.Sign as Sign
import CommonLogic.Morphism as Morphism
--
newtype Symbol = Symbol {symName :: Id.Id}
                 deriving (Show, Eq, Ord)

instance Id.GetRange Symbol where 
    getRange = Id.getRange . symName

instance Pretty Symbol where
    pretty = printSymbol

printSymbol :: Symbol -> Doc
printSymbol x = pretty $ symName x

symOf :: Sign.Sign -> Set.Set Symbol
symOf x = Set.fold (\y -> Set.insert Symbol{symName = y}) Set.empty $
           Sign.items x

-- | Determines the symbol map of a morhpism
getSymbolMap :: Morphism.Morphism -> Map.Map Symbol Symbol
getSymbolMap f =
  foldr (\ x -> Map.insert (Symbol x) (Symbol $ applyMap (propMap f) x))
  Map.empty $ Set.toList $ Sign.items $ source f

-- | Determines the name of a symbol
getSymbolName :: Symbol -> Id.Id
getSymbolName sym = symName sym

symbolToRaw :: Symbol -> Symbol
symbolToRaw = id

idToRaw :: Id.Id -> Symbol
idToRaw mid = Symbol {symName = mid}

matches :: Symbol -> Symbol -> Bool
matches s1 s2 = s1 == s2

addSymbToSign :: Sign.Sign -> Symbol -> Result (Sign.Sign)
addSymbToSign sig sym = Result [] $ Just sig