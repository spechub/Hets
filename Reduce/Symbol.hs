-- todo: nimm SYMB, symbol=rawsymbol
-- statische analyse wandelt symbol -> raw-symbol um
-- inducedfromMorphism wandelt rawsymbolmap in morphismus um
-- voll analysierte symbole

module Reduce.Symbol
where

import Common.Id
import Common.Doc
import Common.DocUtils
import qualified Data.Set as Set
import qualified Data.Map as Map
import Reduce.Sign 
import Reduce.Morphism

-- | Datatype for symbols
newtype Symbol = Symbol {symName :: Id}
            deriving (Show, Eq, Ord)

instance GetRange Symbol where
    getRange = getRange . symName

instance Pretty Symbol where
    pretty = printSymbol

printSymbol :: Symbol -> Doc
printSymbol x = pretty $ symName x

-- | Extraction of symbols from a signature
symOf :: Sign -> Set.Set Symbol
symOf x = Set.fold (\y -> Set.insert Symbol{symName = y}) Set.empty $
           items x

-- | Determines the symbol map of a morhpism
getSymbolMap :: Morphism -> Map.Map Symbol Symbol
getSymbolMap f =
  foldr (\ x -> Map.insert (Symbol x) (Symbol $ applyMap (operatorMap f) x))
  Map.empty $ Set.toList $ items $ source f

-- | Determines the name of a symbol
getSymbolName :: Symbol -> Id
getSymbolName sym = symName sym

-- | make a raw_symbol
idToRaw :: Id -> Symbol
idToRaw mid = Symbol {symName = mid}

-- | convert to raw symbol
symbolToRaw :: Symbol -> Symbol
symbolToRaw = id

-- | does a smybol match a raw symbol?
matches :: Symbol -> Symbol -> Bool
matches s1 s2 = s1 == s2

-- | application function for Symbol Maps
applySymMap :: Map.Map Symbol Symbol -> Symbol -> Symbol
applySymMap smap idt = Map.findWithDefault idt idt $ smap
