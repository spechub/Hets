{- |
Module      :  $Header$
Description :  Definition of signature morphisms for 
               first-order logic with dependent types (DFOL)
-}

module DFOL.Morphism where

import DFOL.AS_DFOL
import DFOL.Sign
import Common.Result
import Common.Doc
import Common.DocUtils
import qualified Data.Map as Map
import qualified Data.Set as Set

-- morphisms for DFOL - maps of symbol names
data Morphism = Morphism 
  { source :: Sign
  , target :: Sign
  , symMap :: Map.Map NAME NAME
  } deriving (Eq, Ord, Show)

-- constructs an identity morphism
idMorph :: Sign -> Morphism
idMorph sig = Morphism sig sig Map.empty

-- composes two morphisms
compMorph :: Morphism -> Morphism -> Result Morphism
compMorph m1 m2 = 
  if target m1 /= source m2
     then fail $ "Cosourceain of the first morphism "
                 ++ "must equal the sourceain of the second."
     else return $ Morphism (source m1) (target m2) $ 
                 Set.fold (\ sym1 -> let sym2 = mapSymbol m2 $ mapSymbol m1 sym1 
                                         in if (sym1 == sym2)
                                               then id
                                               else Map.insert sym1 sym2)
                          Map.empty $ 
                          getSymbols $ source m1  

-- determines whether a morphism is valid     
isValidMorph :: Morphism -> Bool
isValidMorph m = isValidMorphH syms m
                 where syms = Set.toList $ getSymbols $ source m

isValidMorphH :: [NAME] -> Morphism -> Bool
isValidMorphH [] _ = True
isValidMorphH (sym:syms) m = 
  let sig1 = source m
      sig2 = target m
      type1M = getSymbolType sym sig1
      type2M = getSymbolType (mapSymbol m sym) sig2
      in case type1M of
              Nothing -> False
              Just type1 -> case type2M of
                                 Nothing -> False
                                 Just type2 -> if (applyMorphism m type1) == type2
                                                  then isValidMorphH syms m 
                                                  else False  

-- applies a morphism to a symbol
mapSymbol :: Morphism -> NAME -> NAME
mapSymbol m sym = Map.findWithDefault sym sym $ symMap m 

-- translates a term, type or formula along the given morphism
applyMorphism :: Translatable a => Morphism -> a -> a
applyMorphism m t = 
  let syms = getSymbols (target m)
      map1 = Map.fromList $ map (\ (k,a) -> (k, Identifier a)) 
               $ Map.toList $ symMap m               
      in translate map1 syms t 

-- pretty printing
instance Pretty Morphism where
  pretty = printMorph

printMorph :: Morphism -> Doc
printMorph m = 
  if m == (idMorph $ source m)
     then vcat [text "Identity morphism on:", pretty $ source m]
     else vcat [text "Source signature:", pretty $ source m, text "Target signature:", 
                pretty $ target m, text "Mapping:", printSymMap $ symMap m]

printSymMap :: Map.Map NAME NAME -> Doc
printSymMap m = vcat $ map (\ (k,a) -> pretty k <+> text "|->" <+> pretty a) 
                     $ Map.toList m
