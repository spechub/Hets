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
     then fail $ "Codomain of the first morphism "
                 ++ "must equal the domain of the second."
     else return $ Morphism (source m1) (target m2) $ 
                 Set.fold (\ sym1 -> let sym2 = mapSymbol m2 
                                                  $ mapSymbol m1 sym1 
                                         in if (sym1 == sym2)
                                               then id
                                               else Map.insert sym1 sym2)
                          Map.empty $ 
                          getSymbols $ source m1  

-- determines whether a morphism is valid     
isValidMorph :: Morphism -> Bool
isValidMorph m@(Morphism sig1 sig2 map1) =      
  let sym1 = getSymbols sig1
      sym2 = getSymbols sig2
      checkDom = Set.isSubsetOf (Map.keysSet map1) sym1 
      checkCod = Set.isSubsetOf (Set.map (mapSymbol m) sym1) sym2
      checkTypes = map (checkTypePres m) $ Set.toList sym1
      in and $ [checkDom,checkCod] ++ checkTypes

checkTypePres:: Morphism -> NAME -> Bool
checkTypePres m n = 
  let Just type1 = getSymbolType n $ source m
      Just type2 = getSymbolType (mapSymbol m n) $ target m
      in (applyMorphism m type1) == type2

{- converts the morphism into its canonical form where the symbol map contains
   no key/value pairs of the form (k,k) -}
morphCanForm :: Morphism -> Morphism
morphCanForm (Morphism sig1 sig2 map1) =
  let map2 = Map.fromList $ filter (\ (k,a) -> k /= a) $ Map.toList map1
      in Morphism sig1 sig2 map2

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
     else vcat [text "Source signature:", pretty $ source m,
                text "Target signature:", pretty $ target m,
                text "Mapping:", printSymMap $ symMap m]

printSymMap :: Map.Map NAME NAME -> Doc
printSymMap m = vcat $ map (\ (k,a) -> pretty k <+> text "|->" <+> pretty a)
                     $ Map.toList m
