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

-- applies a morphism to a symbol
applyMorph :: Morphism -> NAME -> NAME
applyMorph m sym = Map.findWithDefault sym sym $ symMap m 

-- composes two morphisms
compMorph :: Morphism -> Morphism -> Result Morphism
compMorph m1 m2 = 
  if target m1 /= source m2
     then fail $ "Cosourceain of the first morphism "
                 ++ "must equal the sourceain of the second."
     else return $ Morphism (source m1) (target m2) $ 
                 Set.fold (\ sym1 -> let sym2 = applyMorph m2 $ applyMorph m1 sym1 
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
      type2M = getSymbolType (applyMorph m sym) sig2
      in case type1M of
              Nothing -> False
              Just type1 -> case type2M of
                                 Nothing -> False
                                 Just type2 -> if (translateType type1 m) == type2
                                                  then isValidMorphH syms m 
                                                  else False  

-- translates a type along the given morphism
translateType :: TYPE -> Morphism -> TYPE
translateType t m = 
  let syms = getSymbols (target m)
      vars = getVarsDeclaredInType t
      map1 = getRenameMap vars syms
      map2 = Map.fromList $ map (\ (k,a) -> (k, Identifier a)) 
               $ Map.toList $ symMap m               
      in substitute map1 map2 t

-- pretty printing
instance Pretty Morphism where
  pretty = printMorph

printMorph :: Morphism -> Doc
printMorph m = 
  if m == (idMorph $ source m)
     then vcat [text "Identity morphism on:", pretty $ source m]
     else vcat [text "sourceain signature:", pretty $ source m, text "Cosourceain signature:", 
                pretty $ target m, text "Mapping:", printSymMap $ symMap m]

printSymMap :: Map.Map NAME NAME -> Doc
printSymMap m = vcat $ map (\ (k,a) -> pretty k <+> text "|->" <+> pretty a) 
                     $ Map.toList m
