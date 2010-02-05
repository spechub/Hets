{- |
Module      :  $Header$
Description :  Definition of signature morphisms for the Edinburgh
               Logical Framework
Copyright   :  (c) Kristina Sojakova, DFKI Bremen 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  k.sojakova@jacobs-university.de
Stability   :  experimental
Portability :  portable
-}

module LF.Morphism where

import LF.Sign
import Common.Result
import Common.Doc
import Common.DocUtils
import Common.Id
import qualified Common.Result as Result
import qualified Data.Map as Map
import qualified Data.Set as Set

-- morphisms for LF
data Morphism = Morphism
  { source :: Sign
  , target :: Sign
  , symMap :: Map.Map NAME EXP
  } deriving (Ord, Show)

-- constructs an identity morphism
idMorph :: Sign -> Morphism
idMorph sig = Morphism sig sig Map.empty

-- composes two morphisms
compMorph :: Morphism -> Morphism -> Result Morphism
compMorph m1 m2 =
  if target m1 /= source m2
     then Result.Result [incompatibleMorphsError m1 m2] Nothing 
     else return $ Morphism (source m1) (target m2) $
                 Set.fold (\ s -> let e = applyMorph m2 $ mapSymbol m1 s
                                      in Map.insert s e)

                          Map.empty $
                          getSymbols $ source m1

-- applies a morphism to a symbol
mapSymbol :: Morphism -> NAME -> EXP
mapSymbol m sym = Map.findWithDefault (Var sym) sym $ symMap m

-- translates an expression along the given morphism
applyMorph :: Morphism -> EXP -> EXP
applyMorph m e =
  let syms = getSymbols (target m)
      in translate (symMap m) syms e

{- converts the morphism into its canonical form where the symbol map contains
   no key/value pairs of the form (k,Var k) -}
canForm :: Morphism -> Morphism
canForm (Morphism sig1 sig2 map1) =
  let map2 = Map.fromList $ filter (\ (k,e) -> Var k /= e) $ Map.toList map1
      in Morphism sig1 sig2 map2

-- equality
instance Eq Morphism where
    m1 == m2 = (canForm m1) == (canForm m2)

-- pretty printing
instance Pretty Morphism where
  pretty m = printMorph $ canForm m

printMorph :: Morphism -> Doc
printMorph m =
  if m == (idMorph $ source m)
     then vcat [text "Identity morphism on:", pretty $ source m]
     else vcat [text "Source signature:", pretty $ source m,
                text "Target signature:", pretty $ target m,
                text "Mapping:", printSymMap $ symMap m]

printSymMap :: Map.Map NAME EXP -> Doc
printSymMap m = vcat $ map (\ (k,a) -> pretty k <+> text "|->" <+> pretty a)
                     $ Map.toList m

-- ERROR MESSAGES
incompatibleMorphsError :: Morphism -> Morphism -> Result.Diagnosis
incompatibleMorphsError m1 m2 =
  Result.Diag
    { Result.diagKind = Result.Error
    , Result.diagString = "Codomain of the morphism\n" ++ (show $ pretty m1)
                          ++ "\nis different from the domain of the morphism\n"
                          ++ (show $ pretty m2)
                          ++ "\nhence their composition cannot be constructed."
    , Result.diagPos = nullRange
    }
