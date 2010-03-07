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

data MorphType = Definitional | Postulated | Unknown deriving (Ord,Eq,Show)

-- LF morphism cannot map defined symbols, only declared ones
data Morphism = Morphism
  { morphBase :: BASE
  , morphModule :: MODULE
  , morphName :: NAME
  , source :: Sign
  , target :: Sign
  , morphType :: MorphType
  , symMap :: Map.Map Symbol EXP
  } deriving (Ord, Show)

-- constructs an identity morphism
idMorph :: Sign -> Morphism
idMorph sig = Morphism "" "" "" sig sig Unknown Map.empty

-- composes two morphisms
compMorph :: Morphism -> Morphism -> Result Morphism
compMorph m1 m2 =
  if target m1 /= source m2
     then Result.Result [incompatibleMorphsError m1 m2] Nothing
     else do
       let newmap =
            Set.fold (\ s ->
                        let Just e1 = mapSymbol s m1
                            Just e2 = translateH m2 e1
                            in Map.insert s e2
                     )
                     Map.empty $
                     getDeclaredSyms $ source m1
       return $ Morphism "" "" "" (source m1) (target m2) Unknown newmap

-- applies a morphism to a symbol in the source signature
mapSymbol :: Symbol -> Morphism -> Maybe EXP
mapSymbol s m =
  let sig = source m
      in if (isDeclaredSym s sig)
            then Just $ Map.findWithDefault (Const s) s $ symMap m
            else if (isDefinedSym s sig)
                    then do val <- getSymValue s sig
                            translate m val
                    else Nothing

-- translates a well-formed expression along the given morphism
translate :: Morphism -> EXP -> Maybe EXP
translate m e = translateH m (recForm e)

translateH :: Morphism -> EXP -> Maybe EXP
translateH _ Type = Just Type
translateH _ (Var n) = Just $ Var n
translateH m (Const s) =
  do e <- mapSymbol s m
     return e
translateH m (Appl f [a]) =
  do f1 <- translateH m f
     a1 <- translateH m a
     return $ Appl f1 [a1]
translateH m (Func [t] s) =
  do t1 <- translateH m t
     s1 <- translateH m s
     return $ Func [t1] s1
translateH m (Pi [(x,t)] a) =
  do t1 <- translateH m t
     a1 <- translateH m a
     return $ Pi [(x,t1)] a1
translateH m (Lamb [(x,t)] a) =
  do t1 <- translateH m t
     a1 <- translateH m a
     return $ Lamb [(x,t1)] a1
translateH _ _ = Nothing

{- converts the morphism into its canonical form where the symbol map contains
   no key/value pairs of the form (s, Const s) -}
canForm :: Morphism -> Morphism
canForm (Morphism b m n sig1 sig2 k map1) =
  let map2 = Map.fromList $ filter (\ (s,e) -> Const s /= e) $ Map.toList map1
      in Morphism b m n sig1 sig2 k map2

-- equality
instance Eq Morphism where
    m1 == m2 = (canForm m1) == (canForm m2)

-- pretty printing
instance Pretty Morphism where
  pretty m = printMorph $ canForm m

printMorph :: Morphism -> Doc
printMorph m = printSymMap (source m) (target m) $ symMap m

printSymMap :: Sign -> Sign -> Map.Map Symbol EXP -> Doc
printSymMap sig1 sig2 m =
  vcat $ map (\ (s,e) -> printSymbol sig1 s <+> text "|->" <+> printExp sig2 e)
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
