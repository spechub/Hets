{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./LF/Morphism.hs
Description :  Definition of signature morphisms for the Edinburgh
               Logical Framework
Copyright   :  (c) Kristina Sojakova, DFKI Bremen 2009
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  k.sojakova@jacobs-university.de
Stability   :  experimental
Portability :  portable
-}

module LF.Morphism
   ( MorphType (..)
   , Morphism (..)
   , idMorph
   , compMorph
   , mapSymbol
   , translate
   , canForm
   , inclusionMorph
   , inducedFromToMorphism
   , inducedFromMorphism
   , gen_morph
   ) where

import LF.Sign

import Common.Result
import Common.Doc hiding (space)
import Common.DocUtils
import qualified Control.Monad.Fail as Fail

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Data
import Data.Maybe (isNothing, fromMaybe)

gen_morph :: String
gen_morph = "GEN_MORPH"

data MorphType = Definitional | Postulated | Unknown
  deriving (Ord, Eq, Show, Typeable)

-- LF morphism cannot map defined symbols, only declared ones
data Morphism = Morphism
  { morphBase :: BASE
  , morphModule :: MODULE
  , morphName :: NAME
  , source :: Sign
  , target :: Sign
  , morphType :: MorphType
  , symMap :: Map.Map Symbol EXP
  } deriving (Ord, Show, Typeable)

-- constructs an identity morphism
idMorph :: Sign -> Morphism
idMorph sig = Morphism gen_base gen_module "" sig sig Unknown Map.empty

-- composes two morphisms
compMorph :: Morphism -> Morphism -> Result Morphism
compMorph m1 m2 = do
  let newmap =
        Set.fold (\ s ->
                    let Just e1 = mapSymbol s m1
                        Just e2 = translate m2 e1
                        in Map.insert s e2
                 )
                 Map.empty $
                 getDeclaredSyms $ source m1
  return $ Morphism gen_base gen_module "" (source m1) (target m2) Unknown newmap

-- applies a morphism to a symbol in the source signature
mapSymbol :: Symbol -> Morphism -> Maybe EXP
mapSymbol s m =
  let sig = source m
      in if isDeclaredSym s sig
            then Just $ Map.findWithDefault (Const s) s $ symMap m
            else if isDefinedSym s sig
                    then do val <- getSymValue s sig
                            translate m val
                    else Nothing

-- translates a well-formed expression along the given morphism
translate :: Morphism -> EXP -> Maybe EXP
translate m e = translateH m (recForm e)

translateH :: Morphism -> EXP -> Maybe EXP
translateH _ Type = Just Type
translateH _ (Var n) = Just $ Var n
translateH m (Const s) = mapSymbol s m
translateH m (Appl f [a]) =
  do f1 <- translateH m f
     a1 <- translateH m a
     return $ Appl f1 [a1]
translateH m (Func [t] s) =
  do t1 <- translateH m t
     s1 <- translateH m s
     return $ Func [t1] s1
translateH m (Pi [(x, t)] a) =
  do t1 <- translateH m t
     a1 <- translateH m a
     return $ Pi [(x, t1)] a1
translateH m (Lamb [(x, t)] a) =
  do t1 <- translateH m t
     a1 <- translateH m a
     return $ Lamb [(x, t1)] a1
translateH _ _ = Nothing

{- converts the morphism into its canonical form where the symbol map contains
   no key/value pairs of the form (s, Const s) -}
canForm :: Morphism -> Morphism
canForm (Morphism b m n sig1 sig2 k map1) =
  let map2 = Map.fromList $ filter (\ (s, e) -> Const s /= e) $ Map.toList map1
      in Morphism b m n sig1 sig2 k map2

-- equality
instance Eq Morphism where
    m1 == m2 = eqMorph (canForm m1) (canForm m2)

eqMorph :: Morphism -> Morphism -> Bool
eqMorph (Morphism b1 m1 n1 s1 t1 k1 map1) (Morphism b2 m2 n2 s2 t2 k2 map2) =
  (b1, m1, n1, s1, t1, k1, map1) == (b2, m2, n2, s2, t2, k2, map2)

-- pretty printing
instance Pretty Morphism where
  pretty m = printSymMap $ symMap $ canForm m

printSymMap :: Map.Map Symbol EXP -> Doc
printSymMap m =
  vcat $ map (\ (s, e) -> pretty s <+> mapsto <+> pretty e) $ Map.toList m

-- constructs the inclusion morphism between signatures
inclusionMorph :: Sign -> Sign -> Result Morphism
inclusionMorph sig1 sig2 =
  let m = Morphism gen_base gen_module "" sig1 sig2 Unknown Map.empty
      in Result [] $ Just m

-- induces a morphism from the source and target sigs and a symbol map
inducedFromToMorphism :: Map.Map Symbol (EXP, EXP) -> Sign ->
                         Sign -> Result Morphism
inducedFromToMorphism m sig1 sig2 =
  let mor = Morphism gen_base gen_module "" sig1 sig2 Unknown Map.empty
      defs = filter (\ (Def _ _ v) -> isNothing v) $ getLocalDefs sig1
      in buildFromToMorph defs m mor

buildFromToMorph :: [DEF] -> Map.Map Symbol (EXP, EXP) -> Morphism ->
                    Result Morphism
buildFromToMorph [] _ mor = return mor
buildFromToMorph (Def s t _ : ds) m mor = do
  let m1 = symMap mor
  let t1 = fromMaybe (error $ badTypeError t) $ translate mor t
  let sig2 = target mor
  if Map.member s m
     then do
        let Just (v, t2) = Map.lookup s m
        if t1 == t2
           then buildFromToMorph ds m $ mor {symMap = Map.insert s v m1 }
           else Fail.fail $ badViewError s t1
     else do
        let s1 = if Just t1 == getSymType s sig2 then s else do
                    let syms = getSymsOfType t1 sig2
                    let local = Set.intersection syms $ getLocalSyms sig2
                    case Set.toList syms of
                         [s'] -> s'
                         [] -> error $ noSymError s t1
                         _ -> case Set.toList local of
                                   [s'] -> s'
                                   [] -> error $ noSymError s t1
                                   _ -> error $ manySymError s t1
        buildFromToMorph ds m $ mor {symMap = Map.insert s (Const s1) m1}

-- induces a morphism from the source signature and a symbol map
inducedFromMorphism :: Map.Map Symbol Symbol -> Sign -> Result Morphism
inducedFromMorphism m sig1 = do
  let mor = Morphism gen_base gen_module "" sig1 emptySig Unknown $
              Map.map Const m
  let defs = filter (\ (Def _ _ v) -> isNothing v) $ getDefs sig1
  buildFromMorph defs mor

buildFromMorph :: [DEF] -> Morphism -> Result Morphism
buildFromMorph [] mor = return mor
buildFromMorph (Def s t _ : ds) mor = do
  let sig2 = target mor
  let t1 = fromMaybe (error $ badTypeError t) $ translate mor t
  let Just (Const s1) = mapSymbol s mor
  case getSymType s1 sig2 of
       Just t2 ->
          if t1 == t2
             then buildFromMorph ds mor
             else Fail.fail $ badViewError s1 t1
       Nothing -> buildFromMorph ds $
                    mor { target = addDef (Def s1 t1 Nothing) sig2 }

{- -------------------------------------------------------------------------
------------------------------------------------------------------------- -}

-- ERROR MESSAGES
badTypeError :: EXP -> String
badTypeError t = "Type/kind " ++ show (pretty t) ++ " cannot be translated."

badViewError :: Symbol -> EXP -> String
badViewError s t = "Symbol " ++ show (pretty s) ++
   " must be mapped to an expression of type/kind " ++ show (pretty t) ++ "."

noSymError :: Symbol -> EXP -> String
noSymError s t = "Symbol " ++ show (pretty s) ++
   " cannot be mapped to anything as the target signature contains" ++
   " no symbols of type/kind " ++ show (pretty t) ++ "."

manySymError :: Symbol -> EXP -> String
manySymError s t = "Symbol " ++ show (pretty s) ++
   " cannot be mapped to anything as the target signature contains" ++
   " more than one symbol of type/kind " ++ show (pretty t) ++ "."
