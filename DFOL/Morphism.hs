{- |
Module      :  $Header$
Description :  Definition of signature morphisms for
               first-order logic with dependent types (DFOL)
-}

module DFOL.Morphism
   ( Morphism (..)
   , idMorph
   , compMorph
   , isValidMorph
   , morphCanForm
   , applyMorph
   , mapSymbol
   , inclusionMorph
   , morphUnion
   , inducedFromMorphism
   , inducedFromToMorphism
   ) where

import DFOL.AS_DFOL
import DFOL.Sign
import DFOL.Symbol
import Common.Result
import Common.Doc
import Common.DocUtils
import Common.Id
import Common.ExtSign
import qualified Common.Result as Result
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
      in (applyMorph m type1) == type2

{- converts the morphism into its canonical form where the symbol map contains
   no key/value pairs of the form (k,k) -}
morphCanForm :: Morphism -> Morphism
morphCanForm (Morphism sig1 sig2 map1) =
  let map2 = Map.fromList $ filter (\ (k,a) -> k /= a) $ Map.toList map1
      in Morphism sig1 sig2 map2

-- constructs the inclusion morphism between signatures
inclusionMorph :: Sign -> Sign -> Result.Result Morphism
inclusionMorph sig1 sig2 =
  let m = Morphism sig1 sig2 Map.empty
      in if (isValidMorph m)
            then Result.Result [] $ Just m
            else Result.Result [noSubsigError sig1 sig2] Nothing

-- morphism union
morphUnion :: Morphism -> Morphism -> Result.Result Morphism
morphUnion m1@(Morphism sig1D sig1C map1) m2@(Morphism sig2D sig2C map2) =
  let Result.Result diag1 sigDM = sigUnion sig1D sig2D
      Result.Result diag2 sigCM = sigUnion sig1C sig2C
      Result.Result diag3 map3M = combineMaps map1 map2
      in case sigDM of
              Nothing -> Result.Result diag1 Nothing
              Just sigD ->
                case sigCM of
                     Nothing -> Result.Result diag2 Nothing
                     Just sigC ->
                       case map3M of
                            Nothing -> Result.Result diag3 Nothing
                            Just map3 ->
                              let m = Morphism sigD sigC map3
                                  in if (isValidMorph m)
                                     then Result.Result [] $ Just m
                                     else Result.Result
                                            [invalidMorphError m1 m2] Nothing

combineMaps :: Map.Map NAME NAME -> Map.Map NAME NAME ->
               Result.Result (Map.Map NAME NAME)
combineMaps map1 map2 = combineMapsH map1 $ Map.toList map2

combineMapsH :: Map.Map NAME NAME -> [(NAME,NAME)] ->
                Result.Result (Map.Map NAME NAME)
combineMapsH map1 [] = Result.Result [] $ Just map1
combineMapsH map1 ((k,v):ds) =
  if (Map.member k map1)
     then let Just v1 = Map.lookup k map1
              in if (v == v1)
                 then combineMapsH map1 ds
                 else Result.Result [incompatibleMapError k v v1] Nothing
     else let map2 = Map.insert k v map1
          in combineMapsH map2 ds

-- applies a morphism to a symbol
mapSymbol :: Morphism -> NAME -> NAME
mapSymbol m sym = Map.findWithDefault sym sym $ symMap m

-- translates a term, type or formula along the given morphism
applyMorph :: Translatable a => Morphism -> a -> a
applyMorph m t =
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

-- induces a signature morphism from the source signature and a symbol map
inducedFromMorphism :: Map.Map Symbol Symbol -> Sign -> Result.Result Morphism
inducedFromMorphism map1 sig1 =
  let map2 = toNameMap map1
      Result.Result dgs sig2M = buildSig sig1 map2
      in case sig2M of
              Nothing -> Result.Result dgs Nothing
              Just sig2 -> Result.Result [] $ Just $ Morphism sig1 sig2 map2

buildSig :: Sign -> Map.Map NAME NAME -> Result.Result Sign
buildSig (Sign ds) map1 = buildSigH (expandDecls ds) emptySig map1

buildSigH :: [DECL] -> Sign -> Map.Map NAME NAME -> Result.Result Sign
buildSigH [] sig _ = Result.Result [] $ Just sig
buildSigH (([n1],t1):ds) sig map1 =
  let n2 = Map.findWithDefault n1 n1 map1
      map2 = Map.fromList $ map (\ (k,a) -> (k, Identifier a))
               $ Map.toList map1
      syms = Set.map (\ n -> Map.findWithDefault n n map1)
                 $ getSymbols sig
      t2 = translate map2 syms t1
      in if (isConstant n2 sig)
            then let Just t3 = getSymbolType n2 sig
                 in if t2 == t3
                       then buildSigH ds sig map1
                       else Result.Result [incompatibleViewError1 n2 t2 t3]
                                          Nothing
            else buildSigH ds (addSymbolDecl ([n2],t2) sig) map1
buildSigH _ _ _ = Result.Result [] Nothing

-- induces a signature morphism from the source and target sigs and a symbol map
inducedFromToMorphism :: Map.Map Symbol Symbol -> ExtSign Sign Symbol ->
                         ExtSign Sign Symbol -> Result.Result Morphism
inducedFromToMorphism map1 (ExtSign sig1 _) (ExtSign sig2 _) =
  let map2 = toNameMap map1
      m = Morphism sig1 sig2 map2
      Sign ds = sig1
      in if (isValidMorph m)
            then Result.Result [] $ Just m
            else buildMorph (expandDecls ds) m

buildMorph :: [DECL] -> Morphism -> Result.Result Morphism
buildMorph [] m = Result.Result [] $ Just m
buildMorph (([n1],t1):ds) m@(Morphism _ sig2 map1) =
  if (Map.member n1 map1)
     then let n2 = mapSymbol m n1
              t2 = applyMorph m t1
              Just t3 = getSymbolType n2 sig2
              in if t2 == t3
                    then buildMorph ds m
                    else Result.Result [incompatibleViewError2 n2 t2 t3] Nothing
     else let t2 = applyMorph m t1
              ss = getSymsOfType sig2 t2
              in case ss of
                      [s] -> buildMorph ds $
                                 m {symMap = Map.insert n1 s $ symMap m}
                      []  -> Result.Result [noSymToMapError n1 t2] Nothing
                      _   -> Result.Result [manySymToMapError n1 t2 ss] Nothing
buildMorph _ _ = Result.Result [] Nothing

getSymsOfType :: Sign -> TYPE -> [NAME]
getSymsOfType (Sign ds) t = getSymsOfTypeH ds t

getSymsOfTypeH :: [DECL] -> TYPE -> [NAME]
getSymsOfTypeH [] _ = []
getSymsOfTypeH ((ns,t1):ds) t =
  if (t1 == t)
     then ns ++ (getSymsOfTypeH ds t)
     else getSymsOfTypeH ds t

-- ERROR MESSAGES
incompatibleViewError1 :: NAME -> TYPE -> TYPE -> Result.Diagnosis
incompatibleViewError1 n t1 t2 =
  Result.Diag
    { Result.diagKind = Result.Error
    , Result.diagString = "Symbol\n" ++ (show $ pretty n)
                          ++ "\nmust have both type\n" ++ (show $ pretty t1)
                          ++ "\nand type\n" ++ (show $ pretty t2)
                          ++ "\nin the target signature and hence "
                          ++ "the view is ill-formed."
    , Result.diagPos = nullRange
    }

incompatibleViewError2 :: NAME -> TYPE -> TYPE -> Result.Diagnosis
incompatibleViewError2 n t1 t2 =
  Result.Diag
    { Result.diagKind = Result.Error
    , Result.diagString = "Symbol\n" ++ (show $ pretty n)
                          ++ "\nmust have type\n" ++ (show $ pretty t1)
                          ++ "\nbut instead has type\n" ++ (show $ pretty t2)
                          ++ "\nin the target signature and hence "
                          ++ "the view is ill-formed."
    , Result.diagPos = nullRange
    }

noSymToMapError :: NAME -> TYPE -> Result.Diagnosis
noSymToMapError n t =
  Result.Diag
    { Result.diagKind = Result.Error
    , Result.diagString = "Symbol\n" ++ (show $ pretty n)
                          ++ "\ncannot be mapped to anything as the target "
                          ++ "signature contains no symbols of type\n"
                          ++ (show $ pretty t)
    , Result.diagPos = nullRange
    }

manySymToMapError :: NAME -> TYPE -> [NAME] -> Result.Diagnosis
manySymToMapError n t ss =
  Result.Diag
    { Result.diagKind = Result.Error
    , Result.diagString = "Symbol\n" ++ (show $ pretty n)
                          ++ "\ncannot be uniquely mapped as the target "
                          ++ "signature contains multiple symbols of type\n"
                          ++ (show $ pretty t) ++ "\n namely\n"
                          ++ (show $ printNames ss)
    , Result.diagPos = nullRange
    }

noSubsigError :: Sign -> Sign -> Result.Diagnosis
noSubsigError sig1 sig2 =
  Result.Diag
    { Result.diagKind = Result.Error
    , Result.diagString = "Signature\n" ++ (show $ pretty sig1)
                          ++ "\nis not a subsignature of\n"
                          ++ (show $ pretty sig2)
                          ++ "\nand hence the inclusion morphism "
                          ++ "cannot be constructed."
    , Result.diagPos = nullRange
    }

incompatibleMapError :: NAME -> NAME -> NAME -> Result.Diagnosis
incompatibleMapError n n1 n2 =
  Result.Diag
    { Result.diagKind = Result.Error
    , Result.diagString = "Symbol\n" ++ (show $ pretty n)
                          ++ "\nis mapped both to\n" ++ (show $ pretty n1)
                          ++ "\nand\n" ++ (show $ pretty n2)
                          ++ "\nin the target signature and hence "
                          ++ "the morphism union cannot be constructed."
    , Result.diagPos = nullRange
    }

invalidMorphError :: Morphism -> Morphism -> Result.Diagnosis
invalidMorphError m1 m2 =
  Result.Diag
    { Result.diagKind = Result.Error
    , Result.diagString = "The combination of morphisms\n" ++ (show $ pretty m1)
                          ++ "\nand\n" ++ (show $ pretty m2)
                          ++ "\nis not a valid morphism and hence "
                          ++ "their union cannot be constructed."
    , Result.diagPos = nullRange
    }
