{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, DeriveDataTypeable
  , FlexibleInstances, UndecidableInstances, ExistentialQuantification #-}
{- |
Module      :  ./Logic/Comorphism.hs
Description :  interface and class for logic translations
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2006
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (via Logic)

Central interface (type class) for logic translations (comorphisms) in Hets
   These are just collections of
   functions between (some of) the types of logics.

   References: see Logic.hs
-}

module Logic.Comorphism
    ( CompComorphism (..)
    , InclComorphism
    , inclusion_logic
    , inclusion_source_sublogic
    , inclusion_target_sublogic
    , mkInclComorphism
    , mkIdComorphism
    , Comorphism (..)
    , targetSublogic
    , map_sign
    , wrapMapTheory
    , wrapMapTheoryPossiblyLossy
    , mkTheoryMapping
    , AnyComorphism (..)
    , idComorphism
    , isIdComorphism
    , isModelTransportable
    , hasModelExpansion
    , isEps
    , isRps
    , isWeaklyAmalgamable
    , compComorphism
    ) where

import Logic.Logic
import Logic.Coerce

import Common.AS_Annotation
import Common.Doc
import Common.DocUtils
import Common.Id
import Common.LibName
import Common.ProofUtils
import Common.Result

import Data.Data
import Data.Maybe
import qualified Data.Set as Set

class (Language cid,
       Logic lid1 sublogics1
        basic_spec1 sentence1 symb_items1 symb_map_items1
        sign1 morphism1 symbol1 raw_symbol1 proof_tree1,
       Logic lid2 sublogics2
        basic_spec2 sentence2 symb_items2 symb_map_items2
        sign2 morphism2 symbol2 raw_symbol2 proof_tree2) =>
  Comorphism cid
            lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2
   | cid -> lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2
  where
    {- source and target logic and sublogic
    the source sublogic is the maximal one for which the comorphism works -}
    sourceLogic :: cid -> lid1
    sourceSublogic :: cid -> sublogics1
    sourceSublogic cid = top_sublogic $ sourceLogic cid
    {- needed for lossy translations. Is stricter than sourceSublogic.
       Should be merged with sourceSublogic once #1706 has been fixed. -}
    sourceSublogicLossy :: cid -> sublogics1
    sourceSublogicLossy = sourceSublogic
    minSourceTheory :: cid -> Maybe (LibName, String)
    minSourceTheory _ = Nothing
    targetLogic :: cid -> lid2
    {- finer information of target sublogics corresponding to source sublogics
    this function must be partial because mapTheory is partial -}
    mapSublogic :: cid -> sublogics1 -> Maybe sublogics2
    mapSublogic cid _ = Just $ top_sublogic $ targetLogic cid
    {- the translation functions are partial
    because the target may be a sublanguage
    map_basic_spec :: cid -> basic_spec1 -> Result basic_spec2
    cover theoroidal comorphisms as well -}
    map_theory :: cid -> (sign1, [Named sentence1])
                      -> Result (sign2, [Named sentence2])
    -- map_theory but also consider sentence marks
    mapMarkedTheory :: cid -> (sign1, [Named sentence1])
                      -> Result (sign2, [Named sentence2])
    mapMarkedTheory cid (sig, sens) = do
      (sig2, sens2) <- map_theory cid (sig, map unmark sens)
      return (sig2, map (markSen $ language_name cid) sens2)
    map_morphism :: cid -> morphism1 -> Result morphism2
    map_morphism = mapDefaultMorphism
    map_sentence :: cid -> sign1 -> sentence1 -> Result sentence2
          {- also covers semi-comorphisms
          with no sentence translation
          - but these are spans! -}
    map_sentence = failMapSentence
    map_symbol :: cid -> sign1 -> symbol1 -> Set.Set symbol2
    map_symbol = errMapSymbol
    extractModel :: cid -> sign1 -> proof_tree2
                 -> Result (sign1, [Named sentence1])
    extractModel cid _ _ = fail
      $ "extractModel not implemented for comorphism "
      ++ language_name cid
    -- properties of comorphisms
    is_model_transportable :: cid -> Bool
    {- a comorphism (\phi, \alpha, \beta) is model-transportable
    if for any signature \Sigma,
    any \Sigma-model M and any \phi(\Sigma)-model N
    for any isomorphism           h : \beta_\Sigma(N) -> M
    there exists an isomorphism   h': N -> M' such that \beta_\Sigma(h') = h -}
    is_model_transportable _ = False
    has_model_expansion :: cid -> Bool
    has_model_expansion _ = False
    is_weakly_amalgamable :: cid -> Bool
    is_weakly_amalgamable _ = False
    constituents :: cid -> [String]
    constituents cid = [language_name cid]
    isInclusionComorphism :: cid -> Bool
    isInclusionComorphism _ = False
    -- reduction preserves satisfaction
    rps :: cid -> Bool
    rps _ = True
    -- expansion preserves satisfaction
    eps :: cid -> Bool
    eps _ = True

targetSublogic :: Comorphism cid
            lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2
         => cid -> sublogics2
targetSublogic cid = fromMaybe (top_sublogic $ targetLogic cid)
                           $ mapSublogic cid $ sourceSublogic cid

-- | this function is based on 'map_theory' using no sentences as input
map_sign :: Comorphism cid
            lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2
         => cid -> sign1 -> Result (sign2, [Named sentence2])
map_sign cid sign = wrapMapTheory cid (sign, [])

mapDefaultMorphism :: Comorphism cid
            lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2
         => cid -> morphism1 -> Result morphism2
mapDefaultMorphism cid mor = do
  (sig1, _) <- map_sign cid $ dom mor
  (sig2, _) <- map_sign cid $ cod mor
  inclusion (targetLogic cid) sig1 sig2

failMapSentence :: Comorphism cid
            lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2
         => cid -> sign1 -> sentence1 -> Result sentence2
failMapSentence cid _ _ =
    fail $ "Unsupported sentence translation " ++ show cid

errMapSymbol :: Comorphism cid
            lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2
         => cid -> sign1 -> symbol1 -> Set.Set symbol2
errMapSymbol cid _ _ = error $ "no symbol mapping for " ++ show cid

-- | use this function instead of 'mapMarkedTheory'
wrapMapTheoryPossiblyLossy :: Comorphism cid
            lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2
            => Bool -> cid -> (sign1, [Named sentence1])
                   -> Result (sign2, [Named sentence2])
wrapMapTheoryPossiblyLossy lossy cid (sign, sens) =
  let res = mapMarkedTheory cid (sign, sens)
      lid1 = sourceLogic cid
      thDoc = show (vcat $ pretty sign : map (print_named lid1) sens)
  in
  if isIdComorphism $ Comorphism cid
  then res
  else let sub = if lossy then sourceSublogicLossy cid else sourceSublogic cid
           sigLog = minSublogic sign
           senLog = foldl lub sigLog $ map (minSublogic . sentence) sens
           isInSub s = isSubElem (minSublogic $ sentence s) sub 
           sensLossy = filter isInSub sens
           resLossy = mapMarkedTheory cid (sign, sensLossy)
        in if isSubElem senLog sub
                 then res
                 else
                    if lossy && isSubElem sigLog sub
                    then resLossy 
                    else Result
                     [ Diag Hint thDoc nullRange
                     , Diag Error
                         ("for '" ++ language_name cid ++
                              "' expected sublogic '" ++
                              sublogicName sub ++
                              "'\n but found sublogic '" ++
                              sublogicName senLog ++
                              "' with signature sublogic '" ++
                              sublogicName sigLog ++ "'") nullRange] Nothing

wrapMapTheory :: Comorphism cid
            lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2
            => cid -> (sign1, [Named sentence1])
                   -> Result (sign2, [Named sentence2])
wrapMapTheory = wrapMapTheoryPossiblyLossy False

mkTheoryMapping :: Monad m => (sign1 -> m (sign2, [Named sentence2]))
                   -> (sign1 -> sentence1 -> m sentence2)
                   -> (sign1, [Named sentence1])
                   -> m (sign2, [Named sentence2])
mkTheoryMapping mapSig mapSen (sign, sens) = do
       (sign', sens') <- mapSig sign
       sens'' <- mapM (mapNamedM (mapSen sign) . unmark) sens
       return (sign', nameAndDisambiguate
         $ map (markSen "SignatureProperty") sens' ++ sens'')

data InclComorphism lid sublogics = InclComorphism
  { inclusion_logic :: lid
  , inclusion_source_sublogic :: sublogics
  , inclusion_target_sublogic :: sublogics }
  deriving (Show, Typeable, Data)

-- | construction of an identity comorphism
mkIdComorphism :: (Logic lid sublogics
                      basic_spec sentence symb_items symb_map_items
                      sign morphism symbol raw_symbol proof_tree) =>
                  lid -> sublogics -> InclComorphism lid sublogics
mkIdComorphism lid sub = InclComorphism
  { inclusion_logic = lid
  , inclusion_source_sublogic = sub
  , inclusion_target_sublogic = sub }

-- | construction of an inclusion comorphism
mkInclComorphism :: (Logic lid sublogics
                           basic_spec sentence symb_items symb_map_items
                           sign morphism symbol raw_symbol proof_tree,
                     Monad m) =>
                    lid -> sublogics -> sublogics
                 -> m (InclComorphism lid sublogics)
mkInclComorphism lid srcSub trgSub =
    if isSubElem srcSub trgSub
    then return InclComorphism
      { inclusion_logic = lid
      , inclusion_source_sublogic = srcSub
      , inclusion_target_sublogic = trgSub }
    else fail ("mkInclComorphism: first sublogic must be a " ++
               "subElem of the second sublogic")

instance (Language lid, Eq sublogics, Show sublogics, SublogicName sublogics)
    => Language (InclComorphism lid sublogics) where
        language_name (InclComorphism lid sub_src sub_trg) =
            let sblName = sublogicName sub_src
                lname = language_name lid
            in if sub_src == sub_trg
               then "id_" ++ lname ++
                    if null sblName then "" else '.' : sblName
               else "incl_" ++ lname ++ ':'
                    : sblName ++ "->" ++ sublogicName sub_trg

instance Logic lid sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol proof_tree =>
         Comorphism (InclComorphism lid sublogics)
          lid sublogics
          basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree
          lid sublogics
          basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree
         where
           sourceLogic = inclusion_logic
           targetLogic = inclusion_logic
           sourceSublogic = inclusion_source_sublogic
           mapSublogic cid subl =
               if isSubElem subl $ inclusion_source_sublogic cid
               then Just subl
               else Nothing
           map_theory _ = return
           map_morphism _ = return
           map_sentence _ _ = return
           map_symbol _ _ = Set.singleton
           constituents cid =
               if inclusion_source_sublogic cid
                      == inclusion_target_sublogic cid
               then []
               else [language_name cid]
           is_model_transportable _ = True
           has_model_expansion _ = True
           is_weakly_amalgamable _ = True
           isInclusionComorphism _ = True

data CompComorphism cid1 cid2 = CompComorphism cid1 cid2
  deriving (Show, Typeable, Data)

instance (Language cid1, Language cid2)
          => Language (CompComorphism cid1 cid2) where
   language_name (CompComorphism cid1 cid2) =
     language_name cid1 ++ ";" ++ language_name cid2

instance (Comorphism cid1
            lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2,
          Comorphism cid2
            lid4 sublogics4 basic_spec4 sentence4 symb_items4 symb_map_items4
                sign4 morphism4 symbol4 raw_symbol4 proof_tree4
            lid3 sublogics3 basic_spec3 sentence3 symb_items3 symb_map_items3
                sign3 morphism3 symbol3 raw_symbol3 proof_tree3)
          => Comorphism (CompComorphism cid1 cid2)
              lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
              sign1 morphism1 symbol1 raw_symbol1 proof_tree1
              lid3 sublogics3 basic_spec3 sentence3 symb_items3 symb_map_items3
              sign3 morphism3 symbol3 raw_symbol3 proof_tree3 where
   sourceLogic (CompComorphism cid1 _) =
     sourceLogic cid1
   targetLogic (CompComorphism _ cid2) =
     targetLogic cid2
   sourceSublogic (CompComorphism cid1 _) =
     sourceSublogic cid1
   mapSublogic (CompComorphism cid1 cid2) sl =
         mapSublogic cid1 sl >>=
           mapSublogic cid2 .
            forceCoerceSublogic (targetLogic cid1) (sourceLogic cid2)
   map_sentence (CompComorphism cid1 cid2) si1 se1 =
         do (si2, _) <- map_sign cid1 si1
            se2 <- map_sentence cid1 si1 se1
            (si2', se2') <- coerceBasicTheory
                (targetLogic cid1) (sourceLogic cid2)
                "Mapping sentence along comorphism" (si2, [makeNamed "" se2])
            case se2' of
                [x] -> map_sentence cid2 si2' $ sentence x
                _ -> error "CompComorphism.map_sentence"

   map_theory (CompComorphism cid1 cid2) ti1 =
         do ti2 <- map_theory cid1 ti1
            ti2' <- coerceBasicTheory (targetLogic cid1) (sourceLogic cid2)
                        "Mapping theory along comorphism" ti2
            wrapMapTheory cid2 ti2'

   map_morphism (CompComorphism cid1 cid2) m1 =
       do m2 <- map_morphism cid1 m1
          m3 <- coerceMorphism (targetLogic cid1) (sourceLogic cid2)
                  "Mapping signature morphism along comorphism" m2
          map_morphism cid2 m3

   map_symbol (CompComorphism cid1 cid2) sig1 = let
     th = map_sign cid1 sig1 in
    case maybeResult th of
     Nothing -> error "failed translating signature"
     Just (sig2', _) -> let
       th2 = coerceBasicTheory
                (targetLogic cid1) (sourceLogic cid2)
                "Mapping symbol along comorphism" (sig2', [])
       in case maybeResult th2 of
           Nothing -> error "failed coercing"
           Just (sig2, _) ->
            \ s1 ->
              let mycast = coerceSymbol (targetLogic cid1) (sourceLogic cid2)
              in Set.unions
                (map (map_symbol cid2 sig2 . mycast)
                 (Set.toList (map_symbol cid1 sig1 s1)))

   extractModel (CompComorphism cid1 cid2) sign pt3 =
     let lid1 = sourceLogic cid1
         lid3 = sourceLogic cid2
     in if language_name lid1 == language_name lid3 then do
         bTh1 <- map_sign cid1 sign
         (sign1, _) <-
           coerceBasicTheory (targetLogic cid1) lid3 "extractModel1" bTh1
         bTh2 <- extractModel cid2 sign1 pt3
         coerceBasicTheory lid3 lid1 "extractModel2" bTh2
     else fail $ "extractModel not implemented for comorphism composition with "
          ++ language_name cid1
   constituents (CompComorphism cid1 cid2) =
      constituents cid1 ++ constituents cid2

   is_model_transportable (CompComorphism cid1 cid2) =
       is_model_transportable cid1 && is_model_transportable cid2

   has_model_expansion (CompComorphism cid1 cid2) =
        has_model_expansion cid1 && has_model_expansion cid2

   is_weakly_amalgamable (CompComorphism cid1 cid2) =
        is_weakly_amalgamable cid1 && is_weakly_amalgamable cid2
   isInclusionComorphism (CompComorphism cid1 cid2) =
       isInclusionComorphism cid1 && isInclusionComorphism cid2

-- * Comorphisms and existential types for the logic graph

-- | Existential type for comorphisms
data AnyComorphism = forall cid lid1 sublogics1
        basic_spec1 sentence1 symb_items1 symb_map_items1
        sign1 morphism1 symbol1 raw_symbol1 proof_tree1
        lid2 sublogics2
        basic_spec2 sentence2 symb_items2 symb_map_items2
        sign2 morphism2 symbol2 raw_symbol2 proof_tree2 .
      Comorphism cid
                 lid1 sublogics1 basic_spec1 sentence1
                 symb_items1 symb_map_items1
                 sign1 morphism1 symbol1 raw_symbol1 proof_tree1
                 lid2 sublogics2 basic_spec2 sentence2
                 symb_items2 symb_map_items2
                 sign2 morphism2 symbol2 raw_symbol2 proof_tree2 =>
      Comorphism cid deriving Typeable -- used for GTheory

instance Eq AnyComorphism where
    a == b = compare a b == EQ

instance Ord AnyComorphism where
  compare (Comorphism cid1) (Comorphism cid2) = compare
     (language_name cid1, constituents cid1)
     (language_name cid2, constituents cid2)
  -- maybe needs to be refined, using comorphism translations?

instance Show AnyComorphism where
  show (Comorphism cid) = language_name cid
    ++ " : " ++ language_name (sourceLogic cid)
    ++ " -> " ++ language_name (targetLogic cid)

instance Pretty AnyComorphism where
  pretty = text . show

-- | compute the identity comorphism for a logic
idComorphism :: AnyLogic -> AnyComorphism
idComorphism (Logic lid) = Comorphism (mkIdComorphism lid (top_sublogic lid))

-- | Test whether a comporphism is the identity
isIdComorphism :: AnyComorphism -> Bool
isIdComorphism (Comorphism cid) = null $ constituents cid

-- * Properties of comorphisms

-- | Test whether a comorphism is model-transportable
isModelTransportable :: AnyComorphism -> Bool
isModelTransportable (Comorphism cid) = is_model_transportable cid

-- | Test whether a comorphism has model expansion
hasModelExpansion :: AnyComorphism -> Bool
hasModelExpansion (Comorphism cid) = has_model_expansion cid

-- | Test whether a comorphism is weakly amalgamable
isWeaklyAmalgamable :: AnyComorphism -> Bool
isWeaklyAmalgamable (Comorphism cid) = is_weakly_amalgamable cid

-- | Tests whether a comorphism is rps or eps

isEps :: AnyComorphism -> Bool
isEps (Comorphism cid) = eps cid

isRps :: AnyComorphism -> Bool
isRps (Comorphism cid) = rps cid


-- | Compose comorphisms
compComorphism :: Monad m => AnyComorphism -> AnyComorphism -> m AnyComorphism
compComorphism (Comorphism cid1) (Comorphism cid2) =
   let l1 = targetLogic cid1
       l2 = sourceLogic cid2
       msg = "ogic mismatch in composition of " ++ language_name cid1
                  ++ " and " ++ language_name cid2
   in
   if language_name l1 == language_name l2 then
      if isSubElem (forceCoerceSublogic l1 l2 $ targetSublogic cid1)
            $ sourceSublogic cid2
       then return $ Comorphism (CompComorphism cid1 cid2)
       else fail $ "Subl" ++ msg ++ " (Expected sublogic "
                          ++ sublogicName (sourceSublogic cid2)
                          ++ " but found sublogic "
                          ++ sublogicName (targetSublogic cid1) ++ ")"
    else fail $ 'L' : msg ++ " (Expected logic "
                          ++ language_name l2
                          ++ " but found logic "
                          ++ language_name l1 ++ ")"
