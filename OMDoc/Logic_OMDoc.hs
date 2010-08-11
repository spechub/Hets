{- |
Module      :  $Header$
Description :  Rudimentary Logic-instances for OMDoc
Copyright   :  (c) Hendrik Iben, Uni Bremen 2005-2007
License     :  GPLv2 or higher

Maintainer  :  hiben@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable

Logic and related instances for OMDoc.
-}
module OMDoc.Logic_OMDoc where

import Logic.Logic
import qualified OMDoc.OMDocInterface as OMDoc
import OMDoc.ATC_OMDoc ()

import Common.Id
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import qualified Data.Map as Map

data OMDoc_PUN = OMDoc_PUN

type OMDoc_Sign = OMDoc.Theory

type OMDoc_Morphism = (OMDoc.Inclusion, OMDoc.Theory, OMDoc.Theory)

instance Show OMDoc_PUN where
  show _ = "OMDoc-PUN"

instance Language OMDoc_PUN where
  description _ = "OMDoc-PUN (possible utter nonsense). Logic to deal with OMDoc."

instance Syntax OMDoc_PUN () () ()

instance Category OMDoc_Sign OMDoc_Morphism where
  ide s =
    (
        OMDoc.TheoryInclusion
          {
              OMDoc.inclusionFrom = OMDoc.mkSymbolRef (OMDoc.theoryId s)
            , OMDoc.inclusionTo = OMDoc.mkSymbolRef (OMDoc.theoryId s)
            , OMDoc.inclusionMorphism = Nothing
            , OMDoc.inclusionId = Just "identity"
            , OMDoc.inclusionConservativity = OMDoc.CNone
          }
      , s
      , s
    )
  composeMorphisms (m1, s1, _) (m2, _, t2) =
        let
          im1' = OMDoc.inclusionMorphism m1
          im2' = OMDoc.inclusionMorphism m2
          compim =
            case (im1', im2') of
              (Nothing, Nothing) -> Nothing
              (Just _, Nothing) -> im1'
              (Nothing, Just _) -> im2'
              (Just im1, Just im2) ->
                Just
                  (
                    OMDoc.Morphism
                      {
                          OMDoc.morphismId = Just $
                            (fromMaybe "Unnamed" (OMDoc.morphismId im1))
                            ++ "_comp_"
                            ++ (fromMaybe "Unnamed" (OMDoc.morphismId im2))
                        , OMDoc.morphismHiding =
                            (OMDoc.morphismHiding im1)
                            ++
                            (OMDoc.morphismHiding im2)
                        , OMDoc.morphismBase =
                            (OMDoc.morphismBase im1)
                            ++
                            (OMDoc.morphismBase im2)
                        , OMDoc.morphismRequations =
                            (OMDoc.morphismRequations im1)
                            ++
                            (OMDoc.morphismRequations im2)
                      }
                  )
        in
          return $ (m1 { OMDoc.inclusionMorphism = compim }, s1, t2)
  dom (_, s, _) = s
  cod (_, _, t) = t
  legal_mor (m, s, t) =
    (OMDoc.inclusionFrom m) == (OMDoc.mkSymbolRef (OMDoc.theoryId s))
    &&
    (OMDoc.inclusionTo m) == (OMDoc.mkSymbolRef (OMDoc.theoryId t))

instance Sentences OMDoc_PUN () OMDoc_Sign OMDoc_Morphism OMDoc.Symbol where
  sym_of OMDoc_PUN s =
      singletonList
      $ Set.fromList $ map (\ (OMDoc.CSy s') -> s')
            $ filter OMDoc.isSymbol (OMDoc.theoryConstitutives s)
  symmap_of OMDoc_PUN (m, s1, s2) =
    case OMDoc.inclusionMorphism m of
      Nothing -> Map.empty
      (Just im) ->
        foldl
          (\smap r ->
            case r of
              (OMDoc.MTextOM omobj1, OMDoc.MTextOM omobj2) ->
                case (omobj1, omobj2) of
                  (OMDoc.OMObject (OMDoc.OMES oms1), OMDoc.OMObject (OMDoc.OMES oms2)) ->
                    let
                      name1 = OMDoc.omsName oms1
                      name2 = OMDoc.omsName oms2
                      msymbol1 =
                        case
                          filter
                            (\c ->
                              case c of
                                (OMDoc.CSy symbol) ->
                                  OMDoc.symbolId symbol == name1
                                _ ->
                                  False
                            )
                            (OMDoc.theoryConstitutives s1)
                        of
                          [] -> Nothing
                          ((OMDoc.CSy symbol):_) -> Just symbol
                          _ -> error "OMDoc.Logic_OMDoc.symmap_of"
                      msymbol2 =
                        case
                          filter
                            (\c ->
                              case c of
                                (OMDoc.CSy symbol) ->
                                  OMDoc.symbolId symbol == name2
                                _ ->
                                  False
                            )
                            (OMDoc.theoryConstitutives s2)
                        of
                          [] -> Nothing
                          ((OMDoc.CSy symbol):_) -> Just symbol
                          _ -> error "OMDoc.Logic_OMDoc.symmap_of"
                      newmap =
                        case (msymbol1, msymbol2) of
                          (Nothing, _) -> smap
                          (_, Nothing) -> smap
                          (Just symbol1, Just symbol2) ->
                            Map.insert symbol1 symbol2 smap
                    in
                      newmap
                  _ -> smap
              _ ->
                smap
          )
          Map.empty
          (OMDoc.morphismRequations im)
  sym_name OMDoc_PUN s =
    -- real Id's are saved as Presentation-Elements...
    stringToId $ OMDoc.symbolId s

instance StaticAnalysis OMDoc_PUN () () () () OMDoc_Sign OMDoc_Morphism OMDoc.Symbol () where
  symbol_to_raw OMDoc_PUN _ = ()
  id_to_raw OMDoc_PUN _ = ()
  matches OMDoc_PUN _ _ = False
  empty_signature OMDoc_PUN =
    OMDoc.Theory
    {
        OMDoc.theoryId = "empty"
      , OMDoc.theoryConstitutives = []
      , OMDoc.theoryPresentations = []
      , OMDoc.theoryComment = Nothing
    }

is_subsig :: OMDoc.Theory -> OMDoc.Theory -> Bool
is_subsig s1 s2 =
    -- This currently only checks symbols. Maybe ADTs should also be checked...
    let
      s1sym =
        foldl
          (\s con ->
            case con of
              (OMDoc.CSy sym) ->
                Set.insert sym s
              _ ->
                s
          )
          (Set.empty)
          (OMDoc.theoryConstitutives s1)
      s2sym =
        foldl
          (\s con ->
            case con of
              (OMDoc.CSy sym) ->
                Set.insert sym s
              _ ->
                s
          )
          (Set.empty)
          (OMDoc.theoryConstitutives s2)
    in
     Set.isSubsetOf s1sym s2sym

instance Logic OMDoc_PUN () () () () () OMDoc_Sign OMDoc_Morphism OMDoc.Symbol () ()
