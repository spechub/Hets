module Persistence.Schema.MappingType where

import Data.List (isPrefixOf)
import Database.Persist.TH

data MappingType = LocalDef | LocalThmOpen | LocalThmProved
                 | GlobalDef | GlobalThmOpen | GlobalThmProved
                 | HidingDef
                 | FreeDef | CofreeDef | NPFreeDef | MinimizeDef
                 | HidingOpen | HidingProved
                 | HidingFreeOpen | HidingCofreeOpen
                 | HidingNPFreeOpen | HidingMinimizeOpen
                 | HidingFreeProved | HidingCofreeProved
                 | HidingNPFreeProved | HidingMinimizeProved
                   deriving Eq

instance Show MappingType where
  show LocalDef = "local_def"
  show LocalThmOpen = "local_thm_open"
  show LocalThmProved = "local_thm_proved"
  show GlobalDef = "global_def"
  show GlobalThmOpen = "global_thm_open"
  show GlobalThmProved = "global_thm_proved"
  show HidingDef = "hiding_def"
  show FreeDef = "free_def"
  show CofreeDef = "cofree_def"
  show NPFreeDef = "np_free_def"
  show MinimizeDef = "minimize_def"
  show HidingOpen = "hiding_open"
  show HidingProved = "hiding_proved"
  show HidingFreeOpen = "hiding_free_open"
  show HidingCofreeOpen = "hiding_cofree_open"
  show HidingNPFreeOpen = "hiding_np_free_open"
  show HidingMinimizeOpen = "hiding_minimize_open"
  show HidingFreeProved = "hiding_free_proved"
  show HidingCofreeProved = "hiding_cofree_proved"
  show HidingNPFreeProved = "hiding_np_free_proved"
  show HidingMinimizeProved = "hiding_minimize_proved"

instance Read MappingType where
  readsPrec _ input
    | show LocalDef `isPrefixOf` input = [(LocalDef, drop (length $ show LocalDef) input)]
    | show LocalThmOpen `isPrefixOf` input = [(LocalThmOpen, drop (length $ show LocalThmOpen) input)]
    | show LocalThmProved `isPrefixOf` input = [(LocalThmProved, drop (length $ show LocalThmProved) input)]
    | show GlobalDef `isPrefixOf` input = [(GlobalDef, drop (length $ show GlobalDef) input)]
    | show GlobalThmOpen `isPrefixOf` input = [(GlobalThmOpen, drop (length $ show GlobalThmOpen) input)]
    | show GlobalThmProved `isPrefixOf` input = [(GlobalThmProved, drop (length $ show GlobalThmProved) input)]
    | show HidingDef `isPrefixOf` input = [(HidingDef, drop (length $ show HidingDef) input)]
    | show FreeDef `isPrefixOf` input = [(FreeDef, drop (length $ show FreeDef) input)]
    | show CofreeDef `isPrefixOf` input = [(CofreeDef, drop (length $ show CofreeDef) input)]
    | show NPFreeDef `isPrefixOf` input = [(NPFreeDef, drop (length $ show NPFreeDef) input)]
    | show MinimizeDef `isPrefixOf` input = [(MinimizeDef, drop (length $ show MinimizeDef) input)]
    | show HidingOpen `isPrefixOf` input = [(HidingOpen, drop (length $ show HidingOpen) input)]
    | show HidingProved `isPrefixOf` input = [(HidingProved, drop (length $ show HidingProved) input)]
    | show HidingFreeOpen `isPrefixOf` input = [(HidingFreeOpen, drop (length $ show HidingFreeOpen) input)]
    | show HidingCofreeOpen `isPrefixOf` input = [(HidingCofreeOpen, drop (length $ show HidingCofreeOpen) input)]
    | show HidingNPFreeOpen `isPrefixOf` input = [(HidingNPFreeOpen, drop (length $ show HidingNPFreeOpen) input)]
    | show HidingMinimizeOpen `isPrefixOf` input = [(HidingMinimizeOpen, drop (length $ show HidingMinimizeOpen) input)]
    | show HidingFreeProved `isPrefixOf` input = [(HidingFreeProved, drop (length $ show HidingFreeProved) input)]
    | show HidingCofreeProved `isPrefixOf` input = [(HidingCofreeProved, drop (length $ show HidingCofreeProved) input)]
    | show HidingNPFreeProved `isPrefixOf` input = [(HidingNPFreeProved, drop (length $ show HidingNPFreeProved) input)]
    | show HidingMinimizeProved `isPrefixOf` input = [(HidingMinimizeProved, drop (length $ show HidingMinimizeProved) input)]
    | otherwise = []

derivePersistField "MappingType"
