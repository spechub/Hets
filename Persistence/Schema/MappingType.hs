{-# LANGUAGE TemplateHaskell #-}
module Persistence.Schema.MappingType where

import Data.List (isPrefixOf)
import Database.Persist.TH

data MappingType = LocalDef | LocalThmOpen | LocalThmProved
                 | GlobalDef | GlobalThmOpen | GlobalThmProved
                 | HidingDef
                 | FreeDef | CofreeDef | NPFreeDef | MinimizeDef
                 | HidingOpen | HidingProved
                 | FreeOpen | CofreeOpen | NPFreeOpen | MinimizeOpen
                 | FreeProved | CofreeProved | NPFreeProved | MinimizeProved
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
  show FreeOpen = "free_open"
  show CofreeOpen = "cofree_open"
  show NPFreeOpen = "np_free_open"
  show MinimizeOpen = "minimize_open"
  show FreeProved = "free_proved"
  show CofreeProved = "cofree_proved"
  show NPFreeProved = "np_free_proved"
  show MinimizeProved = "minimize_proved"

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
    | show FreeOpen `isPrefixOf` input = [(FreeOpen, drop (length $ show FreeOpen) input)]
    | show CofreeOpen `isPrefixOf` input = [(CofreeOpen, drop (length $ show CofreeOpen) input)]
    | show NPFreeOpen `isPrefixOf` input = [(NPFreeOpen, drop (length $ show NPFreeOpen) input)]
    | show MinimizeOpen `isPrefixOf` input = [(MinimizeOpen, drop (length $ show MinimizeOpen) input)]
    | show FreeProved `isPrefixOf` input = [(FreeProved, drop (length $ show FreeProved) input)]
    | show CofreeProved `isPrefixOf` input = [(CofreeProved, drop (length $ show CofreeProved) input)]
    | show NPFreeProved `isPrefixOf` input = [(NPFreeProved, drop (length $ show NPFreeProved) input)]
    | show MinimizeProved `isPrefixOf` input = [(MinimizeProved, drop (length $ show MinimizeProved) input)]
    | otherwise = []

derivePersistField "MappingType"
