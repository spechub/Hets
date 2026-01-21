{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./Logic/HDef.hs
Copyright   :  (c) R. Diaconescu, IMAR, 2018
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  mscodescu@gmail.com
Stability   :  provisional
Portability :  non-portable(Grothendieck)

Definitions of hybridizations of logics and comorphisms, with their parameters.

-}


module Logic.HDef where

import Data.Typeable
import Common.Id
import Common.Doc
import Common.DocUtils
import Logic.SemConstr

-- DrIFT command:
{-! global: GetRange !-}

data HLogicDef = HLogicDef {
                  newHybridLogicName :: String,
                  baseLogicName :: (String, Maybe String), -- the second string is the sublogic
                  isExtension :: Bool,
                  semConstrs :: [SemanticConstraint],
                  varKinds :: [(String, Maybe Token)]
                 } deriving (Show, Typeable, Eq, Ord)

instance GetRange HLogicDef where
    getRange = getRange . show
    rangeSpan = rangeSpan . show
    
instance Pretty HLogicDef where
  pretty = printHLogicDef

printHLogicDef :: HLogicDef -> Doc
printHLogicDef hld = 
  text "logic" $+$ text (newHybridLogicName hld)

data HComDef = HComDef {
               newHComName :: String,
               baseComName :: String,
               sourceHLogic :: String
               } deriving (Show, Typeable, Eq, Ord)

instance GetRange HComDef where
    getRange = getRange . show
    rangeSpan = rangeSpan . show
    
instance Pretty HComDef where
  pretty = printHComDef

printHComDef :: HComDef -> Doc
printHComDef hcd = 
  text "comorphism" $+$ text (newHComName hcd)
