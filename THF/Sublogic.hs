{- |
Module      :  $Header$
Description :  Sublogics for THF
Copyright   :  (c) Jonathan von Schroeder, DFKI Bremen 2012
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Jonathan von Schroeder <j.von_schroeder@dfki.de>
Stability   :  experimental
Portability :  non-portable (via Logic.Logic)

Sublogics for THF
-}

module THF.Sublogic
  ( sublogics_all,
    THFSl(..),
    slToInt,
    slFromInt )
where

data THFSl = THFX | THF | THF0 deriving (Ord,Show,Eq)

slToInt :: THFSl -> Int
slToInt THFX = 3
slToInt THF  = 2
slToInt THF0 = 1

slFromInt :: Int -> THFSl
slFromInt 3 = THFX
slFromInt 2 = THF
slFromInt 1 = THF0
slFromInt i = if i < 1 then THF0 else THFX

sublogics_all :: [THFSl]
sublogics_all = [THF,THF0] 
