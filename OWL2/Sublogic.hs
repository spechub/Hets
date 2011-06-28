{- |
Module      :  $Header$
Description :  Sublogics for OWL
Copyright   :  (c) Dominik Luecke, Uni Bremen 2008
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Here is the place where the class Logic is instantiated for OWL DL.
__SROIQ__
-}

module OWL2.Sublogic
    ( OWLSub 
     , sl_top
    ) where

type OWLSub = ()
sl_top :: OWLSub
sl_top = ()
