{- |
Module      :  $Header$
Copyright   :  (c) Klaus Luettich, Uni Bremen 2004
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Predefined global annotations for CASL_DL.
-}

module CASL_DL.PredefinedGlobalAnnos (caslDLGlobalAnnos) where

import Text.ParserCombinators.Parsec

import Common.AS_Annotation (Annotation)
import Common.AnnoParser (annotations)

caslDLGlobalAnnos :: [Annotation]
caslDLGlobalAnnos =
    case parse annotations "CASL_DL.PredefinedGlobalAnnos"
         caslDLGlobalAnnos_str of
    Right l -> l
    Left err -> error $ "Internal Error: " ++ show err

caslDLGlobalAnnos_str :: String
caslDLGlobalAnnos_str =
    "%number(__@@__)%\n" ++
    "%string(emptyString, __:@:__)%\n"
