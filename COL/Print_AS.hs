{- |
Module      :  $Header$
Description :  Pretty printing for COL
Copyright   :  (c) Wiebke Herding, C. Maeder, Uni Bremen 2004-2006
License     :  GPLv2 or higher

Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

pretty printing
-}

module COL.Print_AS where

import qualified Data.Set as Set
import qualified Data.Map as Map
import Common.Doc
import Common.DocUtils
import CASL.ToDoc
import COL.AS_COL
import COL.COLSign

instance Pretty COL_SIG_ITEM where
    pretty = printCOL_SIG_ITEM

printCOL_SIG_ITEM :: COL_SIG_ITEM -> Doc
printCOL_SIG_ITEM csi = case csi of
    Constructor_items ls _ -> keyword (constructorS ++ pluralS ls) <+>
        semiAnnos idDoc ls
    Observer_items ls _ -> keyword observerS <+>
        semiAnnos (printPair idDoc (printMaybe pretty)) ls

instance Pretty COLSign where
    pretty = printCOLSign

printCOLSign :: COLSign -> Doc
printCOLSign s = keyword constructorS <+>
    (fsep $ punctuate semi $ map idDoc (Set.toList $ constructors s))
    $+$ keyword observerS <+>
    (fsep $ punctuate semi $
      map (printPair idDoc pretty) (Map.toList $ observers s))
