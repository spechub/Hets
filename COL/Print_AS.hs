{- |
Module      :  $Header$
Copyright   :  (c) Wiebke Herding, C. Maeder, Uni Bremen 2004-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  till@tzi.de
Stability   :  provisional
Portability :  portable

pretty printing
-}

module COL.Print_AS where

import qualified Common.Lib.Set as Set
import qualified Common.Lib.Map as Map
import Common.Lib.Pretty
import Common.PrettyPrint
import Common.PPUtils
import COL.AS_COL
import COL.COLSign

instance PrettyPrint COL_SIG_ITEM where
    printText0 ga (Constructor_items ls _) =
        text (constructorS ++ pluralS ls) <+> semiAnno_text ga ls
    printText0 ga (Observer_items ls _) =
        text observerS <+> semiAnno_text ga ls


instance PrettyPrint COLSign where
    printText0 ga s =
        text constructorS <+> semiT_text ga (Set.toList $ constructors s)
        $$
        text observerS <+> semiT_text ga (Map.toList $ observers s)
