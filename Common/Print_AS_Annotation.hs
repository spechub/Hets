{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Christian Maeder, Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

This module contains all instances of PrettyPrint for AS_Annotation.hs
-}

module Common.Print_AS_Annotation where

import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.PrettyPrint
import Common.Doc
import Common.DocUtils

instance PrettyPrint Annotation where
    printText0 ga = toText ga . annoDoc

fromText :: PrettyPrint a => GlobalAnnos -> a -> Doc
fromText ga = literalDoc . printText0 ga

instance (PrettyPrint a) => PrettyPrint (Annoted a) where
    printText0 ga = toText ga . printAnnoted (fromText ga)

instance PrettyPrint s => PrettyPrint (Named s) where
    printText0 ga = toText ga . printAnnoted (fromText ga) . fromLabelledSen
