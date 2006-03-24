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
import Common.Lib.Pretty
import qualified Common.Doc as Doc

instance PrettyPrint Annotation where
    printText0 ga = Doc.toText ga . Doc.annoDoc

-- -------------------------------------------------------------------------
-- utilies
-- -------------------------------------------------------------------------

printAnnotationList_Text0 :: GlobalAnnos -> [Annotation] -> Doc
printAnnotationList_Text0 ga = Doc.toText ga . Doc.printAnnotationList

fromText :: PrettyPrint a => GlobalAnnos -> a -> Doc.Doc
fromText ga = Doc.literalDoc . printText0 ga

instance (PrettyPrint a) => PrettyPrint (Annoted a) where
    printText0 ga = Doc.toText ga . Doc.printAnnoted (fromText ga)

instance PrettyPrint s => PrettyPrint (Named s) where
    printText0 ga = printText0 ga . sentence
-- other stuff must be printed logic dependent

-- | print sentence with label and non-axioms with implied annotation
printLabelledSen :: PrettyPrint s => GlobalAnnos -> Named s -> Doc
printLabelledSen ga s =
    text " . " <> printText0 ga (Doc.fromLabelledSen s)
