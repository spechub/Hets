{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Christian Maeder and Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luettich@tzi.de
Stability   :  provisional
Portability :  portable

This classes needs to be instantiated for every datastructure in AS_*
   for LaTeX and isolatin-1 pretty printing.
-}

module Common.PrettyPrint
    ( showPretty
    , PrettyPrint(..)
    , PrintLaTeX(..)
    , printText
    , isChar
    )
    where

import Common.Id
import Common.Lib.Pretty
import Common.GlobalAnnotations

-- | This type class allows latex printing of instantiated data types
class PrintLaTeX a where
    printLatex0 :: GlobalAnnos -> a -> Doc

-- | This type class allows pretty printing of instantiated data types
class PrettyPrint a where
    printText0 :: GlobalAnnos -> a -> Doc

-- | printText uses empty global annotations
printText :: PrettyPrint a  => a -> Doc
printText = printText0 emptyGlobalAnnos

-- | a more pretty alternative for shows
showPretty :: PrettyPrint a => a -> ShowS
showPretty = shows . printText

-- moved instance from Id.hs (to avoid cyclic imports via GlobalAnnotations)
instance PrettyPrint Token where
    printText0 _ = text . tokStr

isChar :: Token -> Bool
isChar t = take 1 (tokStr t) == "\'"

instance PrettyPrint Id where
    printText0 _ = text . show

instance PrettyPrint () where
    printText0 _ga _s = empty

instance PrintLaTeX () where
    printLatex0 _ga _s = empty

instance (PrettyPrint a, PrettyPrint b) => PrettyPrint (Either a b) where
    printText0 ga (Left x) = printText0 ga x
    printText0 ga (Right x) = printText0 ga x

instance (PrintLaTeX a, PrintLaTeX b) => PrintLaTeX (Either a b) where
    printLatex0 ga (Left x) = printLatex0 ga x
    printLatex0 ga (Right x) = printLatex0 ga x

instance PrettyPrint a => PrettyPrint (Maybe a) where
    printText0 ga (Just x) = printText0 ga x
    printText0 _ Nothing = empty

instance PrintLaTeX a => PrintLaTeX (Maybe a) where
    printLatex0 ga (Just x) = printLatex0 ga x
    printLatex0 _ Nothing = empty
