{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2003
Licence     :  All rights reserved.

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable
    
name sentences in CASL, Logic and elsewhere
-}

module Common.Named where

import Common.PrettyPrint
import Common.Lib.Pretty
import Common.Print_AS_Annotation
import Common.AS_Annotation

data Named s = NamedSen { senName  :: String,
                          sentence :: s }
	       deriving (Eq, Show)

instance PrettyPrint s => PrettyPrint (Named s) where
    printText0 ga (NamedSen{senName = label, sentence = s}) =
	printText0 ga s <+> printText0 ga (Label [label] [])
