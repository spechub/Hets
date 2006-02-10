{-
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2005
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  luettichtzi.de
Stability   :  provisional
Portability :  portable

pretty print AS of CASL_DL in ASCII
-}

module CASL_DL.Print_AS where

-- import Common.Id
import Common.Lib.Pretty
import Common.PrettyPrint

import CASL.Print_AS_Basic ()
import CASL_DL.AS_CASL_DL

			     
instance PrettyPrint DL_FORMULA where
    printText0 ga (Cardinality ct pn varTerm natTerm _) = 
        text (case ct of
              CMin   -> minCardinalityS
              CMax   -> maxCardinalityS
              CExact -> cardinalityS)
        <> brackets (printText0 ga pn)
        <> parens (printText0 ga varTerm<>comma<+>printText0 ga natTerm)