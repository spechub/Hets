{- |
Module      :  ./ExtModal/Print_AS.hs
Copyright   :  
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  
Stability   :  experimental
Portability :  

printing AS_ExtModal ExtModalSign data types
-}

module ExtModal.Print_AS where

import Common.Id
import Common.Keywords
import qualified Data.Map as Map
import Common.AS_Annotation
import Common.Doc
import Common.DocUtils
import ExtModal.AS_ExtModal
import ExtModal.ExtModalSign
import CASL.AS_Basic_CASL (FORMULA(..))
import CASL.ToDoc


