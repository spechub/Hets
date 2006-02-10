{- |
Module      :  $Header$
Copyright   :  (c) Wiebke Herding, C. Maeder, Uni Bremen 2004-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luettich@tzi.de
Stability   :  provisional
Portability :  portable

printing AS_ConstraintCASL ConstraintCASLSign data types
-}

module ConstraintCASL.Print_AS where

import Common.Id
import Common.Keywords
import Common.Lib.Pretty
import Common.PrettyPrint
import Common.PPUtils
import Common.GlobalAnnotations
import Common.AS_Annotation
import CASL.Print_AS_Basic
import ConstraintCASL.AS_ConstraintCASL
import CASL.AS_Basic_CASL (FORMULA(..))


instance PrettyPrint ConstraintFORMULA where
   printText0 ga s = ptext $ show s
