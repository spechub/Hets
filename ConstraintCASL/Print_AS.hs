{- |
Module      :  $Header$
Copyright   :  (c) Wiebke Herding, C. Maeder, Uni Bremen 2004-2006
License     :  GPLv2 or higher

Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

printing AS_ConstraintCASL ConstraintCASLSign data types
-}

module ConstraintCASL.Print_AS where

import Common.Doc
import Common.DocUtils
import ConstraintCASL.AS_ConstraintCASL
import CASL.AS_Basic_CASL ()

instance Pretty ConstraintFORMULA where
   pretty = text . show
