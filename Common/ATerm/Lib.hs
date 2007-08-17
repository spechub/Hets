{- |
Module      :  $Header$
Description :  reexports modules needed for ATC generation
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (via imports)

reexports the modules needed for many 'ShATermConvertible' instances
-}

module Common.ATerm.Lib
    ( module Common.ATerm.AbstractSyntax
    , module Common.ATerm.Conversion
    , module Common.ATerm.ConvInstances,
    ) where

import Common.ATerm.AbstractSyntax
import Common.ATerm.Conversion
import Common.ATerm.ConvInstances
