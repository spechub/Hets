{- |
Module      :  $Header$
Description :  reexports modules needed for ATC generation
Copyright   :  (c) Klaus Luettich, Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (via imports)

reexports the modules needed for many 'ShATermConvertible'
instances. For converting 'ShATerm's to and from 'String's you'll need
the module "Common.ATerm.ReadWrite" (that depends on
"Common.SimpPretty"). For more information on ATerms look under
<http://www.asfsdf.org>.
-}

module Common.ATerm.Lib
    ( module Common.ATerm.AbstractSyntax
    , module Common.ATerm.Conversion
    ) where

import Common.ATerm.AbstractSyntax
import Common.ATerm.Conversion
import Common.ATerm.ConvInstances ()
