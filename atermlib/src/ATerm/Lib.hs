{- |
Module      :  $Header$
Description :  reexports modules needed for ATC generation
Copyright   :  (c) Klaus Luettich, Uni Bremen 2002-2004
License     :  similar to LGPL, see LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (via imports)

reexports the modules needed for many 'ShATermConvertible'
instances. For converting 'ShATerm's to and from 'String's you'll need
the module "ATerm.ReadWrite" (that depends on
"ATerm.SimpPretty" and "ATerm.Base64").
For more information on ATerms look under
<http://www.asfsdf.org>.
-}

module ATerm.Lib
    ( module ATerm.AbstractSyntax
    , module ATerm.Conversion
    ) where

import ATerm.AbstractSyntax
import ATerm.Conversion
