{- |
Module      :  $Header$
Description :  Central datastructures for development graphs
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2006
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable(Logic)

Fixed CASL signature needed for translation of CommonLogic to CASL
-}

module CommonLogic.CASLSig where

import qualified CASL.Sign as CSign
import qualified Driver.AnaLib as AnaLib
import qualified Driver.Options as Options
import qualified Data.Map as Map
import qualified System.IO.Unsafe as SysUnsafe
import qualified Static.DevGraph as DevGraph
import qualified Logic.Grothendieck as Grothendieck
import qualified Common.ExtSign as ExtSign
import qualified Logic.Coerce as Coerce
import qualified CASL.Logic_CASL as CASL

baseCASLSig :: CSign.CASLSign
baseCASLSig = sig
  where Just (_,lib) = SysUnsafe.unsafePerformIO $ AnaLib.anaLib Options.defaultHetcatsOpts "CommonLogic/CommonLogic.casl" 
        dgraph = head $ Map.elems lib
        gsig = head $ Map.elems $ DevGraph.sigMap dgraph
        Just esig = case gsig of
                      Grothendieck.G_sign lid extsign _  
                        -> Coerce.coerceSign lid CASL.CASL "error: CommonoLogic.CASLSig" extsign
        ExtSign.ExtSign sig _ = esig
