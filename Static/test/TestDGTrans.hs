{- |
Module      :  $Header$
Copyright   :  Heng Jiang, Uni Bremen 2004-2006
License     :  GPLv2 or higher, see LICENSE.txt

Test Logic translation for development graphs.
   Follows Sect. IV:4.2 of the CASL Reference Manual.
-}

module Main where

import Logic.Comorphism
import Syntax.AS_Library
import Static.AnalysisLibrary
import Static.DevGraph
import Static.DGTranslation
import Driver.Options
import GUI.ShowGraph
import Comorphisms.CASL2PCFOL
import Comorphisms.CASL2SubCFOL
import Common.Result

import Data.Maybe
import System.Environment

process :: HetcatsOpts -> FilePath -> IO (Maybe (LIB_NAME, LibEnv))
process opts file = do
    mResult <- anaLib opts file
    case mResult of
      Just (libName, gcMap) ->
          do ccomor <- compComorphism (Comorphism CASL2PCFOL)
                                      (Comorphism defaultCASL2SubCFOL)
             gcMap' <- trans gcMap ccomor
             return $ Just (libName, gcMap')
      _ -> fail "analib error."

trans :: LibEnv -> AnyComorphism -> IO LibEnv
trans libEnv acm = do
    case libEnv_translation libEnv acm of
      Result diags' maybeLE -> do
        printDiags 2 diags'
        case maybeLE of
          Just libEnv' -> return libEnv'
          Nothing  -> fail "no translation"

main :: IO ()
main = do
  opts <- getArgs >>= hetcatsOpts
  case infiles opts of
    [hd] -> do
         res <- process opts hd
         showGraph hd opts res
    _ -> error "usage: TestDGTrans filename"


