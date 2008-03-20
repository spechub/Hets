{- |
Module      :  $Header$
Copyright   :  Heng Jiang, Uni Bremen 2004-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

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
      _ -> do putStrLn "analib error."
              return mResult

trans :: LibEnv -> AnyComorphism -> IO LibEnv
trans libEnv acm = do
    case libEnv_translation libEnv acm of
      Result diags' maybeLE ->
          do putStrLn ("diagnosis : \n" ++
                       (unlines $ map diagWithoutTail diags'))
             if hasErrors diags' then error "error(s) in translation."
              else do
               case maybeLE of
                Just libEnv' -> return libEnv'
                Nothing  -> do putStrLn "no translation"
                               return libEnv
     where diagWithoutTail d = let s = diagString d
                                   len = length s
                               in  take (len-2) s

main :: IO()
main = do
  opts <- getArgs >>= hetcatsOpts
  files <- getArgs
  if length files /= 1 then
      error "usage: TestDGTrans filename"
      else do let file = head files
              res <- process opts file
              showGraph file defaultHetcatsOpts res
  -- return ()

