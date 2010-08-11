{- |
Module      :  $EmptyHeader$
Description :  <optional short description entry>
Copyright   :  (c) <Authors or Affiliations>
License     :  GPLv2 or higher

Maintainer  :  <email>
Stability   :  unstable | experimental | provisional | stable | frozen
Portability :  portable | non-portable (<reason>)

<optional description>
-}
module Main where

import Control.Monad (when)
import Data.List (intersperse)
import System.Directory (doesFileExist)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (getContents, hWaitForInput, stdin)
import Text.ParserCombinators.Parsec (parse)

import ModalCasl as Casl
import ModalCaslToNuSmvLtl as CaslToLtl
import NuSmv as NuSmv

main :: IO ()

main = do args <- getArgs
          file <- if length args == 1 then doesFileExist (args !! 0)
                                      else return False

          formula <- if file then readFile (args !! 0)
                             else return (concat (intersperse " " args))

          let filename = if file then args !! 0
                                 else "<<arguments>>"

          case parse (Casl.parser CaslToLtl.expr) filename formula of
               Left e1  -> do putStrLn (show e1)
                              exitFailure

               Right cf -> case CaslToLtl.convert cf of
                                Nothing -> do putStrLn "Not a LTL formula."
                                              exitFailure

                                Just lf -> do i <- hWaitForInput stdin 0
                                              when i $ do contents <- getContents
                                                          case parse NuSmv.program "<<input>>" contents of
                                                               Left e2     -> do putStrLn (show e2)
                                                                                 exitFailure

                                                               Right model -> do putStrLn (show model)
                                              putStrLn (show lf)
