{- |
Module      :  $Header$
Copyright   :  (c) Klaus Hartke, Uni Bremen 2008
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

-}

module Main where

import Control.Monad (when)
import Data.List (intersperse)
import System.Directory (doesFileExist)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (getContents, hReady, stdin)
import Text.ParserCombinators.Parsec (parse)

import ModalCasl as Casl
import ModalCaslToNuSmvLtl as CaslToLtl
import NuSmv

main :: IO ()

main = do args <- getArgs
          file <- if length args == 1 then doesFileExist (head args)
                                      else return False

          formula <- if file then readFile (head args)
                             else return (unwords args)

          let filename = if file then head args
                                 else "<<arguments>>"

          case parse (Casl.parser CaslToLtl.expr) filename formula of
               Left e1 -> do print e1
                             exitFailure
               Right cf -> case CaslToLtl.convert cf of
                Nothing -> do putStrLn "Not a LTL formula."
                              exitFailure
                Just lf -> do i <- hReady stdin
                              when i $
                                 do contents <- getContents
                                    case parse NuSmv.program "<<input>>"
                                               contents of
                                     Left e2 -> do print e2
                                                   exitFailure
                                     Right model -> print model
                              print lf
