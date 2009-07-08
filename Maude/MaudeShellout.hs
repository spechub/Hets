#!/usr/bin/env runhaskell

module Main where

import System.IO
import System.Process

import Maude.AS_Maude
import Maude.Sign
import Maude.Printing

import Common.Id (Token)
import Data.Set

import Common.Lib.Rel

import Debug.Trace

maude_cmd :: String
maude_cmd = "/Applications/maude-darwin/maude.intelDarwin -interactive"

wait_threshold = 100

main :: IO Sign -- ()
main = do
    (hIn, hOut, hErr, hProcess) <- runInteractiveCommand maude_cmd
    hPutStrLn hIn "in /Users/adrian/Hets/Maude/hets.prj"
    hPutStrLn hIn ("(fmod A is sorts Foo Nat A B C D . subsort Foo < Nat . " ++
                  "subsort A < B < C < Foo Nat . op a : Foo -> Foo . " ++
                  "op a : Foo Foo -> Foo [assoc] . endfm)")
    hClose hIn
    sOutput <- hGetContents hOut
    let stringSpec = getSpec sOutput
    let spec = read stringSpec :: Spec
    let sign = fromSpec spec
    return sign --- (sign2maude sign)
    -- waitForProcess hProcess

