{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  meader@tzi.de
Stability   :  experimental
Portability :  non-portable(uses programatica)

test translation from Haskell to Isabelle
-}

module Main where

import System.Environment
import Data.Char

import Text.ParserCombinators.Parsec
import Common.Result
import Common.AnnoState
import Common.AS_Annotation
import Common.GlobalAnnotations

import Comorphisms.Hs2HOLCF

import Isabelle.IsaPrint
import Isabelle.IsaSign as IsaSign

import Haskell.HatAna as HatAna
import Haskell.HatParser

pickParser :: Continuity -> AParser () (IsaSign.Sign, [Named IsaSign.Sentence])
pickParser c = do
   b <- hatParser
   let res@(Result _ m) = do
          (_, _, sig, sens) <- hatAna (b, HatAna.emptySign, emptyGlobalAnnos)
          transTheory c sig sens
   case m of
      Nothing -> fail $ show res
      Just x -> return x

main :: IO ()
main = do
  let err = "command line input error: first argument must be"
            ++ " either h (HOL) or hc (HOLCF)."
  l <- getArgs
  case l of
    [] -> putStrLn err
    c : fs -> let elm = elem $ map toLower c in
        mapM_ (process (if elm ["h", "hol"] then NotCont
                   else if elm ["hc", "holcf"] then IsCont
                   else error err)) fs

process :: Continuity -> FilePath -> IO ()
process c fn = do
  putStrLn $ "translating " ++ show fn ++ " to " ++ case c of
             IsCont -> "HOLCF"
             NotCont -> "HOL"
  s <- readFile fn
  ld <- getEnv "HETS_LIB"
  let ds = dropWhile isSpace
      s1 = ds s
      ns = not . isSpace
      (front, rest) = span ns s1
      s2 = if front == "module" then dropWhile ns $ ds rest else s1
  case runParser (pickParser c) (emptyAnnos ()) fn s2 of
    Right (sig, hs) -> do
      let tn = takeWhile (/= '.')
               (reverse . takeWhile ( \ x -> x /= '/') $ reverse fn) ++ "_"
                ++ case c of
                     IsCont -> "hc"
                     NotCont -> "h"
          doc = printIsaTheory tn ld sig hs
          thyFile = tn ++ ".thy"
      putStrLn $ "writing " ++ show thyFile
      writeFile thyFile (shows doc "\n")
    Left err -> putStrLn $ show err
