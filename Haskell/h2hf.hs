{- |
Module      :  $Id$
Description :  a test driver for Haskell to Isabelle HOLCF translations
Copyright   :  (c) Christian Maeder, Uni Bremen 2002-2005
License     :  GPLv2 or higher

Maintainer  :  Christian.Maeder@dfki.de
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
import Common.ExtSign

import Comorphisms.Hs2HOLCF

import Isabelle.IsaPrint
import Isabelle.IsaSign as IsaSign

import Haskell.HatAna as HatAna
import Haskell.HatParser

pickParser :: (Continuity, Bool)
           -> AParser () (IsaSign.Sign, [Named IsaSign.Sentence])
pickParser c = do
   b <- hatParser
   let res@(Result _ m) = do
          (_, ExtSign sig _, sens) <-
              hatAna (b, HatAna.emptySign, emptyGlobalAnnos)
          transTheory (fst c) (snd c) sig sens
   case m of
      Nothing -> fail $ show res
      Just x -> return x

main :: IO ()
main = do
  let err = "command line input error: first argument must be"
            ++ " either h (HOL), hc (HOLCF), mh (HOL with theory morphisms),"
            ++ " mhc (HOLCF with theory morphisms)."
  l <- getArgs
  case l of
    [] -> putStrLn err
    c : fs -> let elm = elem $ map toLower c in
        mapM_ (process (if elm ["h", "hol"] then (NotCont,False)
                   else if elm ["hc", "holcf"] then (IsCont True,False)
                   else if elm ["mh", "mhol"] then (NotCont,True)
                   else if elm ["mhc", "mholcf"] then (IsCont True,True)
                   else error err)) fs

process :: (Continuity,Bool) -> FilePath -> IO ()
process c fn = do
  putStrLn $ "translating " ++ show fn ++ " to " ++ case c of
             (IsCont _,False) -> "HOLCF"
             (NotCont,False) -> "HOL"
             (IsCont _,True) -> "HOLCF with theory morphisms"
             (NotCont,True) -> "HOL with theory morphisms"
  s <- readFile fn
  case runParser (pickParser c) (emptyAnnos ()) fn s of
    Right (sig, hs) -> do
      let tn = takeWhile (/= '.')
               (reverse . takeWhile ( \ x -> x /= '/') $ reverse fn) ++ "_"
                ++ case c of
                     (IsCont _,False) -> "hc"
                     (NotCont,False) -> "h"
                     (IsCont _,True) -> "mhc"
                     (NotCont,True) -> "mh"
          nsig = sig {theoryName = tn}
          doc = printIsaTheory tn nsig hs
          thyFile = tn ++ ".thy"
      putStrLn $ "writing " ++ show thyFile
      writeFile thyFile (shows doc "\n")
    Left err -> putStrLn $ show err
