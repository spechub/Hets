{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  meader@tzi.de
Stability   :  experimental
Portability :  non-portable(programatica and isabelle) 

test translation from Haskell to Isabelle
-}

module Main where

import Debug.Trace
import System.Environment

import Text.ParserCombinators.Parsec
import Common.Result
import Common.AnnoState
import Common.AS_Annotation
import Common.GlobalAnnotations

import Comorphisms.Hs2HOLCF
import Comorphisms.Hs2HOLCFaux

import Isabelle.CreateThy
import Isabelle.IsaSign as IsaSign

import Haskell.HatAna as HatAna
import Haskell.HatParser

pickParser :: Continuity -> AParser () (IsaSign.Sign, [Named IsaSign.Sentence])
pickParser c = case c of 
  NotCont -> kParser 
  IsCont -> hParser

hParser :: AParser () (IsaSign.Sign, [Named IsaSign.Sentence])
hParser = do 
   b <- hatParser
   let res@(Result _ m) = do 
          (_, _, sig, sens) <- hatAna (b, HatAna.emptySign, emptyGlobalAnnos)
          transTheory IsCont sig sens
   case m of 
      Nothing -> error $ show res
      Just x -> return x

kParser :: AParser () (IsaSign.Sign, [Named IsaSign.Sentence])
kParser = do 
   b <- hatParser
   let res@(Result _ m) = do 
          (_, _, sig, sens) <- hatAna (b, HatAna.emptySign, emptyGlobalAnnos)
          transTheory NotCont sig sens
   case m of 
      Nothing -> error $ show res
      Just x -> return x

main :: IO ()
main = do (a:as) <- getArgs 
          b      <- return $ case a of 
                             "hol" -> NotCont
                             "HOL" -> NotCont
                             "h" -> NotCont
                             "holcf" -> IsCont
                             "HOLCF" -> IsCont
                             "hc" -> IsCont
                             _ -> error "command line input error: first argument must be either h (HOL) or hc (HOLCF)."
          trace (show b ++ "\n") $ mapM_ (process b) as

process :: Continuity -> FilePath -> IO ()
process k fn = do s <- readFile fn
                  s1 <- return $ dropWhile (\x -> x == '\n' || x == ' ') s
                  ld <- getEnv "HETS_LIB"  --
                  s2 <- trace (show "h2hf running. Writing filename_hc.thy (HOLCF) - filename_h.thy (HOL)") $ 
                          return $ if takeWhile (/= ' ') s1 == "module" 
                               then dropWhile (/= '\n') s1 else s1  
                  let r = runParser (pickParser k) (emptyAnnos ()) fn s2  
                  case r of 
                       Right (sig, hs) -> let 
                         tn = dropWhile (== '"') $ (takeWhile (/= '.') 
                              $ reverse (takeWhile (\x -> x /= '/') $ reverse 
                              $ show fn)) ++ (case k of 
                                           IsCont -> "_hc"
                                           NotCont -> "_h")
                         doc = printIsaTheory tn ld sig hs   --
                         in writeFile (tn ++ ".thy") (shows doc "\n")
                       Left err -> putStrLn $ show err
