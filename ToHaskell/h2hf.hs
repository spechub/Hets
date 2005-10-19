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

import System.Environment

import Text.ParserCombinators.Parsec
import Common.Result
import Common.AnnoState
import Common.AS_Annotation
import Common.GlobalAnnotations

import Common.Lib.Pretty

import Comorphisms.Hs2HOLCF

import Isabelle.CreateThy
import Isabelle.IsaSign as IsaSign

import Haskell.HatAna as HatAna
import Haskell.HatParser

hParser :: AParser () (IsaSign.Sign, [Named IsaSign.Sentence])
hParser = do 
   b <- hatParser
   let res@(Result _ m) = do 
          (_, _, sig, sens) <- hatAna (b, HatAna.emptySign, emptyGlobalAnnos)
          transTheory sig sens
   case m of 
      Nothing -> error $ show res
      Just x -> return x

main :: IO ()
main = getArgs >>= mapM_ process

process :: FilePath -> IO ()
process fn = do s <- readFile fn
                s1 <- return $ dropWhile (\x -> x == '\n' || x == ' ') s
                s2 <- return $ if takeWhile (/= ' ') s1 == "module" 
                               then dropWhile (/= '\n') s1 else s1  
                let r = runParser hParser (emptyAnnos ()) fn s2  
                case r of 
                       Right (sig, hs) -> let 
                         tn = dropWhile (== '"') $ (takeWhile (/= '.') 
                              $ reverse (takeWhile (\x -> x /= '/') $ reverse 
                              $ show fn)) ++ "_theory" 
                         doc = text "theory" <+> text tn <+> text "=" $$
                            createTheoryText sig hs
                         in writeFile (tn ++ ".thy") (shows doc "\n")
                       Left err -> putStrLn $ show err
