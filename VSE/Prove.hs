{- |
Module      :  $Header$
Description :  Interface to the VSE prover
Copyright   :  (c) C. Maeder, DFKI 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  needs POSIX

call an adaption of VSE II to hets
-}

module VSE.Prove (vse) where

import Logic.Prover
import VSE.As
import VSE.Ana
import VSE.ToSExpr
import Common.SExpr

import Control.Monad
import Data.List
import System.Process
import System.IO

vse :: Prover VSESign Sentence () ()
vse = mkProverTemplate "VSE" () prove

nameP :: String
nameP = "SPECIFICATION-NAMES"

linksP :: String
linksP = "IN-LINKS"

sigP :: String
sigP = "SIG"

lemsP :: String
lemsP = "LEMMABASE"

prx :: String -> String
prx = ("(API::GET-" ++)

readUntilMatchParen :: Handle -> String -> IO (String)
readUntilMatchParen cp str =
  let os = length $ filter (== '(') str
      cs = length $ filter (== ')') str
  in if os == cs && os > 0 then return str
  else do
  mc <- myGetChar cp
  case mc of
    Nothing -> readUntilMatchParen cp str
    Just c -> readUntilMatchParen cp $ c : str

myGetChar :: Handle -> IO (Maybe Char)
myGetChar h = catch (fmap Just $ hGetChar h) $ \ _ -> return Nothing

readMyMsg :: Handle -> String -> IO ()
readMyMsg cp expect = do
  mc <- myGetChar cp
  case mc of
    Nothing -> readMyMsg cp expect
    Just c -> do
    r <- readUntilMatchParen cp [c]
    if isPrefixOf (prx expect) $ dropWhile (/= '(') $ reverse r then return ()
      else putStrLn $ "an error occurred when waiting for: " ++ expect

sendMyMsg :: Handle -> String -> IO ()
sendMyMsg cp str = do
  hPutStrLn cp str
  hFlush cp

readRest :: ProcessHandle -> Handle -> String -> IO String
readRest cp out str = do
  mc <- myGetChar out
  case mc of
    Nothing -> do
       ms <- getProcessExitCode cp
       case ms of
         Nothing -> readRest cp out str
         _ -> return str
    Just c -> readRest cp out $ c : str

prove :: String -> Theory VSESign Sentence () -> IO [Proof_status ()]
prove str (Theory sig thsens) = do
  (inp, out, _, cp) <-
      runInteractiveProcess "hetsvse" ["-std"] Nothing Nothing
  readMyMsg out nameP
  sendMyMsg inp $ "(" ++ str ++ ")"
  readMyMsg out linksP
  sendMyMsg inp "nil"
  readMyMsg out sigP
  let (fsig, sens) = addUniformRestr sig $ toNamedList thsens
  sendMyMsg inp $ show $ prettySExpr $ vseSignToSExpr fsig
  readMyMsg out lemsP
  sendMyMsg inp $ show $ prettySExpr $ SList $ map (namedSenToSExpr fsig) sens
  res <- readRest cp out ""
  putStrLn "--begin--"
  putStrLn $ reverse res
  putStrLn "--end--"
  return []
