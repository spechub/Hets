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

import ChildProcess

import Control.Monad
import Data.List

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

readUntilMatchParen :: ChildProcess -> String -> IO (String)
readUntilMatchParen cp str =
  let os = length $ filter (== '(') str
      cs = length $ filter (== ')') str
  in if os == cs then return str
  else do
    r <- readMsg cp
    readUntilMatchParen cp $ str ++ r

readMyMsg :: ChildProcess -> String -> IO ()
readMyMsg cp expect = do
  s <- readMsg cp
  r <- readUntilMatchParen cp s
  if isPrefixOf (prx expect) r then return ()
    else putStrLn $ "an error occurred when waiting for: " ++ expect

sendMyMsg :: ChildProcess -> String -> IO ()
sendMyMsg cp str = sendMsg cp (str ++ "\n")

prove :: String -> Theory VSESign Sentence () -> IO [Proof_status ()]
prove str (Theory sig thsens) = do
  cp <- newChildProcess "hetsvse" [arguments ["-std"], linemode False]
  readMyMsg cp nameP
  sendMyMsg cp $ "(" ++ str ++ ")"
  readMyMsg cp linksP
  sendMyMsg cp "nil"
  readMyMsg cp sigP
  let (fsig, sens) = addUniformRestr sig $ toNamedList thsens
  sendMyMsg cp $ show $ prettySExpr $ vseSignToSExpr fsig
  readMyMsg cp lemsP
  sendMyMsg cp $ show $ prettySExpr $ SList $ map (namedSenToSExpr fsig) sens
  waitForChildProcess cp
  return []
