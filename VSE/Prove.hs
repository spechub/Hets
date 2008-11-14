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
import Common.AS_Annotation
import Common.SExpr
import Common.Utils

import Control.Monad
import Data.Char
import Data.List
import qualified Data.Map as Map
import System.Process
import System.IO
import Text.ParserCombinators.Parsec

vseProverName :: String
vseProverName = "VSE"

openVseProofStatus :: String -> Proof_status ()
openVseProofStatus n = openProof_status n vseProverName ()

vse :: Prover VSESign Sentence VSEMor () ()
vse = mkProverTemplate vseProverName () prove

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

data MaybeChar = Wait | Stop | JustChar Char

readUntilMatchParen :: ProcessHandle -> Handle -> String -> IO String
readUntilMatchParen cp h str =
  let os = length $ filter (== '(') str
      cs = length $ filter (== ')') str
  in if os == cs && os > 0 then return str
  else do
  mc <- myGetChar cp h
  case mc of
    Wait -> readUntilMatchParen cp h str
    Stop -> return str
    JustChar c -> readUntilMatchParen cp h $ c : str

myGetChar :: ProcessHandle -> Handle -> IO MaybeChar
myGetChar cp h = catch (fmap JustChar $ hGetChar h) $ \ _ -> do
  ms <- getProcessExitCode cp
  return $ case ms of
    Nothing -> Wait
    Just _ -> Stop

readMyMsg :: ProcessHandle -> Handle -> String -> IO ()
readMyMsg cp h expect = do
  mc <- myGetChar cp h
  case mc of
    Wait -> readMyMsg cp h expect
    Stop -> return ()
    JustChar c -> do
      r <- readUntilMatchParen cp h [c]
      unless (isPrefixOf (prx expect) $ dropWhile (/= '(') $ reverse r)
        $ putStrLn $ "an error occurred when waiting for: " ++ expect

sendMyMsg :: Handle -> String -> IO ()
sendMyMsg cp str = catch (hPutStrLn cp str >> hFlush cp) $ \ _ -> return ()

readRest :: ProcessHandle -> Handle -> String -> IO String
readRest cp out str = do
  mc <- myGetChar cp out
  case mc of
    Wait -> readRest cp out str
    Stop -> return str
    JustChar c -> readRest cp out $ c : str

parseSymbol :: Parser SExpr
parseSymbol = skipWhite $ do
  fmap SSymbol $ many1 $ satisfy $ \ c -> not (isSpace c || elem c "()")

parseList :: Parser SExpr
parseList = do
  skipWhite $ char '('
  l <- many parseSExpr
  skipWhite $ char ')'
  return $ SList l

parseSExpr :: Parser SExpr
parseSExpr = parseList <|> parseSymbol

skipWhite :: Parser a -> Parser a
skipWhite p = do
  a <- p
  spaces
  return a

skipJunk :: Parser ()
skipJunk = skipMany $ satisfy (/= '(')

parseSExprs :: Parser [SExpr]
parseSExprs = do
  skipJunk
  sepEndBy parseSExpr skipJunk

findState :: String -> SExpr -> [String] -> [String]
findState str sexpr l = case sexpr of
  SList (SSymbol "API::SET-SENTENCE" : SSymbol nodeStr :
         SList (SSymbol "API::ASENTENCE" : SSymbol senStr :
                SSymbol "API::OBLIGATION" : SSymbol "API::PROVED" : _) : _)
    | nodeStr == "API::" ++ map toUpper str && isPrefixOf "API::" senStr
    -> drop 5 senStr : l
  _ -> l

prove :: String -> Theory VSESign Sentence () -> IO [Proof_status ()]
prove ostr (Theory sig thsens) = do
  let str = map (\ c -> if c == '/' then '-' else c) ostr
      oSens = toNamedList thsens
      (fsig, sens) = addUniformRestr sig oSens
      (disAxs, disGoals) = partition isAxiom oSens
      rMap = Map.fromList $ map (\ SenAttr { senAttr = n } ->
                (map toUpper $ transString n, n)) disGoals
      errfile = "hetvse.out"
  vseBin <- getEnvDef "HETS_VSE" "hetsvse"
  (inp, out, _, cp) <-
      runInteractiveProcess vseBin ["-std"] Nothing Nothing
  readMyMsg cp out nameP
  sendMyMsg inp $ "(" ++ str ++ ")"
  readMyMsg cp out linksP
  sendMyMsg inp "nil"
  readMyMsg cp out sigP
  sendMyMsg inp $ show $ prettySExpr $ vseSignToSExpr fsig
  readMyMsg cp out lemsP
  sendMyMsg inp $ show $ prettySExpr $ SList $ map (namedSenToSExpr fsig) sens
  ms <- getProcessExitCode cp
  case ms of
    Just _ -> do
      putStrLn $ vseBin ++ " unavailable"
      return []
    Nothing -> do
      revres <- readRest cp out ""
      let res = reverse revres
      case parse parseSExprs errfile res of
        Right l -> return
          $ foldr (\ s r -> case Map.lookup s rMap of
                 Nothing -> r
                 Just n -> (openVseProofStatus n)
                   { goalStatus = Proved Nothing
                   , usedAxioms = map senAttr disAxs } : r) []
          $ foldr (findState str) [] l
        Left e -> do
          print e
          writeFile errfile res
          return []
