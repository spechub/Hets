{-# OPTIONS -cpp #-}
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

module VSE.Prove where

import Logic.Prover
import VSE.As
import VSE.Ana
import VSE.ToSExpr
import Common.AS_Annotation
import Common.SExpr
import Common.Utils

import Control.Monad
import Data.Char
import Data.Maybe
import Data.List
import qualified Data.Map as Map
import System.Process
import System.IO
import System.Directory
import Text.ParserCombinators.Parsec
#ifdef TAR_PACKAGE
import qualified Codec.Archive.Tar as Tar
#endif

vseProverName :: String
vseProverName = "VSE"

mkVseProofStatus :: String -> [String] -> Proof_status ()
mkVseProofStatus n axs = (openProof_status n vseProverName ())
   { goalStatus = Proved Nothing
   , usedAxioms = axs }

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

vseErrFile :: String
vseErrFile = "hetsvse.out"

readUntilMatchParen :: ProcessHandle -> Handle -> String -> IO String
readUntilMatchParen = readUntilMatchParenAux 10000

readUntilMatchParenAux :: Int -> ProcessHandle -> Handle -> String -> IO String
readUntilMatchParenAux n cp h str =
  let os = length $ filter (== '(') str
      cs = length $ filter (== ')') str
  in if n < 1 then do
    appendFile vseErrFile $ "readUntilMatchParen failed after\n" ++ str ++ "\n"
    return ""
  else if os == cs && os > 0 then return str
  else do
  mc <- myGetChar cp h
  case mc of
    Wait -> do
      appendFile vseErrFile "waiting for character ...\n"
      readUntilMatchParenAux (n - 1) cp h str
    Stop -> return str
    JustChar c -> readUntilMatchParen cp h $ c : str

myGetChar :: ProcessHandle -> Handle -> IO MaybeChar
myGetChar cp h = catch (fmap JustChar $ hGetChar h) $ \ _ -> do
  ms <- getProcessExitCode cp
  return $ case ms of
    Nothing -> Wait
    Just _ -> Stop

readMyMsg :: ProcessHandle -> Handle -> String -> IO String
readMyMsg = readMyMsgAux 1000

readMyMsgAux :: Int -> ProcessHandle -> Handle -> String -> IO String
readMyMsgAux n cp h expect = if n < 1 then do
    appendFile vseErrFile $ "gave up waiting for: " ++ expect ++ "\n"
    return ""
  else do
  mc <- myGetChar cp h
  case mc of
    Wait -> do
      appendFile vseErrFile "waiting for first character ...\n"
      readMyMsgAux (n - 1) cp h expect
    Stop -> return ""
    JustChar c -> do
      r <- readUntilMatchParen cp h [c]
      let rr = reverse r
      if isPrefixOf (prx expect) $ dropWhile (/= '(') rr
        then return rr else do
        appendFile vseErrFile $ "waiting for '" ++ expect  ++ "' got:\n" ++ rr
          ++ "\ntrying again\n"
        readMyMsgAux (n - 1) cp h expect -- try again

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
parseSymbol = skipWhite
  $ fmap SSymbol $ many1 $ satisfy $ \ c -> not (isSpace c || elem c "()")

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

findState :: SExpr -> Maybe (String, String)
findState sexpr = case sexpr of
  SList (SSymbol "API::SET-SENTENCE" : SSymbol nodeStr :
         SList (SSymbol "API::ASENTENCE" : SSymbol senStr :
                SSymbol "API::OBLIGATION" : SSymbol "API::PROVED" : _) : _)
    | isPrefixOf "API::" nodeStr && isPrefixOf "API::" senStr
    -> Just (drop 5 nodeStr, drop 5 senStr)
  _ -> Nothing

specDir :: String
specDir = "specifications"

allSpecFile :: String
allSpecFile = "all-specifications"

allSpecInDir :: String
allSpecInDir = specDir ++ "/" ++ allSpecFile

#ifdef TAR_PACKAGE
createVSETarFile :: FilePath -> IO ()
createVSETarFile tar = do
  renameFile allSpecFile allSpecInDir
  Tar.create (tar ++ ".tar") "." specDir

moveVSEFiles :: FilePath -> IO ()
moveVSEFiles str = do
  let tarFile = str ++ ".tar"
  hasTarFile <- doesFileExist tarFile
  hasSpecDir <- doesDirectoryExist specDir
  hasAllSpecFile <- doesFileExist allSpecFile
  when (hasSpecDir && hasAllSpecFile) $ do
     createVSETarFile (specDir ++ ".bak")
     removeDirectoryRecursive specDir
  when hasTarFile $ do
    Tar.extract "." tarFile
    renameFile allSpecInDir allSpecFile
#endif

prepareAndCallVSE :: IO (Handle, Handle, ProcessHandle)
prepareAndCallVSE = do
  vseBin <- getEnvDef "HETS_VSE" "hetsvse"
  (inp, out, _, cp) <-
      runInteractiveProcess vseBin ["-std"] Nothing Nothing
  readMyMsg cp out nameP
  return (inp, out, cp)

readFinalVSEOutput :: ProcessHandle -> Handle
                   -> IO (Maybe (Map.Map String [String]))
readFinalVSEOutput cp out = do
  ms <- getProcessExitCode cp
  case ms of
    Just _ -> do
      appendFile vseErrFile "hetsvse unavailable\n"
      return Nothing
    Nothing -> do
      revres <- readRest cp out ""
      let res = reverse revres
      case parse parseSExprs vseErrFile res of
        Right l -> return $ Just $ readLemmas l
        Left e -> do
          print e
          appendFile vseErrFile $ res ++ "\n"
          return Nothing

readLemmas :: [SExpr] -> Map.Map String [String]
readLemmas =
  foldr (\ (node, sen) -> Map.insertWith (++) node [sen]) Map.empty
  . catMaybes . map findState

prove :: String -> Theory VSESign Sentence () -> a -> IO [Proof_status ()]
prove ostr (Theory sig thsens) _freedefs = do
  let str = map (\ c -> if c == '/' then '-' else c) ostr
      oSens = toNamedList thsens
      (fsig, sens) = addUniformRestr sig oSens
      (disAxs, disGoals) = partition isAxiom oSens
      rMap = Map.fromList $ map (\ SenAttr { senAttr = n } ->
                (map toUpper $ transString n, n)) disGoals
#ifdef TAR_PACKAGE
  moveVSEFiles ostr
#endif
  (inp, out, cp) <- prepareAndCallVSE
  sendMyMsg inp $ "(" ++ str ++ ")"
  readMyMsg cp out linksP
  sendMyMsg inp "nil"
  readMyMsg cp out sigP
  sendMyMsg inp $ show $ prettySExpr $ vseSignToSExpr fsig
  readMyMsg cp out lemsP
  sendMyMsg inp $ show $ prettySExpr $ SList $ map (namedSenToSExpr fsig) sens
  ms <- readFinalVSEOutput cp out
#ifdef TAR_PACKAGE
  createVSETarFile ostr
#endif
  case ms of
    Nothing -> return []
    Just lemMap -> return
          $ foldr (\ s r -> case Map.lookup s rMap of
                 Nothing -> r
                 Just n -> mkVseProofStatus n (map senAttr disAxs) : r) []
          $ Map.findWithDefault [] (map toUpper str) lemMap
