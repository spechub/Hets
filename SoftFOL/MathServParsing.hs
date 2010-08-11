{- |
Module      :  $Header$
Description :  Functions for parsing MathServ output as a MathServResponse
Copyright   :  (c) Rainer Grabbe, DFKI GmbH
License     :  GPLv2 or higher

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  unknown

Functions for parsing MathServ output into a MathServResponse structure.

-}

module SoftFOL.MathServParsing
  ( callMathServ
  , parseMathServOut
  , MathServServices(..)
  , MathServOperationTypes(..)
  , MathServCall(..)
  , MathServResponse(..)
  , MWFoAtpResult(..)
  , MWFormalProof(..)
  , MWStatus(..)
  , FoAtpStatus(..)
  , SolvedStatus(..)
  , UnsolvedStatus(..)
  , MWCalculus(..)
  , MWTimeResource(..)
  ) where

import Common.Utils (getEnvSave, readMaybe)

import Text.XML.Light
import Network.HTTP
import Network.HTTP.HandleStream as S

import Data.Char
import Data.List
import Data.Maybe
import Data.Time (TimeOfDay, timeToTimeOfDay)

-- * Datatypes for MathServ services

data ServerAddr = ServerAddr
    { serverName :: String
    , portNumber :: Int }

instance Show ServerAddr where
    showsPrec _ sAdd =
        (serverName sAdd ++) . showChar ':' . shows (portNumber sAdd)

instance Read ServerAddr where
    readsPrec _ s = let (n,portRest) = span (/= ':') s
                        (portS,rest) = if null portRest
                                      then ("", "")
                                      else span isDigit $ tail portRest
                        portN = fromMaybe 8080 $ readMaybe portS
                    in [(ServerAddr { serverName = n, portNumber = portN },
                        rest)]

defaultServer :: ServerAddr
defaultServer = ServerAddr
  { serverName = "mathserv.informatik.uni-bremen.de"
  , portNumber = 8080 }


{- |
  Record type for all needed data to do a MathServ call.
-}
data MathServCall = MathServCall {
    -- | Selected MathServ service
    mathServService :: MathServServices,
    -- | Selected MathServ operation
    mathServOperation :: MathServOperationTypes,
    -- | Problem to prove in TPTP format
    problem :: String,
    -- | Time limit
    proverTimeLimit :: Int,
    -- | Extra options
    extraOptions :: Maybe String
  }

{- |
  MathServ services to select.
-}
data MathServServices =
  -- | Broker service
    Broker
  -- | Vampire service
  | VampireService
  deriving Show

{- |
  MathServ operation to select. These are only common types and will be
  translated into correct MathServOperations.
-}
data MathServOperationTypes =
  -- | stands for ProveProblemOpt
    ProblemOpt
  -- | stands for ProveProblemChoice
  | ProblemChoice
  -- | stands for ProveTPTPProblem or ProveTPTPProblemWithOptions
  | TPTPProblem
  -- | stands for ProveProblem
  | Problem
  deriving Show

{- |
  A MathServ response structure to be filled by parsing all rdf-objects
  returned by MathServ.
-}
data MathServResponse =
       MathServResponse { foAtpResult  :: Either String MWFoAtpResult,
                          timeResource :: MWTimeResource
                          } deriving (Eq, Ord, Show)

data MWFoAtpResult =
       MWFoAtpResult { proof        :: MWFormalProof,
                       outputStr    :: String,
                       systemStatus :: MWStatus,
                       systemStr    :: String,
                       time         :: MWTimeResource
-- defined, but not needed?
--                       timeRes     :: MWTimeResource,
                       } deriving (Eq, Ord, Show)

data MWFormalProof =
       TstpCnfRefutation { formalProof :: String,
                           proofOf     :: MWProvingProblem,
                           calculus    :: MWCalculus,
                           axioms      :: String
                           } deriving (Eq, Ord, Show)

emptyMWFormalProof :: MWFormalProof
emptyMWFormalProof = TstpCnfRefutation
  { formalProof = ""
  , proofOf = UnknownProvingProblem
  , calculus = UnknownCalc
  , axioms = "" }


data MWStatus =
       MWStatus { solved   :: Bool,
                  foAtpStatus :: FoAtpStatus
                  } deriving (Eq, Ord, Show)

--- data MWStatus = MWStatus Bool SystemStatus deriving (Eq, Ord, Show)

data FoAtpStatus =
       Solved SolvedStatus
     | Unsolved UnsolvedStatus
     deriving (Eq, Ord, Show,Read)

data SolvedStatus =
       CounterEquivalent
     | CounterSatisfiable
     | CounterTheorem
     | Equivalent
     | NoConsequence
     | Satisfiable
     | TautologousConclusion
     | Tautology
     | Theorem
     | Unsatisfiable
     | UnsatisfiableConclusion
     deriving (Eq, Ord, Show,Read)

data UnsolvedStatus =
       Assumed
     | GaveUp
     | InputError
     | MemoryOut
     | ResourceOut
     | Timeout
     | Unknown
     | NoStatus
     deriving (Eq, Ord, Show,Read)

data MWProvingProblem =
       TstpFOFProblem
     | TstpProblem
     | UnknownProvingProblem
     deriving (Eq, Ord, Show)

data MWCalculus =
       AprosNDCalculus
     | OmegaNDCalculus
     | EpResCalc
     | SpassResCalc
     | StandardRes
     | OtterCalc
     | VampireResCalc
     | ZenonCalc
     | UnknownCalc
     deriving (Eq, Ord, Show, Read)

data MWTimeResource =
       MWTimeResource { cpuTime       :: TimeOfDay,
                        wallClockTime :: TimeOfDay
                        } deriving (Eq, Ord, Show)

toCData :: String -> CData
toCData s = blank_cdata { cdData = s }

mkProveProblemElem :: MathServCall -- ^ needed data to do a MathServ call
                   -> Element -- ^ resulting XML element
mkProveProblemElem call = let extOpt = extraOptions call in
     unode ("Prove" ++ show (mathServOperation call)
           ++ if isJust extOpt then "WithOptions" else "")
       ([ unode "in0" $ toCData $ problem call
        , unode "in1" $ toCData $ show $ proverTimeLimit call]
        ++ case extOpt of
             Nothing -> []
             Just o2 -> [unode "in2" $ toCData o2])

-- ** functions for handling with soap

soapenvS :: String
soapenvS = "soapenv"

bodyS :: String
bodyS = "Body"

soapEnvQName :: String -> QName
soapEnvQName s = (unqual s) { qPrefix = Just soapenvS }

xmlnsQName :: String -> QName
xmlnsQName s = (unqual s) { qPrefix = Just "xmlns" }

envUri :: String
envUri = "http://schemas.xmlsoap.org/soap/envelope/"

bodyQ :: QName
bodyQ = (soapEnvQName bodyS) { qURI = Just envUri }

mkEnvelope :: Element -> Element
mkEnvelope = add_attrs
  [ Attr (unqual "encodingStyle") "http://schemas.xmlsoap.org/soap/encoding/"
  , Attr (xmlnsQName "xsd") "http://www.w3.org/2001/XMLSchema"
  , Attr (xmlnsQName soapenvS) envUri
  ] . node (soapEnvQName "Envelope")

mkSoapRequest :: MathServCall -> ServerAddr -> Request_String
mkSoapRequest call serverPort =
  let b = showElement $ mkEnvelope $ node bodyQ $ mkProveProblemElem call
      r0 = postRequest $ "http://" ++ show serverPort ++ "/axis/services/"
           ++ show (mathServService call)
      r1 = insertHeader (HdrCustom "SOAPAction") "" r0 { rqBody = b }
      r2 = replaceHeader HdrUserAgent "hets" r1
      r3 = replaceHeader HdrContentLength (show $ length b) r2
  in insertHeader HdrContentType "text/xml" r3

testQnameSuffix :: String -> QName -> Bool
testQnameSuffix s q = let l = qName q in
  isNothing (qPrefix q) && isPrefixOf "Prove" l && isSuffixOf s l

unpackSoapEnvelope :: Either String String -> Either String String
unpackSoapEnvelope rsp = case rsp of
  Left s -> Left s
  Right r -> case parseXMLDoc r of
    Nothing -> Left $ "server returned illegal xml\n" ++ r
    Just x -> case filterElementName (== bodyQ) x of
     Nothing -> Left $ "no soap Body found\n" ++ ppElement x
     Just b -> case filterElementName (testQnameSuffix "Response") b of
      Nothing -> Left $ "no Prove Response found\n" ++ ppElement b
      Just t -> case filterElementName (testQnameSuffix "Return") t of
       Nothing -> Left $ "no Prove Return value found\n" ++ ppElement t
       Just v -> case strContent v of
        "" -> Left $ "no returned content found\n" ++ ppElement v
        ts -> Right ts

-- ** functions for handling with MathServ services

{- |
  Sends a problem in TPTP format to MathServ using a given time limit.
  Either MathServ output is returned or a simple error message (no XML).
-}
callMathServ :: MathServCall -- ^ needed data to do a MathServ call
             -> IO (Either String String )
             -- ^ Left (SOAP error) or Right (MathServ output or error message)
callMathServ call =
    do
       serverPort <- getEnvSave defaultServer "HETS_MATHSERVE" readMaybe
       let r = mkSoapRequest call serverPort
       res <- S.simpleHTTP r
       return $ case res of
                  Left mErr -> Left $ show mErr
                  Right resp -> unpackSoapEnvelope $ Right $ rspBody resp

isMWnode :: String -> QName -> Bool
isMWnode s q = qName q == s && qPrefix q == Just "mw"

getElemText :: String -> Element -> String
getElemText s = maybe "" strContent . filterElementName (isMWnode s)

{- |
  Full parsing of RDF-objects returned by MathServ and putting the results
  into a MathServResponse data-structure.
-}
parseMathServOut :: Either String String
       -- ^ Left (SOAP error) or Right (MathServ output or error message)
                 -> IO (Either String MathServResponse)
       -- ^ parsed rdf-objects in record
parseMathServOut = return . parseResponse

parseResponse :: Either String String -> Either String MathServResponse
parseResponse eMathServOut = do
   mathServOut <- eMathServOut
   case parseXMLDoc mathServOut of
     Nothing -> Left "illegal rdf xml tree"
     Just rdf -> do
        let mr = case parseFailure rdf of
              Just str -> Left str
              Nothing -> parseResult rdf
        t <- parseTimeResource rdf
        return MathServResponse
          { foAtpResult = mr
          , timeResource = t }

parseFailure :: Element -> Maybe String
parseFailure e = case filterElementName (isMWnode "Failure") e of
  Nothing -> Nothing
  Just f -> Just $ getElemText "message" f

parseResult :: Element -> Either String MWFoAtpResult
parseResult rdf = case filterElementName (isMWnode "FoAtpResult") rdf of
       Nothing -> Left "no FoAtpResult found"
       Just e -> do
         stat <- parseStatus e
         tm <- case filterElementName (isMWnode "time") e of
           Nothing -> Left "no time element found"
           Just t -> parseTimeResource t
         let pr = parseProof e
             out = getElemText "output" e
             sys = getElemText "system" e
         return MWFoAtpResult
           { proof = pr
           , outputStr = out
           , systemStatus = stat
           , systemStr = sys
           , time = tm }

parseProof :: Element -> MWFormalProof
parseProof e = case filterElementName
  (\ q -> isMWnode "proof" q || isMWnode "saturation" q) e of
  Nothing -> emptyMWFormalProof
  Just pr -> case filterElementName (\ q -> isMWnode "TstpCnfRefutation" q
    || isMWnode "TstpCnfSaturation" q) pr of
    Nothing -> emptyMWFormalProof
    Just p -> let
        fp0 = getElemText "formalProof" p
        fp = if null fp0 then getElemText "formalSaturation" p else fp0
        prob = case getProblem p "proofOf" of
          UnknownProvingProblem -> getProblem p "saturationOf"
          pa -> pa
        cal = case filterElementName (isMWnode "calculus") p of
                Nothing -> UnknownCalc
                Just c -> getCalcAttr c
        axs = getElemText "axioms" p
       in TstpCnfRefutation
       { formalProof = fp
       , proofOf = prob
       , calculus = cal
       , axioms = axs }

isRdfResource :: QName -> Bool
isRdfResource q = qName q == "resource" && qPrefix q == Just "rdf"

{- |
  Removes first part of string until @#@ (including @#@).
-}
getAnchor :: String -- ^ in-string
          -> String -- ^ part of string after first occurence of @#@
getAnchor s = case dropWhile (/= '#') s of
    [] -> []
    _ : r -> r

getRdfResource :: Element -> String
getRdfResource e = case filter (not . null) . map (getAnchor . attrVal)
  . filter (isRdfResource . attrKey) $ elAttribs e of
  str : _ -> str
  _ -> ""

getProblem :: Element -> String -> MWProvingProblem
getProblem e s = case filterElementName (isMWnode s) e of
  Nothing -> UnknownProvingProblem
  Just po -> getProblemAttr po

getProblemAttr :: Element -> MWProvingProblem
getProblemAttr e = let str = getRdfResource e in
  if isPrefixOf "generated_tstp_fof_problem" str then TstpFOFProblem
  else if isPrefixOf "TstpProblem" str then TstpProblem
  else UnknownProvingProblem

parseStatus :: Element -> Either String MWStatus
parseStatus e = case filterElementName (isMWnode "status") e of
  Nothing -> Left "no status found"
  Just s -> let str = getRdfResource s in case readMaybe str of
       Just sol -> Right $ MWStatus True $ Solved sol
       Nothing -> case readMaybe str of
         Just usol -> Right $ MWStatus False $ Unsolved usol
         Nothing -> Left $ "Could not classify status of proof: " ++ str

elem2Time :: Element -> Either String TimeOfDay
elem2Time e = let s = strContent e in
  case readMaybe s of
    Just x -> Right $ timeToTimeOfDay $ realToFrac $ (x :: Double) / 1000
    Nothing -> Left $ "cannot read time string: " ++ s

parseTimeResource :: Element -> Either String MWTimeResource
parseTimeResource e = case filterElementName (isMWnode "TimeResource") e of
  Nothing -> Left "no time resource found"
  Just tr -> do
    ct <- case filterElementName (isMWnode "cpuTime") tr of
            Nothing -> Left "no cpu time found"
            Just t -> elem2Time t
    wt <- case filterElementName (isMWnode "wallClockTime") tr of
            Nothing -> Left "no wall clock time found"
            Just t -> elem2Time t
    return MWTimeResource
      { cpuTime = ct
      , wallClockTime = wt }

{- |
  Filters @_@ out of a String and upcases each letter after a @_@.
-}
filterUnderline :: Bool  -- ^ upcase next letter
                -> String -- ^ input String
                -> String -- ^ un-dashed output String
filterUnderline b st = case st of
    []  -> []
    h : r -> case h of
             '_' -> filterUnderline True r
             _ -> (if b then toUpper h else h) : filterUnderline False r

getCalcAttr :: Element -> MWCalculus
getCalcAttr e = let str = filterUnderline True $ getRdfResource e in
  case readMaybe str of
    Just c -> c
    Nothing -> UnknownCalc
