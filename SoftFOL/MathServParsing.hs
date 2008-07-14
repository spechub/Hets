{- |
Module      :  $Header$
Description :  Functions for parsing MathServ output as a MathServResponse
Copyright   :  (c) Rainer Grabbe
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  rainer25@informatik.uni-bremen.de
Stability   :  provisional
Portability :  needs POSIX

Functions for parsing MathServ output into a MathServResponse structure.

-}

module SoftFOL.MathServParsing where

import SoftFOL.MathServCommunication
import Common.Utils (getEnvSave)

import Network.URI
import Network.Service
import Org.Xmlsoap.Schemas.Soap.Envelope

import Text.Regex
import Text.XML.HXT.Aliases
import Text.XML.HXT.Parser hiding (when)
import Text.XML.HXT.XPath

import Data.Char (toUpper, isDigit)
import Data.List
import Data.Maybe
import Data.Time (TimeOfDay, timeToTimeOfDay)

import GHC.Read

-- * Datatypes for MathServ services

data ServerAddr = ServerAddr {
     serverName :: String,
     portNumber :: Int
                             }

instance Show ServerAddr where
    showsPrec _ sAdd =
        (serverName sAdd ++) . showChar ':' . shows (portNumber sAdd)

instance Read ServerAddr where
    readsPrec _ s = let (n,portRest) = span (/= ':') s
                        (port,rest) = if null portRest
                                      then ("", "")
                                      else span isDigit $ tail portRest
                        portN = if null port
                                then 8080
                                else either (const 8080) id
                                         (readEither port)
                    in [(ServerAddr {serverName = n,
                                   portNumber = portN },
                        rest)]

defaultServer :: ServerAddr
defaultServer = ServerAddr {
        serverName = "mathserv.informatik.uni-bremen.de",
        portNumber = 8080
                           }


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
  deriving (Show)

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
                       resultFor    :: MWProvingProblem,
                       outputStr    :: String,
                       saturation   :: String,
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


-- ** functions for handling with MathServ services

{- |
  To check whether the selected MathServ operation is known and can be executed
  by the selected MathServ service. It returns the resulting SOAP operation.
-}
mkProveProblem :: MathServCall -- ^ needed data to do a MathServ call
               -> MathServOperations -- ^ resulting MathServOperations
mkProveProblem call =
    case (mathServService call) of
     VampireService -> case (mathServOperation call) of
          TPTPProblem -> maybe ProveTPTPProblem{in0=(problem call),
                                                in1=(proverTimeLimit call)}
                               (ProveTPTPProblemWithOptions (problem call)
                                                    (proverTimeLimit call))
                               (extraOptions call)
          Problem     -> ProveProblem (problem call) (proverTimeLimit call)
          _           -> error $ "unknown Operation for service Vampire\n"++
                       "known operations: ProveProblem, ProveTPTPProblem"
     Broker -> case (mathServOperation call) of
         ProblemOpt    -> ProveProblemOpt (problem call)
                                          (proverTimeLimit call)
         ProblemChoice -> ProveProblemChoice (problem call)
                                             (proverTimeLimit call)
         _ -> error $ "unknown Operation for service Broker\n" ++
                "known operations: ProveProblemOpt, ProveProblemChoice"

-- * MathServ Interfacing Code

makeEndPoint :: String -> Maybe HTTPTransport
makeEndPoint uriStr = maybe Nothing
                            (\ uri -> Just $ HTTPTransport
                                      { httpEndpoint = uri
                                      , httpSOAPAction = Just nullURI})
                            (parseURI uriStr)

{- |
  Sends a problem in TPTP format to MathServ using a given time limit.
  Either MathServ output is returned or a simple error message (no XML).
-}
callMathServ :: MathServCall -- ^ needed data to do a MathServ call
             -> IO (Either String String)
             -- ^ Left (SOAP error) or Right (MathServ output or error message)
callMathServ call =
    do
       serverPort <- getEnvSave defaultServer "HETS_MATHSERVE" readEither
       maybe (return $ Left $ "MathServe not running!")
             (\ endPoint -> do
                 res <- soapCall endPoint $ mkProveProblem call
                 case res :: Either SimpleFault MathServOutput of
                  Left mErr -> do
                    return $ Left $ faultstring mErr
                  Right resp -> do
                    return $ Right $ getResponse resp
             )
             $ makeEndPoint $
                "http://" ++ show serverPort ++ "/axis/services/" ++
                  show (mathServService call)

xpathTag :: String -> String
xpathTag vtag = "//mw:*[local-name()='" ++ vtag ++ "']"

{- |
  Full parsing of RDF-objects returned by MathServ and putting the results
  into a MathServResponse data-structure.
-}
parseMathServOut :: Either String String
       -- ^ Left (SOAP error) or Right (MathServ output or error message)
                 -> IO (Either String MathServResponse)
       -- ^ parsed rdf-objects in record
parseMathServOut eMathServOut =
   case eMathServOut of
   Left errStr -> return $
                  Left ("MathServe/SOAP Error:\n" ++ errStr ++
                        "\nPlease contact " ++
                        "<hets-devel@informatik.uni-bremen.de>")
   Right mathServOut -> do
    mtrees <- parseXML mathServOut
    let rdfTree = maybe emptyRoot head mtrees
        failStr = getMaybeXText failureXPath rdfTree

    return $ Right (MathServResponse {
             foAtpResult = maybe (Right $ parseFoAtpResult rdfTree)
                                 Left failStr
             ,timeResource = parseTimeResource rdfTree })
    where
      failureXPath = xpathTag "Failure" ++ xpathTag "message"

{- |
  Parses an XmlTree for a FoAtpResult object on first level. If existing,
  all values of such an object are recursively parsed from underlying XmlTree.
  All found objects are put into a MWFoAtpResult data structure.
-}
parseFoAtpResult :: XmlTree -- ^ XML tree to parse (should be MathServ output)
                 -> MWFoAtpResult -- ^ parsed Result node
parseFoAtpResult rdfTree =
    MWFoAtpResult { proof        = parseProof nextTree,
                    resultFor    = parseProvingProblem nextTree,
                    outputStr    = getXText outputXPath nextTree,
                    saturation   = getXText saturationXPath nextTree,
                    systemStatus = parseStatus nextTree,
                    systemStr    = getXText systemXPath nextTree,
                    time         = parseTimeResource $ head $
                                     getXPath timeXPath nextTree }
    where
      nextTree = case getXPath atpResultXPath rdfTree of
        [] -> emptyRoot
        h : _ -> h
      atpResultXPath = xpathTag "FoAtpResult"
      outputXPath = xpathTag "output"
      saturationXPath = xpathTag "saturation"
      systemXPath = xpathTag "system"
      timeXPath = xpathTag "time"


{- |
  Parses an XmlTree for a FormalProof object on first level. If existing,
  all values of such an object are recursively parsed from underlying XmlTree.
  All found objects are put into a MWFormalProof data structure.
-}
parseProof :: XmlTree -- ^ XML tree to parse
           -> MWFormalProof -- ^ parsed Formal Proof node
parseProof rdfTree =
-- !! to be completed (recognition of used MWFormalProof's name)
    TstpCnfRefutation { formalProof = getXText formalProofXPath nextTree,
                        proofOf     = parseProvingProblem nextTree,
                        calculus    = parseCalculus nextTree,
                        axioms      = getXText axiomsXPath nextTree }
    where
      nextTree = case getXPath proofXPath rdfTree of
        [] -> emptyRoot
        h : _ -> h
      proofXPath = xpathTag "proof" ++ "/mw:*[1]"
      axiomsXPath = xpathTag "axioms"
      formalProofXPath = xpathTag "formalProof"

xpathTagAttr :: String -> String
xpathTagAttr vtag = xpathTag vtag ++ "/attribute::rdf:*"

{- |
  Parses an XmlTree for a ProvingProblem object on first level.
  Currently only TstpFofProblem can be classified. An empty or non-existing
  problem object will be classified a TstpFofProblem, too. Other occuring
  ProvingProblems will cause an exception.
-}
parseProvingProblem :: XmlTree -- ^ XML tree to parse
                    -> MWProvingProblem -- ^ Parsed Proving Problem node
parseProvingProblem rdfTree =
    let prob = getAnchor $ getXText problemXPath rdfTree
    in  case (matchRegex (mkRegex "generated_tstp_fof_problem") prob) of
          Nothing -> UnknownProvingProblem
          _       -> TstpFOFProblem
    where
      problemXPath = xpathTagAttr "proofOf"

{- |
  Parses an XmlTree for a Calculus object on first level.
  Currently seven different Calculus objects can be classified.
  Other objects (also empty or non-existing ones) will cause an exception.
-}
parseCalculus :: XmlTree -- ^ XML tree to parse
              -> MWCalculus -- ^ parsed Calculus node
parseCalculus rdfTree =
    either (\_ -> UnknownCalc) id
           (readEither (filterUnderline False calc) :: Either String MWCalculus)
    where
      calculusXPath = xpathTagAttr "calculus"
      calc = (getAnchor $ getXText calculusXPath rdfTree)

{- |
  Parses an XmlTree for a Status object on first level.
  Currently 18 different Status objects can be classified.
  Other objects (also empty or non-existing ones) will cause an exception.
  The status is differentiated into solved unsolved by the object itself.
-}
parseStatus :: XmlTree -- ^ XML tree to parse
            -> MWStatus -- ^ parsed Status node
parseStatus rdfTree =
    let foAtp =
          either (\_ ->
                       either (error $ "Could not classify status of proof: "
                                         ++ statusStr)
                         Unsolved
                         (readEither statusStr :: Either String UnsolvedStatus))
                 Solved
                 ((readEither statusStr) :: Either String SolvedStatus)
    in MWStatus {solved      = case foAtp of
                                 Solved _   -> True
                                 Unsolved _ -> False,
                 foAtpStatus = foAtp}
    where
      statusXPath = xpathTagAttr "status"
      statusStr = (getAnchor $ getXText statusXPath rdfTree)

{- |
  Parses an XmlTree for a TimeResource object on first level. If existing,
  cpuTime and wallClockTime are parsed and returned in MWTimeResource record.
-}
parseTimeResource :: XmlTree -- ^ XML tree to parse
                  -> MWTimeResource -- ^ parsed time resource with
                                    --   cpuTime and wallClockTime
parseTimeResource rdfTree =
    MWTimeResource {
      cpuTime       =  prse cpuTimeString,
      wallClockTime =  prse wallClockTimeString }
    where
      prse x = timeToTimeOfDay $ realToFrac
               $ (read x :: Double) / 1000
      cpuTimeString = getXText cpuTimeXPath rdfTree
      wallClockTimeString = getXText wallClockTimeXPath rdfTree

      timeResXPath = xpathTag "TimeResource"
      cpuTimeXPath = timeResXPath ++ xpathTag "cpuTime"
      wallClockTimeXPath =
          timeResXPath ++ xpathTag "wallClockTime"

{- |
  Removes first part of string until @#@ (including @#@).
-}
getAnchor :: String -- ^ in-string
          -> String -- ^ part of string after first occurence of @#@
getAnchor s = case dropWhile (\ch -> not $ ch == '#') s of
    [] -> []
    _ : r -> r

{- |
  This helper function awaits an XPath to an element that contains another
  XText element (or is empty). The content of this XText element will be
  returned.
-}
getXText :: String -- ^ XPath to element containing one XText element
         -> XmlTree -- ^ XML tree to parse
         -> String -- ^ value of XText element
getXText xp rdfTree =
    let xptext = xp ++ "/text()"
        xmltrees = getXPath xptext rdfTree
    in case xmltrees of
         [] -> []
         hd : _ -> let firstNode = getNode hd in
                   if isXTextNode firstNode
                     then (\(XText s) -> s) firstNode
                     else []

{- |
  Same as getXText, but if the element does not exist Nothing will be returned.
  Otherwise Just /Text/ will be returned.
-}
getMaybeXText :: String -- ^ XPath to element containing one XText element
              -> XmlTree -- ^ XML tree to parse
              -> Maybe String -- ^ value of XText element
getMaybeXText xp rdfTree =
    let xmltrees = getXPath xp rdfTree
    in  case xmltrees of
          [] -> Nothing
          _ -> Just $ getXText xp rdfTree

{- |
  Filters @_@ out of a String and uppercases each letter after a @_@.
-}
filterUnderline :: Bool  -- ^ upcase next letter
                -> String -- ^ input String
                -> String -- ^ un-dashed output String
filterUnderline b st = case st of
    []  -> []
    h : r -> case h of
             '_' -> filterUnderline True r
             _ -> (if b then toUpper h else h) : filterUnderline False r
