{- |
Module      :  $Header$
Description :  Help functions for all automatic theorem provers.
Copyright   :  (c) Rainer Grabbe
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  rainer25@tzi.de
Stability   :  provisional
Portability :  needs POSIX

Functions for parsing and mapping MathServ output.

-}

{-
  To do:
  - also parse mw:failure and mw:message
-}

module SPASS.MathServParsing where

import SPASS.MathServCommunication

import Network.URI
import Network.Service
import Org.Xmlsoap.Schemas.Soap.Envelope as ENV

import Text.XML.HXT.Aliases
import Text.XML.HXT.Parser hiding (when)
import Text.XML.HXT.XPath

import Data.List
import Data.Maybe

-- * Datatypes for MathServ services

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
       MathServResponse { foAtpResult  :: MWFoAtpResult,
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
                  foStatus :: FoStatus
                  } deriving (Eq, Ord, Show)

data FoStatus =
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
     | Assumed
     | GaveUp
     | InputError
     | MemoryOut
     | ResourceOut
     | Timeout
     | Unknown
     deriving (Eq, Ord, Show)

data MWProvingProblem =
       TstpFOFProblem
     deriving (Eq, Ord, Show)
       
data MWCalculus =
       AprosNDCalculus
     | OmegaNDCalculus
     | EpResCalc
     | SpassResCalc
     | StandardRes
     | OtterCalc
     | ZenonCalc
     deriving (Eq, Ord, Show)

data MWTimeResource =
       MWTimeResource { cpuTime       :: Int,
                        wallClockTime :: Int
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
         _ -> error $ "unknown Operation for service Broker\n"++
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
             -> IO String -- ^ MathServ output or error message
callMathServ call =
    do
       maybe (do
                return "Could not start MathServ.")
             (\ endPoint -> do
                 (res::Either SimpleFault MathServOutput)
                    <- soapCall endPoint $
                       mkProveProblem call
                 case res of
                  Left mErr -> do
                    return $ show mErr
                  Right resp -> do
                    return $ getResponse resp
             )
             (makeEndPoint $
                "http://"++server++':':port++"/axis/services/"++
                  (show $ mathServService call))
    where
    -- server data
        server = "denebola.informatik.uni-bremen.de"
        port = "8080"


{- |
  Full parsing of RDF-objects returned by MathServ and putting the results
  into a MathServResponse data-structure.
-}
parseMathServOut :: String -- ^ MathServ output or error messages
                 -> IO MathServResponse -- ^ parsed rdf-objects in record
parseMathServOut mathServOut = do
    mtrees <- parseXML mathServOut
    let rdfTree = maybe emptyRoot head mtrees
    return MathServResponse {
             foAtpResult = parseFoAtpResult rdfTree,
             timeResource = parseTimeResource rdfTree }
    where


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
      nextTree =  head $ getXPath atpResultXPath rdfTree
      atpResultXPath = "/mw:*[local-name()='FoAtpResult']"
      outputXPath = "/mw:*[local-name()='output']"
      saturationXPath = "/mw:*[local-name()='saturation']"
      systemXPath = "/mw:*[local-name()='system']"
      timeXPath = "/mw:*[local-name()='time']"


{- |
  Parses an XmlTree for a FormalProof object on first level. If existing,
  all values of such an object are recursively parsed from underlying XmlTree.
  All found objects are put into a MWFormalProof data structure.
-}
parseProof :: XmlTree -- ^ XML tree to parse
           -> MWFormalProof -- ^ parsed Formal Proof node
parseProof rdfTree =
-- to be completed (recognition of used MWFormalProof's name)
    TstpCnfRefutation { formalProof = getXText formalProofXPath nextTree,
                        proofOf     = parseProvingProblem nextTree,
                        calculus    = parseCalculus nextTree,
                        axioms      = getXText axiomsXPath nextTree }
    where
      nextTree = head $ getXPath proofXPath rdfTree
      proofXPath = "/mw:*[local-name()='proof']/mw:*[1]"
      
      axiomsXPath = "/mw:*[local-name()='axioms']"
      formalProofXPath = "/mw:*[local-name()='formalProof']"
    

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
    in  case (tillLastDash prob) of
          "generated_tstp_fof_problem_" -> TstpFOFProblem
          []                            -> TstpFOFProblem
          _                             -> error $
            "Could not classify proving problem: " ++ prob
    where
      problemXPath = "/mw:*[local-name()='proofOf']/attribute::rdf:*"
      tillLastDash = reverse . (dropWhile (\ch -> not $ ch == '_'))
                     . reverse

{- |
  Parses an XmlTree for a Calculus object on first level.
  Currently seven different Calculus objects can be classified.
  Other objects (also empty or non-existing ones) will cause an exception.
-}
parseCalculus :: XmlTree -- ^ XML tree to parse
              -> MWCalculus -- ^ parsed Calculus node
parseCalculus rdfTree = case calc of
      "AProsNDCalculus" -> AprosNDCalculus
      "OmegaNDCalculus" -> OmegaNDCalculus
      "ep_res_calc"     -> EpResCalc
      "spass_res_calc"  -> SpassResCalc
      "otter_calc"      -> OtterCalc
      "zenon_calc"      -> ZenonCalc
      "standard_res"    -> StandardRes
      _                 -> error $ "Could not classify calculus: " ++ calc
    where
      calculusXPath = "/mw:*[local-name()='calculus']/attribute::rdf:*"
      calc = (getAnchor $ getXText calculusXPath rdfTree)
               
{- |
  Parses an XmlTree for a Status object on first level.
  Currently 18 different Status objects can be classified.
  Other objects (also empty or non-existing ones) will cause an exception.
  The status is differentiated into solved unsolved by the object itself.
-}
parseStatus :: XmlTree -- ^ XML tree to parse
            -> MWStatus -- ^ parsed Status node
parseStatus rdfTree = case statusStr of
      "CounterEquivalent"  -> MWStatus { solved = True,
                                         foStatus = CounterEquivalent }
      "CounterSatisfiable" -> MWStatus { solved = True,
                                         foStatus = CounterSatisfiable }
      "CounterTheorem"     -> MWStatus { solved = True,
                                         foStatus = CounterTheorem }
      "Equivalent"         -> MWStatus { solved = True,
                                         foStatus = Equivalent }
      "NoConsequence"      -> MWStatus { solved = True,
                                         foStatus = NoConsequence }
      "Satisfiable"        -> MWStatus { solved = True,
                                         foStatus = Satisfiable }
      "TautologousConclusion" -> MWStatus { solved = True,
                                         foStatus = TautologousConclusion }
      "Tautology"          -> MWStatus { solved = True,
                                         foStatus = Tautology }
      "Theorem"            -> MWStatus { solved = True,
                                         foStatus = Theorem }
      "Unsatisfiable"      -> MWStatus { solved = True,
                                         foStatus = Unsatisfiable }
      "UnsatisfiableConclusion" -> MWStatus { solved = True,
                                         foStatus = UnsatisfiableConclusion }
      "Assumed"            -> MWStatus { solved = False,
                                         foStatus = Assumed }
      "GaveUp"             -> MWStatus { solved = False,
                                         foStatus = GaveUp }
      "InputError"         -> MWStatus { solved = False,
                                         foStatus = InputError }
      "MemoryOut"          -> MWStatus { solved = False,
                                         foStatus = MemoryOut }
      "ResourceOut"        -> MWStatus { solved = False,
                                         foStatus = ResourceOut }
      "Timeout"            -> MWStatus { solved = False,
                                         foStatus = Timeout }
      "Unknown"            -> MWStatus { solved = False,
                                         foStatus = Unknown }
      _                    -> error $ "Could not classify status of proof: "
                                      ++ statusStr
    where
      statusXPath = "/mw:*[local-name()='status']/attribute::rdf:*"
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
      cpuTime       = read cpuTimeString,
      wallClockTime = read wallClockTimeString }
    where
      cpuTimeString = getXText cpuTimeXPath rdfTree
      wallClockTimeString = getXText wallClockTimeXPath rdfTree
      
      timeResXPath = "/mw:*[local-name()='TimeResource']/"
      cpuTimeXPath = timeResXPath ++ "/mw:*[local-name()='cpuTime']"
      wallClockTimeXPath =
          timeResXPath ++ "/mw:*[local-name()='wallClockTime']"
    
{- |
  Removes first part of string until '#' (including '#').
-}
getAnchor :: String -- ^ in-string
          -> String -- ^ part of string after first occurence of '#'
getAnchor s =
    let s' = dropWhile (\ch -> not $ ch == '#') s
    in  case s' of
          [] -> s'
          _  -> tail s'

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
         xt -> let firstNode = getNode $ head xt
               in  if isXTextNode firstNode
                     then (\(XText s) -> s) firstNode
                     else []
