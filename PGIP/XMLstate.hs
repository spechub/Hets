{- |
Module      : $Header$
Description : after parsing XML message a list of XMLcommands is produced,
              containing commands that need to be executed
Copyright   : uni-bremen and DFKI
Licence     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@jacobs-university.de
Stability   : provisional
Portability : portable

PGIP.XMLstate contains the description of the XMLstate and a function
that produces such a state
-}

module PGIP.XMLstate where

import Common.Utils (getEnvDef, trim)
import Common.ToXml

import Text.XML.Light

import Data.List (find, intercalate)
import Data.Time.Clock.POSIX (getPOSIXTime)

import System.IO(Handle)

-- Converts any line text that does not stand for a
-- comment into a theoryitem element
genProofStep :: String -> Element
genProofStep str = let
    iname = case trim str of
             "" -> "whitespace"   -- empty line generates a whitespace element
             '#' : _ -> "comment" -- comments start with #
             _ -> "theoryitem"    -- convert line into a theoryitem element

    in unode iname $ mkText $ str ++ "\n"

-- | adds xml structure to unstructured code
addPgipMarkUp :: String -> Element
addPgipMarkUp str = case lines str of
  [] -> error "addPgipMarkUp.empty"
  hd : tl ->
    unode "parseresult"
        $ add_attr (mkAttr "thyname" "whatever")
             (unode "opentheory" $ mkText hd)
        : map genProofStep tl
        ++ [unode "closetheory" ()]

{-
 - other types of mark ups :
 -   opengoal / closegoal
 -   openblock / closeblock
 -
 -}

-- generates a pgipelem element that contains the input text
genPgipElem :: String -> Element
genPgipElem = unode "pgipelem" . mkText

-- generates a normalresponse element that has a pgml element
-- containing the output text
genNormalResponse :: String -> Element
genNormalResponse = unode "normalresponse"
    . add_attr (mkAttr "area" "message")
    . unode "pgml" . mkText

-- same as above, just for an error instead of normal output
genErrorResponse :: Bool -> String -> Element
genErrorResponse fatality =
  add_attrs [ mkAttr "fatality" "fatal" | fatality]
  . unode "errorresponse"
  . unode "pgmltext" . mkText

-- adds one element to the end of the content of the xml packet that represents
-- the current output of the interface to the broker
addToContent :: CmdlPgipState -> Element -> CmdlPgipState
addToContent pgData el =
  pgData { xmlElement = case xmlElement pgData of
             e -> e { elContent = elContent e ++ [Elem el] } }

-- adds a ready element at the end of the xml packet that represents the
-- current output of the interface to the broker
addReadyXml :: CmdlPgipState -> CmdlPgipState
addReadyXml pgData = addToContent pgData $ unode "ready" ()

-- | State that keeps track of the comunication between Hets and the Broker
data CmdlPgipState = CmdlPgipState
  { pgipId :: String
  , name :: String
  , seqNb :: Int
  , refSeqNb :: Maybe String
  , theMsg :: String
  , xmlElement :: Element
  , hout :: Handle
  , hin :: Handle
  , stop :: Bool
  , resendMsgIfTimeout :: Bool
  , useXML :: Bool
  , maxWaitTime :: Int
  , quietOutput :: Bool }

-- | Generates an empty CmdlPgipState
genCMDLPgipState :: Bool -> Handle -> Handle -> Int -> IO CmdlPgipState
genCMDLPgipState swXML h_in h_out timeOut = do
   pgId <- genPgipID
   return CmdlPgipState
     { pgipId = pgId
     , name = "Hets"
     , quietOutput = False
     , seqNb = 1
     , refSeqNb = Nothing
     , theMsg = []
     , xmlElement = unode "pgip" ()
     , hin = h_in
     , hout = h_out
     , stop = False
     , resendMsgIfTimeout = True
     , useXML = swXML
     , maxWaitTime = timeOut }

-- | Generates the id of the session between Hets and the Broker
genPgipID :: IO String
genPgipID =
  do
   t1 <- getEnvDef "HOSTNAME" ""
   t2 <- getEnvDef "USER" ""
   t3 <- getPOSIXTime
   return $ t1 ++ "/" ++ t2 ++ "/" ++ show t3

-- | Concatenates the input string to the message stored in the state
addToMsg :: String -> String -> CmdlPgipState -> CmdlPgipState
addToMsg str errStr pgD =
  let strings = [theMsg pgD, str, errStr]
  in pgD { theMsg = intercalate "\n" $ filter (not . null) strings }

-- | Resets the content of the message stored in the state
resetMsg :: String -> CmdlPgipState -> CmdlPgipState
resetMsg str pgD = pgD
  { theMsg = str
  , xmlElement = convertPgipStateToXML pgD }

-- the PGIP protocol defines the pgip element as containing a single
-- subelement, but in the state the toplevel pgip element can contain
-- many subelements. This function transforms the single toplevel element
-- with potentially many subelements into many pgip elements with only
-- one subelement and outputs this list as a XML string.
-- This makes it neccessary to distribute new seq-values, and thus it is
-- crucial to update the pgip-state with the new (returned) seq value!
pgipStateToXmlString :: CmdlPgipState -> (String, Int)
pgipStateToXmlString pgipData =
    let e = xmlElement pgipData
        attrs = init $ elAttribs e
        seqAttr = last $ elAttribs e
        seqNum = seqNb pgipData
        outpElem c (i::Integer) =
            showElement
            e{ elContent = [c]
             , elAttribs = attrs ++
                           [seqAttr{ attrVal =
                                         show $ seqNum + fromIntegral i}]}
        subelems = elContent e
    in (unlines $ zipWith outpElem subelems [0..]
       , seqNb pgipData + length subelems - 1)
-- to restore the original behaviour, just use this version:
-- pgipStateToXmlString x = (showElement $ xmlElement x, seqNb x)


-- extracts the xml package in XML.Light format (namely the Content type)
convertPgipStateToXML :: CmdlPgipState -> Element
convertPgipStateToXML pgipData = add_attrs
  ((case refSeqNb pgipData of
      Nothing -> []
      Just v -> [mkAttr "refseq" v])
   ++ [ mkAttr "tag" $ name pgipData
      , mkAttr "class" "pg"
      , mkAttr "id" $ pgipId pgipData
      , mkAttr "seq" $ show $ seqNb pgipData ])
  $ unode "pgip" ()

-- | List of all possible commands inside an XML packet
data CmdlXMLcommands =
   XmlExecute String
 | XmlExit
 | XmlProverInit
 | XmlAskpgip
 | XmlStartQuiet
 | XmlStopQuiet
 | XmlOpenGoal String
 | XmlCloseGoal String
 | XmlGiveUpGoal String
 | XmlUnknown String
 | XmlParseScript String
 | XmlUndo
 | XmlRedo
 | XmlForget String
 | XmlOpenTheory String
 | XmlCloseTheory String
 | XmlCloseFile String
 | XmlLoadFile String deriving (Eq, Show)

-- extracts the refrence number of a xml packet (given as a string)
getRefseqNb :: String -> Maybe String
getRefseqNb input =
  let xmlTree = parseXML input
      elRef = find (\ x -> case x of
                              Elem dt -> qName (elName dt) == "pgip"
                              _ -> False) xmlTree
   in case elRef of
        Nothing -> Nothing
        Just el -> case el of
                     Elem dt -> case find (\ x -> qName (attrKey x) == "seq") $
                                     elAttribs dt of
                                  Nothing -> Nothing
                                  Just elatr -> Just $ attrVal elatr
                     _ -> Nothing

-- | parses the xml message creating a list of commands that it needs to
-- execute
parseXMLTree :: [Content] -> [CmdlXMLcommands] -> [CmdlXMLcommands]
parseXMLTree xmltree acc = case xmltree of
    Elem info : ls -> case parseXMLElement info of
                        Just c -> parseXMLTree ls (c : acc)
                        Nothing -> parseXMLTree (elContent info ++ ls) acc
    _ : ls -> parseXMLTree ls acc
    [] -> acc

parseXMLElement :: Element -> Maybe CmdlXMLcommands
parseXMLElement info = let cnt = strContent info in
  case qName $ elName info of
    "proverinit"   -> Just XmlProverInit
    "proverexit"   -> Just XmlExit
    "startquiet"   -> Just XmlStartQuiet
    "stopquiet"    -> Just XmlStopQuiet
    "opengoal"     -> Just $ XmlOpenGoal cnt
    "proofstep"    -> Just $ XmlExecute cnt
    "closegoal"    -> Just $ XmlCloseGoal cnt
    "giveupgoal"   -> Just $ XmlGiveUpGoal cnt
    "spurioscmd"   -> Just $ XmlExecute cnt
    "dostep"       -> Just $ XmlExecute cnt
    "editobj"      -> Just $ XmlExecute cnt
    "undostep"     -> Just XmlUndo
    "redostep"     -> Just XmlRedo
    "forget"       -> Just $ XmlForget cnt
    "opentheory"   -> Just $ XmlExecute cnt
    "theoryitem"   -> Just $ XmlExecute cnt
    "closetheory"  -> Just $ XmlCloseTheory cnt
    "closefile"    -> Just $ XmlCloseFile cnt
    "loadfile"     -> Just $ XmlLoadFile cnt
    "askpgip"      -> Just XmlAskpgip
    "parsescript"  -> Just $ XmlParseScript cnt
    "pgip"         -> Nothing
    s -> Just $ XmlUnknown s

-- | Given a packet (a normal string or a xml formated string), the function
-- converts it into a list of commands
parseMsg :: CmdlPgipState -> String -> [CmdlXMLcommands]
parseMsg st input = if useXML st
   then parseXMLTree (parseXML input) []
   else concatMap (\ x -> [ XmlExecute x | not $ null $ trim x ]) $ lines input
