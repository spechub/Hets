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

import System.IO(Handle, hPutStrLn, hFlush)

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
addPGIPMarkup :: String -> Element
addPGIPMarkup str = case lines str of
  [] -> error "addPgipMarkUp.empty"
  hd : tl ->
    unode "parseresult"
      $ add_attr (mkAttr "thyname" "whatever") (unode "opentheory" $ mkText hd)
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
genNormalResponse :: Node t => String -> t -> Element
genNormalResponse areaValue = unode "normalresponse"
    . add_attr (mkAttr "area" areaValue)
    . unode "pgml"

-- same as above, just for an error instead of normal output
genErrorResponse :: Bool -> String -> Element
genErrorResponse fatality =
  add_attrs [ mkAttr "fatality" "fatal" | fatality]
  . unode "errorresponse"
  . unode "pgmltext" . mkText

-- | It inserts a given string into the XML packet as
-- normal output
addPGIPAnswer :: String -> String -> CmdlPgipState -> CmdlPgipState
addPGIPAnswer msgtxt errmsg st =
    if useXML st
    then let resp = addPGIPElement st $ genNormalResponse "message"
               $ mkText msgtxt
         in if null errmsg then resp
         else addPGIPElement resp $ genErrorResponse False errmsg
    else addToMsg msgtxt errmsg st

-- | It inserts a given string into the XML packet as
-- error output
addPGIPError :: String -> CmdlPgipState -> CmdlPgipState
addPGIPError str st = case str of
  "" -> st
  _ | useXML st -> addPGIPElement st $ genErrorResponse True str
  _ -> addToMsg [] str st

-- extracts the xml package in XML.Light format (namely the Content type)
addPGIPAttributes :: CmdlPgipState -> Element -> Element
addPGIPAttributes pgipData e = (add_attrs
  ((case refSeqNb pgipData of
      Nothing -> []
      Just v -> [mkAttr "refseq" v])
   ++ [ mkAttr "tag" $ name pgipData
      , mkAttr "class" "pg"
      , mkAttr "id" $ pgipId pgipData
      , mkAttr "seq" $ show $ seqNb pgipData ])
  $ unode "pgip" ()) { elContent = [Elem e]}

-- adds one element to the end of the content of the xml packet that represents
-- the current output of the interface to the broker
addPGIPElement :: CmdlPgipState -> Element -> CmdlPgipState
addPGIPElement pgData el =
  pgData { xmlElements = addPGIPAttributes pgData el : xmlElements pgData
         , seqNb = seqNb pgData + 1 }

-- adds a ready element at the end of the xml packet that represents the
-- current output of the interface to the broker
addPGIPReady :: CmdlPgipState -> CmdlPgipState
addPGIPReady pgData = addPGIPElement pgData $ unode "ready" ()

-- | State that keeps track of the comunication between Hets and the Broker
data CmdlPgipState = CmdlPgipState
  { pgipId :: String
  , name :: String
  , seqNb :: Int
  , refSeqNb :: Maybe String
  , msgs :: [String]
  , xmlElements :: [Element]
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
     , msgs = []
     , xmlElements = []
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
  let strings = [errStr, str]
  in pgD { msgs = filter (not . null) strings ++ msgs pgD }

-- | Resets the content of the message stored in the state
resetPGIPData :: CmdlPgipState -> CmdlPgipState
resetPGIPData pgD = pgD
  { msgs = []
  , xmlElements = [] }

-- the PGIP protocol defines the pgip element as containing a single
-- subelement.
convertPGIPDataToString :: CmdlPgipState -> String
convertPGIPDataToString =
  intercalate "\n" . reverse . map showElement . xmlElements

sendPGIPData :: CmdlPgipState -> IO CmdlPgipState
sendPGIPData pgData =
  do
    let xmlMsg = convertPGIPDataToString pgData
        pgData' = addToMsg xmlMsg [] pgData
    sendMSGData pgData'

sendMSGData :: CmdlPgipState -> IO CmdlPgipState
sendMSGData pgData = do
  hPutStrLn (hout pgData) $ intercalate "\n" $ reverse $ msgs pgData
  hFlush $ hout pgData
  return pgData

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

-- extracts the seq attribute value to be used as reference number elsewhere
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
