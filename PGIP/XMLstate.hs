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

import Data.List(find, intercalate)
import Data.Time.Clock.POSIX(getPOSIXTime)
import System.IO(Handle)

import Common.Utils(getEnvDef, trim)
import Text.XML.Light

-- generates a pgipelem element that contains the input text
genPgipElem :: String -> Content
genPgipElem str =
   Elem Element {
     elName = unqual "pgipelem",
     elAttribs = [],
     elContent = [Text $ CData CDataRaw str Nothing],
     elLine = Nothing
   }

-- generates a normalresponse element that has a pgml element
-- containing the output text
genNormalResponse :: String -> Content
genNormalResponse str =
  Elem Element {
          elName = unqual "normalresponse",
          elAttribs = [],
          elContent = [ Elem Element {
                         elName = unqual "pgml",
                         elAttribs = [Attr {
                                       attrKey = unqual "area",
                                       attrVal = "message"} ],
                         elContent =  [Text $ CData CDataRaw str Nothing],
                         elLine = Nothing } ],
          elLine = Nothing }

-- same as above, just for an error instead of normal output
genErrorResponse :: Bool -> String -> Content
genErrorResponse fatality str =
  Elem Element {
    elName = unqual "errorresponse",
    elAttribs = [ Attr { attrKey = unqual "fatality",
                         attrVal = "fatal" } | fatality ],
    elContent = [ Elem Element {
                    elName = unqual "pgmltext",
                    elAttribs = [],
                    elContent = [Text $ CData CDataRaw str Nothing],
                    elLine = Nothing } ],
    elLine = Nothing
  }

-- adds one element at the end of the content of the xml packet that represents
-- the current output of the interface to the broker
addToContent :: CmdlPgipState -> Content -> CmdlPgipState
addToContent pgData cont =
  pgData {
    xmlContent = case xmlContent pgData of
                  Elem e -> Elem e { elContent = elContent e ++ [cont] }
                  _      -> xmlContent pgData
  }

-- adds a ready element at the end of the xml packet that represents the
-- current output of the interface to the broker
addReadyXml :: CmdlPgipState -> CmdlPgipState
addReadyXml pgData = addToContent pgData $ Elem $ unode "ready" ()

-- | State that keeps track of the comunication between Hets and the Broker
data CmdlPgipState = CmdlPgipState
  { pgipId :: String
  , name :: String
  , seqNb :: Int
  , refSeqNb :: Maybe String
  , theMsg :: String
  , xmlContent :: Content
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
     , xmlContent = Elem blank_element { elName = unqual "pgip" }
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
resetMsg str pgD = pgD {
    theMsg = str,
    xmlContent = convertPgipStateToXML pgD
  }

-- extracts the xml package in XML.Light format (namely the Content type)
convertPgipStateToXML :: CmdlPgipState -> Content
convertPgipStateToXML pgipData =
  let baseElem = Element {
                   elName = unqual "pgip",
                   elAttribs = [ Attr {
                                  attrKey = unqual "tag",
                                  attrVal = name pgipData }
                                , Attr {
                                  attrKey = unqual "class",
                                  attrVal = "pg"}
                                , Attr {
                                  attrKey = unqual "id",
                                  attrVal = pgipId pgipData }
                                , Attr {
                                  attrKey = unqual "seq",
                                  attrVal = show $ seqNb pgipData} ],
                   elContent = [],
                   elLine = Nothing}
   in case refSeqNb pgipData of
    Nothing -> Elem baseElem
    Just v  -> Elem baseElem {
                 elAttribs = Attr { attrKey = unqual "refseq",
                                    attrVal = v } : elAttribs baseElem
               }

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
 | XmlLoadFile String deriving (Eq,Show)

-- extracts the refrence number of a xml packet (given as a string)
getRefseqNb :: String -> Maybe String
getRefseqNb input =
  let xmlTree = parseXML input
      elRef = find (\ x -> case x of
                              Elem dt -> qName (elName dt) == "pgip"
                              _       -> False) xmlTree
   in case elRef of
        Nothing -> Nothing
        Just el -> case el of
                     Elem dt -> case find (\ x -> qName (attrKey x) == "seq") $
                                     elAttribs dt of
                                  Nothing -> Nothing
                                  Just elatr -> Just $ attrVal elatr
                     _       -> Nothing


-- parses the xml message creating a list of commands that it needs to
-- execute
parseXMLTree :: [Content] -> [CmdlXMLcommands] -> [CmdlXMLcommands]
parseXMLTree xmltree acc = case xmltree of
    []             -> acc
    Elem info : ls -> case parseXMLElement info of
                        Just c  -> parseXMLTree ls (c : acc)
                        Nothing -> parseXMLTree (elContent info ++ ls) acc
    _ : ls         -> parseXMLTree ls acc

parseXMLElement :: Element -> Maybe CmdlXMLcommands
parseXMLElement info =
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
    s              -> Just $ XmlUnknown s
  where
    cnt = if null $ elContent info then error "empty head in parseXMLElement"
          else case head $ elContent info of
                 Text smtxt -> cdData smtxt
                 _          -> []

-- | Given a packet (a normal string or a xml formated string), the function
-- converts it into a list of commands
parseMsg :: CmdlPgipState -> String -> [CmdlXMLcommands]
parseMsg st input =
  if useXML st
   then parseXMLTree (parseXML input) []
   else concatMap (\ x -> [ XmlExecute x | not $ null $ trim x ]) $ lines input
