{- |
Module      :$Header$
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

import Data.Time.Clock.POSIX (getPOSIXTime)
import Common.Utils (getEnvDef)
import System.IO (Handle)
import Text.XML.HXT.Arrow

-- | State that keeps track of the comunication between Hets and the Broker
data CMDL_PgipState = CMDL_PgipState {
                    pgip_id            :: String,
                    name               :: String,
                    seqNb              :: Int,
                    theMsg             :: String,
                    nonFatalErrMsg     :: String,
                    hout               :: Handle,
                    hin                :: Handle,
                    stop               :: Bool,
                    resendMsgIfTimeout :: Bool,
                    useXML             :: Bool,
                    maxWaitTime        :: Int,
                    quietOutput        :: Bool
                    }

-- | Generates an empty CMDL_PgipState
genCMDL_PgipState :: Bool -> Handle -> Handle -> IO CMDL_PgipState
genCMDL_PgipState swXML h_in h_out =
  do
   pgId <- genPgipID
   return CMDL_PgipState {
     pgip_id            = pgId,
     name               = "Hets",
     nonFatalErrMsg     = [],
     quietOutput        = False,
     seqNb              = 0,
     theMsg             = [],
     hin                = h_in,
     hout               = h_out,
     stop               = False,
     resendMsgIfTimeout = True,
     useXML             = swXML,
     maxWaitTime        = 2000
     }

-- | Generates the id of the session between Hets and the Broker
genPgipID :: IO String
genPgipID =
  do
   t1 <- getEnvDef "HOSTNAME" ""
   t2 <- getEnvDef "USER" ""
   t3 <- getPOSIXTime
   return $ t1 ++ "/" ++ t2 ++ "/" ++ show t3


-- | Concatenates the input string to the message stored in the state
addToMsg :: String -> String -> CMDL_PgipState -> CMDL_PgipState
addToMsg str errStr pgD
  = pgD {
     theMsg = (theMsg pgD) ++ str,
     nonFatalErrMsg = (nonFatalErrMsg pgD) ++ errStr
     }


-- | Resets the content of the message stored in the state
resetMsg :: String -> CMDL_PgipState -> CMDL_PgipState
resetMsg str pgD
   = pgD {
      theMsg = str
      }


-- | Generates a pgip tag if it uses xml otherwise generates an empty xml
genPgipTag :: CMDL_PgipState -> CMDL_PgipState
genPgipTag pgipData =
  let msg = ( "<pgip "
              ++ "tag =\"" ++ (name pgipData) ++ "\" "
              ++ "class=\"pg\" "
              ++ "id=\""++ (pgip_id pgipData) ++"\" "
              ++ "seq=\"" ++ (show $ seqNb pgipData) ++"\" "
              ++ ">"
              )
  in case useXML pgipData of
   True -> addToMsg msg [] pgipData
   False -> pgipData


-- | List of all possible commands inside an XML  packet
data CMDL_XMLcommands =
   XML_Execute String
 | XML_Exit
 | XML_ProverInit
 | XML_Askpgip
 | XML_StartQuiet
 | XML_StopQuiet
 | XML_OpenGoal String
 | XML_CloseGoal String
 | XML_GiveUpGoal String
 | XML_Unknown String
 | XML_Undo
 | XML_Redo
 | XML_Forget String
 | XML_OpenTheory String
 | XML_CloseTheory String
 | XML_CloseFile String
 | XML_LoadFile String deriving (Eq,Show)

-- | Given a packet (a normal string or a xml formated string), the function
-- converts it into a list of commands
parseMsg :: CMDL_PgipState -> String -> IO [CMDL_XMLcommands]
parseMsg st input
 = do
    let al = [(a_validate,v_0)]
        lns = lines input
    elemsNms <- case useXML st of
                 True -> runX $ elementsName al input
                 False -> return $ concatMap(\x -> case words x of
                                                    [] -> []
                                                    _ -> ["dostep"]) lns
    elmsData<-case useXML st of
               True -> runX $ elementsText al input
               False -> return $ concatMap (\x -> case words x of
                                                   [] -> []
                                                   _ -> [x]) lns
    let elems = map (\(nm,cnt) -> case nm  of
                                         "proverinit" -> XML_ProverInit
                                         "proverexit" -> XML_Exit
                                         "startquiet" -> XML_StartQuiet
                                         "stopquiet"  -> XML_StopQuiet
                                         "opengoal"   -> XML_OpenGoal cnt
                                         "proofstep"  -> XML_Execute cnt
                                         "closegoal"  -> XML_CloseGoal cnt
                                         "giveupgoal" -> XML_GiveUpGoal cnt
                                         "spurioscmd" -> XML_Execute cnt
                                         "dostep"     -> XML_Execute cnt
                                         "editobj"    -> XML_Execute cnt
                                         "undostep"   -> XML_Undo
                                         "redostep"   -> XML_Redo
                                         "forget"     -> XML_Forget cnt
                                         "opentheory" -> XML_OpenTheory cnt
                                         "closetheory"-> XML_CloseTheory cnt
                                         "closefile"  -> XML_CloseFile cnt
                                         "loadfile"   -> XML_LoadFile cnt
                                         "askpgip"    -> XML_Askpgip
                                         _            -> XML_Unknown nm
                                 ) $ zip elemsNms elmsData
    return elems


-- | For a xml packet (contained into a string) the function extracts
-- the name of the tags
elementsName :: Attributes -> String -> IOSArrow b String
elementsName al src
 = readString al src
   >>>
   deep (isElem >>> hasName "pgip")
   >>>
   getChildren
   >>>
   getName

-- | For a xml packet (contained into a string) the function extracts
-- the text inside the tags
elementsText :: Attributes -> String -> IOSArrow b String
elementsText al src
 = readString al src
   >>>
   deep (isElem >>> hasName "pgip")
   >>>
   getChildren
   >>>
   (getChildren >>> getText) `orElse` getName
