{- |
Module      :$Header$
Description : after parsing XML file a XML state is produced, containing
              commands that need to be executed
Copyright   : uni-bremen and DFKI
Licence     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@jacobs-university.de
Stability   : provisional
Portability : portable

PGIP.XMLstate contains the description of the XMLstate and a function
that produces such a state
-}

module PGIP.XMLstate
where


import Text.XML.HXT.Arrow

-- | List of all possible commands inside an XML packet
data CMDL_XMLstate =
   XML_Execute String
 | XML_Exit
 | XML_ProverInit
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

-- | Given a xml packet (as a string), the function converts it into a
-- list of XML commands
parseXMLString :: String -> IO [CMDL_XMLstate]
parseXMLString input
 = do
    let al = [(a_validate,v_0)]
    elemsNms  <- runX $ elementsName al input
    elemsData <- runX $ elementsText al input
    let elems = map (\(name,cnt) -> case name  of
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
                                         "undostep"   -> XML_Undo
                                         "redostep"   -> XML_Redo
                                         "forget"     -> XML_Forget cnt
                                         "opentheory" -> XML_OpenTheory cnt
                                         "closetheory"-> XML_CloseTheory cnt
                                         "closefile"  -> XML_CloseFile cnt
                                         "loadfile"   -> XML_LoadFile cnt
                                         _            -> XML_Unknown name
                                 ) $ zip elemsNms elemsData
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


