{- |
Module       : ./GUI/hets_cgi.hs
Copyright    : (c) Uni Magdeburg 2004-2017
License      : GPLv2 or higher, see LICENSE.txt

Maintainer   : till@iks.cs.ovgu.de
Stability    : provisional
Portability  : non-portable(imports Logic.Logic)

Interface for web page with WASH/CGI
-}

module Main where

import WASH.CGI.CGI as CGI

import Driver.Options
import Driver.WriteLibDefn
import Driver.ReadLibDefn
import Driver.Version

import qualified Data.Set as Set

import qualified Common.Result as CRes
import Common.Doc (renderText)
import Common.GlobalAnnotations
import Common.LibName
import Common.ResultT
import Common.PrintLaTeX

import Comorphisms.LogicGraph

import Static.AnalysisLibrary
import Static.DevGraph

import Syntax.AS_Library
import Syntax.Print_AS_Structured
import Syntax.ToXml

import Text.XML.Light

import System.Random
import System.IO
import System.Time
import System.Process
import System.Posix.IO
import System.Posix.Types
import System.Posix.Files
import System.Posix.Process

import Control.Monad

-- ---- Configuration section -------------------------

-- - site specific configuration

-- a valid email address for the contact field / link
contactUrl :: String
contactUrl = "mailto:" ++ contactText

-- the text displayed with the previous link
contactText :: String
contactText = "hets-devel@informatik.uni-bremen.de"

{- a directory which must be accessable and exposed by the web server,
where all the generated files are stored. This string must end with
a slash! -}
baseDirGenerated :: String
baseDirGenerated = "/home/www.informatik.uni-bremen.de/cofi/hets-tmp/"

-- path to the log file
logFile :: String
logFile = baseDirGenerated ++ "hets.log"

-- the url pointing to the above specified directory
baseUrlGenerated :: String
baseUrlGenerated = "http://www.informatik.uni-bremen.de/cofi/hets-tmp/"

{- the directory where the Hets-lib repository is checked out. Must be
accessable by the cgi script -}
caslLibDir :: String
caslLibDir = "/home/cofi/Hets-lib"

-- where is the pdflatex command for the generation of PDF-files
pdflatexCmd :: String
pdflatexCmd = "/opt/csw/bin/pdflatex"

-- - site independant configuration

cofiUrl :: String
cofiUrl =
  "http://www.cofi.info/"

-- link to the homepage of hetcasl
hetcaslUrl :: String
hetcaslUrl = "http://dol-omg.org/"

hetsUrl :: String
hetsUrl = "http://hets.eu/"

-- link to the manual of Hets
hetsManualUrl :: String
hetsManualUrl = hetsUrl ++ "UserGuide.pdf"

-- link to the hetcasl.sty file
hetcaslStyUrl :: String
hetcaslStyUrl = hetsUrl ++ "hetcasl.sty"

-- ---- End of Configuration section ------------------

webOpts :: HetcatsOpts
webOpts = defaultHetcatsOpts
  { outputToStdout = False
  , libdirs = [caslLibDir]
  , verbose = 0 }

data SelectedBoxes = SB
  { outputTree :: Bool
  , outputTxt :: Bool
  , outputTex :: Bool
  , archive :: Bool
  } deriving Show

data Output = OP
  { asciiTxt :: String
  , parseTree :: String }

defaultOutput :: Output
defaultOutput = OP "" ""

newtype RESL = RESL (CRes.Result Output)

instance Read RESL where
    readsPrec _ _ = error "Read for \"RESL\" not implemented!!"

instance Show RESL where
    showsPrec _ _ _ = error "Show for \"RESL\" not implemented!!"

main :: IO ()
main = run mainCGI

mainCGI :: CGI ()
mainCGI = ask $ html $ do
      CGI.head $ title $ text "Hets Web Interface"
      CGI.body $ makeForm $ page1 hetsVersion

page1 :: String -> WithHTML x CGI ()
page1 title1 = do
      h1 $ text title1
      p $ do
        text "You may also want to try out our experimental "
        hlink (URL "http://rest.hets.eu/")
          $ text "Hets Server"
      p $ do
        text "Enter a "
        hlink (URL hetcaslUrl) $ text "CASL or DOL"
        text
          " specification or library in the input zone, then press SUBMIT:"
      -- Input field
      input <- p $ makeTextarea "" (attr "rows" "22" ## attr "cols" "68")
      -- check box
      selectTxt <- checkboxInputField (attr "valus" "yes")
      text "output pretty print ASCII"
      selectTex <- checkboxInputField (attr "valus" "yes")
      text "output pretty print LaTeX"
      selectTree <- checkboxInputField (attr "valus" "yes")
      text "output xml tree"
      selectAchiv <- p $ b $ checkboxInputField (attr "checked" "checked") ##
        text "If this checkbox is selected, your input will be logged!"
      -- submit/reset botton
      p $ do
        submit (F5 input selectTree selectTxt selectTex selectAchiv)
                 handle (fieldVALUE "Submit")
        submit0 mainCGI (fieldVALUE "reset")
      hr_S CGI.empty
      p $ do
        text "Contact address: "
        hlink (URL contactUrl) $ text contactText

-- handle of the submit botton
handle :: HasValue i => F5 (i String) (i Bool) (i Bool) (i Bool) (i Bool) VALID
       -> CGI ()
handle (F5 input box1 box2 box3 box4) = do
    random1 <- io $ getStdRandom $ randomR (100000, 999999)
    processID <- io getProcessID
    let outputfile = baseDirGenerated ++ "result" ++ show processID
                     ++ show (random1 :: Int)
        str = CGI.value input
        selectedBoxes = SB
          { outputTree = CGI.value box1
          , outputTxt = CGI.value box2
          , outputTex = CGI.value box3
          , archive = CGI.value box4 }
    RESL res <- io $ fmap RESL $ anaInput str selectedBoxes outputfile
    ask $ html $ do
          CGI.head $ title $ text "HETS results"
          CGI.body $ printR str res selectedBoxes outputfile

-- Analyze the input
anaInput :: String -> SelectedBoxes -> FilePath
         -> IO (CRes.Result Output)
anaInput contents selectedBoxes outputfiles = do
  CRes.Result _ (Just (ast : _)) <- runResultT
    $ readLibDefn logicGraph webOpts Nothing "<stdin>" "<stdin>" contents
  CRes.Result ds mres <- runResultT
      $ anaLibDefn logicGraph webOpts Set.empty emptyLibEnv emptyDG ast ""
  let ds1 = filter diagFilter ds
  if CRes.hasErrors ds1 then return $ CRes.Result ds1 Nothing else
    maybe (return $ CRes.Result ds1 Nothing)
           (\ res -> do
              saveLog (archive selectedBoxes)
              process_result ds1 res outputfiles selectedBoxes)
           mres
 where
      diagFilter d = case CRes.diagKind d of
                     CRes.Hint -> False
                     CRes.Debug -> False
                     _ -> True

      process_result :: [CRes.Diagnosis]
                      -> (LibName, LIB_DEFN, GlobalAnnos, LibEnv)
                      -> FilePath
                      -> SelectedBoxes
                      -> IO (CRes.Result Output)
      process_result ds (_, libDefn, gannos, _) outputfile conf = do
             let fMode = foldl unionFileModes nullFileMode
                                [ownerReadMode, ownerWriteMode,
                                 groupReadMode, groupWriteMode,
                                 otherReadMode]
             when (outputTex conf) $ do
                    let pptexFile = outputfile ++ ".pp.tex"
                        latexFile = outputfile ++ ".tex"
                        pdfFile = outputfile ++ ".pdf"
                        tmpFile = outputfile ++ ".tmp"
                    writeLibDefnLatex logicGraph False gannos pptexFile libDefn
                    writeFile latexFile (latexHeader ++
                                         "\\input{" ++ pptexFile ++
                                         "}\n \\end{document}\n")
                    setFileMode pptexFile fMode
                    setFileMode latexFile fMode

                    system ("(cd " ++ baseDirGenerated ++ " ; ls -lh " ++
                            pdflatexCmd ++ " ; " ++ pdflatexCmd ++ " " ++
                           latexFile ++ ") > " ++ tmpFile)
                    setFileMode pdfFile fMode
             when (outputTxt conf) $ do
                    let txtFile = outputfile ++ ".txt"
                    writeFile txtFile $ show (renderText gannos $
                      prettyLG logicGraph libDefn) ++ "\n"
                    setFileMode txtFile fMode
             when (outputTree conf) $ do
                    let txtFile = outputfile ++ ".pp.xml"
                    writeFile txtFile . ppTopElement
                      $ xmlLibDefn logicGraph gannos libDefn
                    setFileMode txtFile fMode
             return (CRes.Result ds $ Just $ selectOut conf libDefn gannos)
      selectOut :: SelectedBoxes -> LIB_DEFN -> GlobalAnnos -> Output
      selectOut conf ld ga = defaultOutput
        { asciiTxt = if outputTxt conf
            then show $ renderText ga $ prettyLG logicGraph ld else ""
        , parseTree = if outputTree conf
            then ppElement $ xmlLibDefn logicGraph ga ld else "" }
      -- log file
      saveLog :: Bool -> IO ()
      saveLog willSave = when willSave $ do
            fd <- openFd logFile ReadWrite Nothing
                               defaultFileFlags {append = True}
            fSize <- sizeof fd
            let filelock = (WriteLock, AbsoluteSeek, 0, fSize)
                fileunlock = (Unlock, AbsoluteSeek, 0, fSize)
            aktTime <- timeStamp
            setLock fd filelock
            fdWrite fd (aktTime ++ "\n" ++ contents ++ "\n\n")
            setLock fd fileunlock
            closeFd fd
      timeStamp :: IO String
      timeStamp = do
            t <- getClockTime
            ct <- toCalendarTime t
            return $ calendarTimeToString ct
      sizeof :: Fd -> IO FileOffset
      sizeof fd = do
            fstatus <- getFdStatus fd
            return $ fileSize fstatus

-- Print the result
printR :: String -> CRes.Result Output -> SelectedBoxes
       -> FilePath
       -> WithHTML x CGI ()
printR str (CRes.Result ds mres) conf outputFile =
  do h3 $ text "You have submitted the CASL or DOL library:"
     mapM_ (\ l -> text l >> br CGI.empty) $ lines str
     h3 $ text "Diagnostic messages of parsing and static analysis:"
     mapM_ (\ l -> text (show l) >> br CGI.empty) ds
     maybe CGI.empty printRes mres
     hr_S CGI.empty
     p $ do
       text "Not the result you expected? Please check the "
       hlink (read hetsManualUrl) $ text "Hets Manual"
       text "."
     hr_S CGI.empty
     p $ do
       text "Contact address: "
       hlink (read contactUrl) $ text contactText
    where
       adjustOutfile ext = baseUrlGenerated ++
         drop (length baseDirGenerated) (outputFile ++ ext)
       printRes res = do
            when (outputTxt conf) $ do
               heading3 "Pretty printed text:"
               formatTxt (asciiTxt res)
               p $ i $ do
                 text "You can download the "
                 hlink (read $ adjustOutfile ".txt") $ text "text file"
                 text " here. The file will be deleted after 30 minutes.\n"
            when (outputTex conf) $ do
               heading3 "LaTeX code:"
               p $ i $ do
                 text "You can download the "
                 hlink (read $ adjustOutfile ".pp.tex") $ text "LaTeX file"
                 text " here. For compiling the LaTeX output, you need "
                 hlink (read hetcaslStyUrl) $ text "hetcasl.sty"
                 text "."
               p $ i $ do
                 text "You can also download the "
                 hlink (read $ adjustOutfile ".pdf") $ text "PDF file"
                 text ". All files will be deleted after 30 minutes.\n"
            when (outputTree conf) $ do
               heading3 "XML parse tree:"
               formatTxt (parseTree res)
               p $ i $ do
                 text "You can download the "
                 hlink (read $ adjustOutfile ".pp.xml") $ text "XML file"
                 text " here. The file will be deleted after 30 minutes.\n"
       formatTxt = p . mapM_ (\ l -> text l >> br CGI.empty) . lines
       heading3 = h3 . text
