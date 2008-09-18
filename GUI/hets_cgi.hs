{- |
Module       : $Header$
Copyright    : (c) Heng Jiang, Klaus Lüttich Uni Bremen 2004-2006
License      : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer   : jiang@informatik.uni-bremen.de
Stability    : provisional
Portability  : non-portable(imports Logic.Logic)

Interface for web page with WASH/CGI
-}

module Main where

import WASH.CGI.CGI as CGI
import Driver.Options
import Driver.WriteFn
import Driver.ReadFn
import Driver.Version
import qualified Data.Map as Map
import qualified Common.Result as CRes
import Common.Doc (toText)
import Common.DocUtils (pretty)
import Common.ResultT
import Static.AnalysisLibrary
import Comorphisms.LogicGraph
import Static.DevGraph
import Syntax.AS_Library

import System.Random
import System.IO
import System.Time
import System.Cmd
import System.Posix.IO
import System.Posix.Types
import System.Posix.Files
import System.Posix.Process
import Control.Monad

------ Configuration section -------------------------

--- site specific configuration

-- a valid email address for the contact field / link
contact_url :: String
contact_url = "mailto:" ++ contact_text

-- the text displayed with the previous link
contact_text :: String
contact_text = "hets-devel@informatik.uni-bremen.de"

-- a directory which must be accessable and exposed by the web server,
-- where all the generated files are stored. This string must end with
-- a slash!
base_dir_generated :: String
base_dir_generated = "/home/www.informatik.uni-bremen.de/cofi/hets-tmp/"

-- path to the log file
logFile :: String
logFile = base_dir_generated ++ "hets.log"

-- the url pointing to the above specified directory
base_url_generated :: String
base_url_generated = "http://www.informatik.uni-bremen.de/cofi/hets-tmp/"

-- the directory where the Hets-lib repository is checked out. Must be
-- accessable by the cgi script
casl_lib_dir :: String
casl_lib_dir = "/home/cofi/Hets-lib"

-- the header of the LaTeX-file that will be processed by pdflatex
latex_header :: String
latex_header = unlines
  [ "\\documentclass{article}"
  , "\\usepackage{hetcasl}"
  , "\\usepackage{textcomp}"
  , "\\usepackage[T1]{fontenc}"
  , "\\begin{document}" ]

-- where is the pdflatex command for the generation of PDF-files
pdflatex_cmd :: String
pdflatex_cmd = "/usr/local/bin/pdflatex"

--- site independant configuration

cofi_url :: String
cofi_url =
  "http://www.informatik.uni-bremen.de/agbkb/forschung/formal_methods/CoFI/"

-- link to the homepage of hetcasl
hetcasl_url :: String
hetcasl_url = cofi_url ++ "HetCASL/index_e.htm"

hets_url :: String
hets_url = "http://www.dfki.de/sks/hets/"

-- link to the manual of Hets
hets_manual_url :: String
hets_manual_url = hets_url ++ "UserGuide.pdf"

-- link to the hetcasl.sty file
hetcasl_sty_url :: String
hetcasl_sty_url = hets_url ++ "hetcasl.sty"

------ End of Configuration section ------------------

webOpts :: HetcatsOpts
webOpts = defaultHetcatsOpts {outputToStdout = False,
                              libdir = casl_lib_dir,
                              verbose = 0}

data SelectedBoxes =
    SB {
        outputTree :: Bool,
        outputTxt  :: Bool,
        outputTex  :: Bool,
        archive    :: Bool
       } deriving Show

data Output =
    OP {ascii_txt  :: String,
        parse_tree :: String}

defaultOutput :: Output
defaultOutput = OP "" ""

newtype RESL = RESL (CRes.Result Output)

instance Read RESL where
    readsPrec _ _ = error "Read for \"RESL\" not implemented!!"

instance Show RESL where
    showsPrec _ _ _ = error "Show for \"RESL\" not implemented!!"

main :: IO()
main = run mainCGI

mainCGI :: CGI()
mainCGI =
  do ask $ html (do CGI.head (title $ text "Hets Web Interface")
                    CGI.body $ makeForm $ page1 ("Hets " ++ hetcats_version))

page1 :: String -> WithHTML x CGI ()
page1 title1 =
    do
      h1 $ text title1
      p $ do
        text "Enter a "
        hlink (read hetcasl_url) $ text "HetCASL"
        text
          " specification or library in the input zone, then press SUBMIT:"
      -- Input field
      input   <- p (makeTextarea "" (attr "rows" "22" ## attr "cols" "68"))
      -- check box
      selectTxt <- checkboxInputField (attr "valus" "yes")
      text "output pretty print ASCII"
      selectTex <- checkboxInputField (attr "valus" "yes")
      text "output pretty print LaTeX"
      selectTree <- checkboxInputField (attr "valus" "yes")
      text "output parse tree"
      selectAchiv <- p $ b $ checkboxInputField(attr "checked" "checked") ##
        text "If this checkbox is selected, your input will be logged!"
      -- submit/reset botton
      p (submit (F5 input selectTree selectTxt selectTex selectAchiv)
                 handle (fieldVALUE "Submit") >>
         submit0 reset (fieldVALUE "reset"))
      hr_S $ CGI.empty
      p $ (do text "Contact address: "
              hlink (read contact_url) $
                     text contact_text)

reset :: CGI()
reset = mainCGI

-- handle of the submit botton
handle :: HasValue i => F5 (i String) (i Bool) (i Bool) (i Bool) (i Bool) VALID
       -> CGI ()
handle (F5 input box1 box2 box3 box4) =
    let str  = CGI.value input
        selectedBoxes = SB {
                            outputTree = CGI.value box1,
                            outputTxt  = CGI.value box2,
                            outputTex  = CGI.value box3,
                            archive    = CGI.value box4
                           }
    in  do
        random1 <- io $ getRandom
        processID <- io $ getProcessID
        let outputfile = base_dir_generated ++ "result" ++ (show processID) ++
                            (show random1)
        RESL res <- io $ do r <- anaInput str selectedBoxes outputfile
                            return (RESL r)
        ask $ html ( do CGI.head (title $ text "HETS results")
                        CGI.body $ printR str res selectedBoxes outputfile)
    where
      getRandom :: IO Int
      getRandom = getStdRandom (randomR (100000,999999))

-- Analyze the input
anaInput :: String -> SelectedBoxes -> FilePath
         -> IO (CRes.Result Output)
anaInput contents selectedBoxes outputfiles =
   do
      let CRes.Result parseErrors mast =
              read_LIB_DEFN_M logicGraph webOpts "<stdin>" contents noTime
      maybe (return $ CRes.Result parseErrors Nothing)
            ana_ast mast

   where
      ana_ast ast =
         do
         CRes.Result ds mres <-
             runResultT (ana_LIB_DEFN logicGraph webOpts emptyLibEnv ast)
         let ds1 = filter diagFilter ds
         if CRes.hasErrors ds1
            then return $ CRes.Result ds1 Nothing
            else
              do
                 maybe (return $ CRes.Result ds1 Nothing)
                       (\res ->
                          do saveLog (archive selectedBoxes)
                             process_result ds1 res outputfiles selectedBoxes)
                       mres

      diagFilter d = case CRes.diagKind d of
                     CRes.Hint  -> False
                     CRes.Debug -> False
                     _     -> True

      process_result :: [CRes.Diagnosis]
                      -> (LIB_NAME, LIB_DEFN, DGraph, LibEnv)
                      -> FilePath
                      -> SelectedBoxes
                      -> IO (CRes.Result Output)
      process_result ds (libName, libDefn, _, libEnv) outputfile conf =
          do let gannos = globalAnnos $ Map.findWithDefault emptyDG
                          libName libEnv
                 fMode = foldl unionFileModes nullFileMode
                                [ownerReadMode, ownerWriteMode,
                                 groupReadMode, groupWriteMode,
                                 otherReadMode]
                 resAsc = shows (toText gannos $ pretty libDefn) "\n"
             when (outputTex conf)
                  (do
                    let pptexFile = outputfile ++ ".pp.tex"
                        latexFile = outputfile ++ ".tex"
                        pdfFile   = outputfile ++ ".pdf"
                        tmpFile   = outputfile ++ ".tmp"
                    write_casl_latex webOpts
                         gannos pptexFile libDefn
                    writeFile latexFile (latex_header ++
                                         "\\input{"++ pptexFile ++
                                         "}\n \\end{document}\n")
                    setFileMode pptexFile fMode
                    setFileMode latexFile fMode

                    system ("(cd "++ base_dir_generated ++" ; ls -lh "++
                            pdflatex_cmd ++" ; "++ pdflatex_cmd ++ " " ++
                           latexFile ++ ") > " ++ tmpFile)
                    setFileMode pdfFile fMode
                  )
             when (outputTxt conf)
                  (do
                    let txtFile = outputfile ++ ".txt"
                    write_casl_asc webOpts gannos txtFile libDefn
                    setFileMode txtFile fMode
                  )
             return (CRes.Result ds $ Just $ selectOut conf libDefn resAsc)

      selectOut :: SelectedBoxes -> LIB_DEFN -> String -> Output
      selectOut conf libDefn ra =
          defaultOutput { ascii_txt  = if outputTxt conf then ra else ""
                        , parse_tree = if outputTree conf
                                          then show libDefn
                                          else ""
                        }

      -- log file
      saveLog :: Bool -> IO()
      saveLog willSave =
          when willSave $ do
                  fd <- openFd logFile ReadWrite Nothing
                               defaultFileFlags{append = True}
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

catcher :: IO a -> IO String
catcher act = catch (act >> return "") (return . show)


-- Print the result
printR :: String -> CRes.Result Output -> SelectedBoxes
       -> FilePath
       -> WithHTML x CGI ()
-- printR _ _ _ _ = CGI.empty
printR str (CRes.Result ds mres) conf outputFile =
  do h1 $ text "You have submitted the HetCASL library:"
     mapM_ (\l -> text l >> br CGI.empty) $ lines str
     h1 $ text "Result of parsing and static checking:"
     mapM_ (\l -> h3 $ text l >> br CGI.empty) (Prelude.map show ds)
     maybe CGI.empty printRes mres
     -- case mres of
     --   Just res -> printRes res
     --   Nothing  -> CGI.empty
     hr_S $ CGI.empty
     p (do text "Not the result you expected ? Please check the "
           hlink (read hets_manual_url) $ text "Hets Manual"
           text "."
       )
     hr_S $ CGI.empty
     p $ (do text "Contact address: "
             hlink (read contact_url) $
                   text contact_text
         )
    where
       adjustOutfile ext = base_url_generated ++
         drop (length base_dir_generated) (outputFile ++ ext)
       printRes res =
         do
            when (outputTxt conf)
                 (do
               heading3 "ASCII code:"
               format_txt (ascii_txt res)
               p $ i(do text "You can download the "
                        hlink (read $ adjustOutfile ".txt")
                                  $ text "ASCII file"
                        text " here. The file will be deleted after \
                             \30 minutes.\n"
                    )
                 )
            when (outputTex conf)
                 (do
               heading3 "LaTeX code:"
               p $ i(do text "You can download the "
                        hlink (read $ adjustOutfile ".pp.tex")
                                  $ text "LaTeX file"
                        text " here. For compiling the LaTeX output, you need "
                        hlink (read hetcasl_sty_url) $ text "hetcasl.sty"
                        text "."
                    )
               p $ i(do text "You can also download the "
                        hlink (read $ adjustOutfile ".pdf")
                                  $ text "PDF file"
                        text ". All files will be deleted after 30 minutes.\n"
                    )
                 )
            when (outputTree conf)
                 (do
               heading3 "Parse tree:"
               format_txt (parse_tree res)
                 )
       format_txt txt = p $ mapM_ (\l -> text l >> br CGI.empty) $ lines txt
       heading3 = h3 . text
