{-|
Module       : $Header$
Copyright    : (c) Heng Jiang, Uni Bremen 2004
Licence      : similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer   : hets@tzi.de
Stability    : provisional
Portability  : non-portable

   Interface for web page with WASH/CGI

   todo:
     - default for checkbox regarding logging of input must be "selected" 
       .. done
     - temporary files should be created with these permissions:
        -rw-rw-r-- (than every member of grp agcofi can remove 
		    temporary files)
       .. done
     - LaTeX code should only be available as download  .. done
     - ASCII code should also be available as download  .. done
     - additionally to (show random) the temporary file names 
       should contain a fraction of the seconds since epoch and/or
       the ProcessID
       .. done
     - english sentences in the output need corrections
       .. ???
     - when the HTML-PrettyPrinting is available: generated HTML-Code 
       instead of poorly rendered ASCII has to be inserted as response
       .. ???
-}

module Main where

import CGI
import Options
import WriteFn
import Common.Lib.Map as Map
import Static.AnalysisLibrary
import Comorphisms.LogicGraph
import Static.DevGraph
import Syntax.AS_Library
import Maybe
import Random
import IO
import Time
import System.Posix.IO
import System.Posix.Types
import System.Posix.Files
import System.Posix.Process

main :: IO()
main =
    run mainCGI

mainCGI :: CGI()
mainCGI =
    do 
       version <- io $ readFile "/home/cofi/www/CASL/HETS/version"
       ask $ html (do CGI.head (title $ text "Hets Web Interface")
	       	      CGI.body $ makeForm $ page1 ("Hets " ++ version)) 

page1 :: String -> WithHTML x CGI ()
page1 title =
    do    
      h1 $ text title
      p (text "Enter a CASL 1.0.1 specification or library in the input zone, then press SUBMIT:")
      -- Input field
      input   <- p (makeTextarea "" (attr "rows" "22" ## attr "cols" "68"))
      -- check box
      selectTree <- checkboxInputField (attr "valus" "yes")
      text "output parse tree"
      selectEnv <- checkboxInputField (attr "valus" "yes")
      text "output pretty print ASCII"
      selectTex <- checkboxInputField (attr "valus" "yes")
      text "output pretty print LaTeX"
      selectAchiv <- p $ b ( checkboxInputField(attr "checked" "checked") ##
			 text "If this checkbox is selected, your input will be logged!")
      -- submit/reset botton
      p (submit (F5 input selectTree selectEnv selectTex selectAchiv)
	         handle (fieldVALUE "Submit") >>
	 submit0 reset (fieldVALUE "reset"))
      hr_S $ CGI.empty
      p $ (do text "Contact address: "
	      hlink (read "mailto:cofi@informatik.uni-bremen.de") $ 
	             text "cofi@informatik.uni-bremen.de")

reset :: CGI()
reset = mainCGI

-- handle of the submit botton
handle (F5 input box1 box2 box3 box4) = 
    let str  = value input
	tree = value box1
	env  = value box2
	tex  = value box3
	achiv= value box4 
    in  do
	random <- io $ getRandom
	processID <- io $ getProcessID
	let outputfileTEX = "/home/www/cofi/hets-tmp/result" ++ (show processID) ++
			    (show random) ++ ".pp.tex"
	    outputfileASC = "/home/www/cofi/hets-tmp/result" ++ (show processID) ++
			    (show random) ++ ".txt"
	res <- io $ anaInput str (tree, env, tex) (outputfileASC, outputfileTEX)
	ask $ html ( do CGI.head (title $ text "HETS results")
			CGI.body $ printR str res (tree, env, tex) 
	                   	     (outputfileASC, outputfileTEX))
	io $ saveLog achiv str
    where
      -- log file
      saveLog :: Bool -> String -> IO()
      saveLog willSave contents 
	| willSave =
	          do 
		  let logFile = "/home/www/cofi/hets-tmp/hets.log"
		  fd <- openFd logFile ReadWrite Nothing defaultFileFlags{append = True} 
		  fileSize <- sizeof fd
		  let filelock = (WriteLock, AbsoluteSeek, 0, fileSize)  
		      fileunlock = (Unlock, AbsoluteSeek, 0, fileSize)
		  aktTime <- timeStamp 
		  setLock fd filelock
		  fdWrite fd (aktTime ++ "\n" ++ contents ++ "\n\n")  
  		  setLock fd fileunlock
		  closeFd fd
	| otherwise = return ()
       
      getRandom :: IO Int
      getRandom = getStdRandom (randomR (100000,999999))

      timeStamp :: IO String
      timeStamp =  do t <- getClockTime		      
		      ct <- toCalendarTime t
		      return $ calendarTimeToString ct

      sizeof :: Fd -> IO FileOffset
      sizeof fd = do fstatus <- getFdStatus fd
		     return $ fileSize fstatus

-- Analyze the input
anaInput :: String -> (Bool,Bool,Bool) -> (FilePath, FilePath) -> IO([(String, String)])
anaInput contents showS outputfileS =
   do 
      res  <- anaString logicGraph defaultLogic defaultHetcatsOpts{outputToStdout = False} emptyLibEnv contents Nothing
      anaInput_aux res outputfileS showS 

   where 		
      anaInput_aux :: Maybe(LIB_NAME, LIB_DEFN, DGraph, LibEnv) 
		      -> (FilePath, FilePath)
                      -> (Bool, Bool, Bool) 
		      -> IO([(String, String)])
      anaInput_aux res (outputfileASC, outputfileTEX) (showTree, showEnv, showTex) =
	  case res of 
	    Just (libName, libDefn, _, libEnv) ->
	      do 
		 let (globalAnnos, _, _) =  fromJust $ Map.lookup libName libEnv
		     fileMode = foldl unionFileModes nullFileMode 
				[ownerReadMode, ownerWriteMode, groupReadMode, groupWriteMode, otherReadMode]
		 resAsc <- write_casl_asc_stdout defaultHetcatsOpts globalAnnos libDefn
		 resTex <- write_casl_latex_stdout defaultHetcatsOpts globalAnnos libDefn
		 if showTex then
		    do
                    write_casl_latex defaultHetcatsOpts globalAnnos outputfileTEX libDefn
		    setFileMode outputfileTEX fileMode
		    else return()
		 if showEnv then
		    do
		    write_casl_asc defaultHetcatsOpts globalAnnos outputfileASC libDefn
		    setFileMode outputfileASC fileMode
		    else return()
	         return $ selectOut [showTree, showEnv, showTex] libDefn resAsc resTex
	    Nothing -> return ([])

      selectOut :: [Bool] -> LIB_DEFN -> String -> String -> [(String, String)]
      selectOut [] _ _ _ = []
      selectOut (hb:rb) libDefn ra rt 
		| length rb == 2 && hb = 
			("Parse tree:", show libDefn):(selectOut rb libDefn ra rt)
		| length rb == 1 && hb = 
			("ASCII code:", ra):(selectOut rb libDefn ra rt)
		| length rb == 0 && hb = 
		      	("LaTeX code:", rt):(selectOut rb libDefn ra rt) 
		| otherwise = selectOut rb libDefn ra rt

-- Print the result		    
printR :: String -> [(String, String)] -> (Bool, Bool, Bool) -> (FilePath, FilePath) 
          -> WithHTML x CGI ()
printR str result selectedBoxes outputFiles =
    do 
       h1 $ text "You have submitted the HetCASL library:"
       mapM_ (\l -> text l >> br CGI.empty) $ lines str
       h1 $ text "Result of parsing and static checking:"
       h2 $ text "Analyzing spec cache ..."
       printRes selectedBoxes outputFiles result 
       hr_S $ CGI.empty
       p (do text "Not the result you expected ? Please check the "
	     hlink (read "http://www.informatik.uni-bremen.de/agbkb/forschung/formal_methods/CoFI/hets/UserGuide.pdf") $ text "Hets Manual"
	     text "."
	 )
       hr_S $ CGI.empty
       p $ (do text "Contact address: "
	       hlink (read "mailto:cofi@informatik.uni-bremen.de") $
		      text "cofi@informatik.uni-bremen.de"
	   )
    where 
        printRes :: (Bool, Bool, Bool) -> (FilePath, FilePath) -> 
		    [(String, String)] -> WithHTML x CGI ()
	printRes _ _ [] = CGI.empty
	printRes (isTree, isEnv, isTex) (outputfileASC, outputfileTEX) 
		     ((title_ana, text_ana):rR) =
          do h3 $ text title_ana
       	     p $ mapM_ (\l -> text l >> br CGI.empty) $ lines text_ana
	     if isTree then
		printRes (False, isEnv, isTex) (outputfileASC, outputfileTEX) rR
		else if isEnv then
		        do  
			p $ i(do text "You can here the " 
			         hlink (read ("http://www.informatik.uni-bremen.de/cofi/hets-tmp/" ++
					      (drop 24 outputfileASC))) $ text "ACSII file" 
			         text " download. The file will be deleted after 30 minutes.\n" 
			      )
			printRes (isTree, False, isTex) (outputfileASC, outputfileTEX) rR
			else if isTex then
			        do
				p $ i(do  text "You can here the " 
				          hlink (read ("http://www.informatik.uni-bremen.de/cofi/hets-tmp/" ++
						       (drop 24 outputfileTEX))) $ text "LaTeX file" 
				          text " download. The file will be deleted after 30 minutes.\n" 
				     )
				p $ i( do  text "For compiling the LaTeX output, you need " 
				           hlink (read "http://www.informatik.uni-bremen.de/agbkb/forschung/formal_methods/CoFI/hets/hetcasl.sty") $ text "hetcasl.sty" 
				           text "."
				     )
				printRes (isTree, isEnv, False) (outputfileASC, outputfileTEX) rR
				else printRes (isTree, isEnv, isTex) (outputfileASC, outputfileTEX) rR




