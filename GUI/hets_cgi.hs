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
     - LaTeX code should only be available as download
     - ASCII code should also be available as download
     - additionally to (show random) the temporary file names 
       should contain a fraction of the seconds since epoch and/or
       the ProcessID
     - english sentences in the output need corrections
     - when the HTML-PrettyPrinting is available: generated HTML-Code 
       instead of poorly rendered ASCII has to be inserted as response
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
      selectAchiv <- p ( checkboxInputField(attr "checked" "checked") ##
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
	let outputfile = "/home/www/cofi/hets-tmp/result" ++ (show random) ++ ".pp.tex"
    	io $ saveLog achiv str
	res <- io $ anaInput str (tree, env, tex) outputfile
	ask $ html ( do CGI.head (title $ text "HETS results")
			CGI.body $ printR str res tex outputfile)
    where
      saveLog :: Bool -> String -> IO()
      saveLog will contents 
	| will = do 
		    let logFile = "/home/www/cofi/hets-tmp/hets.log"
		    aktTime <- timeStamp
		    file <- openFile logFile AppendMode
		    hPutStr file (aktTime ++ "\n" ++ contents ++ "\n\n")  -- must Synchronized
		    hClose file
	| otherwise = return ()

      getRandom :: IO Int
      getRandom = getStdRandom (randomR (100000,999999))

      timeStamp :: IO String
      timeStamp =  do t <- getClockTime		      
		      ct <- toCalendarTime t
		      return $ calendarTimeToString ct

printR :: String -> [(String, String)] -> Bool -> FilePath -> WithHTML x CGI ()
printR str result isTex outputfile =
    do 
       h1 $ text "You have submitted the HetCASL library:"
       mapM_ (\l -> text l >> br CGI.empty) $ lines str
       h1 $ text "Result of parsing and static checking:"
       h2 $ text "Analyzing spec cache ..."
       printRes result 
       if isTex then
	 do
          p $ i(do  text "You can here the " 
	            hlink (read ("http://www.informatik.uni-bremen.de/cofi/hets-tmp/" ++
				(drop 24 outputfile))) $ text "LaTeX file" 
	            text " download. The file will be deleted after 30 minutes.\n" 
	      )
	  p $ i( do  text "For compiling the LaTeX output, you need " 
	             hlink (read "http://www.informatik.uni-bremen.de/agbkb/forschung/formal_methods/CoFI/hets/hetcasl.sty") $ text "hetcasl.sty" 
	             text "."
	      )
	 else CGI.empty
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
        printRes :: [(String, String)] -> WithHTML x CGI ()
	printRes [] = CGI.empty
	printRes ((title_ana, text_ana):rR) =
    		do h3 $ text title_ana
       		   p $ mapM_ (\l -> text l >> br CGI.empty) $ lines text_ana
       		   printRes rR

anaInput :: String -> (Bool,Bool,Bool) -> FilePath -> IO([(String, String)])
anaInput contents showS outputfile =
   do 
      res  <- anaString logicGraph defaultLogic defaultHetcatsOpts{outputToStdout = False} emptyLibEnv contents Nothing
      anaInput_aux res outputfile showS 

   where 		
      anaInput_aux :: Maybe(LIB_NAME, LIB_DEFN, DGraph, LibEnv) 
		      -> FilePath
                      -> (Bool, Bool, Bool) 
		      -> IO([(String, String)])
      anaInput_aux res outputfile (showTree, showEnv, showTex) =
	  case res of 
	    Just (libName, libDefn, _, libEnv) ->
	      do 
		 let (globalAnnos, _, _) =  fromJust $ Map.lookup libName libEnv

		 resAsc <- write_casl_asc_stdout defaultHetcatsOpts globalAnnos libDefn
		 resTex <- write_casl_latex_stdout defaultHetcatsOpts globalAnnos libDefn
		 if showTex then
                    write_casl_latex defaultHetcatsOpts globalAnnos outputfile libDefn
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

