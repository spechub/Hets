module GUI.WebInterface where

import Options
import WriteFn
import Common.Lib.Map as Map
import Char
import Static.AnalysisLibrary
import Comorphisms.LogicGraph
import Logic.Grothendieck
import Static.DevGraph
import Maybe

-- import Debug.Trace

mapString :: Char -> Int
mapString c = case c of
                '0' -> 0
	        '1' -> 1
		'2' -> 2
		'3' -> 3
		'4' -> 4
		'5' -> 5
		'6' -> 6
		'7' -> 7
		'8' -> 8
		'9' -> 9
		'a' -> 10
		'b' -> 11
		'c' -> 12
		'd' -> 13
		'e' -> 14
		'f' -> 15
		'A' -> 10
		'B' -> 11
		'C' -> 12
		'D' -> 13
		'E' -> 14
		'F' -> 15
		s   -> ord s

convert_cgi :: String -> String
convert_cgi "" = ""
convert_cgi (s0:rest) =
               case s0 of
		 '%'  -> if (take 2 rest == "0D") then convert_cgi $ drop 2 rest 
			 else 
			     case rest of
			       s1:s2:rest' -> 
				   (chr((mapString s1)*16 + mapString s2)):(convert_cgi rest')
			       _           -> s0:(convert_cgi rest)
	         '+'  -> ' ':(convert_cgi rest)
		 _    -> s0:(convert_cgi rest)

convert_arg :: (String, String) -> String
convert_arg (arg, spec) = 
    case spec of
            's':'p':'e':'c':'=':s -> convert_cgi s  
	    _                     -> arg

scanwords :: String -> [String]
scanwords str  
	    | length str == 0 = []   
	    | otherwise       = let headStr = takeWhile (\x -> not (x == '&' || x == '\n')) str
				in  headStr:(scanwords $ drop ((length headStr) +1) str)

-- Output File is /tmp/output.web

webInterface :: String -> HetcatsOpts -> IO()
webInterface contents opt =
   do
      defl <- lookupLogic "logic from command line: " (defLogic opt) logicGraph
      let args = scanwords contents
	  outputfile = head args
	  pars = ("tree=yes" `elem` args, "env=yes" `elem` args , "tex=yes" `elem` args)
	  sp = foldl (curry convert_arg) "" (tail args)

      -- putStrLn $ show pars
      -- putStrLn sp
      -- putStrLn $ unwords args
      res  <- anaString logicGraph defl opt emptyLibEnv sp Nothing      
      web_interface_aux1 pars res outputfile

   where 		
         web_interface_aux1 (show_trees, show_env, show_latex) res outfile = 
	     do 
	       case res of 
	          Just (libName, libDefn, _, libEnv) ->
		     let (globalAnnos, globalEnv, dGraph) =  fromJust $ Map.lookup libName libEnv
	             in do 
			if show_trees then 	
			   do
			   putStrLn "<H2>Parse Tree:</H2>"
			   putStrLn $ show libDefn
			   -- globalContexttoShATerm outfile (globalAnnos, globalEnv, dGraph)
			   else return()
		        if show_env then
			   do
			   putStrLn "<H2>Global Environment:</H2>"
			   result <- write_casl_asc_stdout opt globalAnnos libDefn
			   putStrLn $ foldl (\x y -> x ++ "<br>" ++ y) "" (lines result)
			   else return () 
			if show_latex then
			   do
			   putStrLn "<H2>LaTex code:</H2>"
			   result <- write_casl_latex_stdout opt globalAnnos libDefn
			   putStrLn result
		           else return ()
		  Nothing -> return ()
			    

{-
fun  convert_cgi [] = []
|   convert_cgi ("%"::"0"::"D"::s) = convert_cgi s
|   convert_cgi ("%"::s1::s2::rest) = (chr( (mapstring s1) * 16 + mapstring s2)::
                                                                  convert_cgi rest)
|   convert_cgi ("+"::s) = ((" "::(convert_cgi s)))
|   convert_cgi (s::s1) = s::convert_cgi s1

fun convert_arg (_,("s"::"p"::"e"::"c"::"="::s)) = implode (convert_cgi s)
  | convert_arg (arg,_) = arg
fun web_interface s =
let val args = scanwords (fn a => not (a="&")) (explode s@["&"])
    val del_blank = implode o (filter_out is_blank) o explode
    val args' = map del_blank args
-- the following line must be adapted, construct a value of type HetcatsOpts
    val pars = ("tree=yes" mem args',"env=yes" mem args',"tex=yes" mem args')
    val sp = foldl convert_arg ("",map explode args')
-- the following line must be adpated to Hets, see hets.hs or Static/AnalysisLibrary.hs
    val res =  parse_and_check (!basic_lib_env) (fn x => ()) true sp
               handle exn => (empty_lib_env,empty_global_env,empty_lib_defn)
in  
    web_interface_aux1 pars res
end

and web_interface_aux1 (show_trees,show_env,latex) (_,genv,trees) =

    ( 
      if show_trees then
      -- use showPretty instead of print
        (print (print_heading true "Parse tree");
         print (AT.mkA (trees)) )
     else ()
     handle exn => print ("Internal error #2. Please send us your specification");
     if show_env then
        (print (print_heading true "Global Environment");
         print (format_text HTML_pre (StructuredPrint.print_global_env genv trees))
        )
     else ();
     if latex then
        (print (print_heading true "LaTeX code");
         (*print (format_text HTML_pre (Makellos.mkTeX (true,genv,trees)) ) *)
         print (format_text HTML_pre "Sorry, not LaTeX output yet. Use CATS 0.56")
        )
     else ()
    )

-}
