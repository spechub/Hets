{-|
Module       : $Header$
Copyright    : (c) Heng Jiang, Uni Bremen 2004
License      : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer   : jiang@tzi.de
Stability    : provisional
Portability  : non-portable

   Interface for web page
-}

module GUI.WebInterface where

import Driver.Options
import Driver.WriteFn
import Common.Lib.Map as Map
import Char
import Static.AnalysisLibrary
import Comorphisms.LogicGraph
import Logic.Grothendieck
import Static.DevGraph
import Maybe
-- import Debug.Trace

{- -}
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

{-  -}
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

{-  -}
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

{-  -}
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
      putStrLn "<font face=\"Arial\" size=+2>"
      res  <- anaString logicGraph defl opt emptyLibEnv sp Nothing  
      putStrLn "...</font>"
      web_interface_aux1 pars res outputfile

   where                
         web_interface_aux1 (show_trees, show_env, show_latex) res outfile = 
             do 
               case res of 
                  Just (libName, libDefn, _, libEnv) ->
                     let (globalAnnos, _, _) =  fromJust $ Map.lookup libName libEnv
                     in do 
                        if show_trees then      
                           do
                           putStrLn "<H2>Parse tree:</H2>"
                           putStrLn $ show libDefn
                           -- globalContexttoShATerm outfile (globalAnnos, globalEnv, dGraph)
                           else return()
                        if show_env then
                           do
                           putStrLn "<H2>ASCII code:</H2>"
                           result <- write_casl_asc_stdout opt globalAnnos libDefn
                           putStrLn $ foldl (\x y -> x ++ "<br>" ++ y) "" (lines result)
                           else return () 
                        if show_latex then
                           do
                           putStrLn "<H2>LaTeX code:</H2>"
                           result <- write_casl_latex_stdout opt globalAnnos libDefn
                           write_casl_latex opt globalAnnos outfile libDefn
                           putStrLn result
                           write_HTML outfile
                           else return ()
                  Nothing -> return ()

         write_HTML :: FilePath -> IO()
         write_HTML downF = 
             do
              putStrLn "<P><I>You can here <A HREF=\""
              putStrLn "http://www.informatik.uni-bremen.de/cofi/hets-tmp/"
               -- putStrLn ((takeWhile (\x->x /= '.') downF) ++ ".pdf")
              putStrLn $ drop 24 downF
              putStrLn "\">the LaTeX file</A> download. The file will be deleted after 30 minutes<br>"
              putStrLn "For compiling the LaTeX output, you need <A HREF=\"http://www.informatik.uni-bremen.de/agbkb/forschung/formal_methods/CoFI/hets/hetcasl.sty\">hetcasl.sty.</I></P>"

              {-where getName filepath =
                        let rest =  dropWhile (\x -> not (x == '/')) (teil filepath)
                        in  if length rest > 0 then getName rest
                            else filepath
                -}          
