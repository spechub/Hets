{- |
Module      :  $Header$
Copyright   :  Heng Jiang, Uni Bremen 2004-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  jiang@tzi.de
Stability   :  provisional
Portability :  portable

-}

module Main where

import OWL_DL.AS
import OWL_DL.ReadWrite

import Common.ATerm.ReadWrite
import Common.ATerm.Unshared
import System.Exit
import System(getArgs, system)
import System.Environment(getEnv)
import qualified Common.Lib.Map as Map
import qualified List as List


main :: IO()
main =
    do args <- getArgs
       if (null args) || (length args > 2) then
          error "Usage: readAStest [option] <URI or file>"
          -- default option : output OWL_DL abstract syntax
          else if length args == 1 then     
                  process True args  
                  else case head args of
                       "-a" -> process True $ tail args          -- output abstract syntax
                       "-t" -> process False $ tail args         -- output ATerm
                       _    -> error ("unknow option: " ++ (head args))


       where isURI :: String -> Bool
             isURI str = let pre = take 7 str
                         in if pre == "http://" || pre == "file://" 
                               then True
                               else False

             run :: ExitCode -> Bool -> IO()
             run exitCode abs' 
                 | exitCode == ExitSuccess =  processor2 abs' "output.term"
                 | otherwise =  error "process stop!"

             process :: Bool -> [String] -> IO()
             process abs' args  = 
                 do
                  pwd <- getEnv "PWD" 
                  if (head $ head args) == '-' then
                     error "Usage: readAStest [option] <URI or file>"
                     else if isURI $ head args then
                             do exitCode <- system ("./processor " ++ head args)
                                run exitCode abs'
                             else if (head $ head args) == '/' then
                                     do exitCode <- system ("./processor file://" ++ head args)
                                        run exitCode abs'
                                     else do exitCode <- system ("./processor file://" ++ pwd ++ "/" ++ head args)
                                             run exitCode abs'
                        
-- | 
-- the first argument it decides whether the abstract syntax or ATerm is shown,
-- the second argument is the ATerm file which can be read in.
processor2 :: Bool -> String  -> IO()
processor2 abs' filename = 
    do d <- readFile filename
       let aterm = getATermFull $ readATerm d
       if abs' then
          outputList aterm
          else putStrLn $ show aterm

outputList :: ATerm -> IO()
outputList aterm =
    case aterm of
       AList paarList _ -> 
           outputAS paarList
       _ -> error "error by reading file."

-- | 
-- this function show the abstract syntax of each OWL ontology from 
-- UOPaar list.
outputAS :: [ATerm] -> IO()
outputAS [] = putStrLn ""
outputAS (aterm:res) =
       case aterm of
          AAppl "UOPaar" [AAppl uri _  _, AAppl "OWLParserOutput" [valid, msg, ns, onto] _] _ ->
              do
                putStrLn ("URI: " ++ uri)
                putStrLn $ fromATerm valid
                putStrLn $ show (buildMsg msg)
                putStrLn $ show (buildNS ns)
                putStrLn $ show $ propagateNspaces (buildNS ns) $ createEqClass $ reducedDisjoint (fromATerm onto::Ontology)
                outputAS res
          _ -> error "false file."

    where buildNS :: ATerm -> Namespace
          buildNS at = case at of
                       AAppl "Namespace" [AList nsl _] _ ->
                           mkMap nsl (Map.empty)
                       _ -> error ""
          
          mkMap :: [ATerm] -> Namespace -> Namespace
          mkMap [] mp = mp 
          mkMap (h:r) mp = case h of
                           AAppl "NS" [name, uri] _ ->
                               mkMap r (Map.insert (fromATerm name) (fromATerm uri) mp)
                           _ -> error "illegal namespace."

          buildMsg :: ATerm -> Message
          buildMsg at = case at of
                        AAppl "Message" [AList msgl _] _ ->
                                mkMsg msgl (Message [])
                        _ -> error "illegal message:)"

          mkMsg :: [ATerm] -> Message -> Message
          mkMsg [] (Message msg) = Message (reverse msg)
          mkMsg (h:r) (Message preRes) =
                case h of
                        AAppl "Message" [a,b,c] _ ->
                            mkMsg r (Message ((fromATerm a, fromATerm b, fromATerm c):preRes))
                        AAppl "ParseWarning" warnings _ ->
                            mkMsg r (Message (("ParserWarning", fromATerm $ head warnings, ""):preRes))
                        AAppl "ParseError" errors _ ->
                            mkMsg r (Message (("ParserError", fromATerm $ head errors, ""):preRes))
                        _ -> error "unknow message."

          reducedDisjoint :: Ontology -> Ontology
          reducedDisjoint (Ontology oid directives) = 
              Ontology oid (rdDisj $  List.nub directives)

            where rdDisj :: [Directive] -> [Directive]
                  rdDisj [] = []
                  rdDisj (h:r) = case h of
                                 Ax (DisjointClasses _ _ _) ->
                                     if any (eqClass h) r then
                                        rdDisj r
                                        else h:(rdDisj r)
                                 _ -> h:(rdDisj r)
                  
                  eqClass :: Directive -> Directive -> Bool
                  eqClass dj1 dj2 =
                      case dj1 of
                      Ax (DisjointClasses c1 c2 _) ->
                         case dj2 of
                         Ax (DisjointClasses c3 c4 _) ->
                             if (c1 == c4 && c2 == c3) 
                                then True
                                else False
                         _ -> False
                      _ -> False

          createEqClass :: Ontology -> Ontology
          createEqClass (Ontology oid directives) =
              Ontology oid (findAndCreate directives)
           where findAndCreate :: [Directive] -> [Directive]
                 findAndCreate [] = []
                 findAndCreate (h:r) = 
                     case h of
                       Ax (Class cid isdep Complete annos desps) ->
                          (Ax (EquivalentClasses (DC cid) desps)):(findAndCreate r)
                       _ -> h:(findAndCreate r)









