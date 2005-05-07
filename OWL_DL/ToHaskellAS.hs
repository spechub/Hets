module Main where

import OWL_DL.ReadWrite
import Common.ATerm.Lib
import System.Exit
import System(getArgs, system)
import qualified Common.Lib.Map as Map
import qualified List as List


main :: IO()
main =
    do filename <- getArgs
       if null filename then
          error "Usage: readAStest <URI>"
          else do exitCode <- system ("./processor " ++ head filename)
                  putStrLn $ show exitCode
                  if exitCode == ExitSuccess then
                     processor2 "output.term"
                     else error ("opne file " ++ (head filename) ++ "error")

processor2 :: String -> IO()
processor2 filename = 
    do d <- readFile filename
       let aterm = getATermFull $ readATerm d
       case aterm of
          AAppl "OWLParserOutput" [valid, msg, ns, onto] _ ->
              do
                  putStrLn $ fromATerm valid
                  putStrLn $ show (buildMsg msg)
                  putStrLn $ show (buildNS ns)
                  putStrLn $ show $ reducedDisjoint ((fromShATerm $ toATermTable onto)::Ontology)
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

                                    
