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
import OWL_DL.StructureAna
-- import Data.Graph.Inductive.Tree
import Data.Graph.Inductive.Graph
import Static.DevGraph
-- import Data.Graph.Inductive.Internal.FiniteMap
import OWL_DL.StaticAna
import OWL_DL.Sign
import Common.GlobalAnnotations
import Common.Result
import Common.AS_Annotation

main :: IO()
main =
    do args <- getArgs
       if (null args) || (length args > 2) then
          error "Usage: readAStest [option] <URI or file>"
          -- default option : output OWL_DL abstract syntax
          else if length args == 1 then     
                  process 'a' args  
                  else case head args of
                       "-a" -> process 'a' $ tail args   -- output abstract syntax
                       "-t" -> process 't' $ tail args   -- output ATerm
		       "-s" -> process 's' $ tail args   -- output DevGraph from structure analysis
		       "-r" -> process 'r' $ tail args   -- output result of static analysis
		       _    -> error ("unknow option: " ++ (head args))


       where isURI :: String -> Bool
             isURI str = let preU = take 7 str
                         in if preU == "http://" || preU == "file://" 
                               then True
                               else False

             run :: ExitCode -> Char -> IO()
             run exitCode opt 
                 | exitCode == ExitSuccess =  processor2 opt "output.term"
                 | otherwise =  error "process stop!"

             process :: Char -> [String] -> IO()
             process opt args  = 
                 do
                  pwd <- getEnv "PWD" 
                  if (head $ head args) == '-' then
                     error "Usage: readAStest [option] <URI or file>"
                     else if isURI $ head args then
                             do exitCode <- system ("./processor " ++ head args)
                                run exitCode opt
                             else if (head $ head args) == '/' then
                                     do exitCode <- system ("./processor file://" ++ head args)
                                        run exitCode opt
                                     else do exitCode <- system ("./processor file://" ++ pwd ++ "/" ++ head args)
                                             run exitCode opt
                        
-- | 
-- the first argument it decides whether the abstract syntax or ATerm is shown,
-- the second argument is the ATerm file which can be read in.
processor2 :: Char -> String  -> IO()
processor2 opt filename = 
    do d <- readFile filename
       let aterm = getATermFull $ readATerm d
       case opt of
       -- 'a' -> outputList 'a' aterm
            't' -> putStrLn $ show aterm
	    's' -> outputList 's' aterm
	    'r' -> outputList 'r' aterm
	    _   -> outputList 'a' aterm

outputList :: Char -> ATerm -> IO()
outputList opt aterm =
    case aterm of
       AList paarList _ -> 
	   case opt of 
	   'a' -> outputAS paarList
	   's' -> printDG paarList
	   'r' -> printResOfStatic paarList
	   u   -> error ("unknow option: -" ++ [u])
       _ -> error "error by reading file."

-- | 
-- this function show the abstract syntax of each OWL ontology from 
-- UOPaar list.
outputAS :: [ATerm] -> IO()
outputAS [] = putStrLn ""
outputAS (aterm:res) =
       case aterm of
          AAppl "UOPaar" [_, AAppl "OWLParserOutput" [valid, msg, _, _] _] _ ->
              do  let (uri, namespace, ontology) = ontologyParse aterm
                  putStrLn ("URI: " ++ uri)
		  putStrLn $ fromATerm valid
		  putStrLn $ show (buildMsg msg)
		  putStrLn $ show namespace
		  putStrLn $ show ontology
                  outputAS res
          _ -> error "false file."

instance Show DGLinkLab where
    show (DGLink _ _ _) = show ""
instance Show DGNodeLab where
    show (DGNode name _ _ _ _) = show name
    show (DGRef name _ _ _ _) = show name
    
-- for structure analysis
printDG :: [ATerm] -> IO()
printDG al =  
    do let p = paarWithUriAndOntology $ reverse $ parsingAll al
       putStrLn $ show $ buildDevGraph (Map.fromList p)
  where paarWithUriAndOntology :: [(String, Namespace, Ontology)] 
				  -> [(String, Ontology)]
	paarWithUriAndOntology [] = []
	paarWithUriAndOntology ((uri, _, onto):r) =
	    (uri,onto):(paarWithUriAndOntology r)

-- for static analysis
printResOfStatic :: [ATerm] -> IO()
printResOfStatic al = 
   putStrLn $ show (map output $ parsingAll al)
   where output :: (String, Namespace, Ontology) 
	-- 	-> Result (Ontology,Sign,Sign,[Named Sentence])
	        -> Result (Sign,[Named Sentence])
	 output (_, ns, ontology) = 
	     let Result diagsA (Just (_, _, accSig, namedSen)) = 
		     basicOWL_DLAnalysis (ontology, 
					  emptySign {namespaceMap = ns}, 
					  emptyGlobalAnnos)
	     in  Result diagsA (Just (accSig, namedSen))

parsingAll :: [ATerm] -> [(String, Namespace, Ontology)]
parsingAll [] = []
parsingAll (aterm:res) =
	     (ontologyParse aterm):(parsingAll res)
      
ontologyParse :: ATerm -> (String, Namespace, Ontology)
ontologyParse 
    (AAppl "UOPaar" 
        [AAppl uri _  _, 
	 AAppl "OWLParserOutput" [_, _, ns, onto] _] _) 
    = (uri, 
       namespace, 
       propagateNspaces namespace $ createAndReduceClassAxiom
                                         (fromATerm onto::Ontology))
   where namespace = buildNS ns 
ontologyParse _ = error "false ontology file."

buildNS :: ATerm -> Namespace
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

{-
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
-}

createAndReduceClassAxiom :: Ontology -> Ontology
createAndReduceClassAxiom (Ontology oid directives) =
    let (definition, axiom, other) =  
	    findAndCreate (List.nub directives) ([], [], []) 
	directives' = reverse definition ++ reverse axiom ++ reverse other
    in  Ontology oid directives' 
    
   where findAndCreate :: [Directive] 
	               -> ([Directive], [Directive], [Directive])
		       -> ([Directive], [Directive], [Directive])
			  -- (definition of concept and role, axiom, rest)
         findAndCreate [] res = res
         findAndCreate (h:r) (def, axiom, rest) = 
             case h of
             Ax (Class cid _ Complete _ desps) ->
		 -- the original directive must also be saved.
		 findAndCreate r 
		    (h:def,(Ax (EquivalentClasses (DC cid) desps)):axiom,rest)
                 -- h:(Ax (EquivalentClasses (DC cid) desps)):(findAndCreate r)
	     Ax (Class cid _ Partial _ desps) ->
		 if null desps then
		    findAndCreate r (h:def, axiom, rest) -- h:(findAndCreate r)
		    else 
		     findAndCreate r (h:def, 
				      (appendSubClassAxiom cid desps) ++ axiom,
				      rest) 
	     Ax (EnumeratedClass _ _ _ _) -> 
		 findAndCreate r (h:def, axiom, rest)
	     Ax (DisjointClasses _ _ _) ->
                             if any (eqClass h) r then
                                findAndCreate r (def, axiom, rest)
                                else findAndCreate r (def,h:axiom, rest)
	     Ax (DatatypeProperty _ _ _ _ _ _ _) -> 
		 findAndCreate r (h:def, axiom, rest)
	     Ax (ObjectProperty _ _ _ _ _ _ _ _ _) -> 
		 findAndCreate r (h:def, axiom, rest)
	     _ -> findAndCreate r (def, axiom, h:rest)
             
	 appendSubClassAxiom :: ClassID -> [Description] -> [Directive]
	 appendSubClassAxiom _ [] = []
	 appendSubClassAxiom cid (hd:rd) =
	     (Ax (SubClassOf (DC cid) hd)):(appendSubClassAxiom cid rd) 

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









