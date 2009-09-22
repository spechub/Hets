{- |
Module      :$Header$
Description : utilitary functions used throughout the CMDL interface
Copyright   : uni-bremen and DFKI
License     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@jacobs-university.de
Stability   : provisional
Portability : portable

CMDL.Utils contains different basic functions that are
used throughout the CMDL interface and could not be found in
Prelude

-}

module CMDL.Utils
  ( decomposeIntoGoals
  , obtainNodeList
  , createEdgeNames
  , obtainEdgeList
  , obtainGoalEdgeList
  , unfinishedEdgeName
  , stripComments
  , lastChar
  , lastString
  , safeTail
  , fileFilter
  , fileExtend
  , prettyPrintErrList
  , nodeContainsGoals
  , edgeContainsGoals
  , checkIntString
  , delExtension
  , checkPresenceProvers
  , arrowLink
  , checkArrowLink
  ) where

import Data.List
import Data.Maybe
import Data.Char(Char, String, isDigit, isSpace)
import Data.Graph.Inductive.Graph(LNode, LEdge)

import System.Environment(getEnv)
import System.Directory(doesDirectoryExist, doesFileExist,
                        getDirectoryContents)

import Static.GTheory(G_theory(G_theory))
import Static.DevGraph

import Common.AS_Annotation(SenAttr(isAxiom))
import Common.Utils(trim, trimLeft, splitOn)
import qualified Common.OrderedMap as OMap


-- a any version of function that supports IO
anyIO :: (a -> IO Bool) -> [a] -> IO Bool
anyIO fn ls = case ls of
    [] -> return False
    e : l -> do
      result <- fn e
      if result then return True else anyIO fn l

-- checks if provers in the prover list are availabe on
-- the current machine
checkPresenceProvers :: [String] -> IO [String]
checkPresenceProvers ls = case ls of
    [] -> return []
    "SPASS" : l -> do
                  path <- getEnv "PATH"
                  let lsPaths = map trim $ splitOn ':' path
                      completePath x = case x of
                                        [] -> []
                                        _ -> case last x of
                                              '/' -> (x ++ "SPASS")
                                              _ -> (x ++ "/SPASS")
                  result <- anyIO (doesFileExist . completePath)
                               lsPaths
                  if result then do
                     contd <- checkPresenceProvers l
                     return ("SPASS" : contd)
                   else checkPresenceProvers l
    x : l -> do
            contd <- checkPresenceProvers l
            return (x : contd)

-- removes the extension of the file find in the
-- name of the prompter ( it delets everything
-- after the last . and assumes a prompter length of 2 )
delExtension :: String -> String
delExtension str = let rstr = reverse str in
  reverse $ safeTail $ case dropWhile (/= '.') rstr of
    "" -> safeTail rstr
    dstr -> dstr

-- | Checks if a string represents a int or not
checkIntString :: String -> Bool
checkIntString = not . any  (not . isDigit)

localArr :: String
localArr = "..>"

globalArr :: String
globalArr = "->"

padBlanks :: String -> String
padBlanks s = ' ' : s ++ " "

-- | Generates a string representing the type of link
arrowLink :: DGLinkLab -> String
arrowLink edgLab = padBlanks $ if isLocalEdge $ dgl_type edgLab
    then localArr
    else globalArr

-- | Checks if the string starts with an arrow
checkArrowLink :: String -> (Bool, String, String)
checkArrowLink str = case find snd
  $ map (\ s -> (s, isPrefixOf s str)) [localArr, globalArr] of
  Nothing -> (False, [], str)
  Just (a, _) -> (True, padBlanks a, drop (length a) str)

-- | Given a string inserts spaces before and after an
-- arrow
spacesAroundArrows :: String -> String -> String
spacesAroundArrows s output = case s of
       [] -> output
       hd : tl  ->
         case checkArrowLink $ trimLeft s of
          (True, arr, rs)  -> spacesAroundArrows rs
                               (output ++ arr)
          (False, _, _) -> spacesAroundArrows tl
                               (output ++ [hd])

-- | Given a string the function decomposes it into 4 lists,
-- one for node goals, the other for edges, the third for
-- numbered edges and the last for names that could not be
-- processed due to errors
decomposeIntoGoals :: String -> ([String], [String], [String], [String])
decomposeIntoGoals input = let
    -- the new input where words and arrows are separated
    -- by exactly one space
    nwInput = words $ spacesAroundArrows input []
    -- funtion to parse the input and decompose it into
    -- the three goal list
    parse info nbOfArrows word sw listNode listEdge listNbEdge listError =
       case info of
        [] -> case nbOfArrows :: Integer of
               0 -> (word : listNode, listEdge, listNbEdge, listError)
               1 -> (listNode, word : listEdge, listNbEdge, listError)
               2 -> (listNode, listEdge, word : listNbEdge, listError)
               _ -> (listNode, listEdge, listNbEdge, word : listError)
        x : l -> case checkArrowLink x of
                (True, arr, _) ->
                  case word of
                   [] -> (listNode, listEdge, listNbEdge, word : listError)
                   _  -> parse l (nbOfArrows + 1) (word ++ arr) True
                           listNode listEdge listNbEdge listError
                (False, _, _) ->
                  if sw
                   then parse l nbOfArrows (word ++ x) False
                          listNode listEdge listNbEdge listError
                   else
                    case nbOfArrows of
                     0 -> parse l 0 x False
                           (word : listNode) listEdge listNbEdge listError
                     1 -> parse l 0 x False
                           listNode (word : listEdge) listNbEdge listError
                     2 -> parse l 0 x False
                           listNode listEdge (word : listNbEdge) listError
                     _ -> parse l 0 x False
                           listNode listEdge listNbEdge (word : listError)
   in parse nwInput 0 [] True [] [] [] []

-- | mapAndSplit maps a function to a list. If the function can not
-- be applied to an element it is stored in a different list for
-- producing error message later on
mapAndSplit :: (a -> Maybe b) -> [a] -> ([a], [b])
mapAndSplit fn ls =
  let ps = map (\ x -> (x, fn x)) ls
      (oks, errs) = partition (isJust . snd) ps
  in (map fst errs, mapMaybe snd oks)

-- | concatMapAndSplit is similar to mapAndSplit, just that it behaves
-- in a similar manner to concatMap (i.e. sums up lists produced by
-- the function
concatMapAndSplit :: (a -> [b]) -> [a] -> ([a],[b])
concatMapAndSplit fn ls =
  let ps = map (\ x -> (x, fn x)) ls
      (errs, oks) = partition (null . snd) ps
  in (map fst errs, concatMap snd oks)

-- | Given a list of node names and the list of all nodes
-- the function returns all the nodes that have their name
-- in the name list
obtainNodeList :: [String] -> [LNode DGNodeLab] ->([String], [LNode DGNodeLab])
obtainNodeList lN allNodes = mapAndSplit
    (\ x -> find (\ (_, label) -> getDGNodeName label == x) allNodes) lN

-- | Given a node decides if it contains goals or not
nodeContainsGoals:: LNode DGNodeLab -> G_theory -> Bool
nodeContainsGoals (_, l) th =
   (case th of
       G_theory _ _ _ sens _ ->
         not $ OMap.null $ OMap.filter
           (\ s -> not (isAxiom s) && not (isProvenSenStatus s)) sens) ||
           hasOpenNodeConsStatus False l

-- | Given an edge decides if it contains goals or not
edgeContainsGoals:: LEdge DGLinkLab -> Bool
edgeContainsGoals (_, _, l) = case thmLinkStatus $ dgl_type l of
     Just LeftOpen -> True
     _             -> False

-- | Given a list of edges and the complete list of all
-- edges computes not only the names of edges but also the
-- numbered name of edges
createEdgeNames:: [LNode DGNodeLab] -> [LEdge DGLinkLab] -> [String]
createEdgeNames lsN lsE = let
  -- function that returns the name of a node given its number
   nameOf x ls = case lookup x ls of
                  Nothing -> "Unknown node"
                  Just nlab -> showName $ dgn_name nlab
   ordFn (x1, x2, _) (y1, y2, _) = compare (x1, x2) (y1, y2)
   -- sorted and grouped list of edges
   edgs = groupBy ( \ x y -> ordFn x y == EQ) $ sortBy ordFn lsE
   allEds = concatMap (\ l -> case l of
                             [(x, y, edgLab)] ->[(nameOf x lsN ++
                                          arrowLink edgLab ++
                                          nameOf y lsN)]
                             _ -> map (\ (x, y, edgLab) ->
                                   nameOf x lsN ++
                                   arrowLink edgLab ++
                                     showEdgeId (dgl_id edgLab)
                                     ++ arrowLink edgLab
                                     ++ nameOf y lsN) l) edgs
  in allEds


-- | Given a list of edge names and numbered edge names
-- and the list of all nodes and edges the function
-- identifies the edges that appear in the name lists
obtainEdgeList :: [String] ->[String] ->[LNode DGNodeLab]
                    -> [LEdge DGLinkLab]-> ([String],[LEdge DGLinkLab])
obtainEdgeList lsEdge lsNbEdge allNodes allEdges = let
   -- function that searches through a list of nodes to
   -- find the node number for a given name.
       getNodeNb s ls =
          case find ( \ (_, label) ->
                        getDGNodeName label == s) ls of
           Nothing -> Nothing
           Just (nb, _) -> Just nb
  -- converts a string to a number (for some reason I
  -- could not find such a function already implemented
  -- in the Prelude )
       l1 = concatMapAndSplit
            (\ nme ->
               let allx = words nme
                   node1 = getNodeNb (head allx) allNodes
                   node2 = getNodeNb (allx !! 2) allNodes
               in if length allx < 3 then error "CMDL.Utils.obtainEdgeList1"
                 else case node1 of
                Nothing -> []
                Just x ->
                 case node2 of
                 Nothing -> []
                 Just y ->
                  filter (\ (x1, y1, _) -> x == x1 && y == y1) allEdges
            ) lsEdge
             -- compute the list of all numbered edges
       l2 = mapAndSplit
           (\ nme ->
              let allx = words nme
                  node1 = getNodeNb (head allx) allNodes
                  node2 = getNodeNb (allx !! 5) allNodes
                  nb = read (allx !! 3)
              in if length allx < 6 then error "CMDL.Utils.obtainEdgeList2"
                 else case node1 of
               Nothing -> Nothing
               Just x ->
                case node2 of
                Nothing -> Nothing
                Just y ->
                 let ls = filter(\ (x1, y1, elab) -> x == x1 && y == y1 &&
                                   dgl_id elab == EdgeId nb) allEdges
                 in case ls of
                     [] -> Nothing
                     els : _ -> Just els) lsNbEdge
   in (fst l1 ++ fst l2, snd l1 ++ snd l2)

-- | Giben a listof edgenamesand numbered edge names and
-- the list of all nodes and edges the function identifies
-- the edges that appearin the name list and are also goals
obtainGoalEdgeList :: [String] -> [String] -> [LNode DGNodeLab]
                   -> [LEdge DGLinkLab] -> ([String], [LEdge DGLinkLab])
obtainGoalEdgeList ls1 ls2 ls3 ls4 =
    let (l1, l2) = obtainEdgeList ls1 ls2 ls3 ls4
    in (l1, filter edgeContainsGoals l2)

-- | Function that given a string removes comments contained
-- in the string
stripComments :: String -> String
stripComments input =
    let fn ls = case ls of
                '#' : _ -> []
                '%' : ll ->
                   case ll of
                    '%' : _ -> []
                    '{' : _ -> []
                    _ -> '%' : fn ll
                [] -> []
                l : ll  -> l : fn ll
   in trim $ fn input

-- | The function obtain the unfinished edge name from the
-- last position of the input or list of possible unfinished
-- edge names
unfinishedEdgeName :: String -> String
unfinishedEdgeName input = let
      lastButN nb = lastString . reverse . drop nb . reverse
  -- we need a penultimum (the one before the last) function
      prevLast = lastButN 1
  -- and the one before the penultimum
      prevPrevLast = lastButN 2
      prev2PrevLast = lastButN 3
      prev3PrevLast = lastButN 4
      wrds = words input
    in if isSpace $ lastChar input
    then
     -- if so, then either the last word is an arrow, and
     -- then we have the consider last two words, or it
     -- is not an arrow and then we need to consider just
     -- the last word
        case checkArrowLink $ lastString wrds of
          (True, arr1, _) ->
            case checkArrowLink $ prevPrevLast wrds of
             (True, arr2, _) -> prev2PrevLast wrds
               ++ arr2 ++ prevLast wrds ++ arr1
             _ -> prevLast wrds ++ arr1
          --anyhting else
          _ -> case checkArrowLink $ prevLast wrds of
                -- an entire edge name was just inserted
                -- before and now we need a fresh new start
                (True, _, _) -> []
                -- if just the first word of an edge was
                -- inserted then return that
                _ -> case lastString wrds of
                      [] -> []
                      _ -> lastString wrds ++ " "
    else
     -- then we could be in the middle of the first node
     -- name, arrow or the second node name
      case checkArrowLink $ prevLast wrds of
           -- in the middle of the last word
          (True, arr1, _) -> case checkArrowLink $ prev2PrevLast wrds of
             (True, arr2, _) -> prev3PrevLast wrds ++
                           arr2 ++ prevPrevLast wrds ++
                           arr1 ++ lastString wrds
             _ -> prevPrevLast wrds ++ arr1 ++ lastString wrds
          _ -> case checkArrowLink $ prevPrevLast wrds of
                 -- in the middle of the first word
                (True, _, _) -> lastString wrds
                -- in the middle of the arrow
                _ -> case prevLast wrds of
                      [] -> lastString wrds
                      _  -> prevLast wrds ++ " " ++ lastString wrds

-- | Given a list of files and folders the function filters
-- only directory names and files ending in extenstion
-- .casl (why not .het?)
fileFilter :: String -> [String] -> [String] -> IO [String]
fileFilter lPath ls cons = case ls of
    []  -> return cons
    x : l -> do
         -- check if current element is a directory
         b <- doesDirectoryExist (lPath ++ x)
         if b
           -- if it is,then add "/" to indicate is a folder
           then fileFilter lPath l ((x ++ "/") : cons)
           -- if it is not a folder then it must be a file
           -- so check the extension
           else if isSuffixOf ".casl" x
                   then fileFilter lPath l (x : cons)
                   else fileFilter lPath l cons

-- | Given a list of files and folders the function expands
-- the list adding the content of all folders in the list
fileExtend :: String -> [String] -> [String] -> IO [String]
fileExtend lPath ls cons = case ls of
    []  -> return cons
    x : l -> do
          -- check if current element is a directory
          let lPathx = lPath ++ x
          b <- doesDirectoryExist lPathx
          if b then
            -- if it is a folder add its content
            do ll <- getDirectoryContents lPathx
               nll<- fileFilter lPathx ll []
               let nll'= map (x ++) nll
               fileExtend lPath l (nll' ++ cons)
            -- if it is not then leave the file alone
            else fileExtend lPath l (x : cons)

-- | The function behaves exactly as tail just that
-- in the case of empty list returns an empty list
-- instead of an error
safeTail :: [a] -> [a]
safeTail = drop 1

safeLast :: a -> [a] -> a
safeLast d l = if null l then d else last l

-- | The function behaves exactly like last just that
-- in case of an empty list returns the space
-- character (it works only for lists of chars)
lastChar :: String -> Char
lastChar = safeLast ' '

-- | The function behaves exactly like last just that
-- in case of an empty list returns the empty string
-- (it is meant only for list of strings)
lastString::[String]->String
lastString = safeLast ""

-- | The function nicely outputs a list of errors
prettyPrintErrList :: [String] -> String
prettyPrintErrList = unlines
  . map (\ x -> "Input " ++ x ++ " could not be processed")
