{- |
Module      : ./CMDL/Utils.hs
Description : utilitary functions used throughout the CMDL interface
Copyright   : uni-bremen and DFKI
License     : GPLv2 or higher, see LICENSE.txt
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
  , finishedNames
  , stripComments
  , lastChar
  , lastString
  , safeTail
  , fileFilter
  , fileExtend
  , prettyPrintErrList
  , edgeContainsGoals
  , isOpenConsEdge
  , checkIntString
  , delExtension
  , arrowLink
  ) where

import Data.List
import Data.Maybe
import Data.Char (isDigit)
import Data.Graph.Inductive.Graph (LNode, LEdge)

import System.Directory
import System.FilePath

import Static.DevGraph
import Static.DgUtils

import Common.Utils

{- removes the extension of the file find in the
   name of the prompter ( it delets everything
   after the last . and assumes a prompter length of 2 ) -}
delExtension :: String -> String
delExtension str = let rstr = reverse str in
  reverse $ safeTail $ case dropWhile (/= '.') rstr of
    "" -> safeTail rstr
    dstr -> dstr

-- | Checks if a string represents a int or not
checkIntString :: String -> Bool
checkIntString = not . any (not . isDigit)

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
checkArrowLink :: String -> Maybe (String, String)
checkArrowLink str = case find snd
  $ map (\ s -> (s, isPrefixOf s str)) [localArr, globalArr] of
  Nothing -> Nothing
  Just (a, _) -> Just (padBlanks a, drop (length a) str)

{- | Given a string inserts spaces before and after an
   arrow -}
spacesAroundArrows :: String -> String
spacesAroundArrows s = case s of
       [] -> []
       hd : tl -> case checkArrowLink $ trimLeft s of
          Just (arr, rs) -> arr ++ spacesAroundArrows rs
          Nothing -> hd : spacesAroundArrows tl

{- | Given a string the function decomposes it into 4 lists,
   one for node goals, the other for edges, the third for
   numbered edges and the last for names that could not be
   processed due to errors -}
decomposeIntoGoals :: String -> ([String], [String], [String], [String])
decomposeIntoGoals input = let
    {- the new input where words and arrows are separated
       by exactly one space -}
    nwInput = words $ spacesAroundArrows input
    {- function to parse the input and decompose it into
       the three goal list -}
    parse info nbOfArrows word sw listNode listEdge listNbEdge listError =
       case info of
        [] -> case nbOfArrows :: Integer of
               0 -> (word : listNode, listEdge, listNbEdge, listError)
               1 -> (listNode, word : listEdge, listNbEdge, listError)
               2 -> (listNode, listEdge, word : listNbEdge, listError)
               _ -> (listNode, listEdge, listNbEdge, word : listError)
        x : l -> case checkArrowLink x of
                Just (arr, _) ->
                  case word of
                   [] -> (listNode, listEdge, listNbEdge, word : listError)
                   _ -> parse l (nbOfArrows + 1) (word ++ arr) True
                           listNode listEdge listNbEdge listError
                Nothing ->
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
    (ns, es, les, errs) = parse nwInput 0 [] True [] [] [] []
    in (reverse ns, reverse es, reverse les, reverse errs)

{- | mapAndSplit maps a function to a list. If the function can not
   be applied to an element it is stored in a different list for
   producing error message later on -}
mapAndSplit :: (a -> Maybe b) -> [a] -> ([a], [b])
mapAndSplit fn ls =
  let ps = zip ls $ map fn ls
      (oks, errs) = partition (isJust . snd) ps
  in (map fst errs, mapMaybe snd oks)

{- | concatMapAndSplit is similar to mapAndSplit, just that it behaves
   in a similar manner to concatMap (i.e. sums up lists produced by
   the function -}
concatMapAndSplit :: (a -> [b]) -> [a] -> ([a], [b])
concatMapAndSplit fn ls =
  let ps = zip ls $ map fn ls
      (errs, oks) = partition (null . snd) ps
  in (map fst errs, concatMap snd oks)

{- | Given a list of node names and the list of all nodes
   the function returns all the nodes that have their name
   in the name list -}
obtainNodeList :: [String] -> [LNode DGNodeLab] -> ([String], [LNode DGNodeLab])
obtainNodeList lN allNodes = mapAndSplit
    (\ x -> find (\ (_, label) -> getDGNodeName label == x) allNodes) lN

-- | Given an edge decides if it contains goals or not
edgeContainsGoals :: LEdge DGLinkLab -> Bool
edgeContainsGoals (_, _, l) = case thmLinkStatus $ dgl_type l of
     Just LeftOpen -> True
     _ -> False

-- | Given an edge: does it contain an open conservativity goal or not
isOpenConsEdge :: LEdge DGLinkLab -> Bool
isOpenConsEdge (_, _, l) = hasOpenConsStatus False $ getEdgeConsStatus l

{- | Given a list of edges and the complete list of all
   edges computes not only the names of edges but also the
   numbered name of edges -}
createEdgeNames :: [LNode DGNodeLab] -> [LEdge DGLinkLab]
  -> [(String, LEdge DGLinkLab)]
createEdgeNames lsN lsE = let
  -- function that returns the name of a node given its number
   nameOf x ls = case lookup x ls of
                  Nothing -> "Unknown node"
                  Just nlab -> getDGNodeName nlab
   ordFn (x1, x2, _) (y1, y2, _) = compare (x1, x2) (y1, y2)
   -- sorted and grouped list of edges
   edgs = groupBy ( \ x y -> ordFn x y == EQ) $ sortBy ordFn lsE
   in concatMap (\ l -> case l of
                             [el@(x, y, edgLab)] -> [(nameOf x lsN ++
                                          arrowLink edgLab ++
                                          nameOf y lsN, el)]
                             _ -> map (\ el@(x, y, edgLab) ->
                                   (nameOf x lsN ++
                                   arrowLink edgLab ++
                                     showEdgeId (dgl_id edgLab)
                                     ++ arrowLink edgLab
                                     ++ nameOf y lsN, el)) l) edgs

{- | Given a list of edge names and numbered edge names
   and the list of all nodes and edges the function
   identifies the edges that appear in the name lists -}
obtainEdgeList :: [String] -> [String] -> [LNode DGNodeLab]
  -> [LEdge DGLinkLab] -> ([String], [LEdge DGLinkLab])
obtainEdgeList lsEdge lsNbEdge allNodes allEdges = let
   {- function that searches through a list of nodes to
      find the node number for a given name. -}
       getNodeNb s ls =
          case find ( \ (_, label) ->
                        getDGNodeName label == s) ls of
           Nothing -> Nothing
           Just (nb, _) -> Just nb
        -- compute the list of all edges from source node to target
       l1 = concatMapAndSplit
            (\ nme -> case words nme of
              [src, _, tar] -> let
                node1 = getNodeNb src allNodes
                node2 = getNodeNb tar allNodes
                in case node1 of
                Nothing -> []
                Just x ->
                 case node2 of
                 Nothing -> []
                 Just y ->
                  filter (\ (x1, y1, _) -> x == x1 && y == y1) allEdges
              _ -> error "CMDL.Utils.obtainEdgeList1"
            ) lsEdge
        -- compute the list of all numbered edges
       l2 = mapAndSplit
           (\ nme -> case words nme of
             [src, _, numb, _, tar] -> let
               node1 = getNodeNb src allNodes
               node2 = getNodeNb tar allNodes
               mnb = readMaybe numb
               in case node1 of
               Nothing -> Nothing
               Just x -> case node2 of
                Nothing -> Nothing
                Just y -> case mnb of
                 Nothing -> Nothing
                 Just nb -> let
                   ls = filter (\ (x1, y1, elab) -> x == x1 && y == y1 &&
                                   dgl_id elab == EdgeId nb) allEdges
                   in case ls of
                     [] -> Nothing
                     els : _ -> Just els
             _ -> error "CMDL.Utils.obtainEdgeList2") lsNbEdge
   in (fst l1 ++ fst l2, snd l1 ++ snd l2)

{- | Giben a listof edgenamesand numbered edge names and
   the list of all nodes and edges the function identifies
   the edges that appearin the name list and are also goals -}
obtainGoalEdgeList :: [String] -> [String] -> [LNode DGNodeLab]
                   -> [LEdge DGLinkLab] -> ([String], [LEdge DGLinkLab])
obtainGoalEdgeList ls1 ls2 ls3 ls4 =
    let (l1, l2) = obtainEdgeList ls1 ls2 ls3 ls4
    in (l1, filter edgeContainsGoals l2)

{- | Function that given a string removes comments contained
   in the string -}
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
                l : ll -> l : fn ll
   in trim $ fn input

-- | check if edges are to be completed in the presence of nodes
finishedNames :: [String] -> String -> ([String], String)
finishedNames ns i =
  let e@(fs, r) = fNames ns i in
  if not (null r) && any (isPrefixOf r) [localArr, globalArr] then
    case reverse fs of
    lt : ei : ar : sr : fr | elem ar [localArr, globalArr]
      -> (reverse fr, unwords [sr, ar, ei, lt, r])
    lt : fr -> (reverse fr, unwords [lt, r])
    _ -> e
  else e

fNames :: [String] -> String -> ([String], String)
fNames ns input = let i = trimLeft input in
  case filter (isJust . snd) $ zip ns
    $ map ((`stripPrefix` i) . (++ " ")) ns of
    (n, Just r) : _ -> let (fs, s) = fNames ns r in (n : fs, s)
    _ -> ([], i)

{- | Given a list of files and folders the function filters
   only directory names and files ending in extenstion
   .casl or .het or .dol -}
fileFilter :: String -> [String] -> [String] -> IO [String]
fileFilter lPath ls cons = case ls of
    [] -> return cons
    x : l -> do
         -- check if current element is a directory
         b <- doesDirectoryExist (lPath </> x)
         fileFilter lPath l $ if b
           -- if it is,then add "/" to indicate is a folder
           then addTrailingPathSeparator x : cons
           {- if it is not a folder then it must be a file
              so check the extension -}
           else if elem (takeExtensions x) [".casl", ".het", ".dol" ]
                then x : cons else cons

{- | Given a list of files and folders the function expands
   the list adding the content of all folders in the list -}
fileExtend :: String -> [String] -> [String] -> IO [String]
fileExtend lPath ls cons = case ls of
    [] -> return cons
    x : l -> do
          -- check if current element is a directory
          let lPathx = lPath </> x
          b <- doesDirectoryExist lPathx
          if b then
            -- if it is a folder add its content
            do ll <- getDirectoryContents lPathx
               nll <- fileFilter lPathx ll []
               let nll' = map (x </>) nll
               fileExtend lPath l (nll' ++ cons)
            -- if it is not then leave the file alone
            else fileExtend lPath l (x : cons)

{- | The function behaves exactly as tail just that
   in the case of empty list returns an empty list
   instead of an error -}
safeTail :: [a] -> [a]
safeTail = drop 1

safeLast :: a -> [a] -> a
safeLast d l = if null l then d else last l

{- | The function behaves exactly like last just that
   in case of an empty list returns the space
   character (it works only for lists of chars) -}
lastChar :: String -> Char
lastChar = safeLast ' '

{- | The function behaves exactly like last just that
   in case of an empty list returns the empty string
   (it is meant only for list of strings) -}
lastString :: [String] -> String
lastString = safeLast ""

-- | The function nicely outputs a list of errors
prettyPrintErrList :: [String] -> String
prettyPrintErrList = intercalate "\n"
  . map (\ x -> "Input " ++ x ++ " could not be processed")
