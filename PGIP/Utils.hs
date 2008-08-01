{- |
Module      :$Header$
Description : utilitary functions used throughout the CMDL interface
Copyright   : uni-bremen and DFKI
License     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@jacobs-university.de
Stability   : provisional
Portability : portable

PGIP.Utils contains different basic functions that are
used throughout the CMDL interface and could not be found in
Prelude

-}

module PGIP.Utils
       ( isWhiteSpace
       , trim
       , trimLeft
       , trimRight
       , decomposeIntoGoals
       , obtainNodeList
       , createEdgeNames
       , obtainEdgeList
       , obtainGoalEdgeList
       , unfinishedEdgeName
       , stripComments
       , lastChar
       , lastString
       , getInt
       , safeTail
       , fileFilter
       , fileExtend
       , prettyPrintList
       , prettyPrintErrList
       , nodeContainsGoals
       , edgeContainsGoals
       , checkIntString
       , delExtension
       , checkPresenceProvers
       , getPaths
       )where

import Data.List
import Data.Char
import Data.Graph.Inductive.Graph
import Static.GTheory
import Static.DevGraph
import System
import System.Directory
import Common.AS_Annotation
import qualified Common.OrderedMap as OMap


-- splits the paths in the PATH variable (separeted by
-- a ':' symbol)
getPaths ::  String -> String -> [String] -> [String]
getPaths ls acc accLs
 = case ls of
    []       -> accLs++[trim acc]
    ':':l    -> getPaths l [] (accLs++[trim acc])
    c:l      -> getPaths l (acc++[c]) accLs


-- a any version of function that supports IO
anyIO :: (a -> IO Bool) -> [a] -> IO Bool
anyIO fn ls
 = case ls of
    [] -> return False
    e:l -> do
            result <- fn e
            case result of
             True -> return True
             False -> anyIO fn l


-- checks if provers in the prover list are availabe on
-- the current machine
checkPresenceProvers :: [String] -> IO [String]
checkPresenceProvers ls
 = case ls of
    [] -> return []
    "SPASS":l -> do
                  path <- getEnv "PATH"
                  let lsPaths = getPaths path [] []
                      completePath x = case x of
                                        [] -> []
                                        _ -> case last x of
                                              '/' -> (x++"SPASS")
                                              _ -> (x ++ "/SPASS")
                  result <- anyIO ( \x -> doesFileExist $ completePath x)
                               lsPaths
                  case result of
                   True -> do
                            contd <- checkPresenceProvers l
                            return ("SPASS":contd)
                   False -> checkPresenceProvers l
    x:l -> do
            contd <- checkPresenceProvers l
            return (x:contd)


-- removes the extension of the file find in the
-- name of the prompter ( it delets everything
-- after the last . )
delExtension :: String -> String
delExtension str = case find (=='.') str of
                     Nothing -> reverse $ safeTail $ safeTail $
                                  reverse str
                     Just _ -> reverse $ safeTail $
                                dropWhile (/= '.') $ reverse str


-- | Checks if a string represents a int or not
checkIntString :: String -> Bool
checkIntString = not . any  (not . isDigit)

-- | List of all characters considered white spaces
whiteSpaces ::String
whiteSpaces = " \t\n\r\v"


-- | Predicate that tells if a character is a white space
-- or not
isWhiteSpace ::Char -> Bool
isWhiteSpace x = any (x==) whiteSpaces

-- | trims a string both on left and right hand side
trim :: String -> String
trim = reverse . dropWhile isWhiteSpace . reverse
        . dropWhile isWhiteSpace

-- | trims a string only on the left side
trimLeft :: String -> String
trimLeft = dropWhile isWhiteSpace

-- | trims a string only on the right side
trimRight :: String -> String
trimRight = reverse . dropWhile isWhiteSpace . reverse


-- | Given a string inserts spaces before and after an
-- arrow
spacesAroundArrows :: String -> String -> String
spacesAroundArrows s output
 = let
    --function to tell if in the string follows a arrow
    isArrow text = case take 2 $ trimLeft text of
                     "->" ->True
                     _    ->False
   in case s of
       [] -> output
       _  ->
         case isArrow s of
          True  -> spacesAroundArrows (drop 2 $ trimLeft s)
                               (output ++" -> ")
          False -> spacesAroundArrows (safeTail s)
                               (output ++ [head s])

-- | Given a string the function decomposes it into 4 lists,
-- one for node goals, the other for edges, the third for
-- numbered edges and the last for names that could not be
-- processed due to errors
decomposeIntoGoals :: String -> ([String],[String],[String],[String])
decomposeIntoGoals input
 = let
    -- the new input where words and arrows are separated
    -- by exactly one space
    nwInput = words $ spacesAroundArrows input []
    -- funtion to parse the input and decompose it into
    -- the three goal list
    parse info nbOfArrows word sw listNode listEdge
                listNbEdge listError
     = case info of
        [] -> case nbOfArrows :: Integer of
               0 -> ((word:listNode), listEdge, listNbEdge,listError)
               1 -> (listNode, (word:listEdge), listNbEdge,listError)
               2 -> (listNode, listEdge, (word:listNbEdge),listError)
               _ -> (listNode, listEdge, listNbEdge, (word:listError))
        "->":l -> case word of
                   [] -> (listNode,listEdge,listNbEdge,
                           (word:listError))
                   _  -> parse l (nbOfArrows+1) (word++" -> ")
                          True listNode listEdge listNbEdge listError
        x:l -> case sw of
                True -> parse l nbOfArrows (word++x) False
                         listNode listEdge listNbEdge listError
                False ->
                 case nbOfArrows of
                   0 -> parse l 0 x False
                         (word:listNode) listEdge listNbEdge listError
                   1 -> parse l 0 x False
                         listNode (word:listEdge) listNbEdge listError
                   2 -> parse l 0 x False
                         listNode listEdge (word:listNbEdge) listError
                   _ -> parse l 0 x False
                         listNode listEdge listNbEdge (word:listError)
   in parse nwInput 0 [] True [] [] [] []

-- | mapAndSplit maps a function to a list. If the function can not
-- be applied to an element it is stored in a different list for
-- producing error message later on
mapAndSplit :: (a -> Maybe b) -> [a] -> ([a],[b])
mapAndSplit fn ls
 = let mapAndSplit' fn' ls' errs mapped =
          case ls' of
           []  -> (errs,mapped)
           x:l -> case fn' x of
                   Just y -> mapAndSplit' fn' l errs (y:mapped)
                   Nothing-> mapAndSplit' fn' l (x:errs) mapped
   in mapAndSplit' fn ls [] []


-- | concatMapAndSplit is similar to mapAndSplit, just that it behaves
-- in a similar manner to concatMap (i.e. sums up lists produced by
-- the function
concatMapAndSplit :: (a -> [b]) -> [a] -> ([a],[b])
concatMapAndSplit fn ls
 = let concatMapAndSplit' fn' ls' errs mapped =
         case ls' of
          []  -> (errs, mapped)
          x:l -> case fn' x of
                  [] -> concatMapAndSplit' fn' l (x:errs) mapped
                  l' -> concatMapAndSplit' fn' l errs (mapped++l')
   in concatMapAndSplit' fn ls [] []

-- | Given a list of node names and the list of all nodes
-- the function returns all the nodes that have their name
-- in the name list
obtainNodeList :: [String] ->[LNode DGNodeLab]
                           ->([String],[LNode DGNodeLab])
obtainNodeList lN allNodes
 = mapAndSplit
    (\x -> find (\(_,label) -> getDGNodeName label == x) allNodes) lN


-- | Given a node decides if it contains goals or not
nodeContainsGoals:: LNode DGNodeLab -> G_theory -> Bool
nodeContainsGoals (_,l) th
 = -- (not (isDGRef l)) &&
   ((case th of
       G_theory _ _ _ sens _ ->
         not $ OMap.null $ OMap.filter
           (\s-> (not (isAxiom s)) && (not (isProvenSenStatus s))) sens
           ) || hasOpenConsStatus False l)

-- | Given an edge decides if it contains goals or not
edgeContainsGoals:: LEdge DGLinkLab -> Bool
edgeContainsGoals (_,_,l)
 = case thmLinkStatus $ dgl_type l of
     Just LeftOpen -> True
     _             -> False

getInt :: EdgeId -> Int
getInt val
 = case val of
    EdgeId v -> v


-- | Given a list of edges and the complete list of all
-- edges computes not only the names of edges but also the
-- numbered name of edges
createEdgeNames:: [LNode DGNodeLab] -> [LEdge DGLinkLab] -> [String]
createEdgeNames lsN lsE
 =
  let
  -- function that returns the name of a node given its number
   nameOf x ls = case find(\(nb,_) -> nb == x) ls of
                  Nothing -> "Unknown node"
                  Just (_, nlab) -> showName $ dgn_name nlab
   ordFn x y = let (x1,x2,_) = x
                   (y1,y2,_) = y
               in if (x1,x2) > (y1,y2) then GT
                   else if (x1,x2) < (y1,y2) then LT
                         else EQ
  -- sorted and grouped list of edges
   edgs = groupBy ( \(x1,x2,_) (y1,y2,_)-> (x1,x2)==(y1,y2)) $
           sortBy ordFn lsE
   allEds= concatMap (\l -> case l of
                             [(x,y,_)]->[((nameOf x lsN) ++ " -> " ++
                                          (nameOf y lsN))]
                             _ -> map (\(x,y,edgLab) ->
                                   (nameOf x lsN) ++ " -> " ++
                                     (show $ getInt $ dgl_id edgLab)
                                     ++ " -> " ++  (nameOf y lsN)) l) edgs
  in allEds


-- | Given a list of edge names and numbered edge names
-- and the list of all nodes and edges the function
-- identifies the edges that appear in the name lists
obtainEdgeList :: [String] ->[String] ->[LNode DGNodeLab]
                    -> [LEdge DGLinkLab]-> ([String],[LEdge DGLinkLab])
obtainEdgeList lsEdge lsNbEdge allNodes allEdges
 =
   -- function that searches through a list of nodes to
   -- find the node number for a given name.
   let getNodeNb s ls =
          case find ( \(_,label) ->
                        getDGNodeName label == s) ls of
           Nothing -> Nothing
           Just (nb,_) -> Just nb
  -- converts a string to a number (for some reason I
  -- could not find such a function already implemented
  -- in the Prelude )
       l1=concatMapAndSplit
            (\nme ->
               let allx  = words nme
                   node1 = getNodeNb (allx!!0) allNodes
                   node2 = getNodeNb (allx!!2) allNodes
               in
                case node1 of
                Nothing -> []
                Just x ->
                 case node2 of
                 Nothing -> []
                 Just y ->
                  filter(\(x1,y1,_)->(x==x1)&&(y==y1)) allEdges
            ) lsEdge
             -- compute the list of all numbered edges
       l2=mapAndSplit
           (\nme ->
              let allx = words nme
                  node1= getNodeNb (allx!!0) allNodes
                  node2= getNodeNb (allx!!5) allNodes
                  nb   = read (allx!!3)
              in
               case node1 of
               Nothing -> Nothing
               Just x ->
                case node2 of
                Nothing -> Nothing
                Just y ->
                 let ls = filter(\(x1,y1,elab)->(x==x1)&&(y==y1)&&
                                   (dgl_id elab==EdgeId nb)) allEdges
                 in case ls of
                     [] -> Nothing
                     els:_ -> Just els ) lsNbEdge
   in ((fst l1)++(fst l2),(snd l1)++(snd l2))


-- | Giben a listof edgenamesand numbered edge names and
-- the list of all nodes and edges the function identifies
-- the edges that appearin the name list and are also goals
obtainGoalEdgeList :: [String] -> [String] ->
                      [LNode DGNodeLab] -> [LEdge DGLinkLab]
                      -> ([String],[LEdge DGLinkLab])
obtainGoalEdgeList ls1 ls2 ls3 ls4
 = let (l1,l2) = obtainEdgeList ls1 ls2 ls3 ls4
       l2' = filter edgeContainsGoals l2
   in (l1,l2')


-- | Function that given a string removes comments contained
-- in the string
stripComments::String -> String
stripComments input
 = let fn ls = case ls of
                '#':_ -> []
                '%':ll->
                   case ll of
                    '%':_ ->[]
                    '{':_ ->[]
                    _  -> '%':(fn ll)
                []    -> []
                l:ll  -> l:(fn ll)
   in trim $ fn input

-- | The function obtain the unfinished edge name from the
-- last position of the input or list of possible unfinished
-- edge names
unfinishedEdgeName :: String -> String
unfinishedEdgeName input
 =
  -- we need a penultimum (the one before the last) function
  let prevLast s = lastString $ reverse $ safeTail
                                  $ reverse s
  -- and the one before the penultimum
      prevPrevLast s = lastString $ reverse $ safeTail $
                              safeTail $  reverse s
      prev2PrevLast s = lastString $ reverse $ safeTail $
                             safeTail $ safeTail $ reverse s
      prev3PrevLast s = lastString $ reverse $ safeTail $
                          safeTail$ safeTail$ safeTail $
                          reverse s
  in
  -- is the last character an empty space?
   case isWhiteSpace $ lastChar input of
    True ->
     -- if so, then either the last word is an arrow, and
     -- then we have the consider last two words, or it
     -- is not an arrow and then we need to consider just
     -- the last word
        case lastString $ words input of
          "->" -> case prevPrevLast $ words input of
                    "->"->(prev2PrevLast $ words input) ++
                           " -> " ++ (prevLast $ words input)
                           ++ " -> "
                    _ ->(prevLast $ words input) ++ " -> "
          --anyhting else
          _ -> case prevLast $ words input of
                -- an entire edge name was just inserted
                -- before and now we need a fresh new start
                "->" -> []
                -- if just the first word of an edge was
                -- inserted then return that
                _ -> case lastString $ words input of
                      []-> []
                      _ -> (lastString $ words input)++" "
    False ->
     -- then we could be in the middle of the first node
     -- name, arrow or the second node name
      case prevLast $ words input of
           -- in the middle of the last word
          "->" -> case prev2PrevLast $ words input of
                   "->"->(prev3PrevLast $ words input) ++
                           " -> "++(prevPrevLast $ words
                           input)++" -> "++(lastString $
                           words input)
                   _->(prevPrevLast $ words input) ++
                        " -> " ++ (lastString $ words input)
          _ -> case prevPrevLast $ words input of
                 -- in the middle of the first word
                "->" -> lastString $ words input
                -- in the middle of the arrow
                _ -> case prevLast $ words input of
                      [] -> lastString $ words input
                      _  ->( (prevLast $ words input) ++
                             " " ++ (lastString $
                                          words input) )

-- | Given a list of files and folders the function filters
-- only directory names and files ending in extenstion
-- .casl
fileFilter::String ->[String]->[String] -> IO [String]
fileFilter lPath ls cons
 = case ls of
    []  -> return cons
    x:l ->
        do
         -- check if current element is a directory
         b <- doesDirectoryExist (lPath++x)
         case b of
          -- if it is,then add "/" to indicate is a folder
          True -> fileFilter lPath l ((x++"/"):cons)
          -- if it is not a folder then it must be a file
          -- so check the extension
          False-> case isSuffixOf ".casl" x of
                   True -> fileFilter lPath l (x:cons)
                   False-> fileFilter lPath l cons

-- | Given a list of files and folders the function expands
-- the list adding the content of all folders in the list
fileExtend::String->[String]->[String]-> IO [String]
fileExtend lPath ls cons
 = case ls of
    []  -> return cons
    x:l ->
         do
          -- check if current element is a directory
          b<- doesDirectoryExist (lPath++x)
          case b of
           -- if it is not then leave the file alone
           False -> fileExtend lPath l (x:cons)
           -- if it is a folder add its content
           True ->
              do
               ll <- getDirectoryContents (lPath++x)
               nll<- fileFilter (lPath++x) ll []
               let nll'=map (\y -> x++y) nll
               fileExtend lPath l (nll' ++ cons)


-- | The function behaves exactly as tail just that
-- in the case of empty list returns an empty list
-- instead of an error
safeTail::[a]->[a]
safeTail ls
 = case ls of
    []  -> []
    _:l -> l

-- | The function behaves exactly like last just that
-- in case of an empty list returns the space
-- character (it works only for lists of chars)
lastChar::[Char]->Char
lastChar ls
 = case ls of
    [] -> ' '
    _  -> last ls

-- | The function behaves exactly like last just that
-- in case of an empty list returns the empty string
-- (it is meant only for list of strings)
lastString::[String]->String
lastString ls
 = case ls of
    [] -> ""
    _  -> last ls


-- | The function nicely outputs a list of errors
prettyPrintErrList:: [String]->String
prettyPrintErrList list
 = let
     tmpPrint ls acc =
         case ls of
          []   -> []
          x:ll -> tmpPrint ll $ ("Input "++x++
                       " could not be processed\n")++acc
   in tmpPrint list []


-- | The function nicely ouputs a list of strings
prettyPrintList ::[String]->String
prettyPrintList ls
 = unlines ls
