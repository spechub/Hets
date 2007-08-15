{- |
Module      :$Header$
Description : utilitary function used throughout the CMDL interface 
              implementation
Copyright   : uni-bremen and DFKI
Licence     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@iu-bremen.de
Stability   : provisional
Portability : portable

PGIP.CMDLUtils contains different small function that are 
used throughout the CMDL interface

-} 


module PGIP.CMDLUtils 
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
       , safeTail
       , fileFilter
       , fileExtend
       , prettyPrintList
       , prettyPrintErrList
       , nodeContainsGoals
       , edgeContainsGoals
       , checkIntString
       )where

import Data.List
import Data.Char
import Static.GTheory
import Static.DevGraph
import Data.Graph.Inductive.Graph 
import System.Directory
import Common.AS_Annotation
import qualified Common.OrderedMap as OMap


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
 = (not (isDGRef l)) && 
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

-- | Given a list of edges and the complete list of all
-- edges computes not only the names of edges but also the
-- numbered name of edges
createEdgeNames:: [LNode DGNodeLab] -> [LEdge DGLinkLab] 
                  -> [LEdge DGLinkLab] -> [String]
createEdgeNames lsN lsEC lsE 
 =
  let 
   -- given the number of a node it returns its name
   nameOf x ls = case find (\(nb,_) -> nb == x) ls of
                  Nothing -> "Unknown node"
                  Just (_,DGNode t _ _ _ _ _ _) ->
                      showName t
                  Just (_,DGRef t _ _ _ _ _) ->
                      showName t
   -- list of all edge names with duplicates and edge     
   edgs = map(\l@(x,y,_) -> ((nameOf x lsN) ++
                 " -> "++(nameOf y lsN),l)) lsEC
   -- list of uncounted edge names (i.e. n1->n2)              
   simpleEdgs = nub $ map (\(x,_)->x) edgs
   -- list of counted edge name
   nbEdgs = concatMap 
             (\x -> 
              -- list of all occurances of the same name
               let p = filter (\(y,_) -> x == y) edgs
                   -- first node name
                   n1= (words x) !! 0
                   -- second node name
                   n2= (words x) !! 2
                   -- given a number n, a function that
                   -- generates n edge names x->i->y with
                   -- i from 0 to n
                   sz= length p
                   fn n l h=case n of
                             1 ->[(n1++" -> "++(show (sz-1))
                                     ++" -> "++n2 ,
                                     snd $ head h)]++l
                             _->fn (n-1)
                                 ([(n1++" -> "++(show (sz-n))
                                      ++" -> "++n2,
                                      snd $ head h)]++l)
                                      $ tail h
                   -- a list of |p| edge names counted from
                   -- 0 to |p|-1
               in fn sz [] p ) simpleEdgs
   -- compute list of numbered edges that needs to be 
   -- returned
   filEdg = map (\(x',_) -> x') $ 
             concatMap (\x -> filter (\(_,y)-> x==y) nbEdgs)
                  lsE
   -- compute list of unnumbered edges that need to be 
   -- returned
   fSE=filter(\x->case find(\y->((words y)!!0 ==(words x)!!0)
                          && ((words y)!!4 == (words x)!!2)
                         ) filEdg of
                   Nothing -> False
                   Just _  -> True) simpleEdgs
   fE=concatMap
           (\x->let 
                  ks=filter(\y->((words y)!!0==(words x)!!0)
                      &&((words y)!!4==(words x)!!2)) filEdg
                 in case length ks > 1 of
                      True -> ks
                      False -> [] ) simpleEdgs

  in fE ++ fSE



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
       strToInt s val = 
         case s of
          []  -> Just val
          _ -> case isHexDigit $ last s of
                False -> Nothing
                True -> strToInt (init s) 
                          (val * 10  + (digitToInt $ last s))
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
                  node2= getNodeNb (allx!!4) allNodes
                  nb   = strToInt (allx!!2) 0
              in
               case node1 of 
               Nothing -> Nothing
               Just x ->
                case node2 of
                Nothing -> Nothing
                Just y ->
                 case nb of 
                  Nothing -> Nothing
                  Just nb' ->
                   let ls=filter(\(x1,y1,_)->(x==x1)&&(y==y1))allEdges
                   in case length ls < nb' of
                       True -> Nothing
                       False -> Just (ls!!nb') ) lsNbEdge
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
prettyPrintErrList:: [String]->IO ()
prettyPrintErrList ls
 = case ls of
    []    -> return ()
    x:ll  -> do
              putStrLn ("Input "++x++" could not be processed")
              prettyPrintErrList ll

-- | The function nicely ouputs a list of strings
prettyPrintList ::[String]->IO ()
prettyPrintList ls
 = case ls of
    []    -> return ()
    x:ll  -> do 
              putStrLn x
              prettyPrintList ll
