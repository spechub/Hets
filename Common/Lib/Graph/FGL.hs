------------------------------------------------------------------------------
--  
--  FGL.hs -- Functional Graph Library  
--
--  (c) 1999 - 2002 by Martin Erwig [see file COPYRIGHT]
--
------------------------------------------------------------------------------

module FGL where

-- Graph classes
--
--   Graph.hs defines two classes: 
--    (a) Graph    for static graphs that support only graph decomposition
--    (b) DynGraph for dynamic graphs that additionally support graph construction
--
--   GraphM.hs defines one class:
--    (a) GraphM   for static monadic graphs that support only graph decomposition
--        (A monadic graph is decomposed, etc. inside a monad)
--   
import Graph
import GraphM


-- Graph implementations
-- 
--   TreeGraph.hs:  implementation of dynamic graphs by balanced binary search trees
--   IOArrGraph.hs: implementation of static monadic graphs by IO arrays
--   
import TreeGraph   
import IOArrGraph 


-- Example graphs
-- 
import GraphData


-- Tools and algorithms (based on Graph/DynGraph members)
--
import Basic
import RoseTree
import DFS
import BFS
import SP 
import GVD
import MST
import Indep
import MaxFlow
import MaxFlow2
import ArtPoint
import BCC
import Dominators
import TransClos


-- Monadic versions of (some) tools and algorithms (based on GraphM class)
-- 
import MonadicGrAl


-- Version info
-- 
version = putStrLn "\nFGL - Functional Graph Library, September 2002"
