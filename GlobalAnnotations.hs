
{- HetCATS/GlobalAnnotations.hs
   $Id$
   Author: Klaus Lüttich
   Year:   2002

   Some datastructures for fast access of GlobalAnnotations

   todo:

-}

module GlobalAnnotations where

import {-# SOURCE #-} Id 

import Graph
import FiniteMap

data GlobalAnnos = GA { prec_annos     :: PrecedenceGraph
		      , assoc_annos    :: AssocMap
		      , display_annos  :: DisplayMap
		      , literal_annos  :: [Literal_Annos]
		      }

type PrecedenceGraph = Graph Id ()

type AssocMap = FiniteMap Id AssocEither

type DisplayMap = FiniteMap Id [(String,String)]

data Literal_Annos = String_l_anno Id Id 
		   | List_l_anno Id Id Id
		   | Number_l_anno Id 
		   | Float_l_anno Id Id  

data AssocEither = Left | Right deriving (Show)


