
{- HetCATS/GlobalAnnotations.hs
   $Id$
   Author: Klaus Lüttich
   Year:   2002

   Some datastructures for fast access of GlobalAnnotations

   todo:
   did: 12.7.02
   removed PrettyPrint from Id to avoid cyclic imports

-}

module GlobalAnnotations where

import Id

import Graph
import FiniteMap

data GlobalAnnos = GA { prec_annos     :: PrecedenceGraph
		      , assoc_annos    :: AssocMap
		      , display_annos  :: DisplayMap
		      , literal_annos  :: LiteralAnnos
		      } deriving (Show)

type PrecedenceGraph = (FiniteMap Id Node,Graph Id Int)

type AssocMap = FiniteMap Id AssocEither

type DisplayMap = FiniteMap Id [(String,String)]

data LiteralAnnos = LA { string_lit :: Maybe (Id,Id)
			, list_lit   :: Maybe (Id,Id,Id)
			, number_lit :: Maybe Id
			, float_lit  :: Maybe (Id,Id)
			} deriving (Show)

data AssocEither = ALeft | ARight deriving (Show)

instance (Show a,Show b) => Show (FiniteMap a b) where
    show = show . fmToList

