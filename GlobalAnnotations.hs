
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
		      , literal_map    :: LiteralMap
		      } deriving (Show)

type PrecedenceGraph = (FiniteMap Id Node,Graph Id Int)

data PrecRel = Higher | Lower | ExplGroup Direct
	       deriving (Show)

data Direct = BothDirections | NoDirection
	      deriving (Show)

type AssocMap = FiniteMap Id AssocEither

data AssocEither = ALeft | ARight deriving (Show,Eq)

type DisplayMap = FiniteMap Id [(String,String)]

type LiteralMap = FiniteMap Id LiteralType

data LiteralType = StringCons | StringNull
		 | ListBrackets | ListCons | ListNull
		 | Number
		 | Fraction | Floating
		   deriving (Show,Eq)

data LiteralAnnos = LA { string_lit :: Maybe (Id,Id)
		       , list_lit   :: Maybe (Id,Id,Id)
		       , number_lit :: Maybe Id
		       , float_lit  :: Maybe (Id,Id)
		       } deriving (Show)

instance (Show a,Show b) => Show (FiniteMap a b) where
    show = show . fmToList

