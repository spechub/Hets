
{- HetCATS/GlobalAnnotations.hs
   $Id$
   Author: Klaus Lüttich
   Year:   2002

   Some datastructures for fast access of GlobalAnnotations

   todo:
   did: 12.7.02
   removed PrettyPrint from Id to avoid cyclic imports

-}

module Common.GlobalAnnotations where

import Common.Id

import Common.Lib.Graph
import Common.Lib.Map

data GlobalAnnos = GA { prec_annos     :: PrecedenceGraph
		      , assoc_annos    :: AssocMap
		      , display_annos  :: DisplayMap
		      , literal_annos  :: LiteralAnnos
		      , literal_map    :: LiteralMap
		      } deriving (Show)

type PrecedenceGraph = (Map Id Node,Graph Id Int)

data PrecRel = Higher | Lower | ExplGroup Direct
	       deriving (Show)

data Direct = BothDirections | NoDirection
	      deriving (Show)

type AssocMap = Map Id AssocEither

data AssocEither = ALeft | ARight deriving (Show,Eq)

type DisplayMap = Map Id [(String,String)]

type LiteralMap = Map Id LiteralType

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

