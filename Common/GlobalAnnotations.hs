{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Christian Maeder and Uni Bremen 2002-2003 
Licence     :  All rights reserved.

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  portable 
    
   data structures for global annotations
-}

module Common.GlobalAnnotations where

import Common.Id

import qualified Common.Lib.Map as Map
import qualified Common.Lib.Rel as Rel
import qualified Common.Lib.Set as Set
import Common.AS_Annotation

-- | all global annotations
data GlobalAnnos = GA { prec_annos     :: PrecedenceGraph -- ^ precedences
		      , assoc_annos    :: AssocMap  -- ^ associativity
		      , display_annos  :: DisplayMap -- ^ display annotations
		      , literal_annos  :: LiteralAnnos -- ^ literal annotations
		      , literal_map    :: LiteralMap -- ^ redundant 
			-- representation of the previous literal annotations 
		      } deriving (Show)

-- | empty (or initial) global annotations
emptyGlobalAnnos :: GlobalAnnos
emptyGlobalAnnos = GA { prec_annos    = Rel.empty
		      , assoc_annos   = Map.empty
		      , display_annos = Map.empty
		      , literal_annos = emptyLiteralAnnos
		      , literal_map   = Map.empty
		      } 

-- | literal annotations for string, lists, number and floating
data LiteralAnnos = LA { string_lit :: Maybe (Id,Id)
                       , list_lit :: Set.Set (Id, Id, Id)
		       , number_lit :: Maybe Id
		       , float_lit  :: Maybe (Id,Id)
		       } deriving (Show)

-- | empty literal annotations
emptyLiteralAnnos :: LiteralAnnos
emptyLiteralAnnos = LA { string_lit  = Nothing
			, list_lit = Set.empty
			, number_lit = Nothing
			, float_lit  = Nothing
			}

-- | ids to be displayed according to a format
type DisplayMap = Map.Map Id (Map.Map Display_format String)

-- | a redundant map for 'LiteralAnnos' 
type LiteralMap = Map.Map Id LiteralType

-- | description of the type of a literal for a given 'Id' in 'LiteralMap' 
data LiteralType = StringCons Id  -- ^ refer to the 'Id' of the null string 
		 | StringNull
		 | ListCons Id Id  -- ^ brackets (as 'Id') and the 'Id' of the 
                                   -- matching null list
                 | ListNull Id -- ^ brackets (as 'Id') for the empty list
		 | Number
		 | Fraction 
		 | Floating
		 | NoLiteral -- ^ and error value for a 'getLiteralType'
		   deriving (Show,Eq)

-- | the 'LiteralType' of an 'Id' (possibly 'NoLiteral')
getLiteralType ::  GlobalAnnos -> Id -> LiteralType
getLiteralType ga i = 
    Map.findWithDefault NoLiteral i $ literal_map ga

-- | a map of associative ids 
type AssocMap = Map.Map Id AssocEither

-- | check if 'Id' has a given associativity
isAssoc :: AssocEither -> AssocMap -> Id -> Bool
isAssoc ae amap i =
    case Map.lookup i amap of
    Nothing  -> False
    Just ae' -> ae' == ae 

-- | a binary relation over ids as precedence graph
type PrecedenceGraph = Rel.Rel Id

-- | return precedence relation of two ids 
precRel :: PrecedenceGraph -- ^ Graph describing the precedences
	-> Id -- ^ x oID (y iid z) -- outer id
	-> Id -- ^ x oid (y iID z) -- inner id
	-> PrecRel
-- a 'Lower' corresponds to %prec {out_id} < {in_id} 
precRel pg out_id in_id =
    case (Rel.member in_id out_id pg, Rel.member out_id in_id pg) of
    (False,True)  -> Lower
    (True,False)  -> Higher
    (True,True)   -> BothDirections
    (False,False) -> NoDirection
