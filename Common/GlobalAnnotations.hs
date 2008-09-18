{- |
Module      :  $Header$
Description :  data structures for global annotations
Copyright   :  (c) Klaus Lüttich, Christian Maeder and Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

Data structures for global annotations
-}

module Common.GlobalAnnotations where

import qualified Data.Map as Map
import qualified Common.Lib.Rel as Rel
import Common.AS_Annotation
import Common.Id

-- | all global annotations and a field for pretty printing stuff
data GlobalAnnos = GA
  { prec_annos     :: PrecedenceGraph -- ^ precedences
  , assoc_annos    :: AssocMap  -- ^ associativity
  , display_annos  :: DisplayMap -- ^ display annotations
  , literal_annos  :: LiteralAnnos -- ^ literal annotations
  , literal_map    :: LiteralMap -- ^ redundant literal map
  } deriving (Show,Eq)

-- | empty (or initial) global annotations
emptyGlobalAnnos :: GlobalAnnos
emptyGlobalAnnos = GA
  { prec_annos    = Rel.empty
  , assoc_annos   = Map.empty
  , display_annos = Map.empty
  , literal_annos = emptyLiteralAnnos
  , literal_map   = Map.empty }

-- | literal annotations for string, lists, number and floating
data LiteralAnnos = LA
  { string_lit :: Maybe (Id,Id)
  , list_lit   :: Map.Map Id (Id, Id)
  , number_lit :: Maybe Id
  , float_lit  :: Maybe (Id,Id)
  } deriving (Show,Eq)

-- | empty literal annotations
emptyLiteralAnnos :: LiteralAnnos
emptyLiteralAnnos = LA
  { string_lit = Nothing
  , list_lit   = Map.empty
  , number_lit = Nothing
  , float_lit  = Nothing }

-- | ids to be displayed according to a format
type DisplayMap = Map.Map Id (Map.Map Display_format [Token])

-- | a redundant map for 'LiteralAnnos'
type LiteralMap = Map.Map Id LiteralType

-- | description of the type of a literal for a given 'Id' in 'LiteralMap'
data LiteralType =
    StringCons Id  -- ^ refer to the 'Id' of the null string
  | StringNull
  | ListCons Id Id  -- ^ brackets (as 'Id') and 'Id' of matching empty list
  | ListNull Id -- ^ brackets (as 'Id') for the empty list
  | Number
  | Fraction
  | Floating
  | NoLiteral -- ^ and error value for a 'getLiteralType'
    deriving (Show,Eq)

-- | the 'LiteralType' of an 'Id' (possibly 'NoLiteral')
getLiteralType :: GlobalAnnos -> Id -> LiteralType
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
-- BothDirections means <> was given (or derived by transitive closure)
precRel pg out_id in_id =
  case (Rel.member in_id out_id pg, Rel.member out_id in_id pg) of
    (False, True)  -> Lower
    (True, False)  -> Higher
    (True, True)   -> BothDirections
    (False, False) -> NoDirection

-- | lookup of an display [string] in the GlobalAnnos record
lookupDisplay :: GlobalAnnos -> Display_format -> Id -> Maybe [Token]
lookupDisplay ga df i = case Map.lookup i (display_annos ga) of
    Nothing -> Nothing
    Just df_map -> case Map.lookup df df_map of
      Nothing -> Nothing
      r@(Just disp_toks) -> if null disp_toks then Nothing else r
