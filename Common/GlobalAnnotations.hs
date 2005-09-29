{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Christian Maeder and Uni Bremen 2002-2003 
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  experimental
Portability :  portable 

data structures for global annotations
-}

module Common.GlobalAnnotations (module Common.GlobalAnnotations,
                                 Display_format(..))
    where

import Common.Id

import qualified Common.Lib.Map as Map
import qualified Common.Lib.Rel as Rel
import Common.AS_Annotation

-- | all global annotations and a field for PrettyPrint stuff
data GlobalAnnos = GA { prec_annos     :: PrecedenceGraph -- ^ precedences
                      , assoc_annos    :: AssocMap  -- ^ associativity
                      , display_annos  :: DisplayMap -- ^ display annotations
                      , literal_annos  :: LiteralAnnos -- ^ literal annotations
                      , literal_map    :: LiteralMap -- ^ redundant 
                        -- representation of the previous literal annotations
                      , print_conf     :: PrintConfig -- ^ gives the 
                        -- possibility to print things upon position in AST
                      } deriving (Show,Eq)

-- | empty (or initial) global annotations
emptyGlobalAnnos :: GlobalAnnos
emptyGlobalAnnos = GA { prec_annos    = Rel.empty
                      , assoc_annos   = Map.empty
                      , display_annos = Map.empty
                      , literal_annos = emptyLiteralAnnos
                      , literal_map   = Map.empty
                      , print_conf = default_print_conf
                      } 

-- | literal annotations for string, lists, number and floating
data LiteralAnnos = LA { string_lit :: Maybe (Id,Id)
                       , list_lit :: Map.Map Id (Id, Id)
                       , number_lit :: Maybe Id
                       , float_lit  :: Maybe (Id,Id)
                       } deriving (Show,Eq)

-- | empty literal annotations
emptyLiteralAnnos :: LiteralAnnos
emptyLiteralAnnos = LA { string_lit  = Nothing
                        , list_lit = Map.empty
                        , number_lit = Nothing
                        , float_lit  = Nothing
                        }

-- | ids to be displayed according to a format
type DisplayMap = Map.Map Id (Map.Map Display_format [Token])

-- | Options that can be set and used during PrettyPrinting
data PrintConfig = PrC { prc_inside_gen_arg :: Bool -- ^ set to True 
                         -- if inside of PARAMS or FIT_ARG
                       , prc_first_spec_in_param :: Bool 
                         -- ^ set to True when prc_inside_gen_arg is 
                         -- set to True; set to False if first spec 
                         -- is crossed
                       , prc_latex_print :: Bool
                         -- ^ True if printLatex0 is invoked
                         -- used in functions that decide on the same things 
                         -- but do different things
                       } deriving (Show,Eq)

default_print_conf :: PrintConfig
default_print_conf = PrC { prc_inside_gen_arg = False 
                         , prc_first_spec_in_param = False
                         , prc_latex_print = False
                         }

is_inside_gen_arg :: GlobalAnnos -> Bool
is_inside_gen_arg ga = prc_inside_gen_arg $ print_conf ga

set_inside_gen_arg :: Bool -> GlobalAnnos -> GlobalAnnos
set_inside_gen_arg b ga = ga {print_conf = print_conf'}
    where print_conf' = (print_conf ga) {prc_inside_gen_arg = b}

is_latex_print :: GlobalAnnos -> Bool
is_latex_print ga = prc_latex_print $ print_conf ga

set_latex_print :: Bool -> GlobalAnnos -> GlobalAnnos
set_latex_print b ga = ga {print_conf = print_conf'}
    where print_conf' = (print_conf ga) {prc_latex_print = b}

is_first_spec_in_param :: GlobalAnnos -> Bool
is_first_spec_in_param ga = prc_first_spec_in_param $ print_conf ga

set_first_spec_in_param :: Bool -> GlobalAnnos -> GlobalAnnos
set_first_spec_in_param b ga = ga {print_conf = print_conf'}
    where print_conf' = (print_conf ga) {prc_first_spec_in_param = b}

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
-- BothDirections means <> was given (or derived by transitive closure)
precRel pg out_id in_id =
    case (Rel.member in_id out_id pg, Rel.member out_id in_id pg) of
    (False,True)  -> Lower
    (True,False)  -> Higher
    (True,True)   -> BothDirections
    (False,False) -> NoDirection

-- | lookup of an display [string] in the GlobalAnnos record
lookupDisplay :: GlobalAnnos -> Display_format -> Id -> Maybe [Token]
lookupDisplay ga df i =
    case Map.lookup i (display_annos ga) of
    Nothing -> Nothing
    Just df_map -> case Map.lookup df df_map of
                   Nothing -> Nothing 
                   r@(Just disp_toks) -> 
                       if null disp_toks then Nothing else r


