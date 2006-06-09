{- |

Module      :  $Header$
Copyright   :  (c) Till Mossakowski, and Uni Bremen 2002-2003
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  till@tzi.de
Stability   :  experimental
Portability :  portable

This module provides the sublogic functions (as required by Logic.hs)
  for CoCASL. It is based on the respective functions for CASL.

Todo: extend this to the coalgebraic features.

-}

module CoCASL.Sublogic ( -- * datatypes
                   CoCASL_Sublogics(..),

                   -- * functions for SemiLatticeWithTop instance
                   top,
                   sublogics_max,

                   -- * functions for the creation of minimal sublogics
                   bottom,
                   -- * functions for Logic instance
                   
                   -- * sublogic to string conversion
                   sublogics_name,
                   
                   -- * list of all sublogics
                   sublogics_all,

                   -- * checks if element is in given sublogic
                   in_basic_spec,
                   in_sentence,
                   in_symb_items,
                   in_symb_map_items,
                   in_sign,
                   in_morphism,
                   in_symbol,

                   -- * computes the sublogic of a given element
                   sl_basic_spec,
                   sl_sentence,
                   sl_symb_items,
                   sl_symb_map_items,
                   sl_sign,
                   sl_morphism,
                   sl_symbol,
                   
                   -- * projects an element into a given sublogic
                   pr_basic_spec,
                   pr_symb_items,
                   pr_symb_map_items,
                   pr_sign,
                   pr_morphism,
                   pr_epsilon,
                   pr_symbol
                 ) where

import Data.Maybe
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Rel as Rel
import Common.Id
import Common.AS_Annotation
import qualified CASL.Sublogic
import CASL.AS_Basic_CASL
import CASL.Sign
import CASL.Morphism

------------------------------------------------------------------------------
-- | Datatypes for CoCASL sublogics
------------------------------------------------------------------------------

data CoCASL_Sublogics = CoCASL_SL
                        { has_co::Bool,   -- ^ Coalgebra
                          casl::CASL.Sublogic.CASL_Sublogics  -- ^ the CASL part
                        } deriving (Show,Eq)

-----------------------------------------------------------------------------
-- Special sublogics elements
-----------------------------------------------------------------------------

-- top element
--
top :: CoCASL_Sublogics
top = CoCASL_SL True CASL.Sublogic.top

-- bottom element
--
bottom :: CoCASL_Sublogics
bottom = CoCASL_SL False CASL.Sublogic.bottom


-- all elements
-- create a list of all CASL sublogics by generating all possible
-- feature combinations and then filtering illegal ones out
--
sublogics_all :: [CoCASL_Sublogics]
sublogics_all = 
  map (\l -> CoCASL_SL {has_co = False, casl = l}) CASL.Sublogic.sublogics_all
  ++
  map (\l -> CoCASL_SL {has_co = True, casl = l}) CASL.Sublogic.sublogics_all


sublogics_name :: CoCASL_Sublogics -> [String]
sublogics_name x = 
  map (( if (has_co  x) then "Co" else "")++) 
      (CASL.Sublogic.sublogics_name (casl x))


------------------------------------------------------------------------------
-- min/join and max/meet functions
------------------------------------------------------------------------------

sublogics_max :: CoCASL_Sublogics -> CoCASL_Sublogics -> CoCASL_Sublogics
sublogics_max a b = 
  CoCASL_SL { has_co = has_co  a || has_co  b,
              casl   = casl a `CASL.Sublogic.sublogics_max` casl b
            }

------------------------------------------------------------------------------
-- Functions to compute minimal sublogic for a given element, these work
-- by recursing into all subelements
------------------------------------------------------------------------------

sl_basic_spec :: BASIC_SPEC b s f -> CoCASL_Sublogics
sl_basic_spec (Basic_spec l) = 
  CoCASL_SL { has_co = True,
              casl = CASL.Sublogic.sl_basic_spec (Basic_spec l)
            }

sl_symb_items :: SYMB_ITEMS -> CoCASL_Sublogics
sl_symb_items (Symb_items k l p) = 
  CoCASL_SL { has_co = True,
              casl = CASL.Sublogic.sl_symb_items (Symb_items k l p)
            }

sl_symb_map_items :: SYMB_MAP_ITEMS -> CoCASL_Sublogics
sl_symb_map_items (Symb_map_items k l p) = 
  CoCASL_SL { has_co = True,
              casl = CASL.Sublogic.sl_symb_map_items (Symb_map_items k l p)
            }

sl_sign :: Sign f e -> CoCASL_Sublogics
sl_sign s = 
  CoCASL_SL { has_co = True,
              casl = CASL.Sublogic.sl_sign s
            }

sl_sentence :: FORMULA f -> CoCASL_Sublogics
sl_sentence phi = 
  CoCASL_SL { has_co = True,
              casl = CASL.Sublogic.sl_sentence phi
            }


sl_morphism :: Morphism f e m -> CoCASL_Sublogics
sl_morphism m = 
  CoCASL_SL { has_co = True,
              casl = CASL.Sublogic.sl_morphism m
            }

sl_symbol :: Symbol -> CoCASL_Sublogics
sl_symbol (Symbol s t) = 
  CoCASL_SL { has_co = True,
              casl = CASL.Sublogic.sl_symbol (Symbol s t)
            }


in_basic_spec :: CoCASL_Sublogics -> BASIC_SPEC b s f -> Bool
in_basic_spec l x = 
  CASL.Sublogic.in_basic_spec (casl l) x

in_sentence :: CoCASL_Sublogics -> FORMULA f -> Bool
in_sentence l x = 
  CASL.Sublogic.in_sentence (casl l) x

in_symb_items :: CoCASL_Sublogics -> SYMB_ITEMS -> Bool
in_symb_items l x = 
  CASL.Sublogic.in_symb_items (casl l) x

in_symb_map_items :: CoCASL_Sublogics -> SYMB_MAP_ITEMS -> Bool
in_symb_map_items l x = 
  CASL.Sublogic.in_symb_map_items (casl l) x

in_sign :: CoCASL_Sublogics -> Sign f e -> Bool
in_sign l x = 
  CASL.Sublogic.in_sign (casl l) x

in_morphism :: CoCASL_Sublogics -> Morphism f e m -> Bool
in_morphism l x = 
  CASL.Sublogic.in_morphism (casl l) x

in_symbol :: CoCASL_Sublogics -> Symbol -> Bool
in_symbol l x = 
  CASL.Sublogic.in_symbol (casl l) x

------------------------------------------------------------------------------
-- projection functions
------------------------------------------------------------------------------

pr_basic_spec :: CoCASL_Sublogics -> BASIC_SPEC b s f -> BASIC_SPEC b s f
pr_basic_spec l x =
  CASL.Sublogic.pr_basic_spec (casl l) x

pr_symbol :: CoCASL_Sublogics -> Symbol -> Maybe Symbol
pr_symbol l x =
  CASL.Sublogic.pr_symbol (casl l) x

pr_symb_items :: CoCASL_Sublogics -> SYMB_ITEMS -> Maybe SYMB_ITEMS
pr_symb_items l x =
  CASL.Sublogic.pr_symb_items (casl l) x

pr_symb_map_items :: CoCASL_Sublogics -> SYMB_MAP_ITEMS -> Maybe SYMB_MAP_ITEMS
pr_symb_map_items l x =
  CASL.Sublogic.pr_symb_map_items (casl l) x

pr_sign :: CoCASL_Sublogics -> Sign f e -> Sign f e
pr_sign l x =
  CASL.Sublogic.pr_sign (casl l) x
    
pr_morphism :: CoCASL_Sublogics -> Morphism f e m -> Morphism f e m
pr_morphism l x =
  CASL.Sublogic.pr_morphism (casl l) x

pr_epsilon :: Ext f e m -> CoCASL_Sublogics -> Sign f e -> Morphism f e m
pr_epsilon e l x =
  CASL.Sublogic.pr_epsilon e (casl l) x
