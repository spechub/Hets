{- |
Module      :  $Header$
Description :  sublogic analysis for CoCASL
Copyright   :  (c) Till Mossakowski, C.Maeder and Uni Bremen 2002-2006
License     :  GPLv2 or higher
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

This module provides the sublogic functions (as required by Logic.hs)
  for CoCASL. It is based on the respective functions for CASL.
-}

module CoCASL.Sublogic
    ( CoCASL_Sublogics
    , minFormSublogic
    , minCSigItem
    , minCBaseItem
    , hasCoFeature
    , setCoFeature
    ) where

import Common.AS_Annotation
import CASL.Sublogic
import CoCASL.AS_CoCASL

-- | type for CoCASL sublogics
type CoCASL_Sublogics = CASL_SL Bool

hasCoFeature :: CoCASL_Sublogics -> Bool
hasCoFeature = ext_features

setCoFeature :: Bool -> CoCASL_Sublogics -> CoCASL_Sublogics
setCoFeature b s = s { ext_features = b }

theCoFeature :: CoCASL_Sublogics
theCoFeature = setCoFeature True bottom

minFormSublogic :: C_FORMULA -> CoCASL_Sublogics
minFormSublogic cf = case cf of
    BoxOrDiamond _ _ f _ ->
        sublogics_max theCoFeature $ sl_sentence minFormSublogic f
    CoSort_gen_ax _ _ _ -> theCoFeature
        -- may be changed to Constraints with mappings
        -- may be ops need to be checked for partiality?

minCSigItem :: C_SIG_ITEM -> CoCASL_Sublogics
minCSigItem (CoDatatype_items l _) =
    foldl sublogics_max theCoFeature $ map (minCoDatatype . item) l

minCoDatatype :: CODATATYPE_DECL -> CoCASL_Sublogics
minCoDatatype (CoDatatype_decl _ l _) =
    foldl sublogics_max theCoFeature $ map (minCoAlternative . item) l

minCoAlternative :: COALTERNATIVE -> CoCASL_Sublogics
minCoAlternative a = case a of
    Co_construct fk _ l _ ->
        foldl sublogics_max (sl_opkind fk) $ map minCoComponents l
    CoSubsorts _ _ -> need_sub

minCoComponents :: COCOMPONENTS -> CoCASL_Sublogics
minCoComponents (CoSelect _ t _) = sl_op_type t

minCBaseItem :: C_BASIC_ITEM -> CoCASL_Sublogics
minCBaseItem bi = case bi of
     CoFree_datatype l _ ->
         foldl sublogics_max theCoFeature $ map minCoDatatype $ map item l
     CoSort_gen l _ -> foldl sublogics_max theCoFeature $
         map (sl_sig_items minCSigItem minFormSublogic . item) l
