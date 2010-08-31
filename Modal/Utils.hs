{- |
Module      :  $EmptyHeader$
Description :  <optional short description entry>
Copyright   :  (c) <Authors or Affiliations>
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  <email>
Stability   :  unstable | experimental | provisional | stable | frozen
Portability :  portable | non-portable (<reason>)

<optional description>
-}

module Modal.Utils where

import Common.Id
import Common.AS_Annotation

-- CASL
import CASL.AS_Basic_CASL

-- ModalCASL
import Modal.AS_Modal
import Data.Maybe

getModTermSort :: Id -> Id
getModTermSort rs = case rs of
    Id _ [s] _ -> s
    _  -> error "Modal.Utils.getModTermSort"

addNonEmptyLabel :: String -> Maybe (Named a) -> Maybe (Named a)
addNonEmptyLabel _ Nothing = Nothing
addNonEmptyLabel l (Just s)
    | null l    = Just s
    | otherwise = Just $ reName (const l) s

modToTerm :: MODALITY -> Maybe (TERM M_FORMULA)
modToTerm (Simple_mod _) = Nothing
modToTerm (Term_mod t) = Just t

addTerm :: ([VAR] -> TERM M_FORMULA -> TERM ())
        -> PRED_NAME -> [Maybe (TERM M_FORMULA)] -> [VAR]
        -> Maybe (Named CASLFORMULA) -> Maybe (Named CASLFORMULA)
addTerm _ _ mTerms _ nCaslFrm
    | null (catMaybes mTerms) = nCaslFrm
    | otherwise = nCaslFrm -- Term-Modalities not correctly treated yet

{- - run with a State across formula
   - substitute in a nice manna the Terms into the relation symbols

incomplete code:
           Predication pn as qs ->
               let term' = mapT vars term
                   (pn',as') =
                       case pn of
                       Pred_name _ -> error "Modal2CASL: untyped predication"
                       Qual_pred_name prn pType@(Pred_type sorts pps) ps
                            | prn == rel ->
                                 (Qual_pred_name prn
                                          (Pred_type (getModTermSort prn:sorts)
                                                     pps) ps,
                                       term':as)
                            | otherwise -> (pn,as)
               in Predication pn' as' qs
-}
