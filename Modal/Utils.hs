
module Modal.Utils where

import Common.Id
import Common.AS_Annotation

-- CASL
import CASL.Logic_CASL
import CASL.AS_Basic_CASL

-- ModalCASL
import Modal.AS_Modal

import Data.Maybe
import Debug.Trace
getModTermSort :: Id -> Id
getModTermSort rs =
    case rs of
    Id _ [s] _ -> s
    _  -> error ("Modal2CASL: getTermSort: the impossible happened!!")

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
addTerm mapT rel mTerms vars nCaslFrm
    | null (catMaybes mTerms) = nCaslFrm
    | otherwise = trace "Modal.Utils.addTerm: Term-Modalities not corectly treated yet" nCaslFrm

{- - run with a State across formula
   - substitute in a nice manna the Terms into the relation symbols

incomple code:

 let repl f = case f of
           Quantification q vs frm ps ->
                  Quantification q vs (repl frm) ps
           Conjunction fs ps ->
               Conjunction (map (repl) fs) ps
           Disjunction fs ps ->
               Disjunction (map (repl) fs) ps
           Implication f1 f2 b ps ->
               Implication (repl f1)
                           (repl f2) b ps
           Equivalence f1 f2 ps ->
               Equivalence (repl f1)
                           (repl f2) ps
           Negation frm ps -> Negation (repl frm) ps
           True_atom ps -> True_atom ps
           False_atom ps -> False_atom ps
           Existl_equation t1 t2 ps ->
               Existl_equation t1 t2 ps
           Strong_equation t1 t2 ps ->
                  Strong_equation t1 t2 ps
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
           Definedness t ps -> Definedness t ps
           Membership t ty ps -> Membership t ty ps
           _ -> error "Modal.ModalSystems: addTerm: unsupported formula"
        term = fromJust mTerm
     in maybe nCaslFrm
              (\_-> nCaslFrm {sentence = repl (sentence nCaslFrm) }) mTerm
-}
