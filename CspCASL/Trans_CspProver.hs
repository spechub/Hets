{- |
Module      :  $Id: Print_CspCASL.hs 9047 2007-10-13 15:24:00Z gimblett $
Description :  Pretty printing for CspCASL
Copyright   :  (c) Andy Gimblett, Liam O'Reilly and Markus Roggenbach, Swansea University 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  csliam@swansea.ac.uk
Stability   :  provisional
Portability :  portable

transforming Csp Processes to Isabelle terms

-}
module CspCASL.Trans_CspProver where

--import CspCASL.AS_CspCASL
import CspCASL.AS_CspCASL_Process
-- import CspCASL.CspCASL_Keywords
import CspCASL.CspProver_Consts
import Isabelle.IsaSign
import Isabelle.IsaConsts

transProcess :: PROCESS -> Term
transProcess pr = case pr of
    -- precedence 0
    Skip _ -> cspProver_skipOp
    Stop _ -> cspProver_stopOp
    Div  _ -> cspProver_divOp
    Run es _ -> App (cspProver_runOp) (transEventSet es) NotCont
    Chaos es _ -> App (cspProver_chaosOp) (transEventSet es) NotCont

    NamedProcess pn ts _ ->
        let pnTerm = conDouble $ show pn
        in if (null ts)
        then pnTerm
        else App pnTerm (conDouble $ show ts) NotCont
{-
    -- precedence 1
    ConditionalProcess f p q _ ->
        ((keyword cspProver_ifS) <+> (pretty f) <+>
         (keyword cspProver_thenS) <+> (glue pr p) <+>
         (keyword cspProver_elseS) <+> (glue pr q)
        )
    -- precedence 2
    Hiding p es _ ->
        (pretty p) <+> (text cspProver_hidingS) <+> (pretty es)
    RenamingProcess p r _ ->
        ((pretty p) <+>
         (text cspProver_renaming_openS) <+>
         (ppWithCommas r) <+>
         (text cspProver_renaming_closeS))
-}
    -- precedence 3
    Sequential p q _ ->
        cspProver_sequenceOp (transProcess p) (transProcess q)
--        (pretty p) <+> (text cspProver_sequenceS) <+> (glue pr q)
{-    PrefixProcess ev p _ ->
        (text "class(C_X") <+> (pretty ev) <> (text ")") <+> (text cspProver_prefixS) <+> (glue pr p)
    InternalPrefixProcess v s p _ ->
        ((text cspProver_internal_prefixS) <+> (pretty v) <+>
         (text cspProver_colonS) <+> (pretty s) <+>
         (text cspProver_prefixS) <+> (glue pr p)
        )
    ExternalPrefixProcess v s p _ ->
        ((text cspProver_external_prefixS) <+> (pretty v) <+>
         (text cspProver_colonS)  <+> (pretty s) <+>
         (text cspProver_prefixS) <+> (glue pr p)
        )
    -- precedence 4
    InternalChoice p q _ ->
        (pretty p) <+> (text cspProver_internal_choiceS) <+> (glue pr q)
    ExternalChoice p q _ ->
        (pretty p) <+> (text cspProver_external_choiceS) <+> (glue pr q)
    -- precedence 5
    Interleaving p q _ ->
        (pretty p) <+> (text cspProver_interleavingS) <+> (glue pr q)
    SynchronousParallel p q _ ->
        (pretty p) <+> (text cspProver_synchronousS) <+> (glue pr q)
-}
    GeneralisedParallel p es q _ ->
        cspProver_general_parallelOp (transProcess p) (transEventSet es) (transProcess q)

    AlphabetisedParallel p les res q _ ->
        cspProver_alphabetised_parallelOp (transProcess p) (transEventSet les) (transEventSet res) (transProcess q)
{-
-- glue and prec_comp decide whether the child in the parse tree needs
-- to be parenthesised or not.  Parentheses are necessary if the
-- right-child is at the same level of precedence as the parent but is
-- a different operator; otherwise, they're not.

glue :: PROCESS -> PROCESS -> Doc
glue x y = if (prec_comp x y)
           then lparen <+> pretty y <+> rparen
           else pretty y

-- This is really nasty, but sledgehammer effective and allows fine
-- control.  Unmaintainable, however.  :-( I imagine there's a way to
-- compare the types in a less boilerplate manner, but OTOH there are
-- some special cases where it's nice to be explicit.  Also, hiding
-- and renaming are distinctly non-standard.  *shrug*

prec_comp :: PROCESS -> PROCESS -> Bool
prec_comp x y =
    case x of
      Hiding _ _ _ ->
          case y of RenamingProcess _ _ _ -> True
                    _ -> False
      RenamingProcess _ _ _ ->
          case y of Hiding _ _ _ -> True
                    _ -> False
      Sequential _ _ _ ->
          case y of InternalPrefixProcess _ _ _ _ -> True
                    ExternalPrefixProcess _ _ _ _ -> True
                    _ -> False
      PrefixProcess _ _ _ ->
          case y of Sequential _ _ _ -> True
                    _ -> False
      InternalPrefixProcess _ _ _ _ ->
          case y of Sequential _ _ _ -> True
                    _ -> False
      ExternalPrefixProcess _ _ _ _ ->
          case y of Sequential _ _ _ -> True
                    _ -> False
      ExternalChoice _ _ _ ->
          case y of InternalChoice _ _ _ -> True
                    _ -> False
      InternalChoice _ _ _ ->
          case y of ExternalChoice _ _ _ -> True
                    _ -> False
      Interleaving _ _ _ ->
          case y of SynchronousParallel _ _ _ -> True
                    GeneralisedParallel _ _ _ _ -> True
                    AlphabetisedParallel _ _ _ _ _ -> True
                    _ -> False
      SynchronousParallel _ _ _ ->
          case y of Interleaving _ _ _ -> True
                    GeneralisedParallel _ _ _ _ -> True
                    AlphabetisedParallel _ _ _ _ _ -> True
                    _ -> False
      GeneralisedParallel _ _ _ _ ->
          case y of Interleaving _ _ _ -> True
                    SynchronousParallel _ _ _ -> True
                    AlphabetisedParallel _ _ _ _ _ -> True
                    _ -> False
      AlphabetisedParallel _ _ _ _ _ ->
          case y of Interleaving _ _ _ -> True
                    SynchronousParallel _ _ _ -> True
                    GeneralisedParallel _ _ _ _ -> True
                    _ -> False
      _ -> False

instance Pretty EVENT where
    pretty = printEvent

printEvent :: EVENT -> Doc
printEvent (TermEvent t _) = pretty t
printEvent (ChanSend cn t _) = (pretty cn) <+>
                           (text chan_sendS) <+>
                           (pretty t)
printEvent (ChanNonDetSend cn v s _) =
    (pretty cn) <+> (text chan_sendS) <+>
     (pretty v) <+> (text svar_sortS) <+> (pretty s)
printEvent (ChanRecv cn v s _) =
    (pretty cn) <+> (text chan_receiveS) <+>
     (pretty v) <+> (text svar_sortS) <+> (pretty s)

instance Pretty EVENT_SET where
    pretty = printEventSet
-}

transEventSet :: EVENT_SET -> Term
transEventSet (EventSet _ _) = conDouble "not yet done"
--transEventSet (EventSet es _) = conDouble "not yet done"
