{- |
Module      :  $Id$
Description :  Pretty printing for CspCASL
Copyright   :  (c) Andy Gimblett and Uni Bremen 2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  a.m.gimblett@swansea.ac.uk
Stability   :  provisional
Portability :  portable

Printing abstract syntax of CSP-CASL

-}
module CspCASL.Print_CspCASL where

import CASL.AS_Basic_CASL (SORT, TERM)
import CASL.ToDoc ()

import Common.Doc
import Common.DocUtils
import Common.Keywords (elseS, ifS, thenS)

import CspCASL.AS_CspCASL
import CspCASL.AS_CspCASL_Process
import CspCASL.CspCASL_Keywords

instance Pretty CspBasicSpec where
    pretty = printCspBasicSpec

printCspBasicSpec :: CspBasicSpec -> Doc
printCspBasicSpec ccs =
    chan_part $+$ proc_part
        where chan_part = case (length chans) of
                            0 -> empty
                            1 -> (keyword channelS) <+> printChanDecs chans
                            _ -> (keyword channelsS) <+> printChanDecs chans
              proc_part = (keyword processS) <+>
                          (printProcItems (proc_items ccs))
              chans = channels ccs


printChanDecs :: [CHANNEL_DECL] -> Doc
printChanDecs cds = (vcat . punctuate semi . map pretty) cds

instance Pretty CHANNEL_DECL where
    pretty = printChanDecl

printChanDecl :: CHANNEL_DECL -> Doc
printChanDecl (ChannelDecl ns s) =
    (ppWithCommas ns) <+> colon <+> (pretty s)


printProcItems :: [PROC_ITEM] -> Doc
printProcItems ps = foldl ($+$) empty (map pretty ps)

instance Pretty PROC_ITEM where
    pretty = printProcItem

printProcItem :: PROC_ITEM -> Doc
printProcItem (Proc_Decl pn args alpha) =
    (pretty pn) <> (printArgs args) <+> colon <+> (pretty alpha) <+> semi
        where printArgs [] = empty
              printArgs a = parens $ ppWithCommas a
printProcItem (Proc_Eq pn p) =
    (pretty pn) <+> equals <+> (pretty p)


instance Pretty PARM_PROCNAME where
    pretty = printParmProcname

printParmProcname :: PARM_PROCNAME -> Doc
printParmProcname (ParmProcname pn args) =
    pretty pn <> (printArgs args)
        where printArgs [] = empty
              printArgs a = parens $ ppWithCommas a

instance Pretty PROC_ALPHABET where
    pretty = printProcAlphabet

printProcAlphabet :: PROC_ALPHABET -> Doc
printProcAlphabet (ProcAlphabet commTypes _) = ppWithCommas commTypes


instance Pretty PROCESS where
    pretty = printProcess

printProcess :: PROCESS -> Doc
printProcess pr = case pr of
    -- precedence 0
    Skip _ -> text skipS
    Stop _ -> text stopS
    Div _ -> text divS
    Run es _ -> (text runS) <+> lparen <+> (pretty es) <+> rparen
    Chaos es _ -> (text chaosS) <+> lparen <+> (pretty es) <+> rparen
    NamedProcess pn ts _ ->
        (pretty pn) <+>
        if (null ts)
        then empty
        else lparen <+> (ppWithCommas ts) <+> rparen
    -- precedence 1
    ConditionalProcess f p q _ ->
        ((keyword ifS) <+> (pretty f) <+>
         (keyword thenS) <+> (glue pr p) <+>
         (keyword elseS) <+> (glue pr q)
        )
    -- precedence 2
    Hiding p es _ ->
        (pretty p) <+> hiding_proc <+> (pretty es)
    RenamingProcess p r _ ->
        ((pretty p) <+>
         ren_proc_open <+> (pretty r) <+> ren_proc_close)
    -- precedence 3
    Sequential p q _ ->
        (pretty p) <+> sequential <+> (glue pr q)
    PrefixProcess event p _ ->
        (pretty event) <+> prefix_proc $+$ (glue pr p)
    -- precedence 4
    InternalChoice p q _ ->
        (pretty p) <+> internal_choice <+> (glue pr q)
    ExternalChoice p q _ ->
        (pretty p) <+> external_choice <+> (glue pr q)
    -- precedence 5
    Interleaving p q _ ->
        (pretty p) <+> interleave <+> (glue pr q)
    SynchronousParallel p q _ ->
        (pretty p) <+> synchronous <+> (glue pr q)
    GeneralisedParallel p es q _ ->
        ((pretty p) <+> genpar_open <+> (pretty es) <+>
         genpar_close <+> (glue pr q))
    AlphabetisedParallel p les res q _ ->
        ((pretty p) <+> alpar_open <+>
         (pretty les) <+> alpar_sep <+> (pretty res) <+>
         alpar_close <+> (glue pr q)
        )
    FQProcess p _ _ -> pretty p
    -- Alternative pretty printer for FQProcess - Used for debugging
--     FQProcess p commAlpha _ ->
--         let commAlphaList = S.toList commAlpha
--             prettyComms cs = sepByCommas (map pretty cs)
--         in text "[" <+> (pretty p) <> text "]" <+> text "_" <>
--            braces (prettyComms commAlphaList)
           
instance Pretty CommType where
    pretty (CommTypeSort s) = pretty s
    pretty (CommTypeChan (TypedChanName c _)) =
        -- Only show the channel name
        pretty c
        -- parens (pretty c <+> comma <+> pretty s)

instance Pretty RENAMING where
    pretty renaming = case renaming of
                        Renaming ids -> ppWithCommas ids
                        FQRenaming fqTerms -> ppWithCommas fqTerms
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
      Sequential _ _ _ -> False
      PrefixProcess _ _ _ ->
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


-- | print an event.
printEvent :: EVENT -> Doc
printEvent ev =
    case ev of
      TermEvent t _ -> pretty t
      InternalPrefixChoice v s _ ->
          internal_choice <+> (pretty v) <+> (text svar_sortS) <+> (pretty s)
      ExternalPrefixChoice v s _ ->
          external_choice <+> (pretty v) <+> (text svar_sortS) <+> (pretty s)
      ChanSend cn t _ -> (pretty cn) <+> (text chan_sendS) <+> (pretty t)
      ChanNonDetSend cn v s _ ->
          (pretty cn) <+> (text chan_sendS) <+> (pretty v)
                          <+> (text svar_sortS) <+> (pretty s)
      ChanRecv cn v s _ ->
          (pretty cn) <+> (text chan_receiveS) <+> (pretty v)
                          <+> (text svar_sortS) <+> (pretty s)
      FQEvent e mfqChan fqVar _ -> printFQEvent e mfqChan fqVar

-- | Print a fully qualified event. We need the fully qualified
--   channel (if there is one) and the fully qualified term (which may
--   be an event or a variable). these will be passed in fro mthe
--   printEvent that actually has access to the fully qualfied parts
--   of this fully qualified event.
printFQEvent :: EVENT -> Maybe (CHANNEL_NAME, SORT) -> TERM () -> Doc
printFQEvent ev mfqChan t =
    -- We only need to know the underlysing event type as we already
    -- have all the fully qualified information.
    case ev of
      -- mfqChan shoudl be nothing
      -- t is the fully qualified term to send
      TermEvent _ _ -> pretty t
      -- mfqChan shoudl be nothing
      -- t is the fully qualified variable
      InternalPrefixChoice _ _ _ -> internal_choice <+> pretty t
      -- mfqChan shoudl be nothing
      -- t is the fully qualified variable
      ExternalPrefixChoice _ _ _ -> external_choice <+> pretty t
      -- mfqChan should be the fully qualified channel
      -- t is the fully qualified term to send
      ChanSend _ _ _ ->
          case mfqChan of
            Just (cn, s) -> (pretty cn) <> colon <> (pretty s)
                            <+> (text chan_sendS) <+> (pretty t)
            Nothing -> text "Error: Case ChanSend in printFQEvent in CspCASL.Print_CspCASL "
      -- mfqChan should be the fully qualified channel
      -- t is the fully qualified variable
      ChanNonDetSend _ _ _ _ ->
          case mfqChan of
            Just (cn, s) -> (pretty cn) <> colon <> (pretty s)
                            <+> (text chan_sendS) <+> (pretty t)
            Nothing -> text "Error: Case ChanNonDetSend in printFQEvent in CspCASL.Print_CspCASL"
      ChanRecv _ _ _ _ ->
          case mfqChan of
            Just (cn, s) -> (pretty cn) <> colon <> (pretty s)
                            <+> (text chan_receiveS) <+> (pretty t)
            Nothing -> text "Error: Case ChanRecv in printFQEvent in CspCASL.Print_CspCASL"

      -- This option should be impossible
      FQEvent _ _ _ _ -> text "Error: Case FQEvent in printFQEvent in CspCASL.Print_CspCASL"

instance Pretty EVENT_SET where
    pretty = printEventSet

printEventSet :: EVENT_SET -> Doc
printEventSet eventSet =
    case eventSet of
      EventSet es _ -> ppWithCommas es
      FQEventSet es _ -> ppWithCommas es
