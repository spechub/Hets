{- |
Module      :  $Header$
Description :  Pretty printing for CspCASL
Copyright   :  (c) Andy Gimblett and Uni Bremen 2006
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  a.m.gimblett@swansea.ac.uk
Stability   :  provisional
Portability :  portable

Printing abstract syntax of CSP-CASL

-}
module CspCASL.Print_CspCASL where

import CASL.AS_Basic_CASL (SORT, TERM)
import CASL.ToDoc
import Common.Doc
import Common.DocUtils
import Common.Keywords (elseS, ifS, thenS)
import CspCASL.AS_CspCASL
import CspCASL.AS_CspCASL_Process
import CspCASL.CspCASL_Keywords
import qualified Data.Set as Set

instance Pretty CspBasicExt where
    pretty = printCspBasicExt

instance ListCheck CHANNEL_DECL where
  innerList (ChannelDecl l _) = innerList l

printCspBasicExt :: CspBasicExt -> Doc
printCspBasicExt ccs = case ccs of
  Channels cs _ -> keyword (channelS ++ pluralS cs)
    <+> semiAnnos printChanDecl cs
  ProcItems ps _ -> keyword processS
    <+> semiAnnos printProcItem ps

instance Pretty FQ_PROCESS_NAME where
  pretty = printProcessName

-- | Pretty printing for process profiles
instance Pretty ProcProfile where
  pretty = printProcProfile

printProcProfile :: ProcProfile -> Doc
printProcProfile (ProcProfile sorts commAlpha) =
    sep [ printArgs sorts
        , printProcAlphabet (ProcAlphabet $ Set.toList commAlpha)]

printProcessName :: FQ_PROCESS_NAME -> Doc
printProcessName fqPn = case fqPn of
    PROCESS_NAME pn -> pretty pn
    FQ_PROCESS_NAME pn argSorts al -> parens $ sep
      [ keyword processS <+> pretty pn <> printArgs argSorts
      , printProcAlphabet al ]

instance Pretty CHANNEL_DECL where
    pretty = printChanDecl

printChanDecl :: CHANNEL_DECL -> Doc
printChanDecl (ChannelDecl ns s) =
    ppWithCommas ns <+> colon <+> pretty s

instance Pretty PROC_ITEM where
    pretty = printProcItem

printArgs :: Pretty a => [a] -> Doc
printArgs a = if null a then empty else parens $ ppWithCommas a

printProcItem :: PROC_ITEM -> Doc
printProcItem (Proc_Decl pn args alpha) =
    sep [pretty pn <> printArgs args, printProcAlphabet alpha]
printProcItem (Proc_Defn pn args alpha p) =
    sep [ pretty pn <> printOptArgDecls args
        , printProcAlphabet alpha
        , equals <+> pretty p]
printProcItem (Proc_Eq pn p) = sep [pretty pn, equals <+> pretty p]

instance Pretty PARM_PROCNAME where
    pretty = printParmProcname

printParmProcname :: PARM_PROCNAME -> Doc
printParmProcname (ParmProcname pn args) =
    pretty pn <> printArgs args

printProcAlphabet :: PROC_ALPHABET -> Doc
printProcAlphabet (ProcAlphabet commTypes) = colon <+> case commTypes of
  [CommTypeSort s] -> pretty s
  _ -> braces $ ppWithCommas commTypes

instance Pretty PROCESS where
    pretty = printProcess

printProcess :: PROCESS -> Doc
printProcess pr = case pr of
    -- precedence 0
    Skip _ -> text skipS
    Stop _ -> text stopS
    Div _ -> text divS
    Run es _ -> text runS <+> parens (pretty es)
    Chaos es _ -> text chaosS <+> parens (pretty es)
    NamedProcess pn ts _ ->
        pretty pn <+> printArgs ts
    -- precedence 1
    ConditionalProcess f p q _ -> fsep
        [ keyword ifS <+> pretty f
        , keyword thenS <+> pretty p
        , keyword elseS <+> pretty q ]
    -- precedence 2
    Hiding p es _ -> sep
        [ lglue pr p, hiding_proc <+> pretty es ]
    RenamingProcess p r _ -> sep
        [ lglue pr p, ren_proc_open <+> pretty r <+> ren_proc_close ]
    -- precedence 3
    Sequential p q _ -> sep
        [ lglue pr p, sequential <+> glue pr q ]
    PrefixProcess event p _ -> sep
        [ pretty event <+> prefix_proc, glue pr p ]
    -- precedence 4
    InternalChoice p q _ -> sep
        [ lglue pr p, internal_choice <+> glue pr q ]
    ExternalChoice p q _ -> sep
        [ lglue pr p, external_choice <+> glue pr q ]
    -- precedence 5
    Interleaving p q _ -> sep
        [ lglue pr p, interleave <+> glue pr q ]
    SynchronousParallel p q _ -> sep
        [ lglue pr p, synchronous <+> glue pr q ]
    GeneralisedParallel p es q _ -> fsep
        [ lglue pr p
        , genpar_open <+> pretty es <+> genpar_close
        , glue pr q ]
    AlphabetisedParallel p les res q _ -> fsep
        [ lglue pr p
        , alpar_open <+> pretty les
        , alpar_sep <+> pretty res
        , alpar_close <+> glue pr q ]
    FQProcess p _ _ -> pretty p

instance Pretty CommType where
    pretty (CommTypeSort s) = pretty s
    pretty (CommTypeChan (TypedChanName c s)) =
        pretty c <+> colon <+> pretty s

instance Pretty RENAMING where
    pretty renaming = case renaming of
                        Renaming ids -> ppWithCommas ids
                        FQRenaming fqTerms -> ppWithCommas fqTerms

{- glue and lglue decide whether the child in the parse tree needs
to be parenthesised or not. -}

-- | the second argument is a right argument process of the first argument
glue :: PROCESS -> PROCESS -> Doc
glue x y = let
  p = procPrio y
  q = procPrio x in
  (if p < Cond && (p > q || p == q && p > Pre) then parens else id) $ pretty y

-- | the second argument is a left argument process of the first argument
lglue :: PROCESS -> PROCESS -> Doc
lglue x y = (if procPrio y > procPrio x then parens else id) $ pretty y

{- par binds weakest and is left associative. Then choice follows,
then sequence, then prefix and finally renaming or hiding. -}

data Prio = Prim | Post | Pre | Seq | Choice | Par | Cond deriving (Eq, Ord)

procPrio :: PROCESS -> Prio
procPrio x = case x of
  ConditionalProcess _ _ _ _ -> Cond
  SynchronousParallel _ _ _ -> Par
  GeneralisedParallel _ _ _ _ -> Par
  AlphabetisedParallel _ _ _ _ _ -> Par
  Interleaving _ _ _ -> Par
  ExternalChoice _ _ _ -> Choice
  InternalChoice _ _ _ -> Choice
  Sequential _ _ _ -> Seq
  PrefixProcess _ _ _ -> Pre
  Hiding _ _ _ -> Post
  RenamingProcess _ _ _ -> Post
  _ -> Prim

instance Pretty EVENT where
    pretty = printEvent

-- | print an event.
printEvent :: EVENT -> Doc
printEvent ev =
    case ev of
      TermEvent t _ -> pretty t
      InternalPrefixChoice v s _ ->
          internal_choice <+> pretty v <+> text svar_sortS <+> pretty s
      ExternalPrefixChoice v s _ ->
          external_choice <+> pretty v <+> text svar_sortS <+> pretty s
      ChanSend cn t _ -> pretty cn <+> text chan_sendS <+> pretty t
      ChanNonDetSend cn v s _ ->
          pretty cn <+> text chan_sendS <+> pretty v
                          <+> text svar_sortS <+> pretty s
      ChanRecv cn v s _ ->
          pretty cn <+> text chan_receiveS <+> pretty v
                          <+> text svar_sortS <+> pretty s
      FQEvent e mfqChan fqVar _ -> printFQEvent e mfqChan fqVar

{- | Print a fully qualified event. We need the fully qualified
channel (if there is one) and the fully qualified term (which may
be an event or a variable). these will be passed in from the
printEvent that actually has access to the fully qualified parts
of this fully qualified event. -}
printFQEvent :: EVENT -> Maybe (CHANNEL_NAME, SORT) -> TERM () -> Doc
printFQEvent ev mfqChan t =
  let mess msg = text $ "Error: Case " ++ msg
        ++ " in printFQEvent in CspCASL.Print_CspCASL"
    {- We only need to know the underlysing event type as we already
    have all the fully qualified information. -}
  in case ev of
      {- mfqChan should be nothing
      t is the fully qualified term to send -}
      TermEvent _ _ -> pretty t
      {- mfqChan shoudl be nothing
      t is the fully qualified variable -}
      InternalPrefixChoice _ _ _ -> internal_choice <+> pretty t
      {- mfqChan shoudl be nothing
      t is the fully qualified variable -}
      ExternalPrefixChoice _ _ _ -> external_choice <+> pretty t
      {- mfqChan should be the fully qualified channel
      t is the fully qualified term to send -}
      ChanSend _ _ _ ->
          case mfqChan of
            Just (cn, s) -> pretty cn <> colon <> pretty s
                            <+> text chan_sendS <+> pretty t
            Nothing -> mess "ChanSend"
      {- mfqChan should be the fully qualified channel
      t is the fully qualified variable -}
      ChanNonDetSend _ _ _ _ ->
          case mfqChan of
            Just (cn, s) -> pretty cn <> colon <> pretty s
                            <+> text chan_sendS <+> pretty t
            Nothing -> mess "ChanNonDetSend"
      ChanRecv _ _ _ _ ->
          case mfqChan of
            Just (cn, s) -> pretty cn <> colon <> pretty s
                            <+> text chan_receiveS <+> pretty t
            Nothing -> mess "ChanRecv"
      -- This option should be impossible
      FQEvent _ _ _ _ -> mess "FQEvent"

instance Pretty EVENT_SET where
    pretty = printEventSet

printEventSet :: EVENT_SET -> Doc
printEventSet eventSet =
    case eventSet of
      EventSet es _ -> ppWithCommas es
      FQEventSet es _ -> ppWithCommas es
