{- |
Module      :  ./CspCASL/Print_CspCASL.hs
Description :  Pretty printing for CspCASL
Copyright   :  (c) Andy Gimblett and Uni Bremen 2006
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  a.m.gimblett@swansea.ac.uk
Stability   :  provisional
Portability :  portable

Printing abstract syntax of CSP-CASL

-}
module CspCASL.Print_CspCASL where

import CASL.Fold
import CASL.ToDoc
import Common.Doc
import Common.DocUtils
import Common.Keywords (elseS, ifS, thenS, opS, predS)
import CspCASL.AS_CspCASL
import CspCASL.AS_CspCASL_Process
import CspCASL.CspCASL_Keywords
import qualified Data.HashSet as Set

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

printCommAlpha :: CommAlpha -> Doc
printCommAlpha = printProcAlphabet . ProcAlphabet . Set.toList

printProcProfile :: ProcProfile -> Doc
printProcProfile (ProcProfile sorts commAlpha) =
  sep [printArgs sorts, printCommAlpha commAlpha]

printProcessName :: FQ_PROCESS_NAME -> Doc
printProcessName fqPn = case fqPn of
    PROCESS_NAME pn -> pretty pn
    FQ_PROCESS_NAME pn profile -> parens $ sep
      [ keyword processS <+> pretty pn <> printProcProfile profile]

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

instance Pretty Rename where
  pretty (Rename i mk) = let n = pretty i in case mk of
    Nothing -> n
    Just (k, ms) -> case ms of
      Nothing -> case k of
        BinPred -> keyword predS <+> n
        _ -> keyword opS <+> n
      Just (s1, s2) -> n <+> colon <+> pretty s1 <+> case k of
          BinPred -> cross
          TotOp -> funArrow
          PartOp -> pfun
        <+> pretty s2

instance Pretty RENAMING where
    pretty (Renaming ids) = ppWithCommas ids

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
lglue x y =
  (if procPrio y > procPrio x || hasRightCond y then parens else id)
  $ pretty y

hasRightCond :: PROCESS -> Bool
hasRightCond x = case x of
  ConditionalProcess {} -> True
  SynchronousParallel _ y _ -> hasRightCond y
  GeneralisedParallel _ _ y _ -> hasRightCond y
  AlphabetisedParallel _ _ _ y _ -> hasRightCond y
  Interleaving _ y _ -> hasRightCond y
  ExternalChoice _ y _ -> hasRightCond y
  InternalChoice _ y _ -> hasRightCond y
  Sequential _ y _ -> hasRightCond y
  PrefixProcess _ y _ -> hasRightCond y
  _ -> False

{- par binds weakest and is left associative. Then choice follows,
then sequence, then prefix and finally renaming or hiding. -}

data Prio = Prim | Post | Pre | Seq | Choice | Par | Cond deriving (Eq, Ord)

procPrio :: PROCESS -> Prio
procPrio x = case x of
  ConditionalProcess {} -> Cond
  SynchronousParallel {} -> Par
  GeneralisedParallel {} -> Par
  AlphabetisedParallel {} -> Par
  Interleaving {} -> Par
  ExternalChoice {} -> Choice
  InternalChoice {} -> Choice
  Sequential {} -> Seq
  PrefixProcess {} -> Pre
  Hiding {} -> Post
  RenamingProcess {} -> Post
  _ -> Prim

instance Pretty EVENT where
    pretty = printEvent

-- | print an event.
printEvent :: EVENT -> Doc
printEvent ev =
    let printRecord' = printRecord {
          foldQual_var = \ _ v _ _ -> sidDoc v}

        caslPrintTerm = foldTerm printRecord'
    in case ev of
      TermEvent t _ -> caslPrintTerm t
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
      FQTermEvent t _ -> caslPrintTerm t
      FQExternalPrefixChoice t _ -> external_choice <+> pretty t
      FQInternalPrefixChoice t _ -> internal_choice <+> pretty t
      FQChanSend (cn, s) t _ -> pretty cn <> colon <> pretty s <+>
                                text chan_sendS <+> pretty t
      FQChanNonDetSend (cn, s) v _ -> pretty cn <> colon <> pretty s <+>
                                      text chan_sendS <+> pretty v
      FQChanRecv (cn, s) v _ -> pretty cn <> colon <> pretty s <+>
                                text chan_receiveS <+> pretty v

instance Pretty EVENT_SET where
    pretty = printEventSet

printEventSet :: EVENT_SET -> Doc
printEventSet (EventSet es _) = ppWithCommas es
