{- |
Module      :  $Header$
Description :  Parser for CspCASL processes
Copyright   :  (c)
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  a.m.gimblett@swan.ac.uk
Stability   :  experimental
Portability :  portable

Parser for CSP-CASL processes.

-}

module CspCASL.Parse_CspCASL_Process
  ( channel_name
  , comm_type
  , parens
  , parenList
  , cspStartKeys
  , cspSortId
  , parseCspId
  , csp_casl_process
  , event_set
  , process_name
  , simple_process_name
  , var
  , commType
  , bracedList
  , procDeclOrEq
  ) where

import Text.ParserCombinators.Parsec

import CASL.AS_Basic_CASL (FORMULA, SORT, TERM, VAR)
import qualified CASL.Formula
import Common.AnnoState
import Common.Id
import Common.Keywords
import Common.Lexer
import Common.Parsec
import Common.Token (parseId, sortId, varId)

import CspCASL.AS_CspCASL_Process
import CspCASL.CspCASL_Keywords

import qualified Data.Set as Set
import Data.Maybe

csp_casl_process :: AParser st PROCESS
csp_casl_process = cond_proc <|> par_proc

cond_proc :: AParser st PROCESS
cond_proc = do
    ift <- asKey ifS
    f <- formula
    asKey thenS
    p <- csp_casl_process
    asKey elseS
    q <- csp_casl_process
    return $ ConditionalProcess f p q $ compRange ift q

par_proc :: AParser st PROCESS
par_proc = choice_proc >>= par_proc'

par_proc' :: PROCESS -> AParser st PROCESS
par_proc' lp = do
    asKey interleavingS
    rp <- choice_proc
    par_proc' (Interleaving lp rp (compRange lp rp))
  <|> do
    asKey synchronousS
    rp <- choice_proc
    par_proc' (SynchronousParallel lp rp (compRange lp rp))
  <|> do
    asKey genpar_openS
    es <- event_set <?> "communication type"
    asKey genpar_closeS
    rp <- choice_proc
    par_proc' (GeneralisedParallel lp es rp (compRange lp rp))
  <|> do
    asKey alpar_openS
    les <- event_set
    asKey alpar_sepS
    res <- event_set
    asKey alpar_closeS
    rp <- choice_proc
    par_proc' (AlphabetisedParallel lp les res rp (compRange lp rp))
  <|> return lp

choice_proc :: AParser st PROCESS
choice_proc = seq_proc >>= choice_proc'

choice_proc' :: PROCESS -> AParser st PROCESS
choice_proc' lp = do
    asKey external_choiceS
    rp <- seq_proc
    choice_proc' (ExternalChoice lp rp (compRange lp rp))
  <|> do
    asKey internal_choiceS
    rp <- seq_proc
    choice_proc' (InternalChoice lp rp (compRange lp rp))
  <|> return lp

seq_proc :: AParser st PROCESS
seq_proc = pref_proc >>= seq_proc'

cspStartKeys :: [String]
cspStartKeys = startCspKeywords ++ startKeyword

seqSym :: AParser st Token
seqSym = asKey sequentialS `notFollowedWith`
  (forget procDeclOrEq <|> choice (map (forget . asKey) cspStartKeys))

seq_proc' :: PROCESS -> AParser st PROCESS
seq_proc' lp = do
    seqSym
    rp <- pref_proc
    seq_proc' (Sequential lp rp (compRange lp rp))
  <|> return lp

pref_proc :: AParser st PROCESS
pref_proc = do
    e <- try (event << asKey prefix_procS)
    p <- pref_proc
    return (PrefixProcess e p (compRange e p))
  <|> hid_ren_proc

hid_ren_proc :: AParser st PROCESS
hid_ren_proc = prim_proc >>= hid_ren_proc'

hid_ren_proc' :: PROCESS -> AParser st PROCESS
hid_ren_proc' lp = do
    asKey hiding_procS
    es <- event_set
    hid_ren_proc' (Hiding lp es (compRange lp es))
  <|> do
    asKey ren_proc_openS
    rn <- renaming
    ck <- asKey ren_proc_closeS
    hid_ren_proc' (RenamingProcess lp rn (compRange lp ck))
  <|> return lp

-- | parser for parens
parens :: AParser st a -> AParser st a
parens p = oParenT >> p << cParenT

-- | parser for comma-separated items in parens
parenList :: AParser st a -> AParser st [a]
parenList = parens . commaSep1

prim_proc :: AParser st PROCESS
prim_proc = do
    pn <- process_name
    args <- procArgs
    return $ NamedProcess pn args $ compRange pn args
  <|> parens csp_casl_process
  <|> do
    rk <- asKey runS
    es <- parens event_set
    return $ Run es $ getRange rk
  <|> do
    ck <- asKey chaosS
    es <- parens event_set
    return $ Chaos es $ getRange ck
  <|> fmap (Div . getRange) (asKey divS)
  <|> fmap (Stop . getRange) (asKey stopS)
  <|> fmap (Skip . getRange) (asKey skipS)


-- | Parse a process name which can be a simple one or a fully qualified one.
process_name :: AParser st FQ_PROCESS_NAME
process_name = qualProc <|> fmap PROCESS_NAME simple_process_name

-- | Parse a simple process name
simple_process_name :: AParser st PROCESS_NAME
simple_process_name = cspSortId

channel_name :: AParser st CHANNEL_NAME
channel_name = cspSortId

comm_type :: AParser st COMM_TYPE
comm_type = var

-- List of arguments to a named process
procArgs :: AParser st [TERM ()]
procArgs = optionL $ parenList $ CASL.Formula.term cspKeywords

event_set :: AParser st EVENT_SET
event_set = do
    cts <- comm_type `sepBy` commaT
    return (EventSet cts (getRange cts))

{- Events may be simple CASL terms or channel send/receives or
internal / external prefix choice. -}
event :: AParser st EVENT
event = try chan_recv <|> try chan_nondet_send <|> try chan_send
        <|> try externalPrefixChoice <|> try internalPrefixChoice
        <|> term_event

chan_send :: AParser st EVENT
chan_send = do
    cn <- channel_name
    asKey chan_sendS
    t <- CASL.Formula.term cspKeywords
    return (ChanSend cn t (getRange cn))

chan_nondet_send :: AParser st EVENT
chan_nondet_send = do
    cn <- channel_name
    asKey chan_sendS
    v <- var
    asKey svar_sortS
    s <- cspSortId
    return (ChanNonDetSend cn v s (compRange cn s))

chan_recv :: AParser st EVENT
chan_recv = do
    cn <- channel_name
    asKey chan_receiveS
    v <- var
    asKey svar_sortS
    s <- cspSortId
    return (ChanRecv cn v s (compRange cn s))

internalPrefixChoice :: AParser st EVENT
internalPrefixChoice = do
    ipk <- asKey internal_choiceS
    v <- var
    asKey svar_sortS
    s <- cspSortId
    return (InternalPrefixChoice v s (compRange ipk s))

externalPrefixChoice :: AParser st EVENT
externalPrefixChoice = do
    epk <- asKey external_choiceS
    v <- var
    asKey svar_sortS
    s <- cspSortId
    return (ExternalPrefixChoice v s (compRange epk s))

term_event :: AParser st EVENT
term_event = do
    t <- CASL.Formula.term cspKeywords
    return (TermEvent t (getRange t))

{- Formulas are CASL formulas.  We make our own wrapper around them
however. -}

formula :: AParser st (FORMULA ())
formula = CASL.Formula.formula cspKeywords

{- Primitive renaming is done using an operator name or a predicate
name.  They're both Ids.  Separation between operator or predicate
(or some other non-applicable Id) must be a static analysis
problem. -}

renaming :: AParser st RENAMING
renaming = fmap Renaming $ parseCspId `sepBy` commaT

-- names come from CASL/Hets.

var :: AParser st VAR
var = varId cspKeywords

parseCspId :: AParser st Id
parseCspId = parseId cspKeywords

cspSortId :: AParser st SORT
cspSortId = sortId cspKeywords

-- Composition of ranges

compRange :: (GetRange a, GetRange b) => a -> b -> Range
compRange x y = getRange x `appRange` getRange y

-- * parse the beginning of a process declaration or equation

-- | parse many vars with the same sort
sortedVars :: AParser st [(SORT, Maybe SORT)]
sortedVars = do
    is <- commaSep1 cspSortId
    ms <- optionMaybe $ colonT >> cspSortId
    let res = return $ map (\ i -> (i, ms)) is
    case ms of
      Nothing -> res
      Just _ -> if all isSimpleId is then res else
        fail "expecting only simple vars before colon"

-- | parse variables with possibly different sorts
manySortedVars :: AParser st [(SORT, Maybe SORT)]
manySortedVars = flat $ sepBy1 sortedVars anSemiOrComma

-- | parse a sort or a sorted channel
commType :: AParser st CommType
commType = do
  s <- cspSortId
  do
    colonT
    r <- cspSortId
    return $ CommTypeChan $ TypedChanName s r
   <|> return (CommTypeSort s)

-- | parse a possibly empty list of comm types
commTypeList :: AParser st [CommType]
commTypeList = sepBy commType commaT

-- | parse a possibly empty list of comm types within braces
bracedList :: AParser st [CommType]
bracedList = braces commTypeList

-- | parse a possibly empty set of comm types possibly within braces
alphabet :: AParser st [CommType]
alphabet = bracedList <|> commTypeList

-- | possibly sorted arguments
formalProcArgs :: AParser st [(SORT, Maybe SORT)]
formalProcArgs = optionL $ parens manySortedVars

-- | process name plus formal arguments
procHead :: AParser st (PROCESS_NAME, [(SORT, Maybe SORT)])
procHead = pair simple_process_name formalProcArgs

procTail :: AParser st [CommType]
procTail = colonT >> alphabet

procDecl :: AParser st ((PROCESS_NAME, [(SORT, Maybe SORT)]), [CommType])
procDecl = pair procHead procTail

qualProc :: AParser st FQ_PROCESS_NAME
qualProc = do
    try (oParenT >> asKey processS)
    ((pn, fs), al) <- procDecl
    ss <- if all (isNothing . snd) fs then return $ map fst fs else
       fail "expected simple sort list in qualified process"
    cParenT
    return $ PARSED_FQ_PROCESS_NAME pn ss $ ProcAlphabet al

procDeclOrEq :: AParser st
  (FQ_PROCESS_NAME, [(SORT, Maybe SORT)], Maybe [CommType], Bool)
procDeclOrEq = do
    PARSED_FQ_PROCESS_NAME pn ss (ProcAlphabet al) <- qualProc
    as <- formalProcArgs
    ma <- optionMaybe procTail
    equalT
    return (FQ_PROCESS_NAME pn (ProcProfile ss $ Set.fromList al), as, ma, True)
  <|> do
    (pn, as) <- procHead
    ma <- optionMaybe procTail
    e <- case ma of
           Nothing -> fmap Just equalT
           Just _ -> optionMaybe equalT
    return (PROCESS_NAME pn, as, ma, isJust e)
