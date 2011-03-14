{- |
Module      :  $Id$
Description :  Parser for CspCASL processes
Copyright   :  (c)
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  a.m.gimblett@swan.ac.uk
Stability   :  experimental
Portability :

Parser for CSP-CASL processes.

-}

module CspCASL.Parse_CspCASL_Process (
    channel_name,
    comm_type,
    csp_casl_sort,
    csp_casl_process,
    event_set,
    process_name,
    simple_process_name,
    procNameWithParamsAndComms,
    var,
) where

import Text.ParserCombinators.Parsec (option, sepBy, try, (<|>), (<?>))

import CASL.AS_Basic_CASL (FORMULA, SORT, TERM, VAR)
import qualified CASL.Formula
import Common.AnnoState (AParser, asKey, colonT)
import Common.Id
import Common.Keywords
import Common.Lexer (commaSep1, commaT, cParenT, oParenT)
import Common.Parsec ((<<))
import Common.Token (parseId, sortId, varId)

import CspCASL.AS_CspCASL_Process
import CspCASL.CspCASL_Keywords

csp_casl_process :: AParser st PROCESS
csp_casl_process = cond_proc <|> par_proc

cond_proc :: AParser st PROCESS
cond_proc = do ift <- asKey ifS
               f <- formula
               asKey thenS
               p <- csp_casl_process
               asKey elseS
               q <- csp_casl_process
               return (ConditionalProcess f p q (compRange ift q))

par_proc :: AParser st PROCESS
par_proc = choice_proc >>= par_proc'

par_proc' :: PROCESS -> AParser st PROCESS
par_proc' lp =
    do     asKey interleavingS
           rp <- choice_proc
           par_proc' (Interleaving lp rp (compRange lp rp))
    <|> do asKey synchronousS
           rp <- choice_proc
           par_proc' (SynchronousParallel lp rp (compRange lp rp))
    <|> do asKey genpar_openS
           es <- event_set <?> "communication type"
           asKey genpar_closeS
           rp <- choice_proc
           par_proc' (GeneralisedParallel lp es rp (compRange lp rp))
    <|> do asKey alpar_openS
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
choice_proc' lp =
    do     asKey external_choiceS
           rp <- seq_proc
           choice_proc' (ExternalChoice lp rp (compRange lp rp))
    <|> do asKey internal_choiceS
           rp <- seq_proc
           choice_proc' (InternalChoice lp rp (compRange lp rp))
    <|> return lp

seq_proc :: AParser st PROCESS
seq_proc = pref_proc >>= seq_proc'

seq_proc' :: PROCESS -> AParser st PROCESS
seq_proc' lp = do  asKey sequentialS
                   rp <- pref_proc
                   seq_proc' (Sequential lp rp (compRange lp rp))
               <|> return lp

pref_proc :: AParser st PROCESS
pref_proc = do e <- try (event << asKey prefix_procS)
               p <- pref_proc
               return (PrefixProcess e p (compRange e p))
            <|> hid_ren_proc

hid_ren_proc :: AParser st PROCESS
hid_ren_proc = prim_proc >>= hid_ren_proc'

hid_ren_proc' :: PROCESS -> AParser st PROCESS
hid_ren_proc' lp =
    do     asKey hiding_procS
           es <- event_set
           hid_ren_proc' (Hiding lp es (compRange lp es))
    <|> do asKey ren_proc_openS
           rn <- renaming
           ck <- asKey ren_proc_closeS
           hid_ren_proc' (RenamingProcess lp rn (compRange lp ck))
    <|> return lp

prim_proc :: AParser st PROCESS
prim_proc = do     pn <- process_name
                   args <- procArgs
                   return (NamedProcess pn args (compRange pn args))
            <|> do oParenT
                   p <- csp_casl_process
                   cParenT
                   return p
            <|> do rk <- asKey runS
                   oParenT
                   es <- event_set
                   cp <- cParenT
                   return (Run es (compRange rk cp))
            <|> do ck <- asKey chaosS
                   oParenT
                   es <- event_set
                   cp <- cParenT
                   return (Chaos es (compRange ck cp))
            <|> do dk <- asKey divS
                   return (Div (getRange dk))
            <|> do sk <- asKey stopS
                   return (Stop (getRange sk))
            <|> do sk <- asKey skipS
                   return (Skip (getRange sk))

-- | Parse a process name which can be a simple one or a fully qualified one.
process_name :: AParser st FQ_PROCESS_NAME
process_name =  try fq_process_name
                <|> do pn <- simple_process_name
                       return $ PROCESS_NAME pn

-- | Parse a simple process name
simple_process_name :: AParser st SIMPLE_PROCESS_NAME
simple_process_name = varId csp_casl_keywords

-- | Parse a fully qualified process name
fq_process_name :: AParser st FQ_PROCESS_NAME
fq_process_name = do
  oParenT
  asKey processS
  (pn, params, comms) <- procNameWithParamsAndComms
  cParenT
  return $ PARSED_FQ_PROCESS_NAME pn params comms

-- | Parse a process name with parameter sorts and communications set (no semi
-- colon) e.g., 'P(S,T): S,T'. This is more to reconise a declaration or fully
-- qualified process. This is not to recongnise the actual parameter terms.
procNameWithParamsAndComms :: AParser st
                              (SIMPLE_PROCESS_NAME, PROC_ARGS, PROC_ALPHABET)
procNameWithParamsAndComms = do
  pn <- simple_process_name
  parms <- option [] $ do try oParenT
                          parms <- commaSep1 csp_casl_sort
                          cParenT
                          return parms
  colonT
  cts <- (comm_type `sepBy` commaT)
  return $ (pn, parms, ProcAlphabet cts (getRange cts))


channel_name :: AParser st CHANNEL_NAME
channel_name = varId csp_casl_keywords

comm_type :: AParser st COMM_TYPE
comm_type = varId csp_casl_keywords

-- List of arguments to a named process
procArgs :: AParser st [(TERM ())]
procArgs = do oParenT
              es <- commaSep1 (CASL.Formula.term csp_casl_keywords)
              cParenT
              return es
           <|> return []

-- Sort IDs, excluding CspCasl keywords
csp_casl_sort :: AParser st SORT
csp_casl_sort = sortId csp_casl_keywords

event_set :: AParser st EVENT_SET
event_set = do cts <- comm_type `sepBy` commaT
               return (EventSet cts (getRange cts))

-- Events may be simple CASL terms or channel send/receives or
-- internal / external prefix choice.
event :: AParser st EVENT
event = try chan_recv <|> try chan_nondet_send <|> try chan_send
        <|> try externalPrefixChoice <|> try internalPrefixChoice
        <|> term_event

chan_send :: AParser st EVENT
chan_send = do cn <- channel_name
               asKey chan_sendS
               t <- CASL.Formula.term csp_casl_keywords
               return (ChanSend cn t (getRange cn))

chan_nondet_send :: AParser st EVENT
chan_nondet_send = do cn <- channel_name
                      asKey chan_sendS
                      v <- var
                      asKey svar_sortS
                      s <- csp_casl_sort
                      return (ChanNonDetSend cn v s (compRange cn s))

chan_recv :: AParser st EVENT
chan_recv = do cn <- channel_name
               asKey chan_receiveS
               v <- var
               asKey svar_sortS
               s <- csp_casl_sort
               return (ChanRecv cn v s (compRange cn s))

internalPrefixChoice :: AParser st EVENT
internalPrefixChoice = do ipk <- asKey internal_choiceS
                          v <- var
                          asKey svar_sortS
                          s <- csp_casl_sort
                          return (InternalPrefixChoice v s (compRange ipk s))

externalPrefixChoice :: AParser st EVENT
externalPrefixChoice =  do epk <- asKey external_choiceS
                           v <- var
                           asKey svar_sortS
                           s <- csp_casl_sort
                           return (ExternalPrefixChoice v s (compRange epk s))

term_event :: AParser st EVENT
term_event = do t <- CASL.Formula.term csp_casl_keywords
                return (TermEvent t (getRange t))

-- Formulas are CASL formulas.  We make our own wrapper around them
-- however.

formula :: AParser st (FORMULA ())
formula = CASL.Formula.formula csp_casl_keywords

-- Primitive renaming is done using an operator name or a predicate
-- name.  They're both Ids.  Separation between operator or predicate
-- (or some other non-applicable Id) must be a static analysis
-- problem.

renaming :: AParser st RENAMING
renaming =  fmap Renaming $ parseId csp_casl_keywords `sepBy` commaT

-- Variables come from CASL/Hets.

var :: AParser st VAR
var = varId csp_casl_keywords

-- Composition of ranges

compRange :: (GetRange a, GetRange b) => a -> b -> Range
compRange x y = getRange x `appRange` getRange y
