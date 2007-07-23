{- |
Module      :  $Id$
Copyright   :  (c) 
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  a.m.gimblett@swan.ac.uk
Stability   :  experimental
Portability :  

Parser for CSP-CASL processes.

-}

module CspCASL.Parse_CspCASL_Process (
    csp_casl_process,
    process_name,
    recProcess,
    recProcessDefn,
) where

import Text.ParserCombinators.Parsec (sepBy, try, (<|>), chainl1)

import qualified CASL.Formula
import CASL.AS_Basic_CASL (VAR)
import Common.AnnoState (AParser, asKey)
import Common.Id (equalS)
import Common.Keywords (colonS, ifS, inS, letS, thenS, elseS)
import Common.Lexer (semiT)
import Common.Token (colonST, parseId, sortId, varId)

import CspCASL.AS_CspCASL_Process
import CspCASL.CspCASL_Keywords

-- Processes

csp_casl_process :: AParser st PROCESS
csp_casl_process = do p <- process
                      return p

-- Recursive processes
recProcess :: AParser st REC_PROCESS
recProcess = do asKey letS
                rds <- recProcessDefn `sepBy` semiT
                (try semiT)
                asKey inS
                p <- process
                return (RecProcessConstructor rds p)

-- Recursive process definitions
recProcessDefn :: AParser st REC_PROCESS_DEFN
recProcessDefn = try (do pn <- process_name
                         asKey parens_openS
                         (v, es) <- varEventSet
                         asKey parens_closeS
                         asKey equalS
                         p <- process
                         return (RecProcessVar pn v es p)
                      )
                 <|> (do pn <- process_name
                         asKey equalS
                         p <- process
                         return (RecProcessSimple pn p)
                      )

varEventSet :: AParser st (VAR, EVENT_SET)
varEventSet = do v <- var
                 asKey colonS
                 es <- event_set
                 return (v, es)

-- Process names

process_name :: AParser st PROCESS_NAME
process_name = do p_name <- parseId csp_casl_keywords
                  return p_name

-- PROCESS => PARALLEL_PROCESS
process :: AParser st PROCESS
process = conditional_process <|> parallel_process

conditional_process :: AParser st PROCESS
conditional_process = do try (asKey ifS)
                         f <- formula
                         asKey thenS
                         p <- process
                         asKey elseS
                         q <- process
                         return (ConditionalProcess f p q)



-- PARALLEL_PROCESS =>   CHOICE_PROCESS
--                     | PARALLEL_PROCESS || CHOICE_PROCESS
--                     | PARALLEL_PROCESS ||| CHOICE_PROCESS
parallel_process :: AParser st PROCESS
parallel_process = complex_parallel `chainl1` parallel_operator

parallel_operator :: AParser st (PROCESS -> PROCESS -> PROCESS)
parallel_operator = try (do asKey interleavingS
                            return interleaving
                        )
                    <|>
                    try (do asKey synchronousS
                            return synchronous
                        )

synchronous :: PROCESS -> PROCESS -> PROCESS
synchronous left right = SynchronousParallel left right

interleaving :: PROCESS -> PROCESS -> PROCESS
interleaving left right = Interleaving left right

complex_parallel :: AParser st PROCESS
complex_parallel = try (do p <- choice_process
                           asKey general_parallel_openS
                           es <- event_set
                           asKey general_parallel_closeS
                           q <- parallel_process
                           return (GeneralisedParallel p es q)
                       )
                   <|>
                   try (do p <- choice_process
                           asKey alpha_parallel_openS
                           es_p <- event_set
                           asKey alpha_parallel_sepS
                           es_q <- event_set
                           asKey alpha_parallel_closeS
                           q <- parallel_process
                           return (AlphabetisedParallel p es_p es_q q)
                       )
                   <|>
                   choice_process


-- CHOICE_PROCESS =>   PREFIX_SEQUENCE_PROCESS
--                   | CHOICE_PROCESS [] PREFIX_SEQUENCE_PROCESS
--                   | CHOICE_PROCESS |~| PREFIX_SEQUENCE_PROCESS
choice_process :: AParser st PROCESS
choice_process = sequence_process `chainl1` choice_operator

choice_operator :: AParser st (PROCESS -> PROCESS -> PROCESS)
choice_operator = try (do asKey external_choiceS
                          return external
                      )
                  <|>
                  try (do asKey internal_choiceS
                          return internal
                      )

external :: PROCESS -> PROCESS -> PROCESS
external left right = ExternalChoice left right

internal :: PROCESS -> PROCESS -> PROCESS
internal left right = InternalChoice left right

-- SEQUENCE_PROCESS =>   PREFIX_PROCESS
--                     | SEQUENCE_PROCESS ; PREFIX_PROCESS
sequence_process :: AParser st PROCESS
sequence_process = prefix_process `chainl1` sequence_operator

sequence_operator :: AParser st (PROCESS -> PROCESS -> PROCESS)
sequence_operator = try (do asKey semicolonS
                            return sequencing
                        )

sequencing :: PROCESS -> PROCESS -> PROCESS
sequencing left right = Sequential left right

-- PREFIX_PROCESS =>   [] VAR: EVENT-SET -> HIDING_RENAMING_PROCESS
--                   | EVENT -> HIDING_RENAMING_PROCESS
--                   | HIDING_RENAMING_PROCESS
prefix_process :: AParser st PROCESS
prefix_process = try (do asKey external_prefixS
                         v <- var
                         colonST
                         es <- event_set
                         asKey prefixS
                         p <- sequence_process
                         return (ExternalPrefixProcess v es p)
                     )
                 <|>
                 try (do asKey internal_prefixS
                         v <- var
                         colonST
                         es <- event_set
                         asKey prefixS
                         p <- sequence_process
                         return (InternalPrefixProcess v es p)
                     )
                 <|>
                 try (do e <- event
                         asKey prefixS
                         p <- sequence_process
                         return (PrefixProcess e p)
                     )
                 <|>
                 hiding_renaming_process

-- HIDING_RENAMING_PROCESS => PRIMTIVE_PROCESS HIDING_RENAMING_W
--
-- HIDING_RENAMING_W =>   \ EVENT-SET
--                      | [[CSP-RENAMING]]
--                      | epsilon

hiding_renaming_process :: AParser st PROCESS
hiding_renaming_process = do pl <- parenthesised_or_primitive_process
                             p <- (hiding_renaming_w pl)
                             return p

hiding_renaming_w :: PROCESS -> AParser st PROCESS
hiding_renaming_w pl = try (do asKey hidingS
                               es <- event_set
                               p <- (hiding_renaming_w (Hiding pl es))
                               return p)
                       <|>
                       try (do asKey renaming_openS
                               rn <- primitive_renaming
                               asKey renaming_closeS
                               p <- (hiding_renaming_w (Renaming pl rn))
                               return p)
                       <|> (return pl)


-- PARENTHESISED_OR_PRIMITIVE_PROCESS =>   (PROCESS)
--                                       | RUN EventSet
--                                       | Chaos EventSet
--                                       | div
--                                       | SKIP
--                                       | STOP
parenthesised_or_primitive_process :: AParser st PROCESS
parenthesised_or_primitive_process = do asKey parens_openS
                                        p <- process
                                        asKey parens_closeS
                                        return p
                                     <|>
                                     primitive_process

primitive_process :: AParser st PROCESS
primitive_process = try run <|> try chaos <|> try divergence <|> try skip <|> stop



-- Hard-coded primitive processes.

run :: AParser st PROCESS
run = do asKey runS
         es <- event_set
         return (Run es)
        
chaos :: AParser st PROCESS
chaos = do asKey chaosS
           es <- event_set
           return (Chaos es)
        
-- Can't just call this "div" because that clashes with div from the
-- Prelude.
divergence :: AParser st PROCESS
divergence = do asKey divS
                return Div

skip :: AParser st PROCESS
skip = do asKey skipS
          return Skip
        
stop :: AParser st PROCESS
stop = do asKey stopS
          return Stop



-- Event sets are just CASL sorts...

event_set :: AParser st EVENT_SET
event_set = do sort_id <- sortId csp_casl_keywords
               return (EventSet sort_id)

-- Events are CASL terms, but will (later) include stuff to with
-- channels.

event :: AParser st EVENT
event = do t <- CASL.Formula.term csp_casl_keywords
           return (Event t)

-- Formulas are CASL formulas.  We make our own wrapper around them
-- however.

formula :: AParser st CSP_FORMULA
formula = do f <- CASL.Formula.formula csp_casl_keywords
             return (Formula f)

-- Primitive renaming is done using an operator name or a predicate
-- name.  They're both Ids.  Separation between operator or predicate
-- (or some other non-applicable Id) must be a static analysis
-- problem.

primitive_renaming :: AParser st PRIMITIVE_RENAMING
primitive_renaming = do { rid <- parseId csp_casl_keywords
                        ; return rid
                        }

-- Variables come from CASL/Hets.

var :: AParser st VAR
var = varId csp_casl_keywords



