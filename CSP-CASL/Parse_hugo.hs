{- 
  File:           HetCATS/CSP-CASL/Parse_AS_CSP_CASL.hs
  Autors:         Daniel Pratsch 
  last modified:  4.11.2002
-}

module Parse_hugo where

import CCKeywords
import AS_CSP_CASL
import CCToken
import CCLexer

import Prelude
import Parsec

import Token
import Lexer
import Parse_AS_Basic
import Formula

cspCaslCSpec :: GenParser Char st CSP_CASL_C_SPEC
cspCaslCSpec =    do { d <- dataDefn
                     ; c <- channelDecl
                     ; p <- processDefn
                     ; return  (Csp_casl_c_spec d c p)
                     }
              <|> do { d <- dataDefn
                     ; c <- channelDecl
                     ; p <- processDefn
                     ; e <- asKey endS
                     ; return  (Csp_casl_c_spec d c p)
                     }
                     
dataDefn :: GenParser Char st DATA_DEFN
dataDefn = do { rd <- asKey dataS
              ; d  <- basicSpec
              ; return d
              }

channelDecl :: GenParser Char st CHANNEL_DECL
channelDecl = do { rc       <- asKey channelS
                 ; (cs, ps) <- channelItem `separatedBy` semiT
                 ; return (Channel_items cs)
                 }

channelItem :: GenParser Char st CHANNEL_ITEM
channelItem = do { (ns, ps) <- channelName `separatedBy` commaT
	               ; c        <- colonT
	               ; s        <- sortId
	               ; return (Channel_decl ns s)
                 }

              
processDefn :: GenParser Char st PROCESS_DEFN
processDefn = do { rp <- asKey processS
                 ; p  <- process
                 ; return (Basic p)
                 }

{-
namedProcess :: GenParser Char st PROCESS
namedProcess = do { pn <- sortId
                  ; return (Named_process pn)
                  }
-}

primProcess :: GenParser Char st PROCESS
primProcess = do { o <- asKey oRBracketS
                 ; p <- process
                 ; c <- asKey cRBracketS
                 ; return p
                 } 
          <|> do { rs <- asKey skipS
                 ; return Skip
                 }
          <|> do { rs <- asKey stopS
                 ; return Stop
                 }
          <|> do { gp <- namedProcess
                 ; o  <- asKey oRBracketS
                 ; t  <- term
                 ; c  <- asKey cRBracketS
                 ; return (Generic_named_process gp t)
                 }   
          <|> do { np <- namedProcess
                 ; return (Named_process np)
                 }                    

process :: GenParser Char st PROCESS
process = do { (procs, ps) <- primProcess `separatedBy` semiT
             ; return (if length procs == 1 then head procs
                                            else Sequential procs)
             }
      <|> do { (procs, ps) <- primProcess `separatedBy` extChoiceT
             ; return (if length procs == 1 then head procs
                                            else External_choice procs)
             }
      <|> do { (procs, ps) <- primProcess `separatedBy` intChoiceT
             ; return (if length procs == 1 then head procs
                                            else Internal_choice procs)

             }
