{- **********************************************************************

   $Source$

   $Date$
   $Revision$
   Author: Daniel Pratsch (Last modification by $Author$)

  ************************************************************************** 
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
import AS_Basic_CASL

processId = varId
channelId = varId

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
	  <|> do asKey "if"
		 f <- formula
		 asKey "then"
		 p1 <- process
		 asKey "else"
		 p2 <- process
		 return $ Process_conditional f p1 p2
	  <|> do asKey "[]"
		 v <- varId
		 colonT
		 s <- sortId
		 asKey "->"
		 p <- renamedProcess
		 return $ Multiple_prefix v s p
	  <|> do tryEvent
	  <|> do tryNamedProcess
	  <|> do f <- formula
		 do a <- asKey "&"
		    p <- process
		    return (Guarded f p)
 
tryNamedProcess = try $ 
    do i <- processId
       do oParenT
	  t <- term
	  cParenT
	  return (Generic_named_process i t)
         <|> return (Named_process i)


event = sendEvent -- <|> receiveEvent <|> primEvent

tryEvent = do e <- try event
	      asKey "->" 
	      p <- renamedProcess
	      return $ Prefix e p

sendEvent = do i <- channelId
	       asKey "!"
	       t <- term
	       return (Send i t)

renamedProcess = do p <- primProcess
		    do asKey "[["
		       asKey "]]"
		       return p
		      <|> return p 

 
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
