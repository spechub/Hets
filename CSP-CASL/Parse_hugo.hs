{- **********************************************************************

   $Source$

   $Date$
   $Revision$
   Author: Daniel Pratsch (Last modification by $Author$)

  ************************************************************************** 
-}

{-

dies ist ein ueberfluessiger Kommentar

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


-- MiniParser via Umbennung; eventuell Passenderes wählen
processId = varId
channelId = varId


primProcess :: GenParser Char st PROCESS
primProcess =      do { rs <- asKey skipS
                      ; return Skip
                      }
          <|>      do { rs <- asKey stopS
                      ; return Stop
                      }
	        <|> try (do { asKey "if"
		                  ; f <- formula
		                  ; asKey "then"
		                  ; p1 <- process
		                  ; asKey "else"
		                  ; p2 <- process
		                  ; return (Conditional f p1 p2)
		                  }
		              )
	        <|>      do { asKey "if"
		                  ; f <- formula
		                  ; asKey "then"
		                  ; p1 <- process
		              --    ; asKey "else"
		              --    ; p2 <- process
		                  ; return (Conditional f p1 p2)
		                  }
	        <|>      do { asKey "when"                    --else?
		                  ; f <- formula
		                  ; asKey "then"
		                  ; p1 <- process
		              --    ; asKey "else"
		              --    ; p2 <- process
		                  ; return (Guarded_command f p1)
		                  }
      	  <|>      do { asKey "var"
		                  ; v  <- varId
		                  ; colonT
		                  ; es <- eventSet
		                  ; asKey "->"
		                  ; p  <- renamedProcess
		                  ; return (Multiple_prefix v es p)
		              }
	        <|> try ( do { e <- event
         	             ; asKey "->" 
	                     ; p <- renamedProcess
	                     ; return (Prefix e p)
	                     }
	                )
	        <|>       do { o <- asKey oRBracketS
                       ; p <- process
                       ; c <- asKey cRBracketS
                       ; return p
                       } 
	        <|> try ( do { i <- processId
                       ; oParenT
	                     ; t <- term
	                     ; cParenT
	                     ; return (Generic_named_process i t)
	                     }
	                )
          <|>       do { i <- processId
                       ; return (Named_process i)
                       }
                       
                       
--	        <|> do { f <- formula
--		             ; a <- asKey "&"
--		             ; p <- process
--		             ; return (Guarded f p)
--                 }

renamedProcess :: GenParser Char st PROCESS
renamedProcess = try (do { p <- primProcess
		                     ; asKey "[["
		                     ; asKey "]]"
		                     ; return p
		                     }
		                 )
		         <|>      do { p <- primProcess
		                     ; return p
		                     } 

seqProcess :: GenParser Char st PROCESS
seqProcess = try ( do { rp <- hidRenProcess 
                      ; semiT
                      ; sp <- seqProcess
                      ; return (Sequential rp sp)
                      }
                 )
         <|>       do { hrp <- hidRenProcess
                      ; return hrp
                      }  

eventSet :: GenParser Char st EVENT_SET
eventSet = do { si <- sortId
	            ; return (ESort si)
	            }

	            
event :: GenParser Char st EVENT
event = try (do { ci <- channelId
	              ; asKey "!"
	              ; t <- term
	              ; return (Send ci t)
	              }
	          ) 
	  <|> try (do { ci <- channelId
	              ; asKey "?"
	              ; v  <- varId
	              ; colonT
	              ; si <- sortId              
	              ; return (Receive ci v si)
	              }
	          )     
	  <|>      do { t <- term
	              ; return (Term t)
	              }


sortRenaming :: GenParser Char st SORT_RENAMING
sortRenaming = do { (procs, ps) <- opList `separatedBy` asKey ","
                      ; return (if length procs == 1 then head procs
                                                     else Op_list procs)
                  }


opList :: GenParser Char st SORT_RENAMING
opList = do { si <- parseId
            ; return si
	          }


channelRenaming :: GenParser Char st CHANNEL_RENAMING
channelRenaming = do { cn1 <- channelName
	                   ; asKey "<-"
	                   ; cn2 <- channelName
	                   ; return (Channel_renaming cn1 cn2)
	                   } 


hidRenProcess :: GenParser Char st PROCESS
hidRenProcess = try ( do { pp <- primProcess
                         ; hidingT
	                       ; es  <- eventSet
      	                 ; return (Hiding pp es)
	                       }
	                  )
            <|> try ( do { pp <- primProcess
                         ; oRenamingT
	                       ; sr <- sortRenaming
                         ; cRenamingT
	                       ; return (Renaming pp sr)
	                       }
	                  )
            <|>       do { pp <- primProcess
                         ; return pp
                         }             
          
 
         
                 

choiceProcess :: GenParser Char st PROCESS
choiceProcess = try ( do { (procs, ps) <- seqProcess `separatedBy` extChoiceT
                         ; return (if length procs == 1 then head procs
                                                        else External_choice procs)
                         }
                    )
            <|> try ( do { (procs, ps) <- seqProcess `separatedBy` intChoiceT
                         ; return (if length procs == 1 then head procs
                                                        else Internal_choice procs)
                         }
                    )
            <|>       do { sp <- seqProcess
                         ; return sp
                         }           


process :: GenParser Char st PROCESS
process = try ( do { cp1 <- choiceProcess
                   ; oAlPaT
	                 ; es  <- eventSet
	                 ; cAlPaT
	                 ; cp2 <- choiceProcess
	                 ; return (Alphabet_parallel cp1 es cp2)
	                 }
	            )
      <|> try ( do { cp1 <- choiceProcess
                   ; oGenPaT
	                 ; es1 <- eventSet
                   ; mGenPaT
	                 ; es2 <- eventSet	                 
	                 ; cGenPaT
	                 ; cp2 <- choiceProcess
	                 ; return (General_parallel cp1 es1 es2 cp2)
	                 }
	            )
      <|> try ( do { (procs, ps) <- choiceProcess `separatedBy` synParaT
                   ; return (if length procs == 1 then head procs
                                                  else Synchronous_parallel procs)
                   }
	            )
      <|> try ( do { (procs, ps) <- choiceProcess `separatedBy` interParaT
                   ; return (if length procs == 1 then head procs
                                                  else Interleaving_parallel procs)
                   }
	            )           	            	            
      <|>       do { ch <- choiceProcess
                   ; return ch
                   } 


{-
namedProcess :: GenParser Char st PROCESS
namedProcess = do { pn <- sortId
                  ; return (Named_process pn)
                  }
-}