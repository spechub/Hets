{- **********************************************************************

   $Source$

   $Date$
   $Revision$
   Author: Daniel Pratsch (Last modification by $Author$)

  ************************************************************************** 
-}


module CspCASL.Parse_hugo where

--import CspCASL.CCKeywords

import CspCASL.AS_CSP_CASL
import CASL.AS_Basic_CASL(OP_NAME)
import CspCASL.CCToken
import CspCASL.CCLexer

import Common.Lib.Parsec

import Common.Id (Token(..))
import Common.Token
import Common.Lexer(separatedBy)
import CASL.Parse_AS_Basic
import CASL.Formula

import Common.AnnoState

----------------------------------------------------------------------------
-- Parsers for CSP-CASL-specifications
----------------------------------------------------------------------------
interim :: AParser C3PO
interim = try ( do { nc <- namedCspCaslCSpec
                   ; return (Named_c3po nc)
                   }
              )  
      <|>       do { c  <- cspCaslCSpec
                   ; return (C3po c)
                   } 

namedCspCaslCSpec :: AParser NAMED_CSP_CASL_C_SPEC
namedCspCaslCSpec = try ( do { ccspecT
                             ; oRBracketT
                             ; n <- specName
                             ; cRBracketT
                             ; equalT
                             ; c <- cspCaslCSpec
                             ; return (Named_csp_casl_spec n c)
                             }
                        )
                <|>       do { ccspecT
                             ; oRBracketT
                             ; n <- specName
                             ; cRBracketT
                             ; equalT
                             ; c <- cspCaslCSpec
                             ; endT
                             ; return (Named_csp_casl_spec n c)
                             }                       

specName :: AParser SPEC_NAME
specName = varId                     

cspCaslCSpec :: AParser CSP_CASL_C_SPEC
cspCaslCSpec = do { d <- dataDefn
                  ; c <- channelDecl
                  ; p <- processDefn
                  ; return  (Csp_casl_c_spec d c p)
                  }
           <|> do { d <- dataDefn
                  ; c <- channelDecl
                  ; p <- processDefn
                  ; endT
                  ; return  (Csp_casl_c_spec d c p)
                  }

----------------------------------------------------------------------------
-- Parsers for the rest
----------------------------------------------------------------------------
                     
dataDefn :: AParser DATA_DEFN
dataDefn = do { dataT
              ; d  <- basicSpec
              ; return d
              }

channelDecl :: AParser CHANNEL_DECL
channelDecl = do { channelT
                 ; (cs, ps) <- channelItem `separatedBy` semicolonT
                 ; return (Channel_items cs)
                 }

channelItem :: AParser CHANNEL_ITEM
channelItem = do { (ns, ps) <- channelName `separatedBy` commaT
	               ; colonT
	               ; s        <- sortId
	               ; return (Channel_decl ns s)
                 }

              
processDefn :: AParser PROCESS_DEFN
processDefn = try ( do { processT
                       ; letT
                       ; oSBracketT
                       ; (pe, ps) <- processEquation `separatedBy` semicolonT
                       ; cSBracketT
                       ; inT
                       ; np       <- namedProcess
                       ; return (Recursive pe np)
                       }
                  )
          <|> try ( do { processT
                       ; letT
                       ; oSBracketT                       
                       ; (pe, ps) <- processEquation `separatedBy` semicolonT
                       ; cSBracketT                       
                       ; inT
                       ; gnp      <- genericNamedProcess
                       ; return (Generic_recursive pe gnp)
                       }
                  )                  
          <|>       do { processT
                       ; p  <- process
                       ; return (Basic p)
                       }

processEquation :: AParser PROCESS_EQUATION
processEquation = try ( do { np <- namedProcess
                           ; equalT
                           ; p  <- process
                           ; return (Equation np p)
                           }
                      )
              <|>       do { ge <- genericEquation
                           ; equalT
                           ; p <- process
                           ; return (Generic_equation ge p)
                           } 

genericEquation :: AParser GENERIC_EQUATION
genericEquation = do { pn <- processName
     	               ; oRBracketT
	                   ; vi <- varId
	                   ; colonT
	                   ; es <- eventSet             
	                   ; return (Generic pn vi es)
	                   }


genericNamedProcess :: AParser GEN_NAMED_PROCESS
genericNamedProcess = do { pn <- processName
                         ; oRBracketT
	                       ; t  <- term
	                       ; cRBracketT
	                       ; return (Generic_named pn t)
	                       }
	                
namedProcess :: AParser NAMED_PROCESS
namedProcess = do { pn <- processName
                  ; return (Named pn)
                  }

-- MiniParser via Umbennung; eventuell Passenderes wählen

processName :: AParser PROCESS_NAME
processName = varId

channelId :: AParser Token
channelId = varId


primProcess :: AParser PROCESS
primProcess =      do { skipT
                      ; return Skip
                      }
          <|>      do { stopT
                      ; return Stop
                      }
	        <|> try (do { ifT
		                  ; f  <- formula
		                  ; thenT
		                  ; p1 <- process
		                  ; elseT
		                  ; p2 <- process
		                  ; return (Conditional_choice f p1 p2)
		                  }
		              )
	        <|>      do { ifT
		                  ; f <- formula
		                  ; thenT
		                  ; p <- process
		                  ; return (Conditional_process f p)
		                  }
	        <|>      do { whenT                    
		                  ; f <- formula
		                  ; thenT
		                  ; p <- process
		                  ; return (Guarded_command f p)
		                  }
      	  <|>      do { varT
      	              ; v  <- varId
		                  ; colonT                  -- ':'
		                  ; es <- eventSet
		                  ; multiPreT               -- '->'
		                  ; p  <- hidRenProcess
		                  ; return (Multiple_prefix v es p)
		              }
	        <|> try ( do { e <- event
         	             ; prefixT 
	                     ; p <- hidRenProcess
	                     ; return (Prefix e p)
	                     }
	                )
	        <|>       do { oRBracketT
                       ; p <- process
                       ; cRBracketT
                       ; return p
                       } 
	        <|> try ( do { gnp <- genericNamedProcess 
	                     ; return (Generic_named_process gnp)
	                     }
	                )
          <|>       do { np <- namedProcess
                       ; return (Named_process np)
                       }
                       
                       
--	        <|> do { f <- formula
--		             ; a <- asKey "&"
--		             ; p <- process
--		             ; return (Guarded f p)
--                 }

--renamedProcess :: AParser PROCESS
--renamedProcess = try (do { p <- primProcess
--		                     ; oRenamingT
--		                     
--		                     ; cRenamingT
--		                     ; return p
--		                     }
--		                 )
--		         <|>      do { p <- primProcess
--		                     ; return p
--		                     } 


seqProcess :: AParser PROCESS
seqProcess = try ( do { rp <- hidRenProcess 
                      ; semicolonT
                      ; sp <- seqProcess
                      ; return (Sequential [rp, sp])
                      }
                 )
         <|>       do { hrp <- hidRenProcess
                      ; return hrp
                      }  


sortRenaming :: AParser SORT_RENAMING
sortRenaming = do { (procs, ps) <- opList `separatedBy` commaT
                  ; return (Op_list procs)
                  }

channelRenaming :: AParser CHANNEL_RENAMING
channelRenaming = do { cn1 <- channelName
	                   ; chanRenT
	                   ; cn2 <- channelName
	                   ; return (Channel_renaming cn1 cn2)
	                   } 

hidRenProcess :: AParser PROCESS
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
	                       ; return (Csp_sort_renaming pp sr)
	                       }
	                  )
            <|> try ( do { pp <- primProcess
                         ; oRenamingT
	                       ; sr <- channelRenaming
                         ; cRenamingT
	                       ; return (Csp_channel_renaming pp sr)
	                       }
	                  )	                  
            <|>       do { pp <- primProcess
                         ; return pp
                         }             
          

intChoiceProcess :: AParser PROCESS
intChoiceProcess = try ( do { sp  <- seqProcess
                            ; intChoiceT
                            ; icp <- intChoiceProcess
                            ; return (Internal_choice [sp, icp])
                            }
                       )
               <|>       do { sp <- seqProcess
                            ; return sp
                            }  
 
extChoiceProcess :: AParser PROCESS
extChoiceProcess = try ( do { sp  <- seqProcess
                            ; extChoiceT
                            ; ecp <- extChoiceProcess
                            ; return (External_choice [sp, ecp])
                            }
                       )
               <|>       do { sp <- seqProcess
                            ; return sp
                            }                        

choiceProcess :: AParser PROCESS
choiceProcess = try ( do { sp  <- seqProcess 
                         ; extChoiceT
                         ; ecp <- extChoiceProcess 
                         ; return (External_choice [sp, ecp])
                         }
                    )
            <|> try ( do { sp  <- seqProcess 
                         ; intChoiceT
                         ; icp <- intChoiceProcess 
                         ; return (Internal_choice [sp, icp])
                         }
                    )
            <|>       do { sp <- seqProcess
                         ; return sp
                         }           


synParaProcess :: AParser PROCESS
synParaProcess = try ( do { cp  <- choiceProcess
                          ; synParaT
                          ; spp <- synParaProcess
                          ; return (Synchronous_parallel [cp, spp])
                          }
                     )
             <|>       do { cp <- choiceProcess
                          ; return cp
                          }                   

interParaProcess :: AParser PROCESS
interParaProcess = try ( do { cp  <- choiceProcess
                            ; interParaT
                            ; ipp <- interParaProcess
                            ; return (Interleaving_parallel [cp, ipp])
                            }
                       )
               <|>       do { cp <- choiceProcess
                            ; return cp
                            }                   

process :: AParser PROCESS
process = try ( do { cp  <- choiceProcess
                   ; synParaT
                   ; spp <- synParaProcess
                   ; return (Synchronous_parallel [cp, spp])
                   }
	            )
      <|> try ( do { cp  <- choiceProcess 
                   ; interParaT
                   ; ipp <- interParaProcess
                   ; return (Interleaving_parallel [cp, ipp])
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
      <|> try ( do { cp1 <- choiceProcess
                   ; oAlPaT
	                 ; es  <- eventSet
	                 ; cAlPaT
	                 ; cp2 <- choiceProcess
	                 ; return (Alphabet_parallel cp1 es cp2)
	                 }
	            )	            	                         	            
      <|>       do { ch <- choiceProcess
                   ; return ch
                   } 


opList :: AParser OP_NAME
opList = do { pid <- parseId
            ; return pid
	          }

eventSet :: AParser EVENT_SET
eventSet = do { si <- sortId
	            ; return (Event_set si)
	            }
	            
event :: AParser EVENT
event = try (do { ci <- channelId
	              ; sendT
	              ; t <- term
	              ; return (Send ci t)
	              }
	          ) 
	  <|> try (do { ci <- channelId
	              ; receiveT
	              ; v  <- varId
	              ; colonT
	              ; si <- sortId              
	              ; return (Receive ci v si)
	              }
	          )     
	  <|>      do { t <- term
	              ; return (Term t)
	              }



{-
namedProcess :: GenParser Char st PROCESS
namedProcess = do { pn <- sortId
                  ; return (Named_process pn)
                  }


      <|> try ( do { (procs, ps) <- choiceProcess `separatedBy` interParaT
                   ; return (if length procs == 1 then head procs
                                                  else Interleaving_parallel procs)
                   }
	            )

-}
