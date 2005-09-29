{- |
Module      :  $Header$
Copyright   :  (c)  Daniel Pratsch and Uni Bremen 2002-2003
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  M.Roggenbach@swansea.ac.uk
Stability   :  provisional
Portability :  portable

parser for CSP-CASL

-}

{- todo:

   provide a better name for this module!!!

   equation systems of processes 
   
   spec hugo =
     data ...
     channel ...
     process A = a->A
     process P = ...A...Q...
             Q = ...P....
             R = a->P
     reveal R

reveal R should keep CASL data part, and reveal process R


parameterized processes

process + channel names should be Ids

add line numbers (using Annoted)
-}

module CspCASL.Parse_AS_CSP_CASL where

import Debug.Trace

import CspCASL.AS_CSP_CASL
import CASL.AS_Basic_CASL(OP_NAME)
import CspCASL.CCToken
import CspCASL.CCLexer
import CspCASL.CCKeywords

import Text.ParserCombinators.Parsec

import Common.Id (Token(..))
import Common.Token
import Common.Lexer(separatedBy)
import CASL.Parse_AS_Basic
import CASL.Formula

import Common.AnnoState

----------------------------------------------------------------------------
-- Parsers for CSP-CASL-specifications
----------------------------------------------------------------------------

interim :: AParser st C3PO
interim = try ( do { nc <- namedCspCaslCSpec
                   ; eof
                   ; return (Named_c3po nc)
                   }
              )  
      <|>       do { c  <- cspCaslCSpec
                   ; eof
                   ; return (C3po c)
                   } 

gimbo :: Parser Char
gimbo   = do { char '('
             ; char ')'
             }

namedCspCaslCSpec :: AParser st NAMED_CSP_CASL_C_SPEC
namedCspCaslCSpec = try ( do { ccspecT
                             ; n <- specName
                             ; equalT
                             ; c <- cspCaslCSpec
                             ; return (Named_csp_casl_spec n c)
                             }
                        )
                <|>       do { ccspecT
                             ; n <- specName
                             ; equalT
                             ; c <- cspCaslCSpec
                             ; endT
                             ; return (Named_csp_casl_spec n c)
                             }                       

specName :: AParser st SPEC_NAME
specName = var                    

cspCaslCSpec :: AParser st CSP_CASL_C_SPEC
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

basicCspCaslCSpec :: AParser st Basic_CSP_CASL_C_SPEC
basicCspCaslCSpec = do { c <- channelDecl
                  ; p <- processDefn
                  ; return (Basic_csp_casl_c_spec c p)
                  }

----------------------------------------------------------------------------
-- Parsers for the rest
----------------------------------------------------------------------------
                     
dataDefn :: AParser st DATA_DEFN
dataDefn = do { dataT
              ; d  <- basicSpec csp_casl_keywords
              ; return d
              }

channelDecl :: AParser st CHANNEL_DECL
channelDecl = do { channelT
                 ; (cs, ps) <- channelItem `separatedBy` semicolonT
                 ; return (Channel_items cs)
                 }

channelItem :: AParser st CHANNEL_ITEM
channelItem = do { (ns, ps) <- channelName `separatedBy` commaT
                       ; colonT
                       ; s        <- sortId csp_casl_keywords
                       ; return (Channel_decl ns s)
                 }

              
processDefn :: AParser st PROCESS_DEFN
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

processEquation :: AParser st PROCESS_EQUATION
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

genericEquation :: AParser st GENERIC_EQUATION
genericEquation = do { pn <- processName
                       ; oRBracketT
                           ; vi <- var
                           ; colonT
                           ; es <- eventSet             
                           ; return (Generic pn vi es)
                           -- closing bracket missing!!
                           }


genericNamedProcess :: AParser st GEN_NAMED_PROCESS
genericNamedProcess = do { pn <- processName
                         ; oRBracketT
                               ; t  <- term csp_casl_keywords
                               ; cRBracketT
                               ; return (Generic_named pn t)
                               }
                        
namedProcess :: AParser st NAMED_PROCESS
namedProcess = do { pn <- processName
                  ; return (Named pn)
                  }

-- MiniParser via Umbennung; eventuell Passenderes wählen

processName :: AParser st PROCESS_NAME
processName = var

channelId :: AParser st Token
channelId = var


primProcess :: AParser st PROCESS
primProcess =      do { skipT
                      ; return Skip
                      }
          <|>      do { stopT
                      ; return Stop
                      }
                <|> try (do { ifT
                                  ; f  <- formula csp_casl_keywords
                                  ; thenT
                                  ; p1 <- process
                                  ; elseT
                                  ; p2 <- process
                                  ; return (Conditional_choice f p1 p2)
                                  }
                              )
                <|>      do { ifT
                                  ; f <- formula csp_casl_keywords
                                  ; thenT
                                  ; p <- process
                                  ; return (Conditional_process f p)
                                  }
                <|>      do { whenT                    
                                  ; f <- formula csp_casl_keywords
                                  ; thenT
                                  ; p <- process
                                  ; return (Guarded_command f p)
                                  }
          <|>      do { varT
                      ; v  <- var
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
                       
                       
--              <|> do { f <- formula
--                           ; a <- asKey "&"
--                           ; p <- process
--                           ; return (Guarded f p)
--                 }

--renamedProcess :: AParser st PROCESS
--renamedProcess = try (do { p <- primProcess
--                                   ; oRenamingT
--                                   
--                                   ; cRenamingT
--                                   ; return p
--                                   }
--                               )
--                       <|>      do { p <- primProcess
--                                   ; return p
--                                   } 


seqProcess :: AParser st PROCESS
seqProcess = try ( do { rp <- hidRenProcess 
                      ; semicolonT
                      ; sp <- seqProcess
                      ; return (Sequential [rp, sp])
                      }
                 )
         <|>       do { hrp <- hidRenProcess
                      ; return hrp
                      }  


sortRenaming :: AParser st SORT_RENAMING
sortRenaming = do { (procs, ps) <- opList `separatedBy` commaT
                  ; return (Op_list procs)
                  }

channelRenaming :: AParser st CHANNEL_RENAMING
channelRenaming = do { cn1 <- channelName
                           ; chanRenT
                           ; cn2 <- channelName
                           ; return (Channel_renaming cn1 cn2)
                           } 

hidRenProcess :: AParser st PROCESS
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
          

intChoiceProcess :: AParser st PROCESS
intChoiceProcess = try ( do { sp  <- seqProcess
                            ; intChoiceT
                            ; icp <- intChoiceProcess
                            ; return (Internal_choice [sp, icp])
                            }
                       )
               <|>       do { sp <- seqProcess
                            ; return sp
                            }  
 
extChoiceProcess :: AParser st PROCESS
extChoiceProcess = try ( do { sp  <- seqProcess
                            ; extChoiceT
                            ; ecp <- extChoiceProcess
                            ; return (External_choice [sp, ecp])
                            }
                       )
               <|>       do { sp <- seqProcess
                            ; return sp
                            }                        

choiceProcess :: AParser st PROCESS
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


synParaProcess :: AParser st PROCESS
synParaProcess = try ( do { cp  <- choiceProcess
                          ; synParaT
                          ; spp <- synParaProcess
                          ; return (Synchronous_parallel [cp, spp])
                          }
                     )
             <|>       do { cp <- choiceProcess
                          ; return cp
                          }                   

interParaProcess :: AParser st PROCESS
interParaProcess = try ( do { cp  <- choiceProcess
                            ; interParaT
                            ; ipp <- interParaProcess
                            ; return (Interleaving_parallel [cp, ipp])
                            }
                       )
               <|>       do { cp <- choiceProcess
                            ; return cp
                            }                   

process :: AParser st PROCESS
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


opList :: AParser st OP_NAME
opList = do { pid <- parseId csp_casl_keywords
            ; return pid
                  }

eventSet :: AParser st EVENT_SET
eventSet = do { si <- sortId csp_casl_keywords
                    ; return (Event_set si)
                    }
                    
event :: AParser st EVENT
event = try (do { ci <- channelId
                      ; sendT
                      ; t <- term csp_casl_keywords
                      ; return (Send ci t)
                      }
                  ) 
          <|> try (do { ci <- channelId
                      ; receiveT
                      ; v  <- var
                      ; colonT
                      ; si <- sortId csp_casl_keywords             
                      ; return (Receive ci v si)
                      }
                  )     
          <|>      do { t <- term csp_casl_keywords
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
