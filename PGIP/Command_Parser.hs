{- |
Module      :$Header$
Copyright   :
Licence     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@iu-bremen.de
Stability   : provisional
Portability : portable

Parsing the comand line script
-} 


module PGIP.Command_Parser where

import Text.ParserCombinators.Parsec
--import Common.Token
--import Common.Lexer
import Syntax.AS_Library
import Syntax.Parse_AS_Library
--data ID= 
--   Name String
-- deriving (Eq,Read,Show)

data GOAL = 
   Node         LIB_ID
 | Edge         LIB_ID   LIB_ID
 | CountedEdge  LIB_ID   Int       LIB_ID
 deriving (Eq,Read,Show)


data ScriptCommandParameters =
   Path String 
 | Formula                       LIB_ID 
 | Prover                        LIB_ID
 | Goals                         [GOAL]
 | Comorphism                   [LIB_ID]
 | AxiomSelectionWith           [LIB_ID]
 | AxiomSelectionExcluding      [LIB_ID]
 | Formulas                     [LIB_ID]
 | ProofScript                   String
 | Error                         String
 deriving (Eq,Read,Show)


run :: Show a => Parser a -> String -> IO()
run p input
        = case ( parse p "" input) of
           Left err -> do {  putStr "Parse error at "
                           ; print err
                          }
           Right x -> print x



seperator :: Parser ()
seperator = skipMany1 (space <|> char ',' <?> "")




characters 
             =  try (letter)
            <|> try (char '-')
            <|> try (char '_')
            <|> try (digit)



getString = many1 characters



getPath 
        = try (do { v<-getString
                    ; return v
                  } )
            <|> 
          try (do { seperator
                    ; v<-getString
                    ; return v
                  } )


getKeyWord wd 
              =  try  ( string wd )
             <|> 
                 try ( do { seperator
                            ; string wd
                          } )

getNumber 
             =   try ( many1 digit )
            <|> 
                 try  (do { seperator
                          ; v<-many1 digit
                          ; return v
                          } )

getId=libId

getGoal =                  try (do {
                                  v1<-getId
                                  ; getKeyWord "-"
                                  ; v2<-getNumber
                                  ; getKeyWord "->"
                                  ; v3<-getId
                                  ; return (CountedEdge v1 (read v2::Int) v3)
                                   } )       
                          
                       <|> try (do {
                                  v1<-getId
                                  ; getKeyWord "->"                                  
                                  ; v2<-getId
                                  ; return (Edge  v1  v2)
                                    } )
                       <|> try ( do {
                                v <-getId
                               ;return (Node  v)
                                 } )       
getScript = try (do { getKeyWord "end-script"
                     ; return ""
                    } )
             <|> try (do { v<-getString
                     ; vs <-getScript
                    ;return (v++" "++vs)
                     } )
            <|> try (do { seperator
                         ; v<-getString
                         ; vs<-getScript
                         ; return (v++" "++vs)
                          })
                                        
                        
getComorphism = try (do { v<-getId
                          ; getKeyWord ";"
                          ;vs <-getComorphism
                          ; return ( v:vs)
                           } )
              <|> try ( do { v<-getId
     ;return [ v]
			 } )



 
--- end of scan command
scanCommand []     = do { string ""
                         ; return []
                        }
--- scanning a path
scanCommand ("PATH":ls) =do { v <- getPath 
                           ;vs<- scanCommand ls
                           ;return ((Path v):vs)
                           }
--- scanning a prover
scanCommand ("PROVER":ls)   =do { v <- getId 
                           ;vs<- scanCommand ls
                           ;return ((Prover v):vs)
                          }
--- scanning a formula
scanCommand ("FORMULA":ls)   =do { v <- getId 
                           ;vs<- scanCommand ls
                           ;return ((Formula  v):vs)
                          }

--- scanning a comorphism
scanCommand ("COMORPHISM":ls) = do {
                               v <- getComorphism 
                              ;vs<-scanCommand ls
                              ; return ((Comorphism v):vs)
                            }
--- scanning goals
scanCommand ("GOALS":ls) = do {
                          v<-many getGoal
                          ; vs<- scanCommand ls
                          ; return ((Goals v):vs)
                           }
--- scanning none or many formulas
scanCommand ("FORMULA_STAR":ls) = do {
                          v<- many ( do { value<-getId
                                          ; return  value
                                        } )
                          ; vs<-scanCommand ls
                          ; return  ((Formulas v):vs)
                        }
---- scanning one or more formula
scanCommand ("FORMULA_PLUS":ls) = do {
                            v<- many1 ( do { value<-getId
                                            ; return value
			                    } )
			; vs<-scanCommand ls
			; return ((Formulas v):vs)
			}
---- scanning proof script							
scanCommand ("PROOF-SCRIPT":ls) = do {
                         v<- getScript
                         ; vs <-scanCommand ls
                         ; return ((ProofScript v):vs)
                         }
---- scanning keywords						 
scanCommand (keyword:ls) = do {
                        getKeyWord keyword
                        ; vs<- scanCommand ls
                        ; return vs
                         }


test ls = ls



           -- basic datastructures: see Static.DevGraph, Logic.Prover 

commands =     [(["use","PATH"],                                              test), -- Static.AnalysisLibrary, Driver.ReadFn
                (["dg","auto","GOALS"],                                       test), -- Proofs.Auto
                (["dg","glob-subsume","GOALS"],                               test), -- Proofs.Global
                (["dg","glob-decomp","GOALS"],                                test), -- Proofs.Global
                (["dg","loc-infer","GOALS"],                                  test), -- Proofs.Local
                (["dg","loc-decomp","GOALS"],                                 test), -- Proofs.Local
                (["dg","comp","GOALS"],                                       test), -- Proofs.Comp
                (["dg","comp-new","GOALS"],                                   test), -- Proofs.Comp
                (["dg","hide-thm","GOALS"],                                   test), -- Proofs.HideThmShift
                (["dg","thm-hide","GOALS"],                                   test), -- Proofs.ThmHideShift
                (["dg","basic","GOALS"],                                      test), -- Proofs.InferBasic
                (["dg-all","auto"],                                           test), -- dto.
                (["dg-all","glob-subsume"],                                   test),
                (["dg-all","glob-decomp"],                                    test),
                (["dg-all","loc-infer"],                                      test),
                (["dg-all","loc-decomp"],                                     test),
                (["dg-all","comp"],                                           test),
                (["dg-all","comp-new"],                                       test),
                (["dg-all","hide-thm"],                                       test),
                (["dg-all","thm-hide"],                                       test),
                (["dg-all","basic"],                                          test),
                (["show-dg-goals"],                                           test), -- new function
                (["show-theory-goals"],                                       test), -- showTheory in GUI.ConvertAbstractToDevGraph
                (["show-theory"],                                             test), -- dto.
                (["node-info"],                                               test), -- GUI.ConvertAbstractToDevGraph
                (["show-taxonomy"],                                           test), --  GUI.ConvertAbstractToDevGraph
                (["show-concepts"],                                           test), --  GUI.ConvertAbstractToDevGraph
                (["translate","COMORPHISM"],                                  test), -- Proofs.InferBasic
                (["prover","PROVER"],                                         test), -- Proofs.InferBasic
                (["proof-script","FORMULA","PROOF-SCRIPT"],                   test), -- Isabelle.IsaProve.hs (for Isabelle)
                (["cons-check", "PROVER"],                                    test), -- ISabelle.IsaProve.hs (for ISabelle)
                (["prove", "FORMULA_STAR","with","FORMULA_PLUS"],             test), -- Proofs.InferBasic
                (["prove", "FORMULA_STAR","excluding","FORMULA_PLUS"],        test), -- Proofs.InferBasic
                (["prove", "FORMULA_STAR"],                                   test), -- Proofs.InferBasic
                (["prove-all","with","FORMULA_PLUS"],                         test), -- dto.
                (["prove-all","excluding","FORMULA_PLUS"],                    test),
                (["prove-all"],                                               test)]







checkCommand ((command_description, command_fn):command_list) 
           = 
                 try (do {
                      ls<-scanCommand command_description
                    ; try (seperator) <|> try (eof)
                    ; return (command_fn ls)
                      } )
              <|> checkCommand command_list 
checkCommand [] = do { value<-getString
                     ; return ([Error value]) 
                    }
            
parseScript  
                = try ( do { value <- many (checkCommand commands) 
                            ; eof
                            ; return value
                             } )
              <|> try ( do { value <- many (checkCommand commands)
                            ; seperator
                            ; eof
                            ; return value
                             } )      

parseScriptFile fileName
                   = do {
				          input<- readFile fileName
						 ; out<-run parseScript input
						 ; return out
						 }
						 
