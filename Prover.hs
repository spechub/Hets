
{- HetCATS/Prover.hs
   $Id$
   Authors: Till Mossakowski
            Christian Maeder
   Year:    2002

   Provide prover stuff for class Logic.Sentences

-}

module Prover where

-- theories and theory morphisms

data Theory sign sen = 
     Theory {sign_of :: sign, 
             ax_of :: [(String,sen)]
            }

data TheoryMorphism sign sen mor = 
     TheoryMorphism {t_source, t_target :: Theory sign sen,
                     t_morphism :: mor
                    } 

-- proofs and provers

type Rule = String

data Proof_tree sen = Axiom sen
                    | Branch (sen,Rule,[Proof_tree sen])  -- add substitutions here?

type Tactic_script = String  -- the file name

data Proof_status sen = Open sen
                      | Disproved sen 
                      | Proved(sen,
                               [sen], -- used axioms
                               Proof_tree sen,
                               Tactic_script)

data Prover sen symbol = 
     Prover { prover_name :: String,
              prover_sublogic :: String,
              add_sym :: symbol -> IO(Bool),  -- returns True if succeeded
              remove_sym :: symbol -> IO(Bool), -- returns True if succeeded
              add_sen :: sen -> IO(Bool),  -- returns True if succeeded
              remove_sen :: sen -> IO(Bool), -- returns True if succeeded
              prove :: sen -> IO([Proof_status sen]) -- proof status for goal and lemmas
            }

data Cons_checker morphism = 
     Cons_checker {cons_checker_name :: String,
                   cons_checker_sublogic :: String,
                   cons_check :: morphism -> IO(Bool, Tactic_script)
                  }
