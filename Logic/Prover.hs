{-| 
   
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

   Provide prover stuff for class Logic.Sentences

-}

module Logic.Prover where
import Data.Dynamic
import Common.AS_Annotation (Named)

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

type Tactic_script = String  -- the file name

data Proof_status sen proof_tree = Open sen
                      | Disproved sen 
                      | Proved(sen,
                               [sen], -- used axioms
                               String, -- name of prover
                               proof_tree,
                               Tactic_script)

data Prover sign sen proof_tree symbol = 
     Prover { prover_name :: String,
              prover_sublogic :: String,
              prove :: String -> (sign, [Named sen]) -> [Named sen] 
                         -> IO([Proof_status sen proof_tree])
                 -- input: theory name, theory, goals
                 -- output: proof status for goals and lemmas
            }

proverTc :: TyCon
proverTc      = mkTyCon "Logic.Prover.Prover"
instance Typeable (Prover sign sen proof_tree symbol) where
    typeOf _ = mkAppTy proverTc []


{- possibly needed in the future
              add_sym :: symbol -> IO(Bool),  -- returns True if succeeded
              remove_sym :: symbol -> IO(Bool), -- returns True if succeeded
              add_sen :: sen -> IO(Bool),  -- returns True if succeeded
              remove_sen :: sen -> IO(Bool), -- returns True if succeeded
              add_termination_info :: [symbol] -> [(symbol,[symbol])] -> IO(Bool), -- returns True if succeeded
              remove_termination_info :: [symbol] -> [(symbol,[symbol])] -> IO(Bool), -- returns True if succeeded
              replay :: proof_tree -> Maybe sen -- what about the theory???
-}

data Cons_checker morphism = 
     Cons_checker {cons_checker_name :: String,
                   cons_checker_sublogic :: String,
                   cons_check :: morphism -> IO(Bool, Tactic_script)
                  }
