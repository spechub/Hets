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
import Common.DynamicUtils 
import Common.AS_Annotation (Named)
import Data.Dynamic

-- theories and theory morphisms

type Theory sign sen = (sign,[Named sen])

data TheoryMorphism sign sen mor = 
     TheoryMorphism {t_source, t_target :: Theory sign sen,
                     t_morphism :: mor
                    } 

-- proofs and provers

type Rule = String

type Tactic_script = String  -- the file name

data Proof_status proof_tree = Open String
                      | Disproved String 
                      | Proved(String,
                               [String], -- used axioms
                               String, -- name of prover
                               proof_tree,
                               Tactic_script)
     deriving (Eq, Show, Read)

data Prover sign sen proof_tree symbol = 
     Prover { prover_name :: String,
              prover_sublogic :: String,
              prove :: String -> (sign, [Named sen]) -> [Named sen] 
                         -> IO([Proof_status proof_tree])
                 -- input: theory name, theory, goals
                 -- output: proof status for goals and lemmas
            }


{- possibly needed in the future
              add_sym :: symbol -> IO(Bool),  -- returns True if succeeded
              remove_sym :: symbol -> IO(Bool), -- returns True if succeeded
              add_sen :: sen -> IO(Bool),  -- returns True if succeeded
              remove_sen :: sen -> IO(Bool), -- returns True if succeeded
              add_termination_info :: [symbol] -> [(symbol,[symbol])] -> IO(Bool), -- returns True if succeeded
              remove_termination_info :: [symbol] -> [(symbol,[symbol])] -> IO(Bool), -- returns True if succeeded
              replay :: proof_tree -> Maybe sen -- what about the theory???
-}

data ConsChecker morphism = 
     ConsChecker {cons_checker_name :: String,
                   cons_checker_sublogic :: String,
                   cons_check :: morphism -> IO(Maybe Bool, Tactic_script)
                  }


proverTc :: TyCon
proverTc      = mkTyCon "Logic.Prover.Prover"
instance Typeable (Prover sign sen proof_tree symbol) where
    typeOf _ = mkTyConApp proverTc []


consCheckerTc :: TyCon
consCheckerTc      = mkTyCon "Logic.Prover.ConsChecker"
instance Typeable (ConsChecker mor) where
    typeOf _ = mkTyConApp consCheckerTc []


tcProof_status :: TyCon
tcProof_status      = mkTyCon "Logic.Prover.Proof_status"

instance Typeable proof_tree
    => Typeable (Proof_status proof_tree) where
  typeOf b = mkTyConApp tcProof_status
             [typeOf $ (undefined :: Proof_status proof_tree -> proof_tree) b]

