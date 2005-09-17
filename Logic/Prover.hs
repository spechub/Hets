{-| 
   
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  till@tzi.de
Stability   :  provisional
Portability :  portable

Provide prover stuff for class Logic.Sentences

-}

module Logic.Prover where
import Common.DynamicUtils 
import Common.AS_Annotation
import Data.Dynamic

-- theories and theory morphisms

data Theory sign sen = Theory sign [Named sen]

data TheoryMorphism sign sen mor = 
     TheoryMorphism {t_source :: Theory sign sen,
                     t_target :: Theory sign sen,
                     t_morphism :: mor
                    } 

-- proofs and provers

-- e.g. the file name, or the script itself, or a configuration string
data Tactic_script = Tactic_script String deriving (Eq, Ord, Show)

data Proof_status proof_tree = Open String
                      | Disproved String 
                      | Proved { goalName :: String,
                                 usedAxioms :: [String], -- used axioms or theorems or goals
                                 proverName :: String, -- name of prover
                                 proofTree :: proof_tree,
                                 tacticScript :: Tactic_script }
                      | Consistent Tactic_script
     deriving (Eq, Show)

isProvedStat :: Proof_status proof_tree -> Bool
isProvedStat (Proved _ _ _ _ _) = True
isProvedStat _ = False

data ProverTemplate goal proof_tree = Prover
    { prover_name :: String,
      prover_sublogic :: String,
      prove :: String -> goal -> IO([Proof_status proof_tree])
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

type Prover sign sentence proof_tree = 
    ProverTemplate (Theory sign sentence) proof_tree

type ConsChecker sign sentence morphism proof_tree =
    ProverTemplate (TheoryMorphism sign sentence morphism) proof_tree  

theoryTc :: TyCon
theoryTc = mkTyCon "Logic.Prover.Theory"

instance (Typeable a, Typeable b) => Typeable (Theory a b) where
        typeOf t = mkTyConApp theoryTc 
               [typeOf ((undefined :: Theory a b -> a) t),
                typeOf ((undefined :: Theory a b -> b) t)]

theoryMorTc :: TyCon
theoryMorTc = mkTyCon "Logic.Prover.TheoryMorphism"

instance (Typeable a, Typeable b, Typeable c) 
    => Typeable (TheoryMorphism a b c) where
        typeOf t = mkTyConApp theoryMorTc 
               [typeOf ((undefined :: TheoryMorphism a b c -> a) t),
                typeOf ((undefined :: TheoryMorphism a b c -> b) t),
                typeOf ((undefined :: TheoryMorphism a b c -> c) t)]

proverTc :: TyCon
proverTc = mkTyCon "Logic.Prover.ProverTemplate"

instance (Typeable a, Typeable b) => Typeable (ProverTemplate a b) where
    typeOf p = mkTyConApp proverTc 
               [typeOf ((undefined :: ProverTemplate a b -> a) p),
                typeOf ((undefined :: ProverTemplate a b -> b) p)]

tcProof_status :: TyCon
tcProof_status = mkTyCon "Logic.Prover.Proof_status"

instance Typeable proof_tree => Typeable (Proof_status proof_tree) where
  typeOf b = mkTyConApp tcProof_status
             [typeOf $ (undefined :: Proof_status proof_tree -> proof_tree) b]

