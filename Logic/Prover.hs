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

import qualified Common.AS_Annotation as AS_Anno
import Common.PrettyPrint
import Common.ProofUtils
import qualified Common.OrderedMap as OMap

import Data.Dynamic
import Data.List

-- * sentence packing

data SenStatus a tStatus = SenStatus
     { value :: a
     , isAxiom :: Bool
     , isDef :: Bool
     , thmStatus :: [tStatus]
     } deriving Show


instance PrettyPrint a => PrettyPrint (SenStatus a b) where
  printText0 ga x =
     printText0 ga (value x)

emptySenStatus :: SenStatus a b
emptySenStatus = SenStatus { value = error "emptySenStatus"
                           , isDef = False
                           , isAxiom = True
                           , thmStatus = [] }

instance Eq a => Eq (SenStatus a b) where
    d1 == d2 = (value d1) == (value d2)

instance Ord a => Ord (SenStatus a b) where
    d1 <= d2 = (value d1) <= (value d2)

decoTc :: TyCon
decoTc = mkTyCon "Static.DevGraph.SenStatus"

instance (Typeable s,Typeable b) => Typeable (SenStatus s b) where 
  typeOf s = mkTyConApp decoTc [typeOf ((undefined :: SenStatus a b -> a) s),
                                typeOf ((undefined :: SenStatus a b -> b) s)]

elemWOrdTc :: TyCon
elemWOrdTc = mkTyCon "Common.OrderedMap.ElemWOrd"

instance (Typeable a) => Typeable (OMap.ElemWOrd a) where 
  typeOf s = mkTyConApp elemWOrdTc [typeOf ((undefined :: OMap.ElemWOrd a -> a) s)]

instance PrettyPrint a => PrettyPrint (OMap.ElemWOrd a) where
    printText0 ga e = printText0 ga (OMap.ele e)

type ThSens a b = OMap.OMap String (SenStatus a b)

noSens :: ThSens a b
noSens = OMap.empty

-- | join and disambiguate
joinSens :: (Ord a,Eq b) => ThSens a b -> ThSens a b -> ThSens a b
joinSens s1 s2 = let l1 = OMap.toList s1
                     sel = fst
                     upd n (_,e) = (n,e)
                     ns = OMap.keysSet s1  
                     l2 = OMap.toList s2 
                 in OMap.fromList $ mergeSens l1 
                        $ genericDisambigSens sel upd ns l2
    where mergeSens [] l2 = l2
          mergeSens l1 [] = l1
          mergeSens l1@((k1,e1) : r1) l2@((k2,e2) : r2) = 
              case compare e1 e2 of
              LT -> (k1,e1) : mergeSens r1 l2
              EQ -> (k1,e1 { thmStatus = union (thmStatus e1) 
                                               (thmStatus e2) })
                    : mergeSens r1 r2
              GT -> (k2,e2) : mergeSens l1 r2

mapValue :: (a -> b) -> SenStatus a c -> SenStatus b c
mapValue f d = d { value = f $ value d } 

markAsGoal :: Ord a => ThSens a b -> ThSens a b
markAsGoal = OMap.map (\d -> d { isAxiom = False})

toNamedList :: ThSens a b -> [AS_Anno.Named a]
toNamedList = map (uncurry toNamed) . OMap.toList

toNamed :: String -> SenStatus a b -> AS_Anno.Named a
toNamed k s = AS_Anno.NamedSen 
              { AS_Anno.sentence = value s
              , AS_Anno.senName  = k
              , AS_Anno.isDef    = isDef s
              , AS_Anno.isAxiom  = isAxiom s}

toThSens :: Ord a => [AS_Anno.Named a] -> ThSens a b
toThSens = OMap.fromList . map
    ( \ v -> (AS_Anno.senName v,
              emptySenStatus { value   = AS_Anno.sentence v
                             , isAxiom = AS_Anno.isAxiom v
                             , isDef   = AS_Anno.isDef v }))

-- theories and theory morphisms

data Theory sign sen proof_tree = 
    Theory sign (ThSens sen (Proof_status proof_tree))

data TheoryMorphism sign sen mor proof_tree = 
     TheoryMorphism {t_source :: Theory sign sen proof_tree,
                     t_target :: Theory sign sen proof_tree,
                     t_morphism :: mor
                    } 

-- proofs and provers

-- e.g. the file name, or the script itself, or a configuration string
data Tactic_script = Tactic_script String deriving (Eq, Ord, Show)

data Proof_status proof_tree = 
                        Open String
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
    ProverTemplate (Theory sign sentence proof_tree) proof_tree

--    ProverTemplate (Theory sign (sentence, Maybe (Proof_status proof_tree))) proof_tree

type ConsChecker sign sentence morphism proof_tree =
    ProverTemplate (TheoryMorphism sign sentence morphism proof_tree) proof_tree  

theoryTc :: TyCon
theoryTc = mkTyCon "Logic.Prover.Theory"

instance (Typeable a, Typeable b,Typeable c) 
    => Typeable (Theory a b c) where
        typeOf t = mkTyConApp theoryTc 
               [typeOf ((undefined :: Theory a b c -> a) t),
                typeOf ((undefined :: Theory a b c -> b) t),
                typeOf ((undefined :: Theory a b c -> c) t)]

theoryMorTc :: TyCon
theoryMorTc = mkTyCon "Logic.Prover.TheoryMorphism"

instance (Typeable a, Typeable b, Typeable c, Typeable d) 
    => Typeable (TheoryMorphism a b c d) where
        typeOf t = mkTyConApp theoryMorTc 
               [typeOf ((undefined :: TheoryMorphism a b c d -> a) t),
                typeOf ((undefined :: TheoryMorphism a b c d -> b) t),
                typeOf ((undefined :: TheoryMorphism a b c d -> c) t),
                typeOf ((undefined :: TheoryMorphism a b c d -> d) t)]

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

