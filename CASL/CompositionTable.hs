module CompositionTable where

{-
DTD unter http://www.tzi.de/cofi/hets/CompositionTable.dtd
-}
type BaseRel = String

typ CompositionTable = [(BaseRel,BaseRel,[BaseRel])]
type ConverseTable = [(BaseRel,BaseRel)]

data Table = Table { name :: String,
                     compositionTable :: CompositionTable,
                     converseTable :: ConverseTable,
                     identity :: BaseRel,
                     models :: [(String,String)]
                   }

-- hets --spec=RCC8 -o comptable.xml Calculi/Space/RCC8.het
-- writes Calculi/Space/RCC8.comptable.xml

-- add general hets option that omits analysis of current lib if output files/env are up-to-date
--  (also important for GUI)

{-
eliminate ops on rhs, resulting in list of base relations
add equations for id
-}
