
{- HetCATS/CASL/Sublogics.hs
   $Id$
   Authors: Pascal Schmidt
   Year:    2002

   todo:

aufbauend auf Logic.hs Logik für CASL mit Unterlogiken

data CASL_sublogics = CASL_sublogics { has_sub::Bool ...

   sublogic_names :: id -> sublogics -> [String] 
             -- the first name is the principal name
         all_sublogics :: id -> [sublogics]
  <=
  meet, join :: l -> l -> l  -- meet = "Durschnitt"
  top :: l


Weitere Instanzen mit HasCASL, CASL-LTL etc.
  (nur sich selbst als Sublogic)
Logic-Representations (Sublogic immer = top)

Alles zusammenfassen in LogicGraph.hs


min_sublogic_basic_spec  Analysefunktion: für basic spec Bitmaske berechnen
   (Bits fuer Features setzen und rekursiv verodern)
is_in_basic_spec  Testfunktion: pruefen, ob errechnete Bitmaske <= vorgegebene

-}

module Sublogics_CASL where

import AS_Annotation
import AS_Basic_CASL
import LocalEnv

data CASL_Sublogics = CASL_Sublogics
                      { has_sub::Bool,   -- subsorting
                        has_part::Bool,  -- partiality
                        has_cons::Bool,  -- sort generation contraints
                        has_eq::Bool,    -- equality
                        has_pred::Bool,  -- predicates
                        is_ghorn::Bool,  -- generalized positive cond. logic
                        is_horn::Bool,   -- positive conditional logic
                        is_atom::Bool    -- atomic logic
                      } deriving (Show,Eq)

strip_anno :: Annoted a -> a
strip_anno (Annoted i _ _ _) = i
