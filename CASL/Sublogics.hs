
{- HetCATS/CASL/Logic_CASL.hs
   $Id$
   Authors: Klaus Lüttich
   Year:    2002

   Here is the place where the class Logic is instantiated for CASL.
   Also the instances for Syntax an Category.

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

     - writing real functions

-}

import AS_Basic_CASL
import LocalEnv