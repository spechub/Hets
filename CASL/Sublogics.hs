{- HetCATS/CASL/Sublogics.hs
   $Id$
   Authors: Pascal Schmidt
   Year:    2002

   todo:

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

------------------------------------------------------------------------------
-- datatypes for CASL sublogics
------------------------------------------------------------------------------

data CASL_Formulas = FOL     -- first-order logic
                   | GHorn   -- generalized positive conditional logic
                   | Horn    -- positive conditional logic
                   | Atomic  -- atomic logic
                   deriving (Show,Ord,Eq)

data CASL_Sublogics = CASL_SL
                      { has_sub::Bool,   -- subsorting
                        has_part::Bool,  -- partiality
                        has_cons::Bool,  -- sort generation contraints
                        has_eq::Bool,    -- equality
                        has_pred::Bool,  -- predicates
                        which_logic::CASL_Formulas
                      } deriving (Show,Eq)

-- top element
top :: CASL_Sublogics
top = (CASL_SL True True True True True FOL)

-- bottom element
bottom :: CASL_Sublogics
bottom = (CASL_SL False False False False False Atomic)

------------------------------------------------------------------------------
-- conversion to String
------------------------------------------------------------------------------

formulas_name :: Bool -> CASL_Formulas -> String
formulas_name True  FOL    = "FOL"
formulas_name False FOL    = "FOAlg"
formulas_name True  GHorn  = "GHorn"
formulas_name False GHorn  = "GCond"
formulas_name True  Horn   = "Horn"
formulas_name False Horn   = "Cond"
formulas_name True  Atomic = "Atom"
formulas_name False Atomic = "Eq"

sublogics_name :: CASL_Sublogics -> String
sublogics_name x = ( if (has_sub x) then "Sub" else "" ) ++
                   ( if (has_part x) then "P" else "") ++
                   ( if (has_cons x) then "C" else "") ++
                   ( formulas_name (has_pred x) (which_logic x) ) ++
                   ( if (has_eq x) then "=" else "")

------------------------------------------------------------------------------
-- min and max functions
------------------------------------------------------------------------------

formulas_max :: CASL_Formulas -> CASL_Formulas -> CASL_Formulas
formulas_max FOL _    = FOL
formulas_max _ FOL    = FOL
formulas_max GHorn _  = GHorn
formulas_max _ GHorn  = GHorn
formulas_max Horn _   = Horn
formulas_max _ Horn   = Horn
formulas_max _ _ = Atomic

formulas_min :: CASL_Formulas -> CASL_Formulas -> CASL_Formulas
formulas_min Atomic _ = Atomic
formulas_min _ Atomic = Atomic
formulas_min Horn _   = Horn
formulas_min _ Horn   = Horn
formulas_min GHorn _  = GHorn
formulas_min _ GHorn  = GHorn
formulas_min _ _      = FOL

sublogics_max :: CASL_Sublogics -> CASL_Sublogics -> CASL_Sublogics
sublogics_max (CASL_SL a1 b1 c1 d1 e1 l1) (CASL_SL a2 b2 c2 d2 e2 l2)
              = (CASL_SL (a1 || a2) (b1 || b2) (c1 || c2) (d1 || d2)
                 (e1 || e2) (formulas_max l1 l2))

sublogics_min :: CASL_Sublogics -> CASL_Sublogics -> CASL_Sublogics
sublogics_min (CASL_SL a1 b1 c1 d1 e1 l1) (CASL_SL a2 b2 c2 d2 e2 l2)
              = (CASL_SL (a1 && a2) (b1 && b2) (c1 && c2) (d1 && d2)
                 (e1 && e2) (formulas_min l1 l2))

------------------------------------------------------------------------------
-- helper functions
------------------------------------------------------------------------------

strip_anno :: Annoted a -> a
strip_anno (Annoted i _ _ _) = i

------------------------------------------------------------------------------
-- the end
------------------------------------------------------------------------------
