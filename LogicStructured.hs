------------------------------------------------------------------------------
-- HetCATS/LogicStructured.hs
-- $Id$
-- Authors: Pascal Schmidt
-- Year:    2002
------------------------------------------------------------------------------
{- todo:

  Hochziehen auf strukturierte Ebene
    Maybe(existentiellen Typ G_sublogics aus Grothendieck.hs) verwenden
    AS_Structured.hs, AS_Arch.hs, AS_Library.hs
    Funktionen aus Logic_CASL.hs bzw. Logic.hs verwenden
    Nur für homogene Specs das jeweilige Maximum berechnen
      (Vergleich von Logic-ids mit language_name), ansonsten Nothing

-}

module LogicStructured where

import Maybe
import AS_Structured
import AS_Architecture
import AS_Library
