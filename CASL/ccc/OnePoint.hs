{- | 
   
    Module      :  $Header$
    Copyright   :  (c) Mingyi Liu and Till Mossakowski and Uni Bremen 2004
    Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

    Maintainer  :  hets@tzi.de
    Stability   :  provisional
    Portability :  portable

   Check for truth in one-point model
       with all predicates true, all functions total

-}
{-
   todo:
   1. evaluateOnePointFORMULA durch rekursiven Abstieg
      erstmal das Morphism-Argument ignorieren
      für Qauntoren: rekursiv
      für Konjunktion: Funktion all benutzen
      für Disjunktion: Funktion any benutzen
      usw.
      Predication, Gleichungen sind immer wahr
      Sort_gen_ax erstmal weglassen
      Mixfix_formula, Unparsed_formula: Fehler ausgeben (mit error)
   
   2. den 1. Schritt testen.
      Dazu vorübergehend in hets.hs einfügen
         import CASL.ccc.OnePoint
      mit "make hets" übersetzen

   3. Sort_gen_ax [SORT] [OP_SYMB]
      nachgucken, ob zu jeder Sorte in [SORT] ein Term mit
      Operationssymbolen in [OP_SYMB] existiert.
      Dazu Tabelle aufbauen, welche Sorten sind "bewohnt"?
        Anfangs ist die Tabelle leer; dann für jedes totale OP_SYMB
        neue Einträge erzeugen: wenn Argumenten bewohnt sind,
        so ist auch die Zielsorte bewohnt
   
-}

module OnePoint where

import CASL.Sign                -- Sign, OpType
import CASL.Morphism              
import CASL.AS_Basic_CASL       -- FORMULA, OP_{NAME,SYMB}, TERM, SORT, VAR
import Common.Result            -- Result

evaluateOnePoint :: Morphism -> [FORMULA] -> Bool

evaluateOnePointFORMULA :: Morphism -> FORMULA -> Bool


