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

module CASL.CCC.OnePoint where

import CASL.Sign                -- Sign, OpType
import CASL.Morphism              
import CASL.AS_Basic_CASL       -- FORMULA, OP_{NAME,SYMB}, TERM, SORT, VAR
import Common.Result            -- Result

evaluateOnePoint :: Morphism -> [FORMULA] -> Bool
evaluateOnePoint m fs = all (\x->x==True) [evaluateOnePointFORMULA m f|f<-fs] 


evaluateOnePointFORMULA :: Morphism -> FORMULA -> Bool

evaluateOnePointFORMULA m (Quantification _ _ (FORMULA f) _) = 
                    evaluateOnePointFORMULA m (FORMULA f)

evaluateOnePointFORMULA m (Conjunction fs _)=
         all id [evaluateOnePointFORMULA m f|f<-fs]         

evaluateOnePointFORMULA m (Disjunction fs _)=
         any id [evaluateOnePointFORMULA m f|f<-fs]

evaluateOnePointFORMULA m (Implication f1 f2 _ _)
         |evaluateOnePointFORMULA m f1 = evaluateOnePointFORMULA m f2
         |otherwise = True
          
evaluateOnePointFORMULA m (Equivalence f1 f2 _) =
         evaluateOnePointFORMULA m (Implication f1 f2 False _)&&
         evaluateOnePointFORMULA m (Implication f2 f1 False _) 
      
evaluateOnePointFORMULA m (Negation f _)= not (evaluateOnePointFORMULA m f) 

evaluateOnePointFORMULA m (True_atom _)= True

evaluateOnePointFORMULA m (False_atom _)= False

evaluateOnePointFORMULA m (Predication pred_symb ts _)=True

evaluateOnePointFORMULA m (Definedness t _)=True

evaluateOnePointFORMULA m (Existl_equation t1 t2 _)=True

evaluateOnePointFORMULA m (Strong_equation t1 t2 _)=True

evaluateOnePointFORMULA m (Membership term sort _)=True

evaluateOnePointFORMULA m (Mixfix_formula _)= error "Fehler Mixfix_formula"

evaluateOnePointFORMULA m (Unparsed_formula _ _)= error "Fehler Unparsed_formula"

evaluateOnePointFORMULA m (ExtFORMULA _)=error "ExtFORMULA"

evaluateOnePointFORMULA _ _=error "Fehler" -- False?    


