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
         import CASL.CCC.OnePoint
      mit "make hets" übersetzen

   3. One-point-Modell nur für das Bild des Signatur-Morphismus m
      Das heißt:
      bei Gleichungen: die Sorte s der Terme feststellen
         (die Terme sind immer Sorted_Term)
         falls die Sorte s im Bild von m ist
          d..h. falls es ein t in der Source-Signatur gibt
                mit m(t)=s
                Die Menge der in Frage kommenden t's erfährt man mit msource m
                m(t) berechnet man mit Map.lookup (sort_map m) t
           ... falls es also ein t gibt, dann "unklar"
           ... es kein solches t gibt: dann True
         analog bei Definedness (gucke die Sorte des Terms an)
         analog bei Predication (gucke Prädikatsymbol)

      Vorschlag: Maybe Bool
         Nothing       *, unklar
         Just True    True
         Jast False   False


use three-valued logic {true, false, *}, * means "don't know"
equations between new sorts are true, otherwise *
new predicates are true, otherwise *

and t f *
t   t f *
f   f f f
*   * f *

or  t f *
t   t t t
f   t f *
*   t * *

implies t f *
t       t f *
f       t t t
*       t * *

equivalent t f *
t          t f *
f          f t *
*          * * *

not t f *
    f t *

(this is just Kleene's strong three-valued logic)

Implement it using Maybe Bool and monads

   4. Sort_gen_ax [SORT] [OP_SYMB]
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

evaluateOnePoint :: Morphism f e m-> [FORMULA f] -> Bool
evaluateOnePoint m fs = all id [evaluateOnePointFORMULA m f|f<-fs] 


evaluateOnePointFORMULA :: Morphism f e m -> FORMULA f -> Bool

evaluateOnePointFORMULA m (Quantification _ _ f _) = 
                    evaluateOnePointFORMULA m f

evaluateOnePointFORMULA m (Conjunction fs _)=
         all id [evaluateOnePointFORMULA m f|f<-fs]         

evaluateOnePointFORMULA m (Disjunction fs _)=
         any id [evaluateOnePointFORMULA m f|f<-fs]

evaluateOnePointFORMULA m (Implication f1 f2 _ _)
         |evaluateOnePointFORMULA m f1 = evaluateOnePointFORMULA m f2
         |otherwise = True
          
evaluateOnePointFORMULA m (Equivalence f1 f2 pos) =
         evaluateOnePointFORMULA m (Implication f1 f2 False pos)&&
         evaluateOnePointFORMULA m (Implication f2 f1 False pos) 
      
evaluateOnePointFORMULA m (Negation f _)= do
  p <- evaluateOnePointFORMULA m f
  return (not p)

evaluateOnePointFORMULA m (True_atom _)= True

evaluateOnePointFORMULA m (False_atom _)= False

evaluateOnePointFORMULA m (Predication pred_symb ts _)=True

evaluateOnePointFORMULA m (Definedness t _)= do
    (source m)

evaluateOnePointFORMULA m (Existl_equation t1 t2 _)=True

evaluateOnePointFORMULA m (Strong_equation t1 t2 _)=True

evaluateOnePointFORMULA m (Membership term sort _)=True

evaluateOnePointFORMULA m (Mixfix_formula _)= error "Fehler Mixfix_formula"

evaluateOnePointFORMULA m (Unparsed_formula _ _)= error "Fehler Unparsed_formula"

evaluateOnePointFORMULA m (ExtFORMULA _)=error "ExtFORMULA"

evaluateOnePointFORMULA _ _=error "Fehler" -- False?    


