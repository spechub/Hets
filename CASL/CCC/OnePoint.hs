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
      oder den import nicht einfügen, und
         gmake ghci
         :l CASL/CCC/OnePoint.hs

   3. do-Notation wieder rauswerfen, statt do x<- ... 
       let x= .. in
      imageOfMorphism komplettieren (pred wie op)
      in evaluateOnePointFORMULA die lookup-Aufrufe korrigieren
      (Typchecker benutzen!)


      One-point-Modell nur für das Bild des Signatur-Morphismus m
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
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Rel as Rel

evaluateOnePoint :: Morphism f e m -> [FORMULA f] -> Maybe Bool
evaluateOnePoint m fs = 
     let p = [evaluateOnePointFORMULA (imageOfMorphism m) f|f<-fs]
     in if elem (Just False) p then  Just False
        else if elem Nothing p then  Nothing
                               else  Just True  

{-
evaluateOnePoint :: Morphism f e m-> [FORMULA f] -> Maybe Bool
evaluateOnePoint m fs = do
     p <- mapM (evaluateOnePointFORMULA m) fs
     return (all id p)
-}


evaluateOnePointFORMULA :: Sign f e -> FORMULA f -> Maybe Bool
evaluateOnePointFORMULA sig (Quantification _ _ f _) = 
                      evaluateOnePointFORMULA sig f

evaluateOnePointFORMULA sig (Conjunction fs _)=
     let p=[evaluateOnePointFORMULA sig f|f<-fs]
     in if elem (Just False) p then Just False
        else if elem Nothing p then Nothing
                               else Just True  
                  
evaluateOnePointFORMULA sig (Disjunction fs _)=
      let p=[evaluateOnePointFORMULA sig f|f<-fs]
      in if elem (Just True) p then Just True
         else if elem Nothing p then Nothing
                                else Just False
 
evaluateOnePointFORMULA sig (Implication f1 f2 _ _)= 
        let p1=evaluateOnePointFORMULA sig f1
            p2=evaluateOnePointFORMULA sig f2
        in if p1==(Just False) || p2==(Just True) then Just True
           else if p1==(Just True) && p2==(Just False) then Just False
                                                       else Nothing  
evaluateOnePointFORMULA sig (Equivalence f1 f2 pos) =
         let p1=evaluateOnePointFORMULA sig f1 
             p2=evaluateOnePointFORMULA sig f2
         in if p1==Nothing || p2==Nothing then Nothing
            else if p1==p2 then Just True
                           else Just False
      
evaluateOnePointFORMULA sig (Negation f _)= 
      case evaluateOnePointFORMULA sig f of
       Just True -> Just False
       Just False ->Just True
       _ -> Nothing
   

evaluateOnePointFORMULA sig (True_atom _)= Just True

evaluateOnePointFORMULA sig (False_atom _)= Just False

evaluateOnePointFORMULA sig (Predication pred_symb ts _)=
     case pred_symb of
       Pred_name pname ->  Nothing
       Qual_pred_name pname ptype pos ->
                case Map.lookup pname (predMap sig) of
                  Nothing -> Just True
                  Just ptypes -> 
                    if toPredType ptype `Set.member` ptypes then Nothing
                      else Just True 
       

evaluateOnePointFORMULA sig (Definedness t _)=
     let Sorted_term _ sort _=t
     in case Set.member sort (sortSet sig) of
           True->Nothing
           False->Just True  
    
evaluateOnePointFORMULA sig (Existl_equation t1 t2 _)=
     let Sorted_term term1 sort1 pos1=t1
         Sorted_term term2 sort2 pos2=t2
     in if (Set.member sort1 (sortSet sig)==False)
             &&(Set.member sort2 (sortSet sig)==False) then Just True
        else Nothing 

evaluateOnePointFORMULA sig (Strong_equation t1 t2 _)=
     let Sorted_term term1 sort1 pos1=t1
         Sorted_term term2 sort2 pos2=t2
     in if (Set.member sort1 (sortSet sig)==False)
             &&(Set.member sort2 (sortSet sig)==False) then Just True
        else Nothing 

-- todo: auc prüfen, ob Sorte von t in sortSet sig     
evaluateOnePointFORMULA sig (Membership t sort _)
     |Set.member sort (sortSet sig)==False = Just True
     |otherwise= Nothing
 
evaluateOnePointFORMULA sig (Mixfix_formula _)= error "Fehler Mixfix_formula"

evaluateOnePointFORMULA sig (Unparsed_formula _ _)= error "Fehler Unparsed_formula"

evaluateOnePointFORMULA sig (ExtFORMULA _)=error "Fehler ExtFORMULA"

evaluateOnePointFORMULA _ _=error "Fehler" -- False?    


imageOfMorphism :: Morphism f e m  -> Sign f e
imageOfMorphism m = 
        sig {sortSet = Map.image sortMap (sortSet src),
             sortRel = Rel.image (\a->Map.find a sortMap) (sortRel src), 
             opMap = Map.foldWithKey 
                       (\ident ots l ->  
                           Set.fold (\ot l' -> 
                             case mapOpSym sortMap funMap (ident,ot) of
                               Nothing -> l'
                               Just id_ot -> insertOp id_ot l') l ots) 
                       Map.empty (opMap src),
             predMap = Map.foldWithKey                                          
                         (\ident pts l ->                                         
                             Set.fold (\pt l' ->                                  
                               case mapPredSym sortMap pMap (ident,pt) of      
                                 Nothing -> l'                                    
                                 Just id_pt -> insertPred id_pt l') l pts)        
                         Map.empty (predMap src)              
            }
  where sig = mtarget m
        src = msource m
        sortMap = sort_map m
        funMap = fun_map m
        insertOp (ident,ot) opM = 
          case Map.lookup ident opM of
            Nothing -> Map.insert ident (Set.single ot) opM
            Just ots -> Map.insert ident (Set.insert ot ots) opM
        pMap = pred_map m
        insertPred (ident,pt) predM = 
          case Map.lookup ident predM of
            Nothing -> Map.insert ident (Set.single pt) predM
            Just pts -> Map.insert ident (Set.insert pt pts) predM