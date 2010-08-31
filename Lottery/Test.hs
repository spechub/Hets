{- |
Module      :  $EmptyHeader$
Description :  <optional short description entry>
Copyright   :  (c) <Authors or Affiliations>
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  <email>
Stability   :  unstable | experimental | provisional | stable | frozen
Portability :  portable | non-portable (<reason>)

<optional description>
-}
{- Projekt Lottery: Entwurf eines automatischen Formelgenerators

   Stand 16.07.2002
   Einschraenkungen: bis jetzt keine MixFix_Id -}

module Test where

import FiniteMap
import List
import Id
import AS_Basic_CASL


type Sort_Map = FiniteMap SORT [SORT]

type Sort_Op_Index = FiniteMap SORT [Ops]

data Ops = Ops OP_NAME OP_TYPE
           deriving (Show,Eq)

type Env = FiniteMap SORT Int

-- Sort-Section ------------------------------------------------

{- getSortMap erstellt eine FiniteMap aller im Body deklarierten
   Sorten und jeweils einer Liste der direkten Subsorten.
   Wird auf die Liste von Strings nach getBody angewandt!-}
getSortMap (x:xs)
  -- erst pruefen, ob ueberhaupt Sorten deklariert werden
  | not(x == "sorts") = emptyFM
  | otherwise         = listToFM ( getListForFM
                                     (getSortList (getSortDecls xs))
                                     (getSubSortDecls (getSortDecls xs)))

{- getHSMap erstellt aus einer Sort-SubsortList-Map eine
   Sort-SupersortList-Map, einer Sorte wird die Liste der
   direkten Obersorten zugeordnet. -}
getHSMap sMap = let buildEntry s = (s, (getHSorts sMap s))
                 in listToFM (map buildEntry (getSorts sMap))

{- getHSorts liefert eine Liste aller direkten Obersorten
   von s, die in sMap (Sort_Map mit Sort - [Subsort])
   eingetragen sind. -}
getHSorts sMap s = let isSubSort (a , aList) = elem s aList
                       subList = filter isSubSort (fmToList sMap)
                    in if (subList /= []) then
                           fst (unzip subList)
                        else
                           []

{- getSorts liefert eine Liste aller Sorten, die in sMap
   eingetragen sind. -}
getSorts sMap = keysFM sMap

{- getSuperSorts liefert eine Liste der direkten Obersorten von
   Sorte s in der Sort_Map hsMap -}
getSuperSorts s hsMap = lookupWithDefaultFM hsMap [] s


{- getSubSorts liefert eine Liste der direkten Subsorten von
   Sorte s in der Sort_Map sMap -}
getSubSorts s sMap = lookupWithDefaultFM sMap [] s

{- Zieht alle Sorten-Deklarationen aus der Body-String-Liste
   heraus, loescht in jedem String evtl. vorhandene Semikolons
   und gibt sie als Liste von Strings zurueck -}
getSortDecls (x:xs)
  | (x == "sorts") = getSortDecls xs
  | (x == "ops")   = []
  | (x == "preds") = []
  | (x == "")      = []
  | otherwise      = (delSemis x):(getSortDecls xs)

{- getSortList liefert eine Liste aller deklarierten Sorten -}
getSortList list = union (filter isSortDecl list)
                      (map getSortName (getSubSortDecls list))

{- getSortName liefert aus einer Sortendeklaration mit Subsorten
   den Namen der Obersorte -}
getSortName str    = tail (dropWhile isNoLAngle str)

{- getSubSortDecls liefert eine Liste aller Sorten-Deklarationen
   mit Subsorten -}
getSubSortDecls list = filter isSubSortDecl list

{- Erstellt eine Liste von Tupeln, mit der die Sort_Map
   konstruiert werden kann -}
getListForFM [] _  = []

getListForFM (x:xs) list =
  ((str2Id x) , (map str2Id (setSubSorts x list)))
                                          :(getListForFM xs list)

{- getSubSorts sucht aus einer Liste von Subsorten-Deklarationen
   alle Subsorten zu einer Sorte heraus und gibt diese in einer
   Liste zurueck. -}
setSubSorts sort []   = []

setSubSorts sort (x:xs)
  | ((getSortName x) == sort)   = (getSubFromDecl x)++(setSubSorts sort xs)
  | otherwise      = setSubSorts sort xs

{- Hilfsfunktion fuer getSubSorts, die die Namen der Subsorten
   aus einer Subsorten-Deklaration extrahiert und sie als Liste
   zurueckgibt -}
getSubFromDecl str
  -- wenn ein Komma in der Deklaration steht ...
  | (elem ',' str) = (takeWhile isNoComma str):
                          (getSubFromDecl (tail(dropWhile isNoComma str)))
  -- ansonsten ist nur ein Name zu extrahieren
  | otherwise      = [takeWhile isNoLAngle str]

  where isNoComma c = not(c == ',')

isNoLAngle c = not(c == '<')

{- Hilfsfunktion, die True liefert, wenn es sich bei der
   Deklaration um eine Subsorten-Deklaration handelt -}
isSubSortDecl str = (elem '<' str)

{- Hilfsfunktion, die True liefert, wenn es sich bei der
   Deklaration um keine Subsorten-Deklaration handelt -}
isSortDecl str = not(elem '<' str)

-- Op-Section -----------------------------------------------


{- getOpDecls liest aus dem zeilenweise gelisteten Body eines
   .env.txt-Files die Op-Decls. und gibt diese in Form einer
   Liste von Strings ohne Semikolons wieder.-}
getOpDecls b []       = []

getOpDecls b (x:xs)
  | ((b == False) && (not(x == "ops"))) = getOpDecls False xs
  | (x == "ops")       = getOpDecls True xs
  | ((b == True) && (x == "preds"))   = []
  | ((b == True) && (x == ""))        = []
  | otherwise          = (delSemis x):(getOpDecls True xs)

{- Liest die Informationen aus einer Op-Decl. und erstellt
   damit ein Objekt vom Typ Ops -}
getOps str
  | (elem '?' str) = Ops (setOpName str)
                         (Partial_op_type (getParamSorts str)
                                          (getTargetSort str)
                                          [] )
  | otherwise      = Ops (setOpName str)
                         (Total_op_type (getParamSorts str)
                                        (getTargetSort str)
                                        [] )
  where setOpName str = str2Id (takeWhile isNoColon str)


{- getParamSorts sucht aus einer Op-Decl. die Parameter-Sorten
   der Operation heraus und gibt diese als [SORT] zurueck -}
getParamSorts str
  | not(elem '>' str) = []
  | otherwise         = if not(elem '*' str) then
                            getParam (dropName str)
                         else
                            getParamList (dropName str)

  where getParam str = [str2Id (takeWhile isNoMin str)]
        dropName str = tail (dropWhile isNoColon str)
        dropParam str = tail (dropWhile isNoAst str)
        isNoMin c = not(c == '-')
        isNoAst c = not(c == '*')
        getParamList str = if (elem '*' str) then
                               (str2Id (takeWhile isNoAst str))
                                 :(getParamList (dropParam str))
                            else
                               getParam str

{- getTargetSort sucht aus einer Op-Decl. die Zielsorte der
   Operation heraus und gibt sie als SORT zurueck -}
getTargetSort str
  | (elem '?' str) = str2Id (tail (dropWhile isNoQMark str))
  | (not(elem '>' str) && not(elem '?' str)) =
                     str2Id (tail (dropWhile isNoColon str))
  | otherwise      = str2Id (tail (dropWhile isNoRAngle str))

  where isNoQMark c  = not(c == '?')
        isNoRAngle c = not(c == '>')

{- getSortOpList erstellt aus dem "Body" eines
   *.env.txt-files eine Liste, aus der ein
   Sort_Op_Index erstellt werden kann -}
getSortOpList body = if (sortList == []) then
                              []
                           else
                              map getEntry sortList

  where sortList = map str2Id (getSortList (getSortDecls body))
        opList   = map getOps (getOpDecls False body)
        getOpsOfSort s = [op | op <- opList, s == (getOpTS op)]
        getEntry s = (s, (getOpsOfSort s))

{- getSortOpIndex erstellt aus dem "Body" eines
   *.env.txt-files einen Sort_Op_Index -}
getSortOpIndex body = listToFM (getSortOpList body)

{- getOpTS gibt die Ziel-Sorte einer Operation zurueck -}
getOpTS (Ops opname (Total_op_type ps ts pos)) = ts

getOpTS (Ops opname (Partial_op_type ps ts pos)) = ts

{- getOpPS gibt die Liste der Parameter-Sorten einer
   Operation zurueck -}
getOpPS (Ops opname (Total_op_type ps ts pos)) = ps

getOpPS (Ops opname (Partial_op_type ps ts pos)) = ps

{- isTotalOp liefert True, wenn es sich beim Uebergabewert
   um eine totale Operation handelt, sonst wird False
   zurueckgegeben. -}
isTotalOp (Ops opname (Total_op_type ps ts pos)) = True

isTotalOp (Ops opname (Partial_op_type ps ts pos)) = False

{- getOpName liefert den Namen der uebergebenen Operation
   als Rueckgabewert. -}
getOpName (Ops opname (Total_op_type ps ts pos)) = opname

getOpName (Ops opname (Partial_op_type ps ts pos)) = opname


-- Terme zaehlen ... ------------------------------------------
---------------------------------------------------------------
-- Hier stehen die Funktionen die fuer das Zaehlen von Termen
-- gebraucht werden.
---------------------------------------------------------------

{- countTerm :
   Dach- und Ausgabe-Funktion fuer das Zaehlen von Termen
   Aufruf der Funktion:
            countTerm n sort file t sub_B

            wobei: n     - Laenge der Terme
                   sort  - Sorte der Terme
                   file  - .env.txt-File mit der Signatur
                   t     - True, wenn nur die totalen
                           Terme gezaehlt werden sollen
                           sonst False
                   sub_B - True, wenn auch Einbettung in die
                           direkten Obersorten mitgezaehlt
                           werden soll, sonst False
   Das Ergebnis wird durch die Funktion print ausgegeben.
-}
countTerm n sort file t sub_B =
                  do { inp <- readFile file
                     ; let body = getBody (lines inp)
                           sort_map = getSortMap body
                           sort_op_index = getSortOpIndex body
                           s = str2Id sort
                           env = initEnv sort_map
                     ; print (cntTerm n env sort_op_index sort_map t sub_B s)
                     }

{- cntCon zaehlt die Konstanten der Sorte s im Sort_Op_Index ind.
   Wenn t True ist, so werden nur totale Konstanten gezaehlt,
   ist t False, so werden alle Konstanten gezaehlt.
   Zur Anzahl der Konstanten werden noch die Variablen der Sorte
   s in env hinzugezaehlt.
-}
cntCon s env soInd t =
                  let list = getOpList s soInd
                      vars = lookupWithDefaultFM env 0 s
                      cntAll = length ([op | op <- list, (getOpPS op) == []])
                      cntTotal = length ([op | op <- list, (getOpPS op) == [], isTotalOp op])
                  in if (list  == []) then
                         0
                      else
                         if t then
                            cntTotal + vars
                          else
                            cntAll + vars

{- getOpList liefert die Liste der Operationen mit der
   Zielsorte s im Sort_Op_Index ind (Hilfsfunktion) -}
getOpList s ind = lookupWithDefaultFM ind [] s

{- vereinfachter Aufruf fuer die Zaehlung von totalen Termen -}
count_total_terms n env soInd sMap sub_B sort =
                  cntTerm n env soInd sMap True sub_B sort

{- vereinfachter Aufruf fuer die Zaehlung von allen Termen -}
count_all_terms n env soInd sMap sub_B sort =
                  cntTerm n env soInd sMap False sub_B sort

{- vereinfachter Aufruf fuer die Zaehlung von partiellen Termen -}
count_partial_terms n env soInd sMap sub_B sort =
                  count_all_terms n env soInd sMap sub_B sort
                  - count_total_terms n env soInd sMap sub_B sort

{- cntTerm ist die eigentliche Term-zaehl-Fkt.
   n     - Laenge der zu zaehlenden Terme
   env   - FiniteMap Sorte <# Variablen der Sorte als Int>
   soInd - zugrundeliegender Sort_Op_Index
   sMap  - zugrundeliegende Sort_Map
   t     - True, wenn nur totale Terme gezaehlt werden sollen
   sub_B - True, wenn Einbettung in direkte Obersorten
           beruecksichtigt werden soll
   s     - die Sorte der zu zaehlenden Terme
-}
cntTerm:: Int ->Env ->Sort_Op_Index ->Sort_Map ->Bool ->Bool ->SORT ->Int

cntTerm n env soInd sMap t sub_B s
  | (n <= 0)  = 0
  | (n == 1)  = cntCon s env soInd t
  | otherwise = let list = getOpList s soInd
                    op_list = [op | op <- list, 0 < (f op), (f op) <= (n-1)]
                    subsorting_A = sum
                                   (map (cntTerm (n-1) env soInd sMap t sub_B)
                                        (getSubSorts s sMap))
                    subsorting_B = sum
                                   (map (cntTerm (n-1) env soInd sMap t sub_B)
                                        (getSuperSorts s (getHSMap(sMap))))
                    count_total  = sum
                                   (map (sumOp (n-1) env soInd sMap t sub_B)
                                        (filter isTotalOp op_list))
                    count_all    = sum
                                   (map (sumOp (n-1) env soInd sMap t sub_B)
                                         op_list)
                 in if t then
                       if sub_B then
                          count_total
                          + subsorting_A
                          + subsorting_B
                        else
                          count_total
                          + subsorting_A
                     else
                       if sub_B then
                          count_all
                          + subsorting_A
                          + subsorting_B
                        else
                          count_all
                          + subsorting_A

  where f op = length(getOpPS op)
        sumOp m e ind smap b sub_b op =
              sumPart e (getOpPS op) (getPartitions m (f op)) ind smap b sub_B

{- sumPart berechnet die Summe der Terme ueber einer Sequenz von Sorten
   (in Form einer Liste) und einer Liste von Partitionen.
   sList - die Liste der Sorten (hier handelt es sich normalerweise um
           die Parameter-Sorten einer Operation)
   pList - die Liste der Partitionen, fuer die die Anzahl der Terme
           berechnet werden soll
   soInd - der Sort-Op-Index auf dessen Grundlage die Berechnung
           durchgefuehrt wird
   sMap  - sie Sort-Map auf deren Grundlage die Berechnung
           durchgefuehrt wird
   t     - True, wenn nur totale Terme gezaehlt werden sollen,
           sonst False
   sub_B - True, wenn Einbettung in die Obersorte(n) mitgezaehlt werden
           soll, sonst False
-}
sumPart env sList pList soInd sMap t sub_B =
                  sum (map (addPart env sList soInd sMap t sub_B) pList)

  where addPart _ [] _ _ _ _ [] = 1
        addPart e (s:xs) ind smap b s_B (i:xi) =
                  (cntTerm i e ind smap b s_B s)
                   * (addPart e xs ind smap b s_B xi)


-- Partitions-Section -----------------------------------------
---------------------------------------------------------------
-- Hier stehen alle Funktionen, die fuer die Partitionierung
-- und die Darstellung von Partitionen (bzw. deren
-- Strukturierung zur weiteren Verarbeitung der Partitionen).
---------------------------------------------------------------

data TPart = TPart (Int , [TPart])
             deriving (Show,Eq)

type LPart = ([Int] , [TPart])

{- getIntFromTPart liefert den Int-Wert des Tupels einer TPart -}
getIntFromTPart (TPart (i , _)) = i

{- part erstellt eine Liste verschachtelter k-stelliger
   Partitions-Mengen (vom Typ TPart) ueber n -}
part :: Int ->Int ->[TPart]

part n k
  | (n < k)            = []
  | (n < 1) || (k < 1) = []
  | (k == 1)           = [TPart (n,[])]
  | otherwise          = let makePart x =  TPart (x , (part (n-x) (k-1)))
                            in map makePart [1..(n-k+1)]

{- p2l entschachtelt eine Menge von Partition vom Typ TPart
   und haengt jede einzelne dieser Partitionen als Liste von
   Int-Werten an die uebergebene Liste an. -}
p2l :: [[Int]]->TPart->[[Int]]

p2l xs (TPart (i,pList))
  | ((xs == []) && (pList == [])) = [[i]]
  | ((xs == []) && (pList /= [])) = concat (map (p2l [[i]]) pList)
  | ((xs /= []) && (pList == [])) = ls
  | otherwise = concat (map (p2l (mapTakeL ls)) pList)

  where ls = [x ++ [i] | x <- xs]
        takeL c = take (length pList) (repeat c)
        mapTakeL a = concat (map takeL a)

{- erstellt eine List aller k-stelligen Partitionen ueber n,
   die ihrerseits als Listen von Int-Werten dargestellt werden -}
getPartitions n k = nub (concat (map (p2l []) (part n k)))


-- preds-section ----------------------------------------------
---------------------------------------------------------------
-- Hier stehen alle fuer die Behandlung und Auswertung von
-- Praediktaen wichtigen Funktionen.
---------------------------------------------------------------

data Pred = Pred PRED_NAME PRED_TYPE
             deriving (Show,Eq)

type PredList = [Pred]

{- getPredDecls liest aus dem zeilenweise gelisteten Body eines
   .env.txt-Files die Pred-Decls. und gibt diese in Form einer
   Liste von Strings ohne Semikolons wieder.-}
getPredDecls b []       = []

getPredDecls b (x:xs)
  | ((b == False) && (not(x == "preds"))) = getPredDecls False xs
  | (x == "preds")       = getPredDecls True xs
  | ((b == True) && (x == ""))        = []
  | otherwise          = (delSemis x):(getPredDecls True xs)

{- getPreds liest aus einer Pred-Decl die noetigen Infos und
   gibt diese in Form vom Typ Pred zurueck -}
getPreds str
  -- null-stellige Preds
  | (elem '(' str) = Pred (getPredName str) (Pred_type [] [])
  -- sonstige Preds
  | otherwise      = Pred (getPredName str)
                          (Pred_type (readPredSorts str) [])

{- getPredName liest aus einer Pred-Decl den Namen des
   Praedikats und wandelt diesen in eine Id um. -}
getPredName str = str2Id (takeWhile isNoColon str)

{- readPredSorts liest aus einer Pred-Decl die
   "Parameter"-Sorten des Praedikats, wandelt diese in Ids um
   und gibt sie als Liste von SORT zurueck. -}
readPredSorts str = if not(elem '*' str) then
                        getParam (dropName str)
                         else
                            getParamList (dropName str)

  where getParam str = [str2Id str]
        dropName str = tail (dropWhile isNoColon str)
        dropParam str = tail (dropWhile isNoAst str)
        isNoAst c = not(c == '*')
        getParamList str = if (elem '*' str) then
                               (str2Id (takeWhile isNoAst str))
                                 :(getParamList (dropParam str))
                            else
                               getParam str

{- getPredList erstellt aus dem zeilenweise gelisteten body
   eine Liste aller deklarierten Praedikate. -}
getPredList body = map getPreds (getPredDecls False body)

{- getPredSorts liefert die Liste der "Parameter"-Sorten des
   uebergebenen Praedikats -}
getPredSorts (Pred p_name (Pred_type s_list pos_list)) = s_list

{- isZeroPred liefert True, wenn das uebergebene Praedikat
   null-stellig ist, sonst gibt die Fkt. False zurueck. -}
isZeroPred (Pred pred_name (Pred_type xs pos_list)) = (xs == [])


-- Formeln zaehlen ... ----------------------------------------
---------------------------------------------------------------
-- Hier stehen alle Funktionen, die fuer das Zaehlen von
-- Formeln von Bedeutung sind.
---------------------------------------------------------------

{- sum2Part berechnet das Produkt der Anzahl der Terme aller
   Sorten, wobei die jeweiligen Laengen der beiden Terme als
   eine  List (Partition) von zwei Int-Werten uebergeben werden.
   env   ist die Sort-#Var-Map fuer die Zaehlung
   ind   relevanter Sort_Op_Index
   s_map relevante Sort_Map
   b0 -  wenn True, so wird T(x) fuer jede Sorte mit (T(y)-1)
         multipliziert (ist manchmal wichtig, wenn x == y), sonst
         wird (fuer alle Sorten) T(x)*T(y) berechnet
   b1    True, wenn nur totale Terme gezaehlt werden
   b2    True, wenn Einbettung in direkte Obersorten mitgezaehlt
         wird.
   [x,y] Partition mit den entspr. Laengen der Terme
-}
sum2Part :: Env ->Sort_Op_Index ->Sort_Map ->Bool ->Bool ->Bool ->[Int] ->Int

sum2Part env ind s_map b0 b1 b2 [x,y] =
            if b0 then
             (sum (map (cntTerm x env ind s_map b1 b2) (keysFM s_map))) *
               (sum (map (-1+) (map (cntTerm y env ind s_map b1 b2)
                                    (keysFM s_map))))
             else
               (sum (map (cntTerm x env ind s_map b1 b2) (keysFM s_map))) *
                 (sum (map (cntTerm y env ind s_map b1 b2) (keysFM s_map)))

{- wie sum2Part, bloss dass hier lediglich die Summen
   der partiellen Terme miteinander multipliziert werden. -}
sum2Part_p_p :: Env ->Sort_Op_Index ->Sort_Map ->Bool ->Bool ->[Int] ->Int

sum2Part_p_p env ind s_map b0 b2 [x,y] =
            if b0 then
             (sum (map (count_partial_terms x env ind s_map b2)
                       (keysFM s_map)))
             * (sum (map (-1+)
                  (map (count_partial_terms y env ind s_map b2)
                       (keysFM s_map))))
             else
               (sum (map (count_partial_terms x env ind s_map b2)
                         (keysFM s_map)))
               * (sum (map (count_partial_terms y env ind s_map b2)
                           (keysFM s_map)))

{- wie sum2Part, bloss dass hier eine Summe von totalen Termen
   mit einer Summe von partiellen Termen multipliziert wird. -}
sum2Part_t_p :: Env ->Sort_Op_Index ->Sort_Map ->Bool ->[Int] ->Int

sum2Part_t_p env ind s_map b2 [x,y] =
                (sum (map (count_total_terms x env ind s_map b2)
                          (keysFM s_map)))
                * (sum (map (count_partial_terms y env ind s_map b2)
                            (keysFM s_map)))

{- hier wird die Anzahl der Praedikate der Laenge n bezuegl.
   der entsprechenden Parameter berechnet:
   n     - Laenge der Praedikate
   env   - Sort-#Var-Map
   predList - Liste aller deklarierten Praedikate
   soInd - entsprechender Sort_Op_Index
   sMap  - entsprechende Sort_Map
   t     - True, wenn nur totale Terme gezaehlt werden
   sub_B - True, wenn Einbettung in Obersorten mitgezaehlt wird
-}
predicates n env predList soInd sMap t sub_B =
                  sum (map (sumPred (n-1) env soInd sMap t sub_B) predList)

  where sumPred m e ind s_map b1 b2 pred =
                  let sList = getPredSorts pred
                      partList = getPartitions m (length sList)
                   in
                      if ((length sList) > m) then
                         0
                       else
                         sumPart e sList partList ind s_map b1 b2

{- hier wird die Anzahl der Formeln mit starker Gleichheit
   der Laenge n bezuegl. der entsprechenden Parameter berechnet:
   n     - Laenge der Formeln
   env   - Sort-#Var-Map
   predList - Liste aller deklarierten Praedikate
   soInd - entsprechender Sort_Op_Index
   sMap  - entsprechende Sort_Map
   t     - True, wenn nur totale Terme gezaehlt werden
   sub_B - True, wenn Einbettung in Obersorten mitgezaehlt wird
-}
strong_Eq n env soInd sMap t sub_B =
                  let partList1 = filter cond1 (getPartitions (n-1) 2)
                      partList2 = filter cond2 (getPartitions (n-1) 2)
                      cond1 xs = (head xs) < (last xs)
                      cond2 xs = (head xs) == (last xs)
                   in
                      (sum (map (sum2Part env soInd sMap False t sub_B)
                                partList1))
                      + (sum (map (sum2Part env soInd sMap True t sub_B)
                                  partList2))


{- hier wird die Anzahl der Formeln mit schwacher Gleichheit
   der Laenge n bezuegl. der entsprechenden Parameter berechnet:
   n     - Laenge der Formeln
   env   - Sort-#Var-Map
   predList - Liste aller deklarierten Praedikate
   soInd - entsprechender Sort_Op_Index
   sMap  - entsprechende Sort_Map
   t     - True, wenn nur totale Terme gezaehlt werden
   sub_B - True, wenn Einbettung in Obersorten mitgezaehlt wird
-}
weak_Eq n env soInd sMap t sub_B =
                  let partList0 = getPartitions (n-1) 2
                      partList1 = filter cond1 (getPartitions (n-1) 2)
                      partList2 = filter cond2 (getPartitions (n-1) 2)
                      cond1 xs = (head xs) < (last xs)
                      cond2 xs = (head xs) == (last xs)
                   in
                      if t then
                         0
                       else
                         (sum (map (sum2Part_t_p env soInd sMap sub_B)
                                    partList0))
                         + (sum (map (sum2Part_p_p env soInd sMap False sub_B)
                                      partList1))
                         + (sum (map (sum2Part_p_p env soInd sMap True sub_B)
                                      partList2))

{- hier wird die Anzahl der Formeln mit Definiertheit
   der Laenge n bezuegl. der entsprechenden Parameter berechnet:
   n     - Laenge der Formeln
   env   - Sort-#Var-Map
   predList - Liste aller deklarierten Praedikate
   soInd - entsprechender Sort_Op_Index
   sMap  - entsprechende Sort_Map
   t     - True, wenn nur totale Terme gezaehlt werden
   sub_B - True, wenn Einbettung in Obersorten mitgezaehlt wird
-}
definedness n env soInd sMap t sub_B =
                  let s_list = keysFM sMap
                   in
                      if t then
                         0
                       else
                         sum
                          (map (count_partial_terms (n-1) env soInd sMap sub_B)
                                s_list)

{- hier wird die Anzahl der Formeln mit Zugehoerigkeit zu einer
   Sorte der Laenge n bezuegl. der entsprechenden Parameter
   berechnet:
   n     - Laenge der Formeln
   env   - Sort-#Var-Map
   predList - Liste aller deklarierten Praedikate
   soInd - entsprechender Sort_Op_Index
   sMap  - entsprechende Sort_Map
   t     - True, wenn nur totale Terme gezaehlt werden
   sub_B - True, wenn Einbettung in Obersorten mitgezaehlt wird
-}
membership n env soInd sMap t sub_B =
                  let s_list = keysFM sMap
                      x = length s_list
                      terms = sum (map (cntTerm (n-1) env soInd sMap t sub_B)
                                        s_list)
                   in
                      x * terms

{- hier wird die Anzahl der Formeln mit Konjunktion, Disjunktion,
   Aequivalenz und Implikation der Laenge n bezuegl. der
   entsprechenden Parameter berechnet:
   n     - Laenge der Formeln
   env   - Sort-#Var-Map
   predList - Liste aller deklarierten Praedikate
   soInd - entsprechender Sort_Op_Index
   sMap  - entsprechende Sort_Map
   t     - True, wenn nur totale Terme gezaehlt werden
   sub_B - True, wenn Einbettung in Obersorten mitgezaehlt wird
   ex_U  - True, wenn unaere Existenz beruecksichtigt wird
-}
connectives n env pList soInd sMap t sub_B ex_U =
                  let partList1 = filter cond1 (getPartitions (n-1) 2)
                      partList2 = filter cond2 (getPartitions (n-1) 2)
                      partList3 = filter cond3 (getPartitions (n-1) 2)
                      cond1 xs = (head xs) < (last xs)
                      cond2 xs = (head xs) == (last xs)
                      cond3 xs = (head xs) /= (last xs)
                   in -- conjunction + disjunction + equivalence
                      3 * (sum
                           (map (multForm env pList soInd sMap t sub_B ex_U)
                                 partList1)
                          + sum
                            (map (multFormEq env pList soInd sMap t sub_B ex_U)
                                  partList2))
                           -- + implication
                        +  sum
                           (map (multForm env pList soInd sMap t sub_B ex_U)
                                 partList3)
                        +  sum
                           (map (multFormEq env pList soInd sMap t sub_B ex_U)
                                 partList2)

  where multForm e preds ind s_map b1 b2 b3 [x,y] =
                  (countF x e preds ind s_map b1 b2 b3) *
                  (countF y e preds ind s_map b1 b2 b3)
        multFormEq e preds ind s_map b1 b2 b3 [x,y] =
                  (countF x e preds ind s_map b1 b2 b3) *
                  ((countF y e preds ind s_map b1 b2 b3) - 1)

{- hier wird die Anzahl der Formeln mit Negation der Laenge n
   bezuegl. der entsprechenden Parameter berechnet:
   n     - Laenge der Formeln
   env   - Sort-#Var-Map
   predList - Liste aller deklarierten Praedikate
   soInd - entsprechender Sort_Op_Index
   sMap  - entsprechende Sort_Map
   t     - True, wenn nur totale Terme gezaehlt werden
   sub_B - True, wenn Einbettung in Obersorten mitgezaehlt wird
   ex_U  - True, wenn unaere Existenz beruecksichtigt wird
-}
negation n env pList soInd sMap t sub_B ex_U =
                  countF (n-1) env pList soInd sMap t sub_B ex_U

{- hier wird die Anzahl der Formeln mit Quantoren der Laenge n
   bezuegl. der entsprechenden Parameter berechnet:
   n     - Laenge der Formeln
   env   - Sort-#Var-Map
   predList - Liste aller deklarierten Praedikate
   soInd - entsprechender Sort_Op_Index
   sMap  - entsprechende Sort_Map
   t     - True, wenn nur totale Terme gezaehlt werden
   sub_B - True, wenn Einbettung in Obersorten mitgezaehlt wird
   ex_U  - True, wenn unaere Existenz beruecksichtigt wird
-}
quantification n env pList soInd sMap t sub_B ex_U =
            let s_list = keysFM sMap
             in
                if ex_U then
                   3 *
                   (sum
                     (map (cntF_x_env (n-1) env pList soInd sMap t sub_B ex_U)
                           s_list))
                 else
                   2 *
                   (sum
                     (map (cntF_x_env (n-1) env pList soInd sMap t sub_B ex_U)
                           s_list))

  where xEnv e s = addToFM_C addX e s 1
        addX x y = x + y
        cntF_x_env m e preds ind s_map b1 b2 b3 s =
                  countF m (xEnv e s) preds ind s_map b1 b2 b3

{- countForm :
   Dach- und Ausgabe-Funktion fuer das Zaehlen von Formeln
   Aufruf der Funktion:
            countForm n file t sub_B ex_U

            wobei: n     - Laenge der Formeln
                   file  - .env.txt-File mit der Signatur
                   t     - True, wenn nur die totalen
                           Terme gezaehlt werden sollen
                           sonst False
                   sub_B - True, wenn auch Einbettung in die
                           direkten Obersorten mitgezaehlt
                           werden soll, sonst False
                   ex_U  - True, wenn bei den Quantoren auch
                           unaere Existenz mitgezaehlt
                           werden soll, sonst False
   Das Ergebnis wird durch die Funktion print ausgegeben.
-}
countForm 0 file t sub_B ex_U = print 0

countForm 1 file t sub_B ex_U =
                  do { inp <- readFile file
                     ; let body = getBody (lines inp)
                     ; print (length (filter isZeroPred (getPredList body)))
                     }

countForm n file t sub_B ex_U =
             do { inp <- readFile file
                ; let body = getBody (lines inp)
                      soInd = getSortOpIndex body
                      sMap = getSortMap body
                      env = initEnv sMap
                      pList = getPredList body
                ; print (countF n env pList soInd sMap t sub_B ex_U)
                }

{- countF ist die eigentliche Formel-Zaehlfunktion:
   n     - Laenge der zu zaehlenden Terme
   env   - FiniteMap Sorte <# Variablen der Sorte als Int>
   pList - Liste aller deklarierten Praedikate
   soInd - zugrundeliegender Sort_Op_Index
   sMap  - zugrundeliegende Sort_Map
   t     - True, wenn nur totale Terme gezaehlt werden sollen
   sub_B - True, wenn Einbettung in direkte Obersorten
           beruecksichtigt werden soll
   ex_U  - True, wenn bei den Quantoren auch
           unaere Existenz mitgezaehlt
           werden soll, sonst False
-}
countF:: Int ->Env ->[Pred] ->Sort_Op_Index ->Sort_Map ->Bool ->Bool ->Bool ->Int

countF n env pList soInd sMap t sub_B ex_U =
                  predicates n env pList soInd sMap t sub_B       +
                  strong_Eq n env soInd sMap t sub_B              +
                  weak_Eq n env soInd sMap t sub_B                +
                  definedness n env soInd sMap t sub_B            +
                  membership n env soInd sMap t sub_B             +
                  connectives n env pList soInd sMap t sub_B ex_U +
                  negation n env pList soInd sMap t sub_B ex_U    +
                  quantification n env pList soInd sMap t sub_B ex_U

{- Hilfs-Fkt., die aus einer Sort_Map eine (leere)
   Sort_#Var_Map erzeugt. d.h. alle Sorten haben darin
   0 (null) Variablen.
-}
initEnv sMap = let s_list = keysFM sMap
                in
                   listToFM (zip s_list (replicate (length s_list) 0))

----------------- Benutzer-Schnittstelle-----------------------

{- ist eine Hilfsfunktion, die die Eingabe einer Text-Zeile
   als Wert vom Typ Int interpretiert -}
getInt = do line <- getLine
            return (read line :: Int)

{- die Funktion zaehler stellt die Schnittstelle fuer den
   Benutzer dar. Alle relevanten Angaben werden vom Benutzer
   erfragt und dann ueber die entsprechenden
   Interface-Funktionen ausgewertet bzw. weitergereicht -}
zaehler = do { putStr "\nProgramm zum zaehlen von Termen und Formeln\n"
             ; putStr "fuer CASL-Spezifikationen V0.9\n"
             ; putStr "\nHinweis: Der Zaehler arbeitet nur auf *.env.txt-files\n"
             ; putStr "\n Sollen Terme oder Formeln gezaehlt werden? (t/f , default: t)\n"
             ; c0 <- getLine
             ; putStr "\nGib die Datei an, die die Spezifikation enthaelt:\n"
             ; file <- getLine
             ; putStr "\nSollen nur totale Terme beruecksichtigt werden? (y/n , default: n)\n"
             ; c1 <- getLine
             ; putStr "\nSoll Einbettung in die Obersorten beruecksichtigt werden? (y/n , default: n)\n"
             ; c2 <- getLine
             ; if ((c0 == "f") || (c0 == "F")) then
                  do { putStr "\n Soll unaere Existenz beruecksichtigt werden? (y/n , default: n)\n"
                     ; c3 <- getLine
                     ; putStr "\nGib die Laenge der Formeln an:\n"
                     ; n <- getInt
                     ; putStr "\nDas Ergebnis der Zaehlung lautet "
                     ; if ((c1 == "y") || (c1 == "Y")) then
                          if ((c2 == "y") || (c2 == "Y")) then
                             if ((c3 == "y") || (c3 == "Y")) then
                                countForm n file True True True
                              else
                                countForm n file True True False
                           else
                             if ((c3 == "y") || (c3 == "Y")) then
                                countForm n file True False True
                              else
                                countForm n file True False False
                        else
                          if ((c2 == "y") || (c2 == "Y")) then
                             if ((c3 == "y") || (c3 == "Y")) then
                                countForm n file False True True
                              else
                                countForm n file False True False
                           else
                             if ((c3 == "y") || (c3 == "Y")) then
                                countForm n file False False True
                              else
                                countForm n file False False False
                     }
                else
                  do { putStr "\nGib die Laenge der Terme an:\n"
                     ; n <- getInt
                     ; putStr "\nGib die Sorte an, der die Terme angehoeren sollen:\n"
                     ; sort <- getLine
                     ; putStr "\nDas Ergebnis der Zaehlung lautet "
                     ; if ((c1 == "y") || (c1 == "Y")) then
                          if ((c2 == "y") || (c2 == "Y")) then
                             countTerm n sort file True True
                           else
                             countTerm n sort file True False
                        else
                          if ((c2 == "y") || (c2 == "Y")) then
                             countTerm n sort file False True
                           else
                             countTerm n sort file False False
                     }
             }


-- "lexikalische" Hilfsfunktionen ------------------------------

{- delSpaces entfernt alles Leerzeichen aus einem String -}
delSpaces []      = []
delSpaces (x:str)
  | (x == ' ')     = delSpaces str
  | otherwise      = x:(delSpaces str)

{- delSemis entfernt alle Semikolons aus einem String -}
delSemis []       = []
delSemis (x:str)
  | (x == ';')     = delSemis str
  | otherwise      = x:(delSemis str)

{- getBody entfernt alles ausser dem "Body" (bis zu den
   "Axioms") aus der zeilenweisen String-Liste (die man
   durch die Funktion lines erhaelt) vom Inhalt eines
   .env.txt-Files
   Dabei werden in jeder Zeile alle Leerzeichen
   geloescht -}
getBody (x:xs)
  | (x == "Body:") = cutRest "" xs
  | otherwise      = getBody xs

  where cutRest str (x:xs) = if (x == str) then
                                 [""]
                              else
                                 (delSpaces x):(cutRest str xs)

{- Wandelt einen String in eine Id um indem der String
   an die erste Stelle der Token-Liste der Id gesetzt wird -}
str2Id str = Id [Token str nullPos] [] []

{- Umkehr-Funktion von str2Id
   - bisher nur zu Testzwecken gebraucht -}
id2Str (Id [Token str pos] _ _) = str

{- True wenn c kein Doppelpunkt ist -}
isNoColon c = not(c == ':')


----------------- Test-Section --------------------------------
{-

testBody = getBody (lines "Body:\nsorts\n  s1;\n  s2;\n  m;\n  s;\n  m,s < t;\n  t < u\n  s2\nops\n  o : s1;\n  p : s1->?s2;\n  q : s1*s2->s2;\n  schwachsinn : ?s2\npreds\n  p1 : s1;\n  p2 : s1*s2;\n  p_null : ()\n\nAxioms:\n \n")

testGetListForFM = getListForFM (getSortList (getSortDecls testBody))
                             (getSubSortDecls (getSortDecls testBody))


pred_zaehler = do { putStr "\nPred-Zaehler fuer CASL-Spezifikationen V0.4\n"
                  ; putStr "\nHinweis: Der Zaehler arbeitet nur auf *.env.txt-files\n"
                  ; putStr "\nGib die Laenge der Praedikate an:\n"
                  ; n <- getInt
                  ; putStr "\nGib die Datei an, die die Spezifikation enthaelt:\n"
                  ; file <- getLine
                  ; putStr "\nSollen nur totale Terme gezaehlt werden? (y/n)\n"
                  ; c1 <- getLine
                  ; putStr "\nSoll Einbettung in die Obersorten beruecksichtigt werden? (y/n)\n"
                  ; c2 <- getLine
                  ; putStr "\nDas Ergebnis der Zaehlung lautet "
                  ; if ((c1 == "y") || (c1 == "Y")) then
                       if ((c2 == "y") || (c2 == "Y")) then
                          testFCount n file True True
                        else
                          testFCount n file True False
                     else
                       if ((c2 == "y") || (c2 == "Y")) then
                          testFCount n file False True
                        else
                          testFCount n file False False
                  }


testFCount n file t sub_B =
                        do { inp <- readFile file
                           ; let body = getBody (lines inp)
                                 sMap = getSortMap body
                                 env  = initEnv sMap
                                 soInd = getSortOpIndex body
                                 h_s_map = getHSMap sMap
                           -- Test-Informationen <start>
                           {-
                           ; putStr ("\nSubsort-Map :\n")
                           ; print (fmToList sort_map)
                           ; putStr ("\nSupersort-Map :\n")
                           ; print (fmToList h_s_map)
                           ; putStr ("\n")
                           -}
                           -- ; print (fmToList sort_op_index)
                           -- ; print (getOpList (str2Id "s1") sort_op_index)
                           -- ; putStr ("\n")
                           -- ; print (getOpList (str2Id "s2") sort_op_index)
                           -- \Test-Informationen <end>
                           ; print (predicates n env (getPredList body) soInd sMap t sub_B)
                           }

-- parse-Aufruf -----------------------------------------------

parse file  = do { inp <- readFile file
                 ; putStr (head (getBody (lines inp)))
                 ; putStr "\n"
                 }

-}
