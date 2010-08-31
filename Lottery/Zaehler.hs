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

   Zaehler.hs ist ein Programm zum wahlweisen Zaehlen von Formeln
              und Termen die ueber CASL-Spezifikationen gebildet
              werden koennen.

   README     enthaelt weitere Informationen zu diesem Programm.

   Stand:     13.08.2002

   Autoren:   Markus Bandt
              Lutz Schröder
-}

module Zaehler where

import FiniteMap
import List
import Id
import AS_Basic_CASL


type Sort_Map = FiniteMap SORT [SORT]

type Sort_Op_Index = FiniteMap SORT [Ops]

data Ops = Ops OP_NAME OP_TYPE
           deriving (Show,Eq)

data Pred = Pred PRED_NAME PRED_TYPE
             deriving (Show,Eq)

type PredList = [Pred]

-- LS: <begin>

data Sign = Sign {
        sort_map :: Sort_Map,
        sort_op  :: Sort_Op_Index
        }

data ExtSign = ExtSign {
        sign    :: Sign,
        pList   :: PredList
        }

data Options = Options {
        totalOnly, countDowncasts :: Bool
        }

data ExtOptions = ExtOptions {
        options :: Options,
        countUEx :: Bool
        }

-- LS: <end>


type Env = FiniteMap SORT Int

-- Signature-Section (LS) --------------------------------------

{-getSign erstellt Signatur zu Body -}
getSign :: [String] -> Sign
getSign body = Sign {
        sort_map = getSortMap body,
        sort_op = getSortOpIndex body
        }

{-getESign erstellt erweiterte Signatur zu Body -}

getESign :: [String] -> ExtSign

getESign body = ExtSign {
        sign = getSign body,
        pList = getPredList body
        }

-- Sort-Section ------------------------------------------------

{- getSortMap erstellt eine FiniteMap aller im Body deklarierten
   Sorten und jeweils einer Liste der direkten Subsorten.
   Wird auf die Liste von Strings nach getBody angewandt!-}
getSortMap (x:xs)
  -- erst pruefen, ob ueberhaupt Sorten deklariert werden
  | ((x /= "sorts") && (x /="sort")) = emptyFM
  | otherwise         =
      let sd = getSortDecls xs
        in
          listToFM ( getListForFM (getSortList sd) (getSubSortDecls sd))


{- getSuperSorts liefert eine Liste aller direkten Obersorten
   von s, die in sMap (Sort_Map mit Sort - [Subsort])
   eingetragen sind. -}
getSuperSorts s sMap =
  let
    isSubSort a b = elem a (getSubSorts b sMap)
  in
    filter (isSubSort s) (getSorts sMap)

{- getSorts liefert eine Liste aller Sorten, die in sMap
   eingetragen sind. -}
getSorts sMap = keysFM sMap


{- getSubSorts liefert eine Liste der direkten Subsorten von
   Sorte s in der Sort_Map sMap -}
getSubSorts s sMap = lookupWithDefaultFM sMap [] s

{- Zieht alle Sorten-Deklarationen aus der Body-String-Liste
   heraus, loescht in jedem String evtl. vorhandene Semikolons
   und gibt sie als Liste von Strings zurueck -}
getSortDecls (x:xs)
  | ((x == "sorts") || (x == "sort")) = getSortDecls xs
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

{- setSubSorts sucht aus einer Liste von Subsorten-Deklarationen
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

{- Hilfs-Fkt., die aus einer Sort_Map eine (leere)
   Sort_#Var_Map erzeugt. d.h. alle Sorten haben darin
   0 (null) Variablen.
-}
initEnv soInd = let s_list = keysFM soInd
                in
                   listToFM (zip s_list (replicate (length s_list) 0))


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


-- Term counting  ---------------------------------------------
---------------------------------------------------------------

{- countTerm :
   Dach- und Ausgabe-Funktion fuer das Zaehlen von Termen
   Aufruf der Funktion:
            countTerm n sort file opt

            wobei: n     - Laenge der Terme
                   sort  - Sorte der Terme
                   file  - .env.txt-File mit der Signatur
                   opt   - Optionen

   Das Ergebnis wird durch die Funktion print ausgegeben.
-}
countTerm n sort file opt =
                  do { inp <- readFile file
                     ; let body = getBody (lines inp)
                           sg = getSign body
                           soInd = sort_op sg
                           s = str2Id sort
                           env = initEnv soInd
                     -- Test-Informationen <begin>
                     ; putStr ("\nSubsort-Map :\n")
                     ; print (fmToList (sort_map sg))
                     ; putStr ("\nEnv-Map :\n")
                     ; print (fmToList env)
                     ; putStr ("\n")
                     ; putStr ("Sort-Op-Index:\n")
                     ; print (fmToList soInd)
                     ; putStr ("\n Op-List der Sorte Bool:\n")
                     ; print (getOpList (str2Id "Bool") soInd)
                     ; putStr ("\n")
                     -- \Test-Informationen <end>
                     ; print (cntTerm n env sg opt s)
                     }

{- cntTerm ist die eigentliche Term-zaehl-Fkt.
   n     - Laenge der zu zaehlenden Terme
   env   - FiniteMap Sorte <# Variablen der Sorte als Int>
   sg  - zugrundeliegene Signatur
   opt   - geltende Options
   s     - die Sorte der zu zaehlenden Terme
-}
cntTerm:: Int ->Env ->Sign ->Options ->SORT ->Int


cntTerm n env sg opt s
  | (n <= 0)  = 0
  | (n == 1)  = cntCon s env soInd t -- Necessary, since this counts
                                     -- Variables as well
  | otherwise = let sMap = sort_map sg
                    list = getOpList s soInd
                    op_list =
                      [op | op <- list, 0 < (numPS op), (numPS op) <= (n-1)]
                    f_op_list =
                      if t
                        then (filter isTotalOp op_list)
                          else op_list
                    upcasts = sum (map (cntTerm (n-1) env sg opt)
                                       (getSubSorts s sMap))
                    downcasts = sum (map (cntTerm (n-1) env sg opt)
                                         (getSuperSorts s sMap))
                    op_terms  = sum (map (sumOp (n-1) env sg opt)
                                       f_op_list)
                 in
                   op_terms
                   + upcasts
                   + (if (countDowncasts opt) then downcasts else 0)
  where numPS op = length(getOpPS op)
        sumOp m e sg2 opt2 op =
              termTuples m e sg2 opt2 (getOpPS op)
        soInd = sort_op sg
        t = totalOnly opt

-- termTuples counts tuples of Terms of given sorts and given
-- overall length

termTuples :: Int -> Env -> Sign -> Options -> [SORT] -> Int

termTuples n env sg opt [] = if (n == 0) then 1 else 0 -- should never occur
termTuples n env sg opt [st] = cntTerm n env sg opt st
termTuples n env sg opt (st:sts) = bigsum
    1 (n - (length sts))
        (\m -> (cntTerm m env sg opt st)
             * (termTuples (n - m) env sg opt sts))


{- cntCon zaehlt die Konstanten der Sorte s im Sort_Op_Index ind.
   Wenn t True ist, so werden nur totale Konstanten gezaehlt,
   ist t False, so werden alle Konstanten gezaehlt.
   Zur Anzahl der Konstanten werden noch die Variablen der Sorte
   s in env hinzugezaehlt.
-}
cntCon s env soInd t =
                  let list = getOpList s soInd
                      vars = lookupWithDefaultFM env 0 s
                      conList = [op | op <- list, (getOpPS op) == [] ]
                      cntAll = length (conList)
                      cntTotal = length (filter isTotalOp conList)
                  in
                    (if t then cntTotal else cntAll) + vars

{- getOpList liefert die Liste der Operationen mit der
   Zielsorte s im Sort_Op_Index ind (Hilfsfunktion) -}
getOpList s soInd = lookupWithDefaultFM soInd [] s

-- count partial Terms
-- Arguments as usual, including unnecessarily the totalOnly option

count_partial_terms n env sg opt sort =
  let ct = cntTerm n env sg   -- partial evaluation!
    in
      if (totalOnly opt)
        then 0
        else
          (ct opt sort) - (ct opt{totalOnly = True} sort)


-- preds-section ----------------------------------------------
---------------------------------------------------------------
-- Hier stehen alle fuer die Behandlung und Auswertung von
-- Praediktaen wichtigen Funktionen.
---------------------------------------------------------------


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

{- countForm :
   Dach- und Ausgabe-Funktion fuer das Zaehlen von Formeln
   Aufruf der Funktion:
            countForm n file opt ex_U

            wobei: n     - Laenge der Formeln
                   file  - .env.txt-File mit der Signatur
                   eopt   - gueltige ExtOptions

   Das Ergebnis wird durch die Funktion print ausgegeben.
-}
countForm n file eopt =
             do { inp <- readFile file
                ; let body = getBody (lines inp)
                      esg = getESign body
                      soInd = sort_op (sign esg)
                      {-
                         sMap = sort_map sg
                      -}
                      env = initEnv soInd
                -- Test-Informationen <begin>
                {-
                ; putStr ("\nSubsort-Map :\n")
                ; print (fmToList sMap)
                ; putStr ("\nEnv-Map :\n")
                ; print (fmToList env)
                ; putStr ("\n")
                ; putStr ("Sort-Op-Index:\n")
                ; print (fmToList soInd)
                ; putStr ("\n Op-List der Sorte Bit:\n")
                ; print (getOpList (str2Id "Bit") soInd)
                ; putStr ("\n")
                -}
                ; print (quantification n env esg eopt)
                ; print (countF (n-1) (addToFM_C (+) env (str2Id "Bool") 1) esg eopt)
                -- \Test-Informationen <end>
                ; print (countF n env esg eopt)
                }

{- countF ist die eigentliche Formel-Zaehlfunktion:
   n     - Laenge der zu zaehlenden Terme
   env   - FiniteMap Sorte <# Variablen der Sorte als Int>
   esg - underlying extended signature
   eopt  - extended options
-}
countF:: Int ->Env ->ExtSign ->ExtOptions ->Int

countF n env esg eopt
  | (n <= 0)  = 0
  | (n == 1)  = length (filter isZeroPred pl)
  | otherwise =   predicates n env esg eopt
                + strong_Eq n env sg opt
                + exist_Eq n env sg opt
                + definedness n env sg opt
                + membership n env sg opt
                + connectives n env esg eopt
                + negation n env esg eopt
                + quantification n env esg eopt
        where pl = pList esg
              sg = sign esg
              opt = options eopt

{- hier wird die Anzahl der Praedikate der Laenge n bezuegl.
   der entsprechenden Parameter berechnet:
   n     - Laenge der Praedikate
   env   - Sort-#Var-Map
   esg - underlying extended signature
   opt   - (simple) options
-}
predicates n env esg eopt =
    sum (map (sumPred (n-1) env (sign esg) (options eopt))
             (filter (\p -> (length (getPredSorts p)) <=
                                        (n - 1)) (pList esg)))
    where sumPred m e sg opt pred =
              termTuples m e sg opt (getPredSorts pred)

{- Number of (strong or existential) equations
   n     - Laenge der Formeln
   env   - Sort-#Var-Map
   sg  - underlying (simple) signature
   opt   - (simple) options
   b     - (Only in generic functions for equations) True if existential
           equations are being counted. Equations where one side is total
           are counted as strong!!
-}
strong_Eq n env sg opt =
  eqs n env sg opt False

exist_Eq n env sg opt =
  if (totalOnly opt)
    then 0
    else eqs n env sg opt True

eqs n env sg opt b =
  let sorts = getSorts (sort_map sg)
    in
      sum (map (sort_eqs n env sg opt b) sorts)

-- sort_eqs counts the equations for a given sort
-- parameters as above, plus the sort

sort_eqs :: Int -> Env -> Sign -> Options -> Bool -> SORT -> Int

sort_eqs n env sg opt b sort =
  bigsum 1 ((n - 1) `div` 2) (sort_eqs_l n env sg opt b sort)

-- sort_strong_eqs_l counts eqs for a sort, given the length of the
-- left formula.

sort_eqs_l :: Int -> Env -> Sign -> Options -> Bool -> SORT -> Int -> Int

sort_eqs_l n env sg opt b sort l =
  let
    r = (n - 1) - l
    ct = if b then count_partial_terms else cntTerm
    nl = (ct l env sg opt sort)
    nr = (ct r env sg opt sort)
      in
        twoElems (l == r) nl nr


{- # of definedness formulas
   n     - Laenge der Formeln
   env   - Sort-#Var-Map
   sg  - underlying (simple) signature
   opt   - (simple) options
-}
definedness n env sg opt =
                  let s_list = getSorts (sort_map sg)
                   in
                      if (totalOnly opt) then
                         0
                       else
                         sum
                          (map (count_partial_terms (n-1) env sg opt)
                                s_list)

{- hier wird die Anzahl der Formeln mit Zugehoerigkeit zu einer
   Sorte der Laenge n bezuegl. der entsprechenden Parameter
   berechnet:
   n     - Laenge der Formeln
   env   - Sort-#Var-Map
   sg  - underlying (simple) signature
   opt   - (simple) options
-}
membership :: Int -> Env -> Sign -> Options -> Int

membership n env sg opt =
  let s_list = getSorts (sort_map sg)
    in
      sum (map (sort_membership n env sg opt) s_list)

-- sort_membership counts the membership formulas for a fixed sort
-- parameters as above, plus the sort

sort_membership :: Int -> Env -> Sign -> Options -> SORT -> Int

sort_membership n env sg opt sort =
  (cntTerm (n - 1) env sg opt sort) *
    (length (getSubSorts sort (sort_map sg)))

{- hier wird die Anzahl der Formeln mit Konjunktion, Disjunktion,
   Aequivalenz und Implikation der Laenge n bezuegl. der
   entsprechenden Parameter berechnet:
   n     - Laenge der Formeln
   env   - Sort-#Var-Map
   esg - underlying extended signature
   eopt  - extended options
-}
connectives n env esg eopt =
  3 *  -- conjunction + disjunction + equivalence
    bigsum 1 ((n - 1) `div` 2) (sym_connectives_l n env esg eopt)
  + bigsum 1 (n - 1) (implication_l n env esg eopt)


-- sym_connectives_l counts the number of formulas with given
-- size of the left side and symmetric and non-doubling junctor

sym_connectives_l n env esg eopt l =
  let
    r = (n - 1) - l
    nl = countF l env esg eopt
    nr = countF r env esg eopt
  in
    twoElems (l == r) nl nr

-- implication_l counts implications with given size of the premise.
-- No A => A, but A => B is different from B => A.

implication_l n env esg eopt l =
  let
    r = (n - 1) - l
    nl = countF l env esg eopt
    nr = countF r env esg eopt
  in
    if (l == r)
      then nl * (nl - 1)
      else nl * nr

{- hier wird die Anzahl der Formeln mit Negation der Laenge n
   bezuegl. der entsprechenden Parameter berechnet:
   n     - Laenge der Formeln
   esg - underlying extended signature
   eopt  - extended options
-}
negation n env esg eopt =
                  countF (n-1) env esg eopt

{- hier wird die Anzahl der Formeln mit Quantoren der Laenge n
   bezuegl. der entsprechenden Parameter berechnet:
   n     - Laenge der Formeln
   env   - Sort-#Var-Map
   esg - underlying extended signature
   eopt  - extended options
-}
quantification n env esg eopt =
            let s_list = getSorts (sort_map (sign esg))
             in
                (if (countUEx eopt) then 3 else 2) *
                   (sum
                     (map (cntF_x_env (n-1) env esg eopt)
                           s_list))

  where xEnv e s = addToFM_C addX e s 1
        addX x y = x + y
        cntF_x_env m e esg2 eopt2 s =
                  (countF m (xEnv e s) esg2 eopt2) - (countF m e esg2 eopt2)


----------------- Benutzer-Schnittstelle-----------------------

{- die Funktion zaehler stellt die Schnittstelle fuer den
   Benutzer dar. Alle relevanten Angaben werden vom Benutzer
   erfragt und dann ueber die entsprechenden
   Interface-Funktionen ausgewertet bzw. weitergereicht -}
zaehler = do { putStr "\nProgramm zum zaehlen von Termen und Formeln\n"
             ; putStr "fuer CASL-Spezifikationen (Version 0.92)\n"
             ; putStr "\nHinweis: Der Zaehler arbeitet nur auf *.env.txt-files\n"
             ; putStr "\nSollen Terme oder Formeln gezaehlt werden? (t/f , default: t)\n"
             ; c0 <- getLine
             ; b0 <- return ((c0 == "f") || (c0 == "F"))
             ; putStr "\nGib die Datei an, die die Ausgabe von CATS\n"
             ; putStr "(im *.env.txt-Format) enthaelt:\n"
             ; file <- getLine
             ; putStr "\nSollen nur totale Terme beruecksichtigt werden? (y/n , default: n)\n"
             ; c1 <- getLine
             ; b1 <- return ((c1 == "y") || (c1 == "Y"))
             ; putStr "\nSollen Downcasts beruecksichtigt werden? (y/n , default: n)\n"
             ; c2 <- getLine
             ; b2 <- return ((c2 == "y") || (c2 == "Y"))
             ; opt <- return Options{
                        totalOnly = b1,
                        countDowncasts = b2
                        }
             ; if b0 then
                  do { putStr "\nSoll eindeutige Existenz beruecksichtigt werden? (y/n , default: n)\n"
                     ; c3 <- getLine
                     ; b3 <- return ((c3 == "y") || (c3 == "Y"))
                     ; putStr "\nGib die Laenge der Formeln an:\n"
                     ; n <- getInt
                     ; putStr "\nDas Ergebnis der Zaehlung lautet "
                     ; countForm n file ExtOptions{
                                          options = opt,
                                          countUEx = b3
                                        }
                   }
                else
                  do { putStr "\nGib die Laenge der Terme an:\n"
                     ; n <- getInt
                     ; putStr "\nGib die Sorte an, der die Terme angehoeren sollen:\n"
                     ; sort <- getLine
                     ; putStr "\nDas Ergebnis der Zaehlung lautet "
                     ; countTerm n sort file opt
                 }
             }

{- getInt ist eine Hilfsfunktion, die die Eingabe einer Text-Zeile
   als Wert vom Typ Int interpretiert -}
getInt = do line <- getLine
            return (read line :: Int)

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

------------ Arithmetic auxiliary functions ---------------------
--- (These are probably in the libraries!!) --------------------

-- bigsum works like the sum symbol: lower bound, upper bound,
-- summand function --> sum

bigsum :: Num a => Int -> Int -> (Int -> a) -> a

bigsum n m f =
        if (m < n)
                then 0
                else (f n) + (bigsum (n + 1) m f)

-- twoElems calculates the number of distinct pairs formed
-- from either one set (True) or two disjoint ones (False)
-- of given sizes

twoElems :: Bool -> Int -> Int -> Int

twoElems b n1 n2 =
  if b
    then ((n1 * (n1 - 1)) `div` 2)
    else n1 * n2


----------------- Test-Section --------------------------------
{-
-- pred_zaehler zaehlt nur die Praedikate, der festgelegten Laenge
-- die mit einer Spezifikation gebildet werden koennen

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
                           -- Test-Informationen <start>
                           {-
                           ; putStr ("\nSubsort-Map :\n")
                           ; print (fmToList sort_map)
                           ; putStr ("\nSupersort-Map :\n")
                           ; putStr ("\n")
                           -- ; print (fmToList sort_op_index)
                           -- ; print (getOpList (str2Id "s1") sort_op_index)
                           -- ; putStr ("\n")
                           -- ; print (getOpList (str2Id "s2") sort_op_index)
                           -}
                           -- \Test-Informationen <end>
                           ; print (predicates n env (getPredList body) soInd sMap t sub_B)
                           }
-}
