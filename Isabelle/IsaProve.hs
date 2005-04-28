
{- |
Module      :  $Header$
Copyright   :  (c) University of Cambridge, Cambridge, England
               adaption (c) Till Mossakowski, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

   Interface for Isabelle theorem prover.
-}
{-
  todo: thy files in subdir
  
  Interface between Isabelle and Hets:
  Hets writes Isabelle .thy file and opens window with button (GUI/HTkUtils.hs, uni/htk/test, ask cxl)
  User extends .thy file with proofs
  User presses button
  Hets reads in user-modified .thy file
  Hets write new .thy file (different name), consisting of
    - original theory (i.e. put theory string into variable)
    - proof part of user-modified file (look for first "\ntheorem")
    - ML code for check_theorem
    - ML "check_theorem \"name1\" \"theorem1\" name.thy"   (name: thName)
      ...
    - ML "check_theorem \"namen\" "\theoremn\" name.thy"
  Hets runs new .thy file in Isar batch mode (system " .... ")
  Hets inspects log file and extracts proven theorems

  fun check_theorem name thm thy =
    aconv(#prop(rep_thm(Drule.freeze_all(get_thm thy name))), snd(read_axm (sign_of thy) (name,thm)))
    handle _ => false;
-}

module Isabelle.IsaProve where

import Logic.Prover
import Isabelle.IsaSign
import Isabelle.IsaPrint
import Isabelle.Translate

import Common.AS_Annotation
import Common.PrettyPrint

import Data.List
import Data.Maybe

import Configuration

import ChildProcess
import Directory
import System

import HTk

isabelleProver :: Prover Sign Sentence () ()
isabelleProver =
     Prover { prover_name = "Isabelle",
              prover_sublogic = "Isabelle",
              prove = isaProve False
            }

isabelleConsChecker :: ConsChecker Sign Sentence IsabelleMorphism ()
isabelleConsChecker =
     ConsChecker { cons_checker_name = "Isabelle-refute",
                   cons_checker_sublogic = "Isabelle",
                   cons_check = \ thn mor -> isaProve True thn (t_target mor) [] }

                 -- input: theory name, theory, goals
                 -- output: proof status for goals and lemmas
isaProve :: Bool -> String -> (Sign,[Named Sentence]) -> [Named Sentence] 
              -> IO([Proof_status ()])
isaProve checkCons thName (sig,axs) goals = do
  ex <- doesFileExist fileName
  exorig <- doesFileExist origName
  case (ex,exorig) of
    (True,True) -> do 
             putStrLn ("diff -u "++origName++" "++fileName++" > "++patchName)
             system ("diff -u "++origName++" "++fileName++" > "++patchName)
             writeFile fileName theory 
             putStrLn ("cp "++fileName++" "++origName)
             system ("cp "++fileName++" "++origName)
             putStrLn ("patch -u "++fileName++" "++patchName)
             system ("patch -u "++fileName++" "++patchName)
             return ()
    (True,False) -> do
             system ("cp "++fileName++" "++fileName++".old")
             writeFile fileName theory 
             system ("cp "++fileName++" "++origName)
             return ()
    (False,_) -> do
             writeFile fileName theory 
             system ("cp "++fileName++" "++origName)
             return ()
  isabelle <- getEnv "HETS_ISABELLE"
  isa <- newChildProcess isabelle [arguments [fileName]]
  t <- createToplevel [text "Proof confirmation window"]
  b <- newButton t [text "Please press me when current theory is proved!",size(50,10)]
  pack b []
  clickedb <- clicked b
  sync (clickedb >>> destroy t)
--  closeChildProcessFds isa
  provedThy <- readFile fileName
  let newThy = withoutThms theory ++ onlyThms provedThy 
                                  ++ checkThm 
                                  ++ concat (map checkThms disGoals)

  writeFile provedName newThy
--   system (isabelle ++ "/isabelle -e "++newThy++" -q HOL" ++ " heap.isa")
  return [] -- ??? to be implemented
  where
      thName' = thName++if checkCons then "_c" else ""
      fileName = thName'++".thy"
      origName = thName'++".orig.thy"
      patchName = thName'++".patch"
      provedName = thName'++"_proved.thy"
      theory = if checkCons then showConsTheory else showTheory
      disAxs = disambiguateSens [] $ nameSens $ transSens axs
      (lemmas, decs) = unzip (map formLemmas disAxs)
      showLemma = if showLemmas sig 
                   then concat lemmas ++ "\n" ++ concat (map (++"\n") decs)
                   else ""
      showAxs = concat $ map ((++"\n") . showSen) (markSimp disAxs)
      disGoals = disambiguateSens disAxs $ nameSens $ transSens goals
      showGoals = concat $ map showGoal disGoals
      getFN = reverse . fst . break (=='/') . reverse
      showGoal goal = (("theorem "++) .  (++"\noops\n") . showSen) goal
      showTheory = thyPath ++ "theory " ++ getFN thName ++ " = " 
                   ++ showPretty sig "\n\naxioms\n" 
                   ++ showAxs ++ "\n" ++ showLemma ++ "\n\n" ++ showGoals
                   ++ "\nend\n"
      withoutThms thy = 
        let thy' = takeWhile (isNotPrefixOf "theorem") (lines thy)
            sub = map subThyName thy'
            subThyName s | "theory" `isPrefixOf` s = 
                              unwords (map subTN (words s))
                         | otherwise = s
            subTN s | s == (getFN thName) = (getFN thName)++"_proved"
                    | otherwise = s
        in (unlines . dropWhile (isNotPrefixOf "theory")) sub
      onlyThms thy = 
        let l = lines thy
            newl = if null l then l
                     else init l ++ [methodSetUp] ++ [last l]
        in (unlines . 
              dropWhile (isNotPrefixOf "theorem")) newl
      isNotPrefixOf t s = (not . (isPrefixOf t)) s
      methodSetUp = "method_setup ML_init = "
                    ++ "\"Method.ctxt_args (fn ctxt => "
                    ++ "((context (ProofContext.theory_of ctxt);"
                    ++ " Method.METHOD (fn thm  => (Simp_tac 1)))))\""
                    ++ " ML_init\n"
      checkThm = "ML \"fun check_theorem name thm =\n" 
                 ++ "let val thy = (the_context())\n"
                 ++ "in aconv(#prop(rep_thm(Drule.freeze_all(get_thm thy "
                 ++ "name))),snd(read_axm (sign_of thy) "
                 ++ "(name,thm))) handle _ => false\n"
                 ++ "end\"\n"
      checkThms thm = "ML \"check_theorem \\\""
                      ++ senName thm ++ "\\\" " 
                      ++ "\\\"" ++ showPretty (sentence thm) "\\\"\"\n " 
      thyPath = "ML \"val hetsLib = (OS.Process.getEnv \\\"HETS_LIB\\\"); \n"
                   ++ "case hetsLib of NONE => add_path \\\".\\\" \n"
                   ++ "| SOME s => add_path (s ^ \\\"/Isabelle\\\")\"\n\n"
      showConsTheory = 
         "theory " ++ getFN thName ++ " = " 
         ++ showBaseSig (baseSig sig) ++" : \n"
         ++ "lemma inconsistent:\n "
         ++ "\"~( (" 
         ++ concat (intersperse " ) & \\\n(" 
               (map (showConsAx . mapNamed freeTypesSen) disAxs))
         ++ ") )\"\nrefute\noops\n\n"
      showConsAx ax = showPretty (sentence ax) ""

markSimp = map (\ax -> ax{senName = senName ax ++ 
	if isSimpRule (senTerm (sentence ax)) then " [simp]" else ""})  

isSimpRule App {funId = Const {termName = "All"}, argId = arg} = isSimpRule (termId arg)
isSimpRule App {funId = Const {termName = "Not"}, argId = arg} = isSimpRule arg
-- hier die argumente noch ueberpruefen?
isSimpRule Const {termName = t} = True

isSimpRule App {funId = App {funId = fun, argId = arg}, argId = arg2} =
	case termName fun of 							
		"op ="    -> (isSimpRule arg) && (isSimpRule arg2)
		"op =="   -> (isSimpRule arg) && (isSimpRule arg2)
		"op &"    -> (isSimpRule arg) && (isSimpRule arg2)
		"op -->"  -> (isSimpRule arg) && (isSimpRule arg2)
		otherwise -> isConst fun && isSimpRule arg && isSimpRule arg2

isSimpRule Free{}  = True
isSimpRule Var{}   = True
isSimpRule Bound{} = True
isSimpRule Abs{}   = False
isSimpRule arg     = False

isConst Const {}   = True
isConst _          = False

-- translate special characters in sentence names
transSens :: [Named a] -> [Named a]
transSens = map (\ax -> ax{senName = concatMap replaceChar $ senName ax})

-- disambiguate sentence names
disambiguateSens :: [Named a] -> [Named a] -> [Named a]
disambiguateSens others axs = reverse $ disambiguateSensAux others axs []

disambiguateSensAux :: [Named a] -> [Named a] -> [Named a] -> [Named a]
disambiguateSensAux _ [] soFar = soFar
disambiguateSensAux others (ax:rest) soFar =
  disambiguateSensAux (ax':others) rest (ax':soFar)
  where
  name' = fromJust $ find (not . flip elem namesSoFar) 
                          (name:[name++show (i :: Int) | i<-[1..]])
  name = senName ax 
  namesSoFar = map senName others
  ax' = ax{senName = name'}


-- output a sentences
showSen :: PrettyPrint a => Named a -> String
showSen s =  (if null (senName s) then "" 
                else senName s++": ")
             ++ "\""++showPretty (sentence s) "\""

-- name unlabeled axioms with "Axnnn"
nameSens :: [Named a] -> [Named a]
nameSens sens = 
  map nameSen (zip sens [1..length sens])
  where nameSen (sen,no) = if senName sen == "" 
                              then sen{senName = "Ax"++show no}
                              else sen

-- form a lemmas from given axiom and add them both to Isabelles simplifier
formLemmas :: Named a -> (String, String)
formLemmas sen = 
  let (sn, ln) = lemmaName (senName sen)
   in
     ("lemmas " ++ ln ++ " = " ++ sn ++ " [simplified]\n",
      dec ln ++ "\n" ++ dec sn)
  where 
  lemmaName s = (s, s++"'")
  dec s = "declare " ++ s ++ " [simp]"


-- remove type constants from a term
freeTypesSen (Sentence t) = Sentence (freeTypesTerm t)

freeTypesTerm :: Term -> Term
--freeTypesTerm (Const "O") = Const "OO"  
--freeTypesTerm (Const c) = Const c 
--freeTypesTerm (Free v) = Free v  
freeTypesTerm (Const "O" t) = Const "OO" (freeTypesTyp t) 
freeTypesTerm (Const c t) = Const c (freeTypesTyp t)
freeTypesTerm (Free v t) = Free v (freeTypesTyp t) 
freeTypesTerm (Abs v ty t f) = Abs (freeTypesTerm v) (freeTypesTyp ty) (freeTypesTerm t) f 
freeTypesTerm (App t1 t2 f) = App (freeTypesTerm t1) (freeTypesTerm t2) f
freeTypesTerm (Case term alts) = 
  Case (freeTypesTerm term) (map freeTypesTermPair alts)
freeTypesTerm (If t1 t2 t3) =
  If (freeTypesTerm t1) (freeTypesTerm t2) (freeTypesTerm t3) 
freeTypesTerm (Let defs body) = 
  Let (map freeTypesTermPair defs) (freeTypesTerm body)
freeTypesTerm (Fix f) =
  Fix (freeTypesTerm f)

freeTypesTermPair (t1,t2) = (freeTypesTerm t1,freeTypesTerm t2)

freeTypesTyp (Type t s _) = TFree t s
freeTypesTyp t = t
