{- |
Module      :  $Header$
Copyright   :  (c) University of Cambridge, Cambridge, England
               adaption (c) Till Mossakowski, Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

Interface for Isabelle theorem prover.
-}
{-
  todo: thy files in subdir

  Interface between Isabelle and Hets:
  Hets writes Isabelle .thy file and opens window with button (GUI/HTkUtils.hs,
    uni/htk/test, ask cxl)
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
    aconv(#prop(rep_thm(Drule.freeze_all(get_thm thy name))),
           snd(read_axm (sign_of thy) (name,thm)))
    handle _ => false;
-}

module Isabelle.IsaProve where

import Logic.Prover
import Isabelle.IsaSign
import Isabelle.IsaPrint
import Isabelle.IsaConsts
import Isabelle.Translate

import Common.AS_Annotation
import Common.PrettyPrint
import Common.DefaultMorphism
import Common.ProofUtils

import Data.List

import ChildProcess
import Directory
import System

import HTk

isabelleProver :: Prover Sign Sentence ()
isabelleProver =
     Prover { prover_name = "Isabelle",
              prover_sublogic = "Isabelle",
              prove = isaProve False
            }

isabelleConsChecker :: ConsChecker Sign Sentence (DefaultMorphism Sign) ()
isabelleConsChecker =
     Prover { prover_name = "Isabelle-refute",
              prover_sublogic = "Isabelle",
              prove = \ thn mor -> isaProve True thn (t_target mor) }

isaProve :: Bool -> String -> Theory Sign Sentence () -> IO([Proof_status ()])
isaProve checkCons thName (Theory sig nSens) = do
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
  newChildProcess isabelle [arguments [fileName]]
  t <- createToplevel [text "Proof confirmation window"]
  b <- newButton t [text "Please press me when current theory is proved!",
                         size(50,10)]
  pack b []
  clickedb <- clicked b
  sync (clickedb >>> destroy t)
  provedThy <- readFile fileName
  let newThy = withoutThms theory ++ onlyThms provedThy
                                  ++ checkThm
                                  ++ concat (map checkThms disGoals)

  writeFile provedName newThy
--   system (isabelle ++ "/isabelle -e "++newThy++" -q HOL" ++ " heap.isa")
  return [] -- ??? to be implemented
  where
      nSens' = prepareSenNames transString (toNamedList nSens)
      (disAxs, disGoals) = partition Common.AS_Annotation.isAxiom nSens'
      thName' = thName++if checkCons then "_c" else ""
      fileName = thName'++".thy"
      origName = thName'++".orig.thy"
      patchName = thName'++".patch"
      provedName = thName'++"_proved.thy"
      theory = if checkCons then showConsTheory else showTheory
      (lemmas, decs) = unzip (map formLemmas disAxs)
      showLemma = if showLemmas sig
                   then concat lemmas ++ "\n" ++ concat (map (++"\n") decs)
                   else ""
--
      showAxs = concat $ map ((++"\n") . showSen) (map markSimp disAxs)
      showGoals = concat $ map showGoal disGoals
      getFN = reverse . fst . break (=='/') . reverse
      showGoal goal = (("theorem "++) .  (++"\noops\n") . showSen)
                      (markSimp goal)
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
             ("(? x . True)":map (showConsAx . mapNamed freeTypesSen) disAxs))
         ++ ") )\"\nrefute\noops\n\n"
      showConsAx ax = showPretty (sentence ax) ""

markSimp :: Named Sentence -> Named Sentence
markSimp ax = ax{senName = senName ax ++
               (if isSimpRuleSen $ sentence ax then " [simp]" else "")}

isSimpRuleSen :: Sentence -> Bool
isSimpRuleSen sen = case sen of
    RecDef {} -> False
    _ -> isSimpRule $ senTerm sen

-- | test whether a formula should be put into the simpset
isSimpRule :: Term -> Bool
-- only universal quantifications
isSimpRule App { funId = Const {termName = VName { new = q }}
               , argId = arg@Abs{}}
    | q == exS || q == ex1S = False
    | q == allS             = isSimpRule (termId arg)
-- accept everything expect from abstractions
isSimpRule App {funId = arg1, argId = arg2} =
    isSimpRule arg1 && isSimpRule arg2
isSimpRule MixfixApp {funId = arg1, argIds = [arg2, arg3]} =
    isSimpRule arg1 && isSimpRule arg2 && isSimpRule arg3
isSimpRule Const{} = True
isSimpRule Free{}  = True
isSimpRule Var{}   = True
isSimpRule Bound{} = True
isSimpRule Abs{}   = False
isSimpRule If{}    = True
isSimpRule Case{}  = True
isSimpRule Let{}   = True
isSimpRule (Paren t) = isSimpRule t
isSimpRule _       = False

-- output a sentences
showSen :: Named Sentence -> String
showSen = show . printNamedSen

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

mapSentence :: (Term -> Term) -> Sentence -> Sentence
mapSentence f sen = case sen of
    RecDef kw sens -> RecDef kw $ map (map f) sens
    _ -> sen { senTerm = f $ senTerm sen }

-- | remove type constants from a term
freeTypesSen :: Sentence -> Sentence
freeTypesSen = mapSentence freeTypesTerm

freeTypesTerm :: Term -> Term
freeTypesTerm (Const vn t) = Const
    (if new vn == "O" then vn {new="OO"} else vn) (freeTypesTyp t)
freeTypesTerm (Free v t) = Free v (freeTypesTyp t)
freeTypesTerm (Abs v ty t f) =
    Abs (freeTypesTerm v) (freeTypesTyp ty) (freeTypesTerm t) f
freeTypesTerm (App t1 t2 f) = App (freeTypesTerm t1) (freeTypesTerm t2) f
freeTypesTerm (MixfixApp t1 t2 f) =
    MixfixApp (freeTypesTerm t1) (map freeTypesTerm t2) f
freeTypesTerm (Case term alts) =
  Case (freeTypesTerm term) (map freeTypesTermPair alts)
freeTypesTerm (If t1 t2 t3 c) =
  If (freeTypesTerm t1) (freeTypesTerm t2) (freeTypesTerm t3) c
freeTypesTerm (Let defs body) =
  Let (map freeTypesTermPair defs) (freeTypesTerm body)
freeTypesTerm (Fix f) =
  Fix (freeTypesTerm f)
freeTypesTerm t = t

freeTypesTermPair :: (Term, Term) -> (Term, Term)
freeTypesTermPair (t1, t2) = (freeTypesTerm t1, freeTypesTerm t2)

freeTypesTyp :: Typ -> Typ
freeTypesTyp (Type t s _) = TFree t s
freeTypesTyp t = t
