{-# OPTIONS -cpp #-}
{-| 
Module      :  $Header$
Copyright   :  (c) C. Maeder, Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  paolot@tzi.de
Stability   :  provisional
Portability :  non-portable(Logic)

dumping a LibEnv to Isabelle theory files
-}

module Isabelle.CreateTheories where

import Data.Maybe
import Data.List

import Common.AS_Annotation
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import Common.Id
import Common.PrettyPrint
import Common.PPUtils
import Common.Result
import Common.Lib.Pretty as P

import Logic.Logic
import Logic.Comorphism
import Logic.Grothendieck

import Syntax.AS_Library
import Syntax.Print_AS_Library()

import Static.DevGraph
import Static.DGToSpec

import Isabelle.IsaSign as IsaSign
import Isabelle.Translate
import Isabelle.IsaPrint as IsaPrint
import Isabelle.IsaHOLCFPrint 

import CASL.Logic_CASL
import HasCASL.Logic_HasCASL

import Comorphisms.CASL2PCFOL
import Comorphisms.PCFOL2FOL
import Comorphisms.CASL2IsabelleHOL
import Comorphisms.HasCASL2IsabelleHOL
#ifdef PROGRAMATICA
import Comorphisms.Haskell2IsabelleHOLCF
import Haskell.Logic_Haskell
#endif

printLibEnv :: LibEnv -> IO ()
printLibEnv le  = 
      mapM_ (printLibrary le) $ Map.toList le

printLibrary :: LibEnv -> (LIB_NAME, GlobalContext) -> IO ()
printLibrary le (ln, (_, ge, dg)) = 
      mapM_ (printTheory ln le dg) $ Map.toList ge

printTheory :: LIB_NAME -> LibEnv -> DGraph 
            -> (SIMPLE_ID, GlobalEntry) -> IO ()
printTheory ln le dg (sn, ge) = case ge of 
    SpecEntry (_,_,_, e) -> case getNode e of 
        Nothing -> return ()
        Just n -> case maybeResult $ computeTheory le ln dg n of
            Nothing -> return ()
            Just (G_theory lid sign0 sens0) ->
                let r1 = do
                      sign1 <- coerce CASL lid sign0 
                      sens1 <- coerce CASL lid sens0
                      th1 <- map_theory CASL2PCFOL (sign1, sens1)
                      th2 <- map_theory PCFOL2FOL th1
                      map_theory CASL2IsabelleHOL th2
#ifdef PROGRAMATICA                                  
                    r2 = do 
                      sign1 <- coerce Haskell lid sign0 
                      sens1 <- coerce Haskell lid sens0
                      map_theory Haskell2IsabelleHOLCF (sign1, sens1)
#else 
                    r2 = r1
#endif
                    r4 = do 
                      sign1 <- coerce HasCASL lid sign0 
                      sens1 <- coerce HasCASL lid sens0
                      map_theory HasCASL2IsabelleHOL (sign1, sens1)
                    r3 = case maybeResult r1 of 
                         Nothing -> case maybeResult r2 of 
                             Nothing -> r4
                             _ -> r2
                         _ -> r1
                in case maybeResult r3 of 
                   Nothing -> return ()
                   Just (sign, sens) -> let 
                     tn = reverse (takeWhile (/= '/') $ reverse $ show ln)
                          ++ "_" ++ showPretty sn ""
                     doc = text "theory" <+> text tn <+> text "=" $$
                          createTheoryText sign sens
                     in writeFile (tn ++ ".thy") (shows doc "\n")
    _ -> return ()

getAxioms, getDefs :: [Named Sentence] -> 
                 ([Named Sentence], [Named Sentence])
getAxioms = partition ( \ s -> case sentence s of 
                            Sentence _ -> True
                            _ -> False)

getDefs = partition ( \ s -> case sentence s of 
                            ConstDef _ -> True
                            _ -> False)

disambiguate :: Sign -> [Named Sentence] -> [Named Sentence]
disambiguate sign axs = 
    let s0 = Map.findWithDefault Set.empty (baseSig sign) isaPrelude
        number :: Set.Set String -> Int -> String -> String
        number given c n = let new = n ++ show c in 
                               if Set.member new given then 
                                  number given (c+1) n else new
        rename given n = if Set.member n given then number given 2 n else n
        accFun s a = let m = senName a
                         n = if null m then number s 1 "Ax" 
                                 else rename s (transString m) 
                     in (Set.insert n s, a { senName = n})
     in snd $ mapAccumL accFun s0 axs

createTheoryText :: Sign -> [Named Sentence] -> Doc
createTheoryText sig sens =
    let (axs, rest) = getAxioms sens
        (defs, _) = getDefs rest
--    in printText sig $++$ -- text specialDefinitions $++$
    in printText sig $++$
    (if null axs then empty else text "axioms" $$ 
        vcat (map printNamedSen $ disambiguate sig axs)) $++$
    (if null defs then empty else text "defs" $$
        vcat (map printNamedSen defs)) 
    $++$ text "end"     
--    \$\$ vcat (map (text . show) defs) 
--    \$\$ (text ("\n" ++ (show \$ constTab sig)))
--    \$\$ (text ("\n" ++ (show \$ arities \$ tsig sig)))
--    \$\$ (text ("\n" ++ (show \$ classrel \$ tsig sig)))

printNamedSen :: Named Sentence -> Doc
printNamedSen (NamedSen lab _ s) = text (case s of
    ConstDef _ -> lab ++ "_def"
    Sentence _ -> lab
    Theorem _ _ _ -> "theorem " ++ lab) 
    <+> colon <+> doubleQuotes (case senTerm s of
      IsaEq (Const df y) t ->  
        text (df ++ " ::" ++ (showTyp Unquoted 1000 y) ++ " == " ++ (showOUTerm t))
      _ -> (printText s))

specialDefinitions :: String
specialDefinitions = "constdefs \n fromInteger :: \"int lift -> int lift\" \n" ++
    "\"fromInteger == flift2 id\" \n" ++ "inst__Prelude_Num_Int :: \"int lift -> int lift\" \n"
    ++ "\"inst__Prelude_Num_Int == flift2 id\" \n"
