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

import qualified Common.Lib.Map as Map
import Common.Id
import Common.PrettyPrint
import Common.Result
import Common.Lib.Pretty as P

import Logic.Logic
import Logic.Comorphism
import Logic.Grothendieck

import Syntax.AS_Library
import Syntax.Print_AS_Library()

import Static.DevGraph
import Static.DGToSpec

import Isabelle.CreateThy as CreateThy

import CASL.Logic_CASL
import HasCASL.Logic_HasCASL

import Comorphisms.CASL2PCFOL
import Comorphisms.PCFOL2CFOL
import Comorphisms.CFOL2IsabelleHOL
import Comorphisms.HasCASL2IsabelleHOL
#ifdef PROGRAMATICA
import Comorphisms.Haskell2IsabelleHOLCF
import Haskell.Logic_Haskell
#endif

printLibEnv :: LibEnv -> IO ()
printLibEnv le  =  mapM_ (printLibrary le) $ Map.toList le

printLibrary :: LibEnv -> (LIB_NAME, GlobalContext) -> IO ()
printLibrary le (ln, (_, ge, dg)) =
      mapM_ (printTheory ln le dg) $ Map.toList ge

printTheory :: LIB_NAME -> LibEnv -> DGraph 
            -> (SIMPLE_ID, GlobalEntry) -> IO ()
printTheory ln le dg (sn, ge) = case ge of 
    SpecEntry (_,_,_, e) -> case getNode e of 
        Nothing -> return ()
        Just n -> 
          case maybeResult $ computeTheory le ln dg n of
            Nothing -> return ()
            Just (G_theory lid sign0 sens0) ->
                let r1 = do
                      sign1 <- coerce CASL lid sign0 
                      sens1 <- coerce CASL lid sens0
                      th1 <- map_theory CASL2PCFOL (sign1, sens1)
                      th2 <- map_theory PCFOL2CFOL th1
                      map_theory CFOL2IsabelleHOL th2
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
                   Nothing -> 
                          return ()
                   Just (sign, sens) -> let 
                     tn = reverse (takeWhile (/= '/') $ reverse $ show ln)
                          ++ "_" ++ showPretty sn ""
                     doc = text "theory" <+> text tn <+> text "=" $$
                          createTheoryText sign sens
                     in do
                        putStrLn $ "Writing " ++ tn ++ ".thy"
                        writeFile (tn ++ ".thy") (shows doc "\n")
    _ -> return ()

