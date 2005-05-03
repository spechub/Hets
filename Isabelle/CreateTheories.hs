{-| 
   
Module      :  $Header$
Copyright   :  (c) C. Maeder, Uni Bremen 2005
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  non-portable(Logic)

   dumping a LibEnv
-}

module Isabelle.CreateTheories where

import Logic.Logic
import Logic.Grothendieck
import Logic.Comorphism
import Syntax.AS_Library
import Syntax.Print_AS_Library
import Common.AS_Annotation
import Common.GlobalAnnotations
import qualified Common.Lib.Map as Map
import Common.Id
import Common.PrettyPrint
import Common.PPUtils
import Common.Result
import Common.Lib.Pretty as P
import Static.DevGraph
import Static.DGToSpec
import CASL.Logic_CASL
import HasCASL.Logic_HasCASL
import Comorphisms.CASL2PCFOL
import Comorphisms.PCFOL2FOL
import Comorphisms.CASL2IsabelleHOL
import Comorphisms.Haskell2IsabelleHOLCF
import Isabelle.IsaSign as IsaSign
import Isabelle.Logic_Isabelle
import Haskell.Logic_Haskell
import Isabelle.Translate
import Isabelle.IsaSign
import Data.Maybe

printLibEnv :: LibEnv -> IO ()
printLibEnv le  = 
      mapM_ (printLibrary le) $ Map.toList le

printLibrary :: LibEnv -> (LIB_NAME, GlobalContext) -> IO ()
printLibrary le (ln, (ga, ge, dg)) = 
      mapM_ (printTheory ln le ga dg) $ Map.toList ge

printTheory :: LIB_NAME -> LibEnv -> GlobalAnnos -> DGraph 
            -> (SIMPLE_ID, GlobalEntry) -> IO ()
printTheory ln le ga dg (sn, ge) = case ge of 
    SpecEntry (_,_,_, e) -> case getNode e of 
        Nothing -> return ()
        Just n -> case maybeResult $ computeTheory le dg n of
            Nothing -> return ()
            Just (G_theory lid sign0 sens0) ->
                let r1 = Result [] Nothing
{-                      sign1 <- coerce CASL lid sign0 
                      sens1 <- coerce CASL lid sens0
                      th1 <- map_theory CASL2PCFOL (sign1, sens1)
                      th2 <- map_theory PCFOL2FOL th1
                      map_theory CASL2IsabelleHOL th2  -}
                    r2 = do 
                      sign1 <- coerce Haskell lid sign0 
                      sens1 <- coerce Haskell lid sens0
                      map_theory Haskell2IsabelleHOLCF (sign1, sens1)
                    r3 = case maybeResult r1 of 
                         Nothing -> r2
                         _ -> r1
                in case maybeResult r3 of 
                   Nothing -> putStrLn $ showPretty r3 ""
                   Just (sign, sens2) -> let 
                     sens = sens2
{-  let
                     sens = zipWith (\ s i -> 
                                    s { senName = transStringT 
                                                  (baseSig sign) (senName s
                                          ++ "_" ++ show i) }) sens2
                           [1::Int .. ]                                        -}
                     tn = reverse (takeWhile (/= '/') $ reverse $ show ln)
                          ++ "_" ++ showPretty sn ""
                     doc = text "theory" <+> text tn <+> text "=" $$
                          printText0 ga sign $$ 
                          (if null sens then P.empty else text "defs" $$
                          vsep (map (printText0 ga) sens)) $$ text "\n" $$
                          text "end"
--                          $$ (text $ show (IsaSign.constTab sign))               
 {-                         (text $ show (IsaSign.domainTab sign)) <+> text "\n" $$ 
                          (text $ show (IsaSign.constTab sign))               
  **                      (if null sens then P.empty else text "axioms" $$
                          vsep (map (print_named Isabelle ga . 
                                mapNamed (simplify_sen Isabelle sign)) sens))   -}
                     in writeFile (tn ++ ".thy") (shows doc "\n")
    _ -> return ()
