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
import Comorphisms.CASL2PCFOL
import Comorphisms.PCFOL2FOL
import Comorphisms.CASL2IsabelleHOL
import Isabelle.Logic_Isabelle
import Isabelle.Translate
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
                let Result _ (Just (sign1, sens1)) = 
                        map_theory CASL2PCFOL 
                                       (fromJust $ coerce CASL lid sign0, 
                                        fromJust $ coerce CASL lid sens0) 
                    Result _ (Just (sign2, sens2)) = 
                        map_theory PCFOL2FOL (sign1, sens1) 
                    Result _ (Just (sign, sens3)) = 
                        map_theory CASL2IsabelleHOL (sign2, sens2)
                    sens = zipWith (\ s i -> 
                                    s { senName = transString (senName s)
                                          ++ "_" ++ show i }) sens3 
                           [1::Int .. ]
                    -- drop "Basic/"
                    tn = drop 6 (shows ln "_" ++ showPretty sn "")
                    doc = text "theory" <+> text tn <+> text "=" $$
                          printText0 ga sign $$ 
                          (if null sens then P.empty else text "axioms" $$
                          vsep (map (print_named Isabelle ga . 
                                mapNamed (simplify_sen Isabelle sign)) sens))
                          $$ text "end"
                in writeFile (tn ++ ".thy") (shows doc "\n")
    _ -> return ()
