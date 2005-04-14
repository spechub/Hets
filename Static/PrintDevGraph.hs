{-| 
   
Module      :  $Header$
Copyright   :  (c) C. Maeder, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  non-portable(Logic)

   dumping a LibEnv
-}

module Static.PrintDevGraph where

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
import Common.Keywords
import Common.Lib.Pretty as P
import Static.DevGraph
import Static.DGToSpec
import CASL.Logic_CASL
import Comorphisms.CASL2PCFOL
import Comorphisms.PCFOL2FOL
import Comorphisms.CASL2IsabelleHOL
import Isabelle.Logic_Isabelle
import Data.Maybe

instance PrettyPrint LibEnv where
    printText0 _ le = vcat (map (printLibrary le) $ Map.toList le)

printLibrary :: LibEnv -> (LIB_NAME, GlobalContext) -> Doc
printLibrary le (ln, (ga, ge, dg)) = 
    text libraryS <+> printText0 ga ln $$ 
         foldr (aboveWithNLs 2) P.empty 
                   (map (printTheory le ga dg) $ Map.toList ge)

printTheory :: LibEnv -> GlobalAnnos -> DGraph 
            -> (SIMPLE_ID, GlobalEntry) -> Doc
printTheory le ga dg (sn, ge) = case ge of 
    SpecEntry (_,_,_, e) -> case getNode e of 
        Nothing -> P.empty
        Just n -> case maybeResult $ computeTheory le dg n of
            Nothing -> P.empty
            Just (G_theory lid sign0 sens0) ->
                let Result _ (Just (sign1, sens1)) = 
                        map_theory CASL2PCFOL 
                                       (fromJust $ coerce CASL lid sign0, 
                                        fromJust $ coerce CASL lid sens0) 
                    Result _ (Just (sign2, sens2)) = 
                        map_theory PCFOL2FOL (sign1, sens1) 
                    Result _ (Just (sign, sens)) = 
                        map_theory CASL2IsabelleHOL (sign2, sens2) in
                text specS <+> printText0 ga sn $$
                 printText0 ga sign $$ text "" $$
                   vsep (map (print_named Isabelle ga . 
                              mapNamed (simplify_sen Isabelle sign)) sens)
    _ -> P.empty                             
