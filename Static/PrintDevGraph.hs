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
import Syntax.AS_Library
import Syntax.Print_AS_Library
import Common.GlobalAnnotations
import Common.Lib.Graph as Graph
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import Common.Id
import Common.PrettyPrint
import Common.PPUtils
import Common.Result
import Common.Keywords
import Common.Lib.Pretty as P
import Static.DevGraph
import Static.DGToSpec

instance PrettyPrint LibEnv where
    printText0 _ le = vcat (map (printLibrary le) $ Map.toList le)

printLibrary :: LibEnv -> (LIB_NAME, GlobalContext) -> Doc
printLibrary le (ln, (ga, ge, dg)) = 
    text libraryS <+> printText0 ga ln $$ 
         vcat (map (printTheory le ga dg) $ Map.toList ge)

printTheory :: LibEnv -> GlobalAnnos -> DGraph 
            -> (SIMPLE_ID, GlobalEntry) -> Doc
printTheory le ga dg (sn, ge) = case ge of 
    SpecEntry (_,_,_, e) -> case getNode e of 
        Nothing -> P.empty
        Just n -> case maybeResult $ computeTheory le dg n of
            Nothing -> P.empty
            Just (G_theory lid sign sens) ->
                text specS <+> printText0 ga sn $$
                 printText0 ga sign $$ text "" $$
                   vcat (map (print_named lid ga) sens)
    _ -> P.empty                             
                       
    
