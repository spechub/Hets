{-| 
   
Module      :  $Header$
Copyright   :  (c) C. Maeder, Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  till@tzi.de
Stability   :  provisional
Portability :  non-portable(Logic)

   dumping a LibEnv
-}

module Static.PrintDevGraph where

import Logic.Logic
import Logic.Grothendieck
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

instance PrettyPrint LibEnv where
    printText0 _ le = vcat (map (printLibrary le) $ Map.toList le)

printLibrary :: LibEnv -> (LIB_NAME, GlobalContext) -> Doc
printLibrary le (ln, (ga, ge, dg)) = 
    text libraryS <+> printText0 ga ln $$ 
         foldr (aboveWithNLs 2) P.empty 
                   (map (printTheory le ln ga dg) $ Map.toList ge)

printTheory :: LibEnv -> LIB_NAME -> GlobalAnnos -> DGraph 
            -> (SIMPLE_ID, GlobalEntry) -> Doc
printTheory le ln ga dg (sn, ge) = case ge of 
    SpecEntry (_,_,_, e) -> case getNode e of 
        Nothing -> P.empty
        Just n -> case maybeResult $ computeTheory le ln dg n of
            Nothing -> P.empty
            Just (G_theory lid sign sens) ->
                text specS <+> printText0 ga sn $$
                 printText0 ga sign $$ text "" $$
                   vsep (map (print_named lid ga . 
                              mapNamed (simplify_sen lid sign)) sens)
    _ -> P.empty                             
