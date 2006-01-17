{- |
Module      :  $Header$
Copyright   :  (c) C. Maeder, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  non-portable(DevGraph)

pretty printing (parts of) a LibEnv
-}

module Static.PrintDevGraph where

import Syntax.AS_Library
import Syntax.Print_AS_Library()
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

printLibrary :: LibEnv -> (LIB_NAME, GlobalContext) -> Doc
printLibrary le (ln, GlobalContext { globalAnnos = ga, globalEnv = ge }) =
    text libraryS <+> printText0 ga ln $$
         foldr (aboveWithNLs 2) P.empty
                   (map (uncurry $ printTheory le ln ga) $ Map.toList ge)

printTheory :: LibEnv -> LIB_NAME -> GlobalAnnos
            -> SIMPLE_ID -> GlobalEntry -> Doc
printTheory le ln ga sn ge = case ge of
    SpecEntry (_,_,_, NodeSig n _) ->
        case maybeResult $ computeTheory le ln n of
            Nothing -> P.empty
            Just g -> printTh ga sn g
    _ -> P.empty

printTh :: GlobalAnnos -> SIMPLE_ID -> G_theory -> Doc
printTh ga sn g = text specS <+> printText0 ga sn <+> text equalS
                    $$ printText0 ga g
