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
import Common.Doc as Doc
import Common.DocUtils
import Common.Result
import Common.Keywords
import Static.DevGraph
import Static.DGToSpec
import Common.ConvertGlobalAnnos()

printLibrary :: LibEnv -> (LIB_NAME, GlobalContext) -> Doc
printLibrary le (ln, GlobalContext { globalAnnos = ga, globalEnv = ge }) =
    keyword libraryS <+> pretty ln $+$
         foldr ($++$) Doc.empty
                   (map (uncurry $ printTheory le ln ga) $ Map.toList ge)

printTheory :: LibEnv -> LIB_NAME -> GlobalAnnos
            -> SIMPLE_ID -> GlobalEntry -> Doc
printTheory le ln ga sn ge = case ge of
    SpecEntry (_,_,_, NodeSig n _) ->
        case maybeResult $ computeTheory le ln n of
            Nothing -> Doc.empty
            Just g -> printTh ga sn g
    _ -> Doc.empty

printTh :: GlobalAnnos -> SIMPLE_ID -> G_theory -> Doc
printTh ga sn g = useGlobalAnnos ga $ pretty ga $+$
                  keyword specS <+> sidDoc sn <+> equals
                    $+$ pretty g
