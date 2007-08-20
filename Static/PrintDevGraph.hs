{- |
Module      :  $Header$
Description :  pretty printing (parts of) a LibEnv
Copyright   :  (c) C. Maeder, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(DevGraph)

pretty printing (parts of) a LibEnv
-}

module Static.PrintDevGraph
    ( printLibrary
    , printTh
    ) where

import Logic.Logic
import Static.GTheory
import Static.DevGraph
import Static.DGToSpec

import Syntax.AS_Library
import Syntax.Print_AS_Library ()

import Common.GlobalAnnotations
import Common.Id
import Common.Doc as Doc
import Common.DocUtils
import Common.Result
import Common.Keywords
import Common.ConvertGlobalAnnos
import Common.AnalyseAnnos
import qualified Common.Lib.Rel as Rel
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List

printLibrary :: LibEnv -> (LIB_NAME, DGraph) -> Doc
printLibrary le (ln, DGraph { globalAnnos = ga, globalEnv = ge }) =
    keyword libraryS <+> pretty ln $+$
         foldr ($++$) Doc.empty
                   (map (uncurry $ printTheory le ln ga) $ Map.toList ge)

printTheory :: LibEnv -> LIB_NAME -> GlobalAnnos
            -> SIMPLE_ID -> GlobalEntry -> Doc
printTheory le ln ga sn ge = case ge of
    SpecEntry (_, _, _, NodeSig n _) ->
        case maybeResult $ computeTheory le ln n of
            Nothing -> Doc.empty
            Just g -> printTh ga sn g
    _ -> Doc.empty

printTh :: GlobalAnnos -> SIMPLE_ID -> G_theory -> Doc
printTh oga sn g@(G_theory lid _ _ _ _) =
    let ga = removeProblematicListAnnos oga in
    useGlobalAnnos ga $ pretty ga $+$
    keyword logicS <+> structId (language_name lid) $+$
    sep [keyword specS <+> sidDoc sn <+> equals, pretty g]

removeProblematicListAnnos :: GlobalAnnos -> GlobalAnnos
removeProblematicListAnnos ga = let
    is = Map.keysSet $ Rel.toMap $ prec_annos ga
    la = literal_annos ga
    nla = la { list_lit = Map.filterWithKey ( \ li _ ->
        let (op, cl, cs) = getListBrackets li in
          Set.null $ Set.filter ( \ (Id ts ics _) ->
              cs == ics && isPrefixOf op ts && isSuffixOf cl ts) is)
        $ list_lit la }
    Result _ (Just lm) = store_literal_map Map.empty $ c_lit_an nla
    in ga { literal_annos = nla
          , literal_map = lm }
