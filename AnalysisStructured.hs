{- HetCATS/DevGraph.hs
   $Id$
   Till Mossakowski

   Analysis of structured specifications

   Follows the extended static semantic rules in:

   T. Mossakowski, S. Autexier, D. Hutter, P. Hoffman:
   CASL Proof calculus.
   Available from http://www.informatik.uni-bremen.de/~till/calculus.ps
   To appear in teh CASL book.
-}


module AnalysisStructured
where

import Logic
import Grothendieck
import Graph
import DevGraph
import AS_Annotation
import GlobalAnnotations
import AS_Structured
import Result

lookupNode n dg = lab' $ context n dg

ana_SPEC :: GlobalAnnos -> GlobalEnv -> DGraph -> Node -> SPEC -> (Node,DGraph)

ana_SPEC gannos genv dg n sp = case dgn_sign $ lookupNode n dg of

  G_sign logid sigma ->

   case sp of

    Basic_spec (G_basic_spec logid' bspec) ->
     case coerce logid logid' sigma of
       Nothing -> error ("logic mismatch: "++language_name logid++" expected, but "
              ++language_name logid'++" found")
       Just sigma' -> case basic_analysis logid' of
        Nothing -> error ("no basic analysis for logic "++language_name logid')
        Just b ->
          let res = b (bspec,sigma',gannos) 
            in case maybeResult res of 
              Nothing -> error (show (diags res))
              Just (sigma_local, sigma_complete, ax) -> 
                let node_contents = DGNode {
                      dgn_sign = G_sign logid' sigma_local, -- only the delta
                      dgn_sens = G_l_sentence logid' ax,
                      dgn_origin = DGBasic }
                    [node] = newNodes 1 dg
                  in (node,insNode (node,node_contents) dg)

    Translation asp (Renaming ren pos) ->
     let sp = item asp
         ren' = zip ren (tail pos)
         (n',dg') = ana_SPEC gannos genv dg n sp
         gSigma' = dgn_sign $ lookupNode n' dg'
         mor = foldl (ana_RENAMING dg) (g_ide gSigma') ren'
       in undefined --case  of
--        G_sign logid' sigma' -> 
         

    Reduction asp restr ->
     undefined

    Union asps pos ->
     undefined

    Extension asps pos ->
     undefined

    Free_spec asp pos ->
     undefined

    Cofree_spec asp pos ->
     undefined

    Local_spec asp1 asp2 pos ->
     undefined

    Closed_spec asp pos ->
     undefined

    Group asp pos ->
     undefined

    Spec_inst spname afitargs ->
     undefined

    Qualified_spec logname asp pos ->
     undefined

ana_RENAMING = undefined 