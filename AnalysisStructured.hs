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
import AS_Structured
import AS_Annotation
import GlobalAnnotations
import AS_Structured
import Result
import Id

lookupNode n dg = lab' $ context n dg

ana_SPEC :: GlobalAnnos -> GlobalEnv -> DGraph -> Node -> SPEC
              -> Result (Node,DGraph)

ana_SPEC gannos genv dg n sp = case dgn_sign $ lookupNode n dg of

  G_sign lid sigma ->

   case sp of

    Basic_spec (G_basic_spec lid' bspec) ->
      do sigma' <- rcoerce lid lid' nullPos sigma
         b <- maybeToResult nullPos 
                  ("no basic analysis for logic "++language_name lid') 
                  (basic_analysis lid')
         (sigma_local, sigma_complete, ax) <- b (bspec,sigma',gannos) 
         let node_contents = DGNode {
             dgn_sign = G_sign lid' sigma_local, -- only the delta
             dgn_sens = G_l_sentence lid' ax,
             dgn_origin = DGBasic }
             [node] = newNodes 1 dg
         return (node,insNode (node,node_contents) dg)

    Translation asp ren ->
     do let sp = item asp
        (n',dg') <- ana_SPEC gannos genv dg n sp
        mor <- ana_RENAMING dg n' ren
        G_sign xx yy <- return (cod Grothendieck mor)
        return (case cod Grothendieck mor of
         G_sign lid' sigma' ->
          let node_contents = DGNode {
               dgn_sign = G_sign lid' (empty_signature lid'), -- delta is empty
               dgn_sens = G_l_sentence lid' [],
               dgn_origin = DGTranslation }
              [node] = newNodes 1 dg'
              link = DGLink {
                dgl_morphism = mor,
                dgl_type = GlobalDef,
                dgl_origin = DGTranslation }
           in (node,insEdge (n',node,link) (insNode (node,node_contents) dg'))
          )
         

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

ana_ren1 dg (GMorphism lid1 lid2 r sigma mor) 
           (G_symb_map (G_symb_map_items_list lid sis),pos) = do
  sis1 <- rcoerce lid2 lid pos sis
  rmap <- stat_symb_map_items lid2 sis1
  mor1 <- induced_from_morphism lid2 rmap (cod lid2 mor)
  mor2 <- maybeToResult pos 
                        "renaming: signature morphism composition failed" 
                        (comp lid2 mor mor1)
  return (GMorphism lid1 lid2 r sigma mor2)
 
ana_ren1 dg mor (G_logic_translation (Logic_code tok src tar pos1),pos2) =
  error "analysis of logic translations"

ana_ren :: DGraph -> Result GMorphism -> (G_mapping,Pos) -> Result GMorphism
ana_ren dg mor_res ren =
  do mor <- mor_res
     ana_ren1 dg mor ren

ana_RENAMING :: DGraph -> Node -> RENAMING -> Result GMorphism
ana_RENAMING dg n (Renaming ren pos) = 
  foldl (ana_ren dg) (return (ide Grothendieck gSigma')) ren'
  where
  gSigma' = dgn_sign $ lookupNode n dg
  ren' = zip ren (tail (pos++nulls))
  nulls = nullPos:nulls
