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
import LogicRepr
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

nulls = nullPos:nulls

ana_SPEC :: GlobalAnnos -> GlobalEnv -> DGraph -> Node -> G_sign -> SPEC
              -> Result (Node,G_sign,DGraph)

ana_SPEC gannos genv dg n gsigma@(G_sign lid sigma) sp = 

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
         return (node,G_sign lid' sigma_complete,
                 insNode (node,node_contents) dg)

    Translation asp ren ->
     do let sp = item asp
        (n',sigma',dg') <- ana_SPEC gannos genv dg n gsigma sp
        mor <- ana_RENAMING dg sigma' ren
        -- ??? check that mor is identity on local env
        let gsigma' = cod Grothendieck mor 
             -- ??? to simplistic for non-comorphism inter-logic translations 
        G_sign lid' sigma' <- return gsigma'
        let node_contents = DGNode {
              dgn_sign = G_sign lid' (empty_signature lid'), -- delta is empty
              dgn_sens = G_l_sentence lid' [],
              dgn_origin = DGTranslation }
            [node] = newNodes 1 dg'
            link = DGLink {
              dgl_morphism = mor,
              dgl_type = GlobalDef,
              dgl_origin = DGTranslation }
        return (node,gsigma',insEdge (n',node,link) (insNode (node,node_contents) dg'))
      
    Reduction asp restr ->
     do let sp = item asp
        (n',gsigma',dg') <- ana_SPEC gannos genv dg n gsigma sp
        (hmor,tmor) <- ana_RESTRICTION dg gsigma gsigma' restr
        -- we treat hiding and revealing differently
        -- in order to keep the dg as simple as possible
        case tmor of
         Nothing ->
          do let gsigma' = dom Grothendieck hmor
             -- ??? to simplistic for non-comorphism inter-logic reductions 
             G_sign lid' sigma' <- return gsigma'
             let node_contents = DGNode {
                   dgn_sign = G_sign lid' (empty_signature lid'), 
                   dgn_sens = G_l_sentence lid' [],
                   dgn_origin = DGHiding }
                 [node] = newNodes 1 dg'
                 link = DGLink {
                    dgl_morphism = hmor,
                    dgl_type = HidingDef,
                    dgl_origin = DGHiding }
             return (node,gsigma',
                     insEdge (n',node,link) $
                     insNode (node,node_contents) dg')
         Just tmor' ->
          do let gsigma1 = dom Grothendieck tmor'
                 gsigma'' = cod Grothendieck tmor'
             -- ??? to simplistic for non-comorphism inter-logic reductions 
             G_sign lid1 sigma1 <- return gsigma1
             G_sign lid'' sigma'' <- return gsigma''
             let [node1,node''] = newNodes 1 dg'
                 node_contents1 = DGNode {
                   dgn_sign = G_sign lid1 (empty_signature lid1),
                   dgn_sens = G_l_sentence lid1 [],
                   dgn_origin = DGRevealing }
                 link1 = DGLink {
                   dgl_morphism = hmor,
                   dgl_type = HidingDef,
                   dgl_origin = DGRevealing }
                 node_contents'' = DGNode {
                   dgn_sign = G_sign lid'' (empty_signature lid''),
                   dgn_sens = G_l_sentence lid'' [],
                   dgn_origin = DGRevealTranslation }
                 link'' = DGLink {
                   dgl_morphism = tmor',
                   dgl_type = GlobalDef,
                   dgl_origin = DGRevealTranslation }
             return (node'',gsigma'',
                     insEdge (node1,node'',link'') $
                     insNode (node'',node_contents'') $
                     insEdge (n,node1,link1) $
                     insNode (node1,node_contents1) dg')


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

-- analysis of renamings

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
  fatal_error "no analysis of logic translations yet" pos2

ana_ren :: DGraph -> Result GMorphism -> (G_mapping,Pos) -> Result GMorphism
ana_ren dg mor_res ren =
  do mor <- mor_res
     ana_ren1 dg mor ren

ana_RENAMING :: DGraph -> G_sign -> RENAMING -> Result GMorphism
ana_RENAMING dg gSigma (Renaming ren pos) = 
  foldl (ana_ren dg) (return (ide Grothendieck gSigma)) ren'
  where
  ren' = zip ren (tail (pos++nulls))
  nulls = nullPos:nulls


-- analysis of restrictions

ana_restr1 dg (GMorphism lid1 lid2 r sigma mor) 
           (G_symb_list (G_symb_items_list lid sis),pos) = do
  sis1 <- rcoerce lid1 lid pos sis
  rmap <- stat_symb_items lid1 sis1
  mor1 <- cogenerated_sign lid1 rmap sigma
  mor1' <- maybeToResult pos 
             ("restriction: could not map morphism along" ++ repr_name r)
             (map_morphism r mor1)
  mor2 <- maybeToResult pos 
                        "restriction: signature morphism composition failed" 
                        (comp lid2 mor1' mor)
  return (GMorphism lid1 lid2 r (dom lid1 mor1) mor2)
 
ana_restr1 dg mor (G_logic_projection (Logic_code tok src tar pos1),pos2) =
  fatal_error "no analysis of logic projections yet" pos2

ana_restr :: DGraph -> Result GMorphism -> (G_hiding,Pos) -> Result GMorphism
ana_restr dg mor_res restr =
  do mor <- mor_res
     ana_restr1 dg mor restr

ana_RESTRICTION :: DGraph -> G_sign -> G_sign -> RESTRICTION 
       -> Result (GMorphism, Maybe GMorphism)
ana_RESTRICTION dg gSigma gSigma' (Hidden restr pos) = 
  do mor <- foldl (ana_restr dg) (return (ide Grothendieck gSigma)) restr'
     return (mor,Nothing)
  where
  restr' = zip restr (tail (pos++nulls))
ana_RESTRICTION dg gSigma gSigma' (Revealed (G_symb_map_items_list lid sis) pos) = 
  do G_sign lid1 sigma <- return gSigma
     sis1 <- rcoerce lid lid1 (head (pos++nulls)) sis
     rmap <- stat_symb_map_items lid1 sis1
     mor1 <- induced_from_morphism lid1 rmap sigma
     return undefined     
