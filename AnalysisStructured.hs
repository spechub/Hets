{- HetCATS/AnalysisStructured.hs
   $Id$
   Till Mossakowski

   Analysis of structured specifications

   Follows the extended static semantic rules in:

   T. Mossakowski, S. Autexier, D. Hutter, P. Hoffman:
   CASL Proof calculus.
   Available from http://www.informatik.uni-bremen.de/~till/calculus.ps
   To appear in the CASL book.

   Todo:
   Check that translations and reductions do not effect local env

   Unions (already in the parser) need unions of logics  
     = suprema in the lattice of default logic inclusions!

   Should we use institution independent analysis over the Grothendieck logic?
      abstract syntax + devgraph would have to be changed to homogeneous case
      logic translations are symbol maps in the Grothendieck logic
      Problem with this approach: symbol functor goes into rel,
      and induced_from_morphism gets difficult to implement

   Unions need inclusion morphisms. Should these play a special role?
     At least we need a function delivering the inclusion morphism
     between two (sub)signatures.
     In most logics, inclusions could be represented specially, such
     that composition for them becomes fast.
     Should we even identify an inclusion subcategory?      

   Treatment of translations and reductions along logic translations
   (see WADT 02 paper).
   Open question:
    may local env be translated, and even reduced, along logic translations?
    if yes: how is local env linked to signature of resulting spec?
      (important e.g. for checking that local env is not being renamed?)
      does signature+comorphism suffice, such that c(local env)\subseteq sig?
    if no: this means that only closed specs may be translated


   Pushouts: only admissible within one logic?
-}


module AnalysisStructured
where

import Maybe
import Logic
import LogicRepr
import Grothendieck
import Graph
import DevGraph
import AS_Structured
import AS_Annotation
import GlobalAnnotations
import Result
import Id
import Set
import FiniteMap

lookupNode n dg = lab' $ context n dg

setFilter p s = mkSet (filter p (setToList s))
setAny p s = any p (setToList s)
s1 `disjoint` s2 = s1 `intersect` s2 == emptySet

domFM m = mkSet (keysFM m)

ana_SPEC :: GlobalAnnos -> GlobalEnv -> DGraph -> NodeSig -> SPEC
              -> Result (NodeSig,DGraph)

ana_SPEC gannos genv dg nsig sp = 

  case sp of

    Basic_spec (G_basic_spec lid bspec) ->
      do Logic lid' <- return (getLogic nsig)
         sigma <- rcoerce lid' lid nullPos (getSig nsig)
         b <- maybeToResult nullPos 
                  ("no basic analysis for logic "++language_name lid) 
                  (basic_analysis lid)
         (sigma_local, sigma_complete, ax) <- b (bspec,sigma,gannos) 
         let node_contents = DGNode {
               dgn_sign = G_sign lid sigma_local, -- only the delta
               dgn_sens = G_l_sentence lid ax,
               dgn_origin = DGBasic }
             [node] = newNodes 1 dg
             dg' = insNode (node,node_contents) dg
             link = DGLink {
                      dgl_morphism = undefined, -- where to get it from ???
                      dgl_type = GlobalDef,
                      dgl_origin = DGExtension }
             dg'' = case nsig of
                      EmptyNode _ -> dg'
                      NodeSig (n,_) -> insEdge (n,node,link) dg'
         return (NodeSig (node,G_sign lid sigma_complete),dg')

    Translation asp ren ->
     do let sp = item asp
        (nsig',dg') <- ana_SPEC gannos genv dg nsig sp
        n' <- maybeToResult nullPos "Translation of empty spec" (getNode nsig')
        mor <- ana_RENAMING dg (getSig nsig') ren
        -- ??? check that mor is identity on local env
        let gsigma' = cod Grothendieck mor 
             -- ??? too simplistic for non-comorphism inter-logic translations 
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
        return (NodeSig(node,gsigma'),
                insEdge (n',node,link) $
                insNode (node,node_contents) dg')
      
    Reduction asp restr ->
     do let sp = item asp
        (nsig',dg') <- ana_SPEC gannos genv dg nsig sp
        let gsigma = getSig nsig
            gsigma' = getSig nsig'
        n' <- maybeToResult nullPos "Reduction of empty spec" (getNode nsig')
        (hmor,tmor) <- ana_RESTRICTION dg gsigma gsigma' restr
        -- we treat hiding and revealing differently
        -- in order to keep the dg as simple as possible
        case tmor of
         Nothing ->
          do let gsigma' = dom Grothendieck hmor
             -- ??? too simplistic for non-comorphism inter-logic reductions 
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
             return (NodeSig(node,gsigma'),
                     insEdge (n',node,link) $
                     insNode (node,node_contents) dg')
         Just tmor' ->
          do let gsigma1 = dom Grothendieck tmor'
                 gsigma'' = cod Grothendieck tmor'
             -- ??? too simplistic for non-comorphism inter-logic reductions 
             G_sign lid1 sigma1 <- return gsigma1
             G_sign lid'' sigma'' <- return gsigma''
             let [node1,node''] = newNodes 2 dg'
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
             return (NodeSig(node'',gsigma''),
                     insEdge (node1,node'',link'') $
                     insNode (node'',node_contents'') $
                     insEdge (n',node1,link1) $
                     insNode (node1,node_contents1) dg')


    Union [] pos -> return (nsig,dg)
    Union asps pos ->
     do let sps = map item asps
        (nsigs,dg') <- let ana r sp = do
                            (nsigs,dg) <- r
                            (nsig,dg1) <- ana_SPEC gannos genv dg nsig sp
                            return (nsig:nsigs,dg1)
                      in foldl ana (return ([],dg)) sps
        G_sign lid' sigma' <- return (getSig (head nsigs))
        let nsigs' = reverse nsigs
            nodes = catMaybes (map getNode nsigs')
        sigmas <- let coerce_lid (G_sign lid1 sigma1) = 
                          rcoerce lid' lid1 (head (pos++nullPosList)) sigma1
                   in sequence (map (coerce_lid . getSig) (tail nsigs'))
        big_sigma <- let sig_union s1 s2 = do
                             s1' <- s1
                             signature_union lid' s1' s2
                      in foldl sig_union (return sigma') sigmas
        let node_contents = DGNode {
              dgn_sign = G_sign lid' (empty_signature lid'), 
              dgn_sens = G_l_sentence lid' [],
              dgn_origin = DGUnion }
            [node] = newNodes 1 dg'
            link = DGLink {
               dgl_morphism = undefined, -- ??? how to get it?
               dgl_type = GlobalDef,
               dgl_origin = DGUnion }
        return (let insE dg n = insEdge (n,node,link) dg -- link should vary
                in (NodeSig(node,G_sign lid' big_sigma),
                    foldl insE (insNode (node,node_contents) dg') nodes))


    Extension asps pos ->
     foldl ana (return (nsig,dg)) (map item asps)
     where
     ana res sp = do
       (nsig,dg) <- res
       ana_SPEC gannos genv dg nsig sp

    Free_spec asp pos ->
     ana_err "free specs"

    Cofree_spec asp pos ->
     ana_err "cofree specs"

    Local_spec asp1 asp2 pos ->
     ana_err "local specs"

    Closed_spec asp pos ->
     ana_err "closed specs"

    Group asp pos ->
     ana_SPEC gannos genv dg nsig (item asp)


    Spec_inst spname afitargs ->
     ana_err "spec inst"

    Qualified_spec logname asp pos ->
     ana_err "logic qualified specs"

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
  ren' = zip ren (tail (pos++nullPosList))


-- analysis of restrictions

ana_restr1 dg (G_sign lid sigma) (GMorphism lid1 lid2 r sigma1 mor) 
           (G_symb_list (G_symb_items_list lid' sis'),pos) = do
  sis1 <- rcoerce lid1 lid' pos sis'
  rsys <- stat_symb_items lid1 sis1
  let sys = sym_of lid1 sigma1
  let sys' = filter (\sy -> any (\rsy -> matches lid1 sy rsy) rsys) 
                    (setToList sys)
--     if sys' `disjoint` () then return ()
--      else plain_error () "attempt to hide symbols from the local environment" pos
  mor1 <- cogenerated_sign lid1 sys' sigma1
  mor1' <- maybeToResult pos 
             ("restriction: could not map morphism along" ++ repr_name r)
             (map_morphism r mor1)
  mor2 <- maybeToResult pos 
                        "restriction: signature morphism composition failed" 
                        (comp lid2 mor1' mor)
  return (GMorphism lid1 lid2 r (dom lid1 mor1) mor2)
 
ana_restr1 dg gSigma mor 
           (G_logic_projection (Logic_code tok src tar pos1),pos2) =
  fatal_error "no analysis of logic projections yet" pos2

ana_restr :: DGraph -> G_sign -> Result GMorphism -> (G_hiding,Pos) 
               -> Result GMorphism
ana_restr dg gSigma mor_res restr =
  do mor <- mor_res
     ana_restr1 dg gSigma mor restr

ana_RESTRICTION :: DGraph -> G_sign -> G_sign -> RESTRICTION 
       -> Result (GMorphism, Maybe GMorphism)
ana_RESTRICTION dg gSigma gSigma' (Hidden restr pos) = 
  do mor <- foldl (ana_restr dg gSigma) 
                  (return (ide Grothendieck gSigma'))
                  restr'
     return (mor,Nothing)
  where
  restr' = zip restr (tail (pos++nullPosList))
ana_RESTRICTION dg gSigma@(G_sign lid sigma) gSigma'@(G_sign lid' sigma') 
     (Revealed (G_symb_map_items_list lid1 sis) pos) = 
  do let sys = sym_of lid sigma
         sys' = sym_of lid' sigma'
     sis' <- rcoerce lid1 lid' (head (pos++nullPosList)) sis
     rmap <- stat_symb_map_items lid' sis'
     let sys'' = 
          mkSet
           [sy | sy <- setToList sys', rsy <- keysFM rmap, matches lid' sy rsy]
     sys1 <- rcoerce lid lid' (head (pos++nullPosList)) sys
        -- ??? this is too simple in case that local env is translated
        -- to a different logic
     if sys1 `disjoint` sys'' then return ()
      else plain_error () "attempt to hide symbols from the local environment" (head (pos++nullPosList))
     mor1 <- generated_sign lid' (setToList (sys1 `union` sys'')) sigma'
     mor2 <- induced_from_morphism lid' rmap (dom lid' mor1)
     return (gEmbed (G_morphism lid' mor1),
             Just (gEmbed (G_morphism lid' mor2)))



ana_GENERICITY :: GlobalAnnos -> GlobalEnv -> DGraph -> AnyLogic -> GENERICITY
              -> Result (ExtGenSig,DGraph)
ana_GENERICITY gannos genv dg l 
               (Genericity (Params []) (Imported []) pos) = 
  return ((EmptyNode l,[],EmptyNode l),dg)

ana_GENERICITY gannos genv dg l (Genericity params imps pos) = 
  ana_err "parameterized specs"

---- helpers ---------------------------------
ana_err :: String -> a
ana_err fname = 
    error ("*** Analysis of \"" ++ fname ++ "\" is not yet implemented!")

----------------------------------------------