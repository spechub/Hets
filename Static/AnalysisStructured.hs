{- | 
   
   Module      :  $Header$
   Copyright   :  (c)  Till Mossakowski and Uni Bremen 2003
   Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

   Maintainer  :  hets@tzi.de
   Stability   :  provisional
   Portability :  portable

   Analysis of structured specifications

   Follows the extended static semantic rules in:

   T. Mossakowski, S. Autexier, D. Hutter, P. Hoffman:
   CASL Proof calculus.
   Available from <http://www.informatik.uni-bremen.de/~till/calculus.ps>
   To appear in the CASL book.

   Todo:
   Combine signature fragments into whole signatures

   Name views in devgraphs?

   Check that translations and reductions do not effect local env

   Unions (already in the parser) need unions of logics  
     = suprema in the lattice of default logic inclusions!
     (also needed by closed specs)

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
     Then inclusions are represented by pair of signatures
     (Non-inclusions could be specially displayed in the DG)

   Treatment of translations and reductions along logic translations
   (see WADT 02 paper).
   Open question:
    may local env be translated, and even reduced, along logic translations?
    if yes: how is local env linked to signature of resulting spec?
      (important e.g. for checking that local env is not being renamed?)
      does signature+comorphism suffice, such that c(local env)\subseteq sig?
    if no: this means that only closed specs may be translated

   Revealings without translations: just one arrow

   Pushouts: only admissible within one logic?
   Instantiations with formal parameter: add no new internal nodes
    call extend_morphism

   Optimizations:
   Union nodes can be extended by a basic spec directly (no new node needed)
   no new nodes for trivial translations
   use foldM
   Also: free, cofree nodes
   Basic specs: if local env node is otherwise unused, overwrite it with 
                local sig+axioms

   Ensure that just_struct option leads to disabling of various dg operations
   (show sig, show mor, proving)
-}


module Static.AnalysisStructured (ana_SPEC, ana_GENERICITY, ana_VIEW_TYPE, ana_err)
where

import Data.Maybe
import Logic.Logic
import Logic.Comorphism
import Logic.Grothendieck
import Common.Lib.Graph hiding (empty)
import Static.DevGraph
import Syntax.AS_Structured
import Common.AS_Annotation
import Common.Result
import Common.Id
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Map as Map
import Data.List hiding (union)
import Common.PrettyPrint
import Common.Lib.Pretty
import Control.Monad 

import Common.Lib.Parsec.Pos -- for testing purposes

-- | analyze a SPEC
-- Parameters: global context, local environment,
-- the SIMPLE_ID may be a name if the specification shall be named,
-- flag: shall only the structure be analysed?
ana_SPEC :: LogicGraph -> GlobalContext -> NodeSig -> Maybe SIMPLE_ID -> 
            Bool -> SPEC -> Result (SPEC,NodeSig,DGraph)

ana_SPEC lg gctx@(gannos,genv,dg) nsig name just_struct sp = 

 case sp of

  Basic_spec (G_basic_spec lid bspec) ->
    do G_sign lid' sigma' <- return (getSig nsig)
       sigma <- rcoerce lid' lid (newPos "a" 0 0) sigma'
       (bspec',sigma_local, sigma_complete, ax) <- 
          if just_struct 
           then return (bspec,empty_signature lid, empty_signature lid,[])
           else do b <- maybeToResult (newPos "b" 0 0) 
                          ("no basic analysis for logic "
                                         ++language_name lid) 
                          (basic_analysis lid)
                   b (bspec,sigma,gannos) 
       incl <- ginclusion lg 
                      (G_sign lid sigma) (G_sign lid sigma_complete)
       let node_contents = DGNode {
             dgn_name = name,
             dgn_sign = G_sign lid sigma_complete, -- no, not only the delta
             dgn_sens = G_l_sentence lid ax,
             dgn_origin = DGBasic }
           [node] = newNodes 0 dg
           dg' = insNode (node,node_contents) dg
           link = DGLink {
                    dgl_morphism = incl,
                    dgl_type = GlobalDef,
                    dgl_origin = DGExtension }
           dg'' = case nsig of
                    EmptyNode _ -> dg'
                    NodeSig (n,_) -> insEdge (n,node,link) dg'
       return (Basic_spec (G_basic_spec lid bspec'),
               NodeSig (node,G_sign lid sigma_complete),
               dg'')

  Translation asp ren ->
   do let sp1 = item asp
      (sp1',nsig',dg') <- ana_SPEC lg gctx nsig Nothing just_struct sp1
      n' <- maybeToResult (newPos "c" 0 0) 
              "Internal error: Translation of empty spec" (getNode nsig')
      let gsigma = getSig nsig'
      mor <- ana_RENAMING dg gsigma just_struct ren
      -- ??? check that mor is identity on local env
      let gsigma' = cod Grothendieck mor 
           -- ??? too simplistic for non-comorphism inter-logic translations 
      G_sign lid' _ <- return gsigma'
      let node_contents = DGNode {
            dgn_name = name,
            dgn_sign = gsigma',
            dgn_sens = G_l_sentence lid' [],
            dgn_origin = DGTranslation }
          [node] = newNodes 0 dg'
          link = (n',node,DGLink {
            dgl_morphism = mor,
            dgl_type = GlobalDef,
            dgl_origin = DGTranslation })
      return (Translation (replaceAnnoted sp1' asp) ren,
              NodeSig(node,gsigma'),
              insEdge link $
              insNode (node,node_contents) dg')
      
  Reduction asp restr ->
   do let sp1 = item asp
      (sp1',nsig',dg') <- ana_SPEC lg gctx nsig Nothing just_struct sp1
      let gsigma = getSig nsig
          gsigma' = getSig nsig'
      n' <- maybeToResult (newPos "d" 0 0) 
             "Internal error: Reduction of empty spec" (getNode nsig')
      (hmor,tmor) <- ana_RESTRICTION dg gsigma gsigma' just_struct restr
      -- we treat hiding and revealing differently
      -- in order to keep the dg as simple as possible
      case tmor of
       Nothing ->
        do let gsigma'' = dom Grothendieck hmor
           -- ??? too simplistic for non-comorphism inter-logic reductions 
           G_sign lid' _ <- return gsigma''
           let node_contents = DGNode {
                 dgn_name = name,
                 dgn_sign = gsigma'', -- G_sign lid' (empty_signature lid'), 
                 dgn_sens = G_l_sentence lid' [],
                 dgn_origin = DGHiding }
               [node] = newNodes 0 dg'
               link = (n',node,DGLink {
                  dgl_morphism = hmor,
                  dgl_type = HidingDef,
                  dgl_origin = DGHiding })
           return (Reduction (replaceAnnoted sp1' asp) restr,
                   NodeSig(node,gsigma''),
                   insEdge link $
                   insNode (node,node_contents) dg')
       Just tmor' ->
        -- the case with identity translation leads to a simpler dg
        if tmor' == ide Grothendieck (dom Grothendieck tmor')
         then do
           let gsigma1 = dom Grothendieck tmor'
           -- ??? too simplistic for non-comorphism inter-logic reductions 
           G_sign lid1 _ <- return gsigma1
           let [node1] = newNodes 0 dg'
               node_contents1 = DGNode {
                 dgn_name = name,
                 dgn_sign = gsigma1, --G_sign lid1 (empty_signature lid1),
                 dgn_sens = G_l_sentence lid1 [],
                 dgn_origin = DGRevealing }
               link1 = (n',node1,DGLink {
                 dgl_morphism = hmor,
                 dgl_type = HidingDef,
                 dgl_origin = DGRevealing })
           return (Reduction (replaceAnnoted sp1' asp) restr,
                   NodeSig(node1,gsigma1),
                   insEdge link1 $
                   insNode (node1,node_contents1) dg')
         else do
           let gsigma1 = dom Grothendieck tmor'
               gsigma'' = cod Grothendieck tmor'
           -- ??? too simplistic for non-comorphism inter-logic reductions 
           G_sign lid1 _ <- return gsigma1
           G_sign lid'' _ <- return gsigma''
           let [node1,node''] = newNodes 1 dg'
               node_contents1 = DGNode {
                 dgn_name = Nothing,
                 dgn_sign = gsigma1, --G_sign lid1 (empty_signature lid1),
                 dgn_sens = G_l_sentence lid1 [],
                 dgn_origin = DGRevealing }
               link1 = (n',node1,DGLink {
                 dgl_morphism = hmor,
                 dgl_type = HidingDef,
                 dgl_origin = DGRevealing })
               node_contents'' = DGNode {
                dgn_name = name,
                 dgn_sign = gsigma'', -- G_sign lid'' (empty_signature lid''),
                 dgn_sens = G_l_sentence lid'' [],
                 dgn_origin = DGRevealTranslation }
               link'' = (node1,node'',DGLink {
                 dgl_morphism = tmor',
                 dgl_type = GlobalDef,
                 dgl_origin = DGRevealTranslation })
           return (Reduction (replaceAnnoted sp1' asp) restr,
                   NodeSig(node'',gsigma''),
                   insEdge link'' $
                   insNode (node'',node_contents'') $
                   insEdge link1 $
                   insNode (node1,node_contents1) dg')


  Union [] _ -> return (sp,nsig,dg)
  Union asps pos ->
   do let sps = map item asps
      (sps',nsigs,dg') <- 
          let ana r sp' = do
                (sps1,nsigs,dg') <- r
                (sp1,nsig',dg1) <- ana_SPEC lg (gannos,genv,dg') 
                                            nsig Nothing just_struct sp'
                return (sp1:sps1,nsig':nsigs,dg1)
           in foldl ana (return ([],[],dg)) sps
      let nsigs' = reverse nsigs
      gbigSigma <- homogeneousGsigManyUnion (headPos pos) (map getSig nsigs')
      G_sign lid' _ <- return gbigSigma
      let node_contents = DGNode {
            dgn_name = name,
            dgn_sign = gbigSigma, -- G_sign lid' (empty_signature lid'), 
            dgn_sens = G_l_sentence lid' [],
            dgn_origin = DGUnion }
          [node] = newNodes 0 dg'
          insE dgres (n,gsigma) = do
            dg1 <- dgres
            incl <- ginclusion lg gsigma gbigSigma
            let link = DGLink {
              dgl_morphism = incl,
              dgl_type = GlobalDef,
              dgl_origin = DGUnion }
            return (insEdge (n,node,link) dg1)
      dg'' <- foldl insE (return (insNode (node,node_contents) dg'))
                         (catMaybes (map getNodeAndSig nsigs'))
      return (Union (map (uncurry replaceAnnoted)
                         (zip (reverse sps') asps))
                    pos,
              NodeSig(node,gbigSigma),
              dg'')



  --Extension [] pos -> return (sp,nsig,dg)
  Extension asps pos -> do
   (sps',nsig1,dg1) <- foldl ana (return ([],nsig,dg)) namedSps
   return (Extension (map (uncurry replaceAnnoted)
                          (zip (reverse sps') asps))
                     pos,
           nsig1,dg1)
   where
   namedSps = zip (map (\_ -> Nothing) (tail asps) ++ [name]) (map item asps)
   ana res (name',sp') = do
     (sps',nsig',dg') <- res
     (sp1',nsig1,dg1) <- ana_SPEC lg (gannos,genv,dg') nsig' name' just_struct sp'
     return (sp1':sps',nsig1,dg1)

  Free_spec asp pos ->
   do let sp1 = item asp
      (sp',nsig',dg') <- ana_SPEC lg gctx nsig Nothing just_struct sp1
      n' <- maybeToResult (newPos "e" 0 0) 
            "Internal error: Free spec over empty spec" (getNode nsig')
      let gsigma' = getSig nsig'
      G_sign lid' _ <- return gsigma'
      incl <- ginclusion lg (getSig nsig) gsigma'
      let node_contents = DGNode {
            dgn_name = name,
            dgn_sign = gsigma', -- G_sign lid' (empty_signature lid'), -- delta is empty
            dgn_sens = G_l_sentence lid' [],
            dgn_origin = DGFree }
          [node] = newNodes 0 dg'
          link = (n',node,DGLink {
            dgl_morphism = incl,
            dgl_type = FreeDef nsig,
            dgl_origin = DGFree })
      return (Free_spec (replaceAnnoted sp' asp) pos,
              NodeSig(node,gsigma'),
              insEdge link $
              insNode (node,node_contents) dg')

  Cofree_spec asp pos ->
   do let sp1 = item asp
      (sp',nsig',dg') <- ana_SPEC lg gctx nsig Nothing just_struct sp1
      n' <- maybeToResult (newPos "f" 0 0) 
            "Internal error: Cofree spec over empty spec" (getNode nsig')
      let gsigma' = getSig nsig'
      G_sign lid' _ <- return gsigma'
      incl <- ginclusion lg (getSig nsig) gsigma'
      let node_contents = DGNode {
            dgn_name = name,
            dgn_sign = gsigma', -- G_sign lid' (empty_signature lid'), -- delta is empty
            dgn_sens = G_l_sentence lid' [],
            dgn_origin = DGCofree }
          [node] = newNodes 0 dg'
          link = (n',node,DGLink {
            dgl_morphism = incl,
            dgl_type = CofreeDef nsig,
            dgl_origin = DGCofree })
      return (Cofree_spec (replaceAnnoted sp' asp) pos,
              NodeSig(node,gsigma'),
              insEdge link $
              insNode (node,node_contents) dg')

  Local_spec asp asp' pos ->
   do let sp1 = item asp
          sp1' = item asp'
      (sp2,nsig',dg') <- ana_SPEC lg gctx nsig Nothing just_struct sp1
      (sp2',nsig'',dg'') <- ana_SPEC lg (gannos,genv,dg') nsig' Nothing just_struct sp1'
      n'' <- maybeToResult (newPos "g" 0 0) 
            "Internal error: Local spec over empty spec" (getNode nsig'')
      let gsigma = getSig nsig
          gsigma' = getSig nsig'
          gsigma'' = getSig nsig''
      G_sign lid sigma <- return gsigma
      G_sign lid' sigma' <- return gsigma'
      G_sign lid'' sigma'' <- return gsigma''
      sigma1 <- rcoerce lid' lid (newPos "h" 0 0) sigma'
      sigma2 <- rcoerce lid'' lid (newPos "i" 0 0) sigma''
      let sys = sym_of lid sigma
          sys1 = sym_of lid sigma1
          sys2 = sym_of lid sigma2
      mor3 <- if just_struct then return (ide lid sigma2)
               else cogenerated_sign lid 
                      (sys1 `Set.difference` sys) sigma2
      let sigma3 = dom lid mor3
          -- gsigma2 = G_sign lid sigma2
          gsigma3 = G_sign lid sigma3
          sys3 = sym_of lid sigma3
      when (not( just_struct || sys2 `Set.difference` sys1 `Set.subset` sys3))
       (plain_error () 
         "attempt to hide symbols from the local environment" (headPos pos))
      let node_contents = DGNode {
            dgn_name = name,
            dgn_sign = gsigma3, -- G_sign lid (empty_signature lid), -- delta is empty
            dgn_sens = G_l_sentence lid [],
            dgn_origin = DGLocal }
          [node] = newNodes 0 dg''
          link = (n'',node,DGLink {
            dgl_morphism = gEmbed (G_morphism lid mor3),
            dgl_type = HidingDef,
            dgl_origin = DGLocal })
      return (Local_spec (replaceAnnoted sp2 asp)
                         (replaceAnnoted sp2' asp')
                         pos,
              NodeSig(node,gsigma3),
              insEdge link $
              insNode (node,node_contents) dg'')
        

  Closed_spec asp pos ->
   do let sp1 = item asp
          l = getLogic nsig
      (sp',nsig',dg') <- ana_SPEC lg gctx (EmptyNode l) Nothing just_struct sp1
      n' <- maybeToResult (newPos "j" 0 0) 
            "Internal error: Closed spec over empty spec" (getNode nsig')
      let gsigma = getSig nsig
          gsigma' = getSig nsig'
      gsigma'' <- homogeneousGsigUnion (headPos pos) gsigma gsigma' 
                -- also allow different logics???
      G_sign lid'' _ <- return gsigma''
      incl1 <- ginclusion lg gsigma' gsigma''
      incl2 <- ginclusion lg gsigma' gsigma''
      let [node] = newNodes 0 dg'
          node_contents = DGNode {
            dgn_name = name,
            dgn_sign =  gsigma'', -- G_sign lid'' (empty_signature lid''),
            dgn_sens = G_l_sentence lid'' [],
            dgn_origin = DGClosed }
          link1 = (n',node,DGLink {
            dgl_morphism = incl1,
            dgl_type = GlobalDef,
            dgl_origin = DGClosed })
          link2 = DGLink {
            dgl_morphism = incl2,
            dgl_type = GlobalDef,
            dgl_origin = DGClosedLenv }
          insLink2 = case (getNode nsig) of
                       Nothing -> id
                       Just n -> insEdge (n,node,link2)
      return (Closed_spec (replaceAnnoted sp' asp) pos,
              NodeSig(node,gsigma''),
              insLink2 $
              insEdge link1 $
              insNode (node,node_contents) dg')

  Group asp pos -> do
   (sp',nsig',dg') <- ana_SPEC lg gctx nsig name just_struct (item asp)
   return (Group (replaceAnnoted sp' asp) pos,nsig',dg')


  Spec_inst spname afitargs pos ->
   case Map.lookup spname genv of
    Nothing -> plain_error (sp,nsig,dg) 
                 ("Specification "++ showPretty spname " not found") (headPos pos)
    Just (ViewEntry _) -> 
     plain_error (sp,nsig,dg) 
      (showPretty spname " is a view, not a specification") (headPos pos)
    Just (ArchEntry _) -> 
     plain_error (sp,nsig,dg) 
      (showPretty spname
       " is an architectural, not a structured specification") (headPos pos)
    Just (UnitEntry _) -> 
     plain_error (sp,nsig,dg) 
      (showPretty spname
       " is a unit specification, not a structured specification") (headPos pos)
    Just (SpecEntry gs@(imps,params,_,body)) -> 
     case (\x y -> (x,x-y)) (length afitargs) (length params) of

      -- the case without parameters leads to a simpler dg
      (0,0) -> do
       let gsigmaB = getSig body
       gsigma <- gsigLeftUnion lg (headPos pos) (getSig nsig) gsigmaB
       G_sign lid _ <- return gsigma
       nB <- maybeToResult (headPos pos) 
             "Internal error: empty body spec" (getNode body)
       case (getNode nsig) of

         -- the subcase with empty local env leads to an even simpler dg
         Nothing -> 
          -- if the node shall not be named and the logic does not change, 
          if isNothing name && langNameSig gsigma==langNameSig gsigmaB
            -- then just return the body
           then return (sp,body,dg)
            -- otherwise, we need to create a new one
           else do
             incl <- ginclusion lg gsigmaB gsigma
             let [node] = newNodes 0 dg
                 node_contents = DGNode {
                   dgn_name = name,
                   dgn_sign = gsigma, -- G_sign lid (empty_signature lid),
                   dgn_sens = G_l_sentence lid [],
                   dgn_origin = DGSpecInst spname}
                 link = (nB,node,DGLink {
                   dgl_morphism = incl,
                   dgl_type = GlobalDef,
                   dgl_origin = DGSpecInst spname})
             return (sp,
                     NodeSig(node,gsigma),
                     insEdge link $
                     insNode (node,node_contents) dg)
              
         -- the subcase with nonempty local env 
         Just n -> do
           incl1 <- ginclusion lg (getSig nsig) gsigma
           incl2 <- ginclusion lg gsigmaB gsigma
           let [node] = newNodes 0 dg
               node_contents = DGNode {
                 dgn_name = name,
                 dgn_sign = gsigma, -- G_sign lid (empty_signature lid),
                 dgn_sens = G_l_sentence lid [],
                 dgn_origin = DGSpecInst spname}
               link1 = (n,node,DGLink {
                 dgl_morphism = incl1,
                 dgl_type = GlobalDef,
                 dgl_origin = DGSpecInst spname})
               link2 = (nB,node,DGLink {
                 dgl_morphism = incl2,
                 dgl_type = GlobalDef,
                 dgl_origin = DGSpecInst spname})
           return (sp,
                   NodeSig(node,gsigma),
                   insEdge link1 $
                   insEdge link2 $
                   insNode (node,node_contents) dg)
       
      -- now the case with parameters
      (_,0) -> do
       let fitargs = map item afitargs
       (fitargs',dg',args) <- 
          foldl anaFitArg (return ([],dg,[])) (zip params fitargs)
       let actualargs = reverse args
       (gsigma',morDelta) <- apply_GS (headPos pos) gs actualargs
       gsigmaRes <- homogeneousGsigUnion (headPos pos) (getSig nsig) gsigma'
       G_sign lidRes _ <- return gsigmaRes
       nB <- maybeToResult (headPos pos) 
             "Internal error: empty body spec" (getNode body)
       incl1 <- ginclusion lg (getSig nsig) gsigmaRes
       let [node] = newNodes 0 dg'
           node_contents = DGNode {
             dgn_name = name,
             dgn_sign = gsigmaRes, -- G_sign lid' (empty_signature lid'),
             dgn_sens = G_l_sentence lidRes [],
             dgn_origin = DGSpecInst spname}
           link1 = DGLink {
             dgl_morphism = incl1,
             dgl_type = GlobalDef,
             dgl_origin = DGSpecInst spname}
           insLink1 = case (getNode nsig) of
                        Nothing -> id
                        Just n -> insEdge (n,node,link1)
           link2 = (nB,node,DGLink {
             dgl_morphism = gEmbed morDelta,
             dgl_type = GlobalDef,
             dgl_origin = DGSpecInst spname})
           parLinks = catMaybes (map (parLink gsigmaRes node) actualargs)
       return (Spec_inst spname 
                         (map (uncurry replaceAnnoted)
                              (zip (reverse fitargs') afitargs))
                         pos,
               NodeSig(node,gsigmaRes),
               foldr insEdge
                  (insLink1 $
                   insEdge link2 $
                   insNode (node,node_contents) dg')
                parLinks)
       where
       anaFitArg res (nsig',fa) = do
         (fas',dg1,args) <- res
         (fa',dg',arg) <- ana_FIT_ARG lg (gannos,genv,dg1) 
                                  spname imps nsig' just_struct fa
         return (fa':fas',dg',arg:args)
       parLink gsigma' node (mor_i,nsigA_i) = do
        nA_i <- getNode nsigA_i
        incl <- maybeResult $ ginclusion lg (getSig nsigA_i) gsigma'
        let link = DGLink {
             dgl_morphism = incl,
             dgl_type = GlobalDef,
             dgl_origin = DGClosed }
        return (nA_i,node,link)

      -- finally the case with conflicting numbers of formal and actual parameters
      _ -> 
        plain_error (sp,nsig,dg) 
          (showPretty spname " expects "++show (length params)++" arguments"
           ++" but was given "++show (length afitargs)) (headPos pos)



  Qualified_spec logname asp pos ->
   ana_err "logic qualified specs"

{-
  Data (Logic lid1) asp1 asp2 pos ->
   do let sp1 = item asp1
          sp2 = item asp2
          l = getLogic nsig
      (sp1',nsig1,dg1) <- 
         ana_SPEC lg gctx (EmptyNode lid1) Nothing just_struct sp1
      (sp2',nsig2,dg2) <- 
         ana_SPEC lg (gannos,genv,dg1) nsig1 Nothing just_struct sp2
      n' <- maybeToResult (newPos "k" 0 0) 
            "Internal error: Data spec over empty spec" (getNode nsig1)
      let gsigma' = getSig nsig1
      G_sign lid' sigma' <- return gsigma'
      let node_contents = DGNode {
            dgn_name = name,
            dgn_sign = gsigma', -- G_sign lid' (empty_signature lid'), -- delta is empty
            dgn_sens = G_l_sentence lid' [],
            dgn_origin = DGFree }
          [node] = newNodes 0 dg2
          link = (n',node,DGLink {
            dgl_morphism = error "AnalysisStructured.hs:5", -- ??? inclusion
            dgl_type = FreeDef nsig,
            dgl_origin = DGFree })
      return (Data (Logic lid1) 
                   (replaceAnnoted sp1' asp1) 
                   (replaceAnnoted sp2' asp2) 
                   pos,
              NodeSig(node,gsigma'),
              insEdge link $
              insNode (node,node_contents) dg2)
-}

-- analysis of renamings

ana_ren1 :: DGraph -> GMorphism -> (G_mapping,Pos) -> Result GMorphism
ana_ren1 _ (GMorphism r sigma mor) 
           (G_symb_map (G_symb_map_items_list lid sis),pos) = do
  let lid2 = targetLogic r
  sis1 <- rcoerce lid2 lid pos sis
  rmap <- stat_symb_map_items lid2 sis1
  mor1 <- induced_from_morphism lid2 rmap (cod lid2 mor)
  mor2 <- maybeToResult pos 
                        "renaming: signature morphism composition failed" 
                        (comp lid2 mor mor1)
  return (GMorphism r sigma mor2)
 
ana_ren1 _ mor (G_logic_translation (Logic_code tok src tar pos1),pos2) =
  fatal_error "no analysis of logic translations yet" pos2

ana_ren :: DGraph -> Result GMorphism -> (G_mapping,Pos) -> Result GMorphism
ana_ren dg mor_res ren =
  do mor <- mor_res
     ana_ren1 dg mor ren

ana_RENAMING :: DGraph -> G_sign -> Bool -> RENAMING -> Result GMorphism
ana_RENAMING dg gSigma just_struct (Renaming ren pos) = 
  if just_struct 
     then return (ide Grothendieck gSigma)
     else foldl (ana_ren dg) (return (ide Grothendieck gSigma)) ren'
  where
  ren' = zip ren (tail (pos ++ repeat (newPos "l" 0 0)))


-- analysis of restrictions

ana_restr1 :: DGraph -> G_sign -> GMorphism -> (G_hiding,Pos) -> Result GMorphism
ana_restr1 _ (G_sign lid sigma) (GMorphism cid sigma1 mor) 
           (G_symb_list (G_symb_items_list lid' sis'),pos) = do
  let lid1 = sourceLogic cid
      lid2 = targetLogic cid
  sis1 <- rcoerce lid1 lid' pos sis'
  rsys <- stat_symb_items lid1 sis1
  let sys = sym_of lid1 sigma1
  let sys' = Set.filter (\sy -> any (\rsy -> matches lid1 sy rsy) rsys)
                        sys
--     if sys' `disjoint` () then return ()
--      else plain_error () "attempt to hide symbols from the local environment" pos
  mor1 <- cogenerated_sign lid1 sys' sigma1
  mor1' <- maybeToResult pos 
             ("restriction: could not map morphism along" ++ language_name cid)
             (map_morphism cid mor1)
  mor2 <- maybeToResult pos 
                        "restriction: signature morphism composition failed" 
                        (comp lid2 mor1' mor)
  return (GMorphism cid (dom lid1 mor1) mor2)
 
ana_restr1 dg gSigma mor 
           (G_logic_projection (Logic_code tok src tar pos1),pos2) =
  fatal_error "no analysis of logic projections yet" pos2

ana_restr :: DGraph -> G_sign -> Result GMorphism -> (G_hiding,Pos) 
               -> Result GMorphism
ana_restr dg gSigma mor_res restr =
  do mor <- mor_res
     ana_restr1 dg gSigma mor restr

ana_RESTRICTION :: DGraph -> G_sign -> G_sign -> Bool -> RESTRICTION 
       -> Result (GMorphism, Maybe GMorphism)
ana_RESTRICTION _ _ gSigma True _ =
  return (ide Grothendieck gSigma,Nothing)
ana_RESTRICTION dg gSigma gSigma' False (Hidden restr pos) = 
  do mor <- foldl (ana_restr dg gSigma) 
                  (return (ide Grothendieck gSigma'))
                  restr'
     return (mor,Nothing)
  where
  restr' = zip restr (tail (pos ++ repeat (newPos "m" 0 0)))
  -- ??? Need to check that local env is not affected !
ana_RESTRICTION _ (G_sign lid sigma) (G_sign lid' sigma') 
     False (Revealed (G_symb_map_items_list lid1 sis) pos) = 
  do let sys = sym_of lid sigma
         sys' = sym_of lid' sigma'
     sis' <- rcoerce lid1 lid' (headPos pos) sis
     rmap <- stat_symb_map_items lid' sis'
     let sys'' = 
          Set.fromList
           [sy | sy <- Set.toList sys', rsy <- Map.keys rmap, matches lid' sy rsy]
     sys1 <- rcoerce lid lid' (headPos pos) sys
        -- ??? this is too simple in case that local env is translated
        -- to a different logic
     mor1 <- generated_sign lid' (sys1 `Set.union` sys'') sigma'
     mor2 <- induced_from_morphism lid' rmap (dom lid' mor1)
     return (gEmbed (G_morphism lid' mor1),
             Just (gEmbed (G_morphism lid' mor2)))


ana_FIT_ARG :: LogicGraph -> GlobalContext -> SPEC_NAME -> NodeSig -> NodeSig 
               -> Bool 
               -> FIT_ARG
               -> Result (FIT_ARG, DGraph, (G_morphism,NodeSig))
ana_FIT_ARG lg gctx spname nsigI nsigP just_struct 
            (Fit_spec asp gsis pos) = do
   let adj = adjustPos (headPos pos)
   nP <- maybeToResult (headPos pos) 
         "Internal error: empty parameter spec" (getNode nsigP)
   (sp',nsigA,dg') <- ana_SPEC lg gctx nsigI Nothing just_struct (item asp)
   nA <- maybeToResult (headPos pos) 
         "Internal error: empty argument spec" (getNode nsigA)
   let gsigmaP = getSig nsigP
       gsigmaA = getSig nsigA
       gsigmaI = getSig nsigI
   G_sign lidP sigmaP <- return gsigmaP
   G_sign lidA sigmaA <- return gsigmaA
   G_sign lidI sigmaI <- return gsigmaI
   G_symb_map_items_list lid sis <- return gsis
   sigmaA' <- rcoerce lidA lidP (headPos pos) sigmaA
   sigmaI' <- rcoerce lidI lidP (headPos pos) sigmaI
   mor <- if just_struct then return (ide lidP sigmaP)
           else do
             rmap <- adj $ stat_symb_map_items lid sis
             rmap' <- rcoerce lid lidP (headPos pos) rmap
             adj $ induced_from_to_morphism lidP rmap' sigmaP sigmaA'
   let symI = sym_of lidP sigmaI'
       symmap_mor = symmap_of lidP mor
   -- are symbols of the imports left untouched?
  {- if Set.all (\sy -> lookupFM symmap_mor sy == Just sy) symI
    then return ()
    else plain_error () "Fitting morphism must not affect import" (headPos pos)
   -} -- ??? does not work
      -- ??? also output some symbol that is affected
   let link = (nP,nA,DGLink {
         dgl_morphism = gEmbed (G_morphism lidP mor),
         dgl_type = GlobalThm Open None Open,
         dgl_origin = DGSpecInst spname})
   return (Fit_spec (replaceAnnoted sp' asp) gsis pos,
           insEdge link dg',
           (G_morphism lidP mor,nsigA)
           )

ana_FIT_ARG lg gctx@(gannos,genv,dg) spname nsigI nsigP just_struct 
            fv@(Fit_view vn afitargs pos ans) = do
   case Map.lookup vn genv of
    Nothing -> plain_error (fv,dg,error "no morphism") 
                 ("View "++ showPretty vn " not found") (headPos pos)
    Just (SpecEntry _) -> 
     plain_error (fv,dg,error "no fit view") 
      (showPretty spname " is a specification, not a view") (headPos pos)
    Just (ArchEntry _) -> 
     plain_error (fv,dg,error "no fit view") 
      (showPretty spname
       " is an architectural specification, not a view ") (headPos pos)
    Just (UnitEntry _) -> 
     plain_error (fv,dg,error "no fit view") 
      (showPretty spname
       " is a unit specification, not a view") (headPos pos)
    Just (ViewEntry (src,mor,gs@(imps,params,_,target))) -> do
     nSrc <- maybeToResult (headPos pos) 
             "Internal error: empty source spec of view" (getNode src)
     nTar <- maybeToResult (headPos pos) 
             "Internal error: empty target spec of view" (getNode target)
     nP <- maybeToResult (headPos pos) 
             "Internal error: empty parameter specification" (getNode nsigP)
     let gsigmaS = getSig src
         gsigmaT = getSig target
         gsigmaP = getSig nsigP
         gsigmaI = getSig nsigI
     gsigmaIS <- gsigLeftUnion lg (headPos pos) gsigmaI gsigmaS
     when (not (gsigmaIS == gsigmaP))
          (pplain_error () 
              (ptext "Parameter does not match source of fittig view."
               $$ ptext "Parameter signature:"
               $$ printText gsigmaP
               $$ ptext "Source signature of fitting view (united with import):"
               $$ printText gsigmaIS) (headPos pos))
     GMorphism cid _ morHom <- return mor
     let lid = targetLogic cid
     when (not (language_name (IdComorphism lid) == language_name cid))
          (fatal_error  
                 "heterogeneous fitting views not yet implemented"
                 (headPos pos))
     case (\x y -> (x,x-y)) (length afitargs) (length params) of

      -- the case without parameters leads to a simpler dg
      (0,0) -> case (getNode nsigI) of

         -- the subcase with empty import leads to a simpler dg
         Nothing -> do
           let link = (nP,nSrc,DGLink {
                 dgl_morphism = ide Grothendieck gsigmaP,
                 dgl_type = GlobalThm Open None Open,
                 dgl_origin = DGFitView spname})
           return (fv,insEdge link dg,(G_morphism lid morHom,target))
              
         -- the subcase with nonempty import
         Just nI -> do
           G_sign lidI sigI1 <- return gsigmaI
           sigI <- rcoerce lidI lid (headPos pos) sigI1
           mor_I <- morphism_union lid morHom $ ide lid sigI 
           gsigmaA <- gsigLeftUnion lg (headPos pos) gsigmaI gsigmaT
           G_sign lidA _ <- return gsigmaA
           G_sign lidP _ <- return gsigmaP
           incl1 <- ginclusion lg gsigmaI gsigmaA
           incl2 <- ginclusion lg gsigmaT gsigmaA
           incl3 <- ginclusion lg gsigmaI gsigmaP
           incl4 <- ginclusion lg gsigmaS gsigmaP
           let [nA,n'] = newNodes 1 dg
               node_contentsA = DGNode {
                 dgn_name = Nothing,
                 dgn_sign = gsigmaA, 
                 dgn_sens = G_l_sentence lidA [],
                 dgn_origin = DGFitViewA spname}
               node_contents' = DGNode {
                 dgn_name = Nothing,
                 dgn_sign = gsigmaP, 
                 dgn_sens = G_l_sentence lidP [],
                 dgn_origin = DGFitView spname}
               link = (nP,n',DGLink {
                 dgl_morphism = ide Grothendieck gsigmaP,
                 dgl_type = GlobalThm Open None Open,
                 dgl_origin = DGFitView spname})
               link1 = (nI,nA,DGLink {
                 dgl_morphism = incl1,
                 dgl_type = GlobalDef,
                 dgl_origin = DGFitViewAImp spname})
               link2 = (nTar,nA,DGLink {
                 dgl_morphism = incl2,
                 dgl_type = GlobalDef,
                 dgl_origin = DGFitViewA spname})
               link3 = (nI,n',DGLink {
                 dgl_morphism = incl3,
                 dgl_type = GlobalDef,
                 dgl_origin = DGFitViewImp spname})
               link4 = (nSrc,n',DGLink {
                 dgl_morphism = incl4,
                 dgl_type = GlobalDef,
                 dgl_origin = DGFitView spname})
           return (fv,
                   insEdge link $
                   insEdge link1 $
                   insEdge link2 $
                   insEdge link3 $
                   insEdge link4 $
                   insNode (nA,node_contentsA) $
                   insNode (n',node_contents') dg,
                   (G_morphism lid mor_I,NodeSig (nA,gsigmaA)))
{-
      -- now the case with parameters
      (_,0) -> do
       let fitargs = map item afitargs
       (fitargs',dg',args) <- 
          foldl anaFitArg (return ([],dg,[])) (zip params fitargs)
       let actualargs = reverse args
       (gsigma',morDelta) <- apply_GS (headPos pos) gs actualargs
       gsigmaRes <- homogeneousGsigUnion (headPos pos) (getSig nsig) gsigma'
       G_sign lidRes _ <- return gsigmaRes
       nB <- maybeToResult (headPos pos) 
             "Internal error: empty target spec" (getNode target)
       incl1 <- ginclusion lg (getSig nsig) gsigmaRes
       let [node] = newNodes 0 dg'
           node_contents = DGNode {
             dgn_name = name,
             dgn_sign = gsigmaRes, -- G_sign lid' (empty_signature lid'),
             dgn_sens = G_l_sentence lidRes [],
             dgn_origin = DGSpecInst spname}
           link1 = DGLink {
             dgl_morphism = incl1,
             dgl_type = GlobalDef,
             dgl_origin = DGSpecInst spname}
           insLink1 = case (getNode nsig) of
                        Nothing -> id
                        Just n -> insEdge (n,node,link1)
           link2 = (nB,node,DGLink {
             dgl_morphism = gEmbed morDelta,
             dgl_type = GlobalDef,
             dgl_origin = DGSpecInst spname})
           parLinks = catMaybes (map (parLink gsigmaRes node) actualargs)
       return (Spec_inst spname 
                         (map (uncurry replaceAnnoted)
                              (zip (reverse fitargs') afitargs))
                         pos,
               NodeSig(node,gsigmaRes),
               foldr insEdge
                  (insLink1 $
                   insEdge link2 $
                   insNode (node,node_contents) dg')
                parLinks)
       where
       anaFitArg res (nsig',fa) = do
         (fas',dg1,args) <- res
         (fa',dg',arg) <- ana_FIT_ARG lg (gannos,genv,dg1) 
                                  spname imps nsig' just_struct fa
         return (fa':fas',dg',arg:args)
       parLink gsigma' node (mor_i,nsigA_i) = do
        nA_i <- getNode nsigA_i
        incl <- maybeResult $ ginclusion lg (getSig nsigA_i) gsigma'
        let link = DGLink {
             dgl_morphism = incl,
             dgl_type = GlobalDef,
             dgl_origin = DGClosed }
        return (nA_i,node,link)

      -- finally the case with conflicting numbers of formal and actual parameters
      _ -> 
        plain_error (fv,dg,error "no fit view") 
          (showPretty spname " expects "++show (length params)++" arguments"
           ++" but was given "++show (length afitargs)) (headPos pos)

  warning () "Fitting views not yet implemented!!!" (headPos pos)
  G_sign lid sigma <- return (getSig nsigP)
  return (Fit_view vn fas pos ans,
          dg,
          (G_morphism lid (ide lid sigma),nsigP))
  -- ??? Needs to be implemented
-}

-- Extension of signature morphisms (for instantitations)
-- first some auxiliary functions

{- not really needed:
-- for an Id, compute the list of components that are relevant for extension
idComponents :: Id -> Set.Set Id -> [Id]
idComponents (Id toks comps pos) ids =
  foldl (\x y -> y++x) []
    $ map (\id1 -> if id1 `Set.member` ids
                        then [id1]
                        else idComponents id1 ids)
          comps

-- 
componentRelation :: Set.Set Id -> Set.Set (Id,[Id])
componentRelation ids =
  Set.image (\id -> (id,idComponents id ids)) ids
-}

mapID :: Pos -> Map.Map Id (Set.Set Id) -> Id -> Result Id
mapID pos idmap id@(Id toks comps pos1) =
  case Map.lookup id idmap of
    Nothing -> do
      compsnew <- sequence $ map (mapID pos idmap) comps
      return (Id toks compsnew pos1)
    Just ids -> case Set.size ids of
      0 -> return id
      1 -> return $ Set.findMin ids
      2 -> pplain_error id 
             (ptext "Identifier component " <+> printText id
              <+> ptext "can be mapped in various ways:"
              <+> printText ids) pos

extID1 :: Pos -> Map.Map Id (Set.Set Id) -> Id 
              -> Result (Map.EndoMap Id) -> Result (Map.EndoMap Id)
extID1 pos idmap id@(Id toks comps pos1) m = do
  m1 <- m
  compsnew <- sequence $ map (mapID pos idmap) comps
  if comps==compsnew 
   then return m1
   else return (Map.insert id (Id toks compsnew pos1) m1)

extID :: Pos -> Set.Set Id -> Map.Map Id (Set.Set Id) -> Result (Map.EndoMap Id)
extID pos ids idmap = 
  Set.fold (extID1 pos idmap) (return Map.empty) ids


extendMorphism :: Pos -> G_sign -> G_sign -> G_sign -> G_morphism
                      -> Result(G_sign,G_morphism)
extendMorphism pos (G_sign lid sigmaP) (G_sign lidB sigmaB1)
                   (G_sign lidA sigmaA1) (G_morphism lidM fittingMor1) = do
  -- for now, only homogeneous instantiations....
  sigmaB <- rcoerce lidB lid pos sigmaB1
  sigmaA <- rcoerce lidA lid pos sigmaA1
  fittingMor <- rcoerce lidM lid pos fittingMor1
  let symsP = sym_of lid sigmaP
      symsB = sym_of lid sigmaB
      idsB = Set.image (sym_name lid) symsB
      h = symmap_of lid fittingMor
      symbMapToRawSymbMap =
          Map.foldWithKey (\sy1 sy2 -> Map.insert (symbol_to_raw lid sy1) 
                                                  (symbol_to_raw lid sy2)) 
                          Map.empty
      rh = symbMapToRawSymbMap h
      idh = Map.foldWithKey 
             (\sy1 sy2 -> Map.setInsert (sym_name lid sy1) (sym_name lid sy2)) 
             Map.empty h
  idhExt <- extID pos idsB idh
  let rIdExt = Map.foldWithKey 
                (\id1 id2 -> Map.insert (id_to_raw lid id1) (id_to_raw lid id2)) 
                Map.empty 
                (foldr (\id -> Map.delete id) idhExt $ Map.keys idh)
      r = rh `Map.union` rIdExt
      -- do we need combining function catching the clashes???
  mor <- induced_from_morphism lid r sigmaB
  let hmor = symmap_of lid mor
      sigmaAD = cod lid mor
  sigma <- final_union lid sigmaA sigmaAD
  let illShared = (sym_of lid sigmaA `Set.intersection` sym_of lid sigmaAD )
                   Set.\\ Map.image h symsP
  when (not (Set.isEmpty illShared))
   (pplain_error () (ptext 
     "Symbols shared between actual parameter and body must be in formal parameter"
     $$ printText illShared) pos)
  let newIdentifications = Map.kernel hmor Set.\\ Map.kernel h
                           Set.\\ Set.fromList (map (\x -> (x,x)) (Map.keys hmor))
  when (not (Set.isEmpty newIdentifications))
   (pplain_error () (ptext 
     "Fitting morphism leads to forbidden identifications"
     $$ printText newIdentifications) pos)
  incl <- inclusion lid sigmaAD sigma
  mor1 <- maybeToResult pos 
            ("extendMorphism: composition of two morphisms failed:" 
             ++showPretty mor "\n" ++ showPretty incl "") 
            $ comp lid mor incl
  return (G_sign lid sigma, G_morphism lid mor1)


apply_GS :: Pos -> ExtGenSig -> [(G_morphism,NodeSig)] -> Result(G_sign,G_morphism)
apply_GS pos (nsigI,params,gsigmaP,nsigB) args = do
  let mor_i = map fst args
      gsigmaA_i = map (getSig . snd) args
      gsigmaB = getSig nsigB
      gsigmaI = getSig nsigI
  G_sign lidI sigmaI <- return gsigmaI
  let idI = ide lidI sigmaI
  gsigmaA <- homogeneousGsigManyUnion pos gsigmaA_i
  mor_f <- homogeneousMorManyUnion pos (G_morphism lidI idI:mor_i)
  extendMorphism pos gsigmaP gsigmaB gsigmaA mor_f

-- | analyze a GENERICITY
-- Parameters: global context, current logic, just-structure-flag, GENERICITY
ana_GENERICITY :: LogicGraph -> GlobalContext -> AnyLogic -> Bool 
                    -> GENERICITY
                    -> Result (GENERICITY,ExtGenSig,DGraph)

-- zero parameters,
ana_GENERICITY _ (_,_,dg) l@(Logic lid) _
               gen@(Genericity (Params []) (Imported imps) pos) = do
  when (not (null imps)) 
   (plain_error () "Parameterless specifications must not have imports" 
     (headPos pos))
  return (gen,(EmptyNode l,[],G_sign lid (empty_signature lid),EmptyNode l),dg)

-- one parameter ...
ana_GENERICITY lg gctx@(gannos,genv,_) l just_struct 
               (Genericity (Params [asp]) imps pos) = do
  (imps',nsigI,dg') <- ana_IMPORTS lg gctx l just_struct imps
  (sp',nsigP,dg'') <- ana_SPEC lg (gannos,genv,dg') nsigI Nothing just_struct (item asp)
  return (Genericity (Params [replaceAnnoted sp' asp]) imps' pos,
          (nsigI,[nsigP],getSig nsigP,nsigP),
          dg'')

-- ... and more parameters
ana_GENERICITY lg gctx@(gannos,genv,_) l just_struct 
               (Genericity params imps pos) = do
  (imps',nsigI,dg') <- ana_IMPORTS lg gctx l just_struct imps
  (params',nsigPs,dg'') <- 
      ana_PARAMS lg (gannos,genv,dg') l nsigI just_struct params
  gsigmaP <- homogeneousGsigManyUnion (headPos pos) (map getSig nsigPs)
  G_sign lidP _ <- return gsigmaP
  let node_contents = DGNode {
        dgn_name = Nothing,
        dgn_sign = gsigmaP, -- G_sign lidP (empty_signature lidP),
        dgn_sens = G_l_sentence lidP [],
        dgn_origin = DGFormalParams }
      [node] = newNodes 0 dg''
      dg''' = insNode (node,node_contents) dg''
      inslink dgres nsig = do
        dg <- dgres
        case getNode nsig of
         Nothing -> return dg
         Just n -> do 
           incl <- ginclusion lg (getSig nsig) gsigmaP
           return (insEdge (n,node,DGLink {
                     dgl_morphism = incl,
                     dgl_type = GlobalDef,
                     dgl_origin = DGFormalParams }) dg)
  dg4 <- foldl inslink (return dg''') nsigPs
  return (Genericity params' imps' pos,
          (nsigI,nsigPs,gsigmaP,NodeSig(node,gsigmaP)),
           dg4)

ana_PARAMS :: LogicGraph -> GlobalContext -> AnyLogic -> NodeSig -> Bool 
                -> PARAMS
                -> Result (PARAMS,[NodeSig],DGraph)
ana_PARAMS lg (gannos,genv,dg) _ nsigI just_struct (Params asps) = do
  (sps',pars,dg') <- foldl ana (return ([],[],dg)) (map item asps)
  return (Params (map (uncurry replaceAnnoted)
                      (zip (reverse sps') asps)),
          reverse pars,
          dg')
  where
  ana res sp = do
    (sps',pars,dg1) <- res
    (sp',par,dg') <- ana_SPEC lg (gannos,genv,dg1) nsigI Nothing just_struct sp
    return (sp':sps',par:pars,dg')

ana_IMPORTS ::  LogicGraph -> GlobalContext -> AnyLogic -> Bool -> IMPORTED
                -> Result (IMPORTED,NodeSig,DGraph)
ana_IMPORTS lg gctx l just_struct (Imported asps) = do
  let sp = Union asps (map (\_ -> (newPos "p" 0 0)) asps)
  (Union asps' _,nsig',dg') <- 
       ana_SPEC lg gctx (EmptyNode l) Nothing just_struct sp
  return (Imported asps',nsig',dg')
   -- ??? emptyExplicit stuff needs to be added here

-- | analyze a VIEW_TYPE
-- The first three arguments give the global context
-- The AnyLogic is the current logic
-- The NodeSig is the signature of the parameter of the view
-- flag, whether just the structure shall be analysed
ana_VIEW_TYPE:: LogicGraph -> GlobalContext -> AnyLogic -> NodeSig -> Bool
                 -> VIEW_TYPE
                 -> Result (VIEW_TYPE,(NodeSig,NodeSig),DGraph)
ana_VIEW_TYPE lg gctx@(gannos,genv,_) l parSig just_struct
              (View_type aspSrc aspTar pos) = do
  (spSrc',srcNsig,dg') <- 
     ana_SPEC lg gctx (EmptyNode l) Nothing just_struct (item aspSrc)
  (spTar',tarNsig,dg'') <- 
     ana_SPEC lg (gannos,genv,dg') parSig Nothing just_struct (item aspTar)
  return (View_type (replaceAnnoted spSrc' aspSrc) 
                    (replaceAnnoted spTar' aspTar) 
                    pos,
          (srcNsig,tarNsig),
          dg'')


-- | Auxiliary function for not yet implemented features
ana_err :: String -> a
ana_err fname = 
    error ("*** Analysis of " ++ fname ++ " is not yet implemented!")

