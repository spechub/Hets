{- HetCATS/Static/AnalysisStructured.hs
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

   Revealings wihout translations: just one arrow

   Pushouts: only admissible within one logic?

   Optimizations:
   Union nodes can be extended by a basic spec directly no new node needed)
   Also: free, cofree nodes
-}


module Static.AnalysisStructured
where

import Data.Maybe
import Logic.Logic
import Logic.LogicRepr
import Logic.Grothendieck
import Common.Lib.Graph hiding (empty)
import Static.DevGraph
import Syntax.AS_Structured
import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.GlobalAnnotationsFunctions
import Common.Result
import Common.Id
import Common.Lib.Set hiding (filter)
import qualified Common.Lib.Map as Map
import Data.List hiding (union)
import Common.PrettyPrint

pretty x = show $ printText0 emptyGlobalAnnos x

lookupNode n dg = lab' $ context n dg

setFilter p s = fromList (filter p (toList s))
setAny p s = any p (toList s)
setAll p s = all p (toList s)
s1 `disjoint` s2 = s1 `intersection` s2 == empty

domFM m = fromList (Map.keys m)

ana_SPEC :: GlobalAnnos -> GlobalEnv -> DGraph -> NodeSig 
              -> Maybe SIMPLE_ID -> SPEC
              -> Result (NodeSig,DGraph)

ana_SPEC gannos genv dg nsig name sp = 

 case sp of

  Basic_spec (G_basic_spec lid bspec) ->
    do G_sign lid' sigma' <- return (getSig nsig)
       sigma <- rcoerce lid' lid nullPos sigma'
       b <- maybeToResult nullPos 
                ("no basic analysis for logic "++language_name lid) 
                (basic_analysis lid)
       (sigma_local, sigma_complete, ax) <- b (bspec,sigma,gannos) 
       let node_contents = DGNode {
             dgn_name = name,
             dgn_sign = G_sign lid sigma_local, -- only the delta
             dgn_sens = G_l_sentence lid ax,
             dgn_origin = DGBasic }
           [node] = newNodes 0 dg
           dg' = insNode (node,node_contents) dg
           link = DGLink {
                    dgl_morphism = undefined, -- where to get it from ???
                    dgl_type = GlobalDef,
                    dgl_origin = DGExtension }
           dg'' = case nsig of
                    EmptyNode _ -> dg'
                    NodeSig (n,_) -> insEdge (n,node,link) dg'
       return (NodeSig (node,G_sign lid sigma_complete),dg'')

  Translation asp ren ->
   do let sp = item asp
      (nsig',dg') <- ana_SPEC gannos genv dg nsig Nothing sp
      n' <- maybeToResult nullPos 
              "Internal error: Translation of empty spec" (getNode nsig')
      mor <- ana_RENAMING dg (getSig nsig') ren
      -- ??? check that mor is identity on local env
      let gsigma' = cod Grothendieck mor 
           -- ??? too simplistic for non-comorphism inter-logic translations 
      G_sign lid' sigma' <- return gsigma'
      let node_contents = DGNode {
            dgn_name = name,
            dgn_sign = G_sign lid' (empty_signature lid'), -- delta is empty
            dgn_sens = G_l_sentence lid' [],
            dgn_origin = DGTranslation }
          [node] = newNodes 0 dg'
          link = (n',node,DGLink {
            dgl_morphism = mor,
            dgl_type = GlobalDef,
            dgl_origin = DGTranslation })
      return (NodeSig(node,gsigma'),
              insEdge link $
              insNode (node,node_contents) dg')
      
  Reduction asp restr ->
   do let sp = item asp
      (nsig',dg') <- ana_SPEC gannos genv dg nsig Nothing sp
      let gsigma = getSig nsig
          gsigma' = getSig nsig'
      n' <- maybeToResult nullPos 
             "Internal error: Reduction of empty spec" (getNode nsig')
      (hmor,tmor) <- ana_RESTRICTION dg gsigma gsigma' restr
      -- we treat hiding and revealing differently
      -- in order to keep the dg as simple as possible
      case tmor of
       Nothing ->
        do let gsigma' = dom Grothendieck hmor
           -- ??? too simplistic for non-comorphism inter-logic reductions 
           G_sign lid' sigma' <- return gsigma'
           let node_contents = DGNode {
                 dgn_name = name,
                 dgn_sign = G_sign lid' (empty_signature lid'), 
                 dgn_sens = G_l_sentence lid' [],
                 dgn_origin = DGHiding }
               [node] = newNodes 0 dg'
               link = (n',node,DGLink {
                  dgl_morphism = hmor,
                  dgl_type = HidingDef,
                  dgl_origin = DGHiding })
           return (NodeSig(node,gsigma'),
                   insEdge link $
                   insNode (node,node_contents) dg')
       Just tmor' ->
        do let gsigma1 = dom Grothendieck tmor'
               gsigma'' = cod Grothendieck tmor'
           -- ??? too simplistic for non-comorphism inter-logic reductions 
           G_sign lid1 sigma1 <- return gsigma1
           G_sign lid'' sigma'' <- return gsigma''
           let [node1,node''] = newNodes 1 dg'
               node_contents1 = DGNode {
                 dgn_name = Nothing,
                 dgn_sign = G_sign lid1 (empty_signature lid1),
                 dgn_sens = G_l_sentence lid1 [],
                 dgn_origin = DGRevealing }
               link1 = (n',node1,DGLink {
                 dgl_morphism = hmor,
                 dgl_type = HidingDef,
                 dgl_origin = DGRevealing })
               node_contents'' = DGNode {
                dgn_name = name,
                 dgn_sign = G_sign lid'' (empty_signature lid''),
                 dgn_sens = G_l_sentence lid'' [],
                 dgn_origin = DGRevealTranslation }
               link'' = (node1,node'',DGLink {
                 dgl_morphism = tmor',
                 dgl_type = GlobalDef,
                 dgl_origin = DGRevealTranslation })
           return (NodeSig(node'',gsigma''),
                   insEdge link'' $
                   insNode (node'',node_contents'') $
                   insEdge link1 $
                   insNode (node1,node_contents1) dg')


  Union [] pos -> return (nsig,dg)
  Union asps pos ->
   do let sps = map item asps
      (nsigs,dg') <- let ana r sp = do
                          (nsigs,dg) <- r
                          (nsig,dg1) <- ana_SPEC gannos genv dg nsig Nothing sp
                          return (nsig:nsigs,dg1)
                    in foldl ana (return ([],dg)) sps
      let nsigs' = reverse nsigs
          nodes = catMaybes (map getNode nsigs')
      G_sign lid' bigSigma <- 
           homogeneousGsigManyUnion (headPos pos) (map getSig nsigs')
      let node_contents = DGNode {
            dgn_name = name,
            dgn_sign = G_sign lid' (empty_signature lid'), 
            dgn_sens = G_l_sentence lid' [],
            dgn_origin = DGUnion }
          [node] = newNodes 0 dg'
          link = DGLink {
             dgl_morphism = undefined, -- ??? how to get it?
             dgl_type = GlobalDef,
             dgl_origin = DGUnion }
      return (let insE dg n = insEdge (n,node,link) dg -- link should vary
              in (NodeSig(node,G_sign lid' bigSigma),
                  foldl insE (insNode (node,node_contents) dg') nodes))


  Extension [] pos -> return (nsig,dg)
  Extension asps pos ->
   foldl ana (return (nsig,dg)) namedSps
   where
   namedSps = zip (map (\_ -> Nothing) (tail asps) ++ [name]) (map item asps)
   ana res (name,sp) = do
     (nsig,dg) <- res
     ana_SPEC gannos genv dg nsig name sp

  Free_spec asp pos ->
   do let sp = item asp
      (nsig',dg') <- ana_SPEC gannos genv dg nsig Nothing sp
      n' <- maybeToResult nullPos 
            "Internal error: Free spec over empty spec" (getNode nsig')
      let gsigma' = getSig nsig'
      G_sign lid' sigma' <- return gsigma'
      let node_contents = DGNode {
            dgn_name = name,
            dgn_sign = G_sign lid' (empty_signature lid'), -- delta is empty
            dgn_sens = G_l_sentence lid' [],
            dgn_origin = DGFree }
          [node] = newNodes 0 dg'
          link = (n',node,DGLink {
            dgl_morphism = undefined, -- ??? inclusion
            dgl_type = FreeDef nsig,
            dgl_origin = DGFree })
      return (NodeSig(node,gsigma'),
              insEdge link $
              insNode (node,node_contents) dg')

  Cofree_spec asp pos ->
   do let sp = item asp
      (nsig',dg') <- ana_SPEC gannos genv dg nsig Nothing sp
      n' <- maybeToResult nullPos 
            "Internal error: Free spec over empty spec" (getNode nsig')
      let gsigma' = getSig nsig'
      G_sign lid' sigma' <- return gsigma'
      let node_contents = DGNode {
            dgn_name = name,
            dgn_sign = G_sign lid' (empty_signature lid'), -- delta is empty
            dgn_sens = G_l_sentence lid' [],
            dgn_origin = DGCofree }
          [node] = newNodes 0 dg'
          link = (n',node,DGLink {
            dgl_morphism = undefined, -- ??? inclusion
            dgl_type = CofreeDef nsig,
            dgl_origin = DGCofree })
      return (NodeSig(node,gsigma'),
              insEdge link $
              insNode (node,node_contents) dg')

  Local_spec asp asp' pos ->
   do let sp = item asp
          sp' = item asp'
      (nsig',dg') <- ana_SPEC gannos genv dg nsig Nothing sp
      (nsig'',dg'') <- ana_SPEC gannos genv dg' nsig' Nothing sp'
      n'' <- maybeToResult nullPos 
            "Internal error: Local spec over empty spec" (getNode nsig'')
      let gsigma = getSig nsig
          gsigma' = getSig nsig'
          gsigma'' = getSig nsig''
      G_sign lid sigma <- return gsigma
      G_sign lid' sigma' <- return gsigma'
      G_sign lid'' sigma'' <- return gsigma''
      sigma1 <- rcoerce lid' lid nullPos sigma'
      sigma2 <- rcoerce lid'' lid nullPos sigma''
      let sys = sym_of lid sigma
          sys1 = sym_of lid sigma1
          sys2 = sym_of lid sigma2
      mor3 <- cogenerated_sign lid (toList (sys1 `difference` sys)) sigma2
      let sigma3 = dom lid mor3
          gsigma2 = G_sign lid sigma2
          gsigma3 = G_sign lid sigma3
          sys3 = sym_of lid sigma3
      if sys2 `difference` sys1 `subset` sys3 then return ()
        else plain_error () 
         "attempt to hide symbols from the local environment" (headPos pos)
      let node_contents = DGNode {
            dgn_name = name,
            dgn_sign = G_sign lid (empty_signature lid), -- delta is empty
            dgn_sens = G_l_sentence lid [],
            dgn_origin = DGLocal }
          [node] = newNodes 0 dg''
          link = (n'',node,DGLink {
            dgl_morphism = gEmbed (G_morphism lid mor3),
            dgl_type = HidingDef,
            dgl_origin = DGLocal })
      return (NodeSig(node,gsigma3),
              insEdge link $
              insNode (node,node_contents) dg'')
        

  Closed_spec asp pos ->
   do let sp = item asp
          l = getLogic nsig
      (nsig',dg') <- ana_SPEC gannos genv dg (EmptyNode l) Nothing sp
      n' <- maybeToResult nullPos 
            "Internal error: Closed spec over empty spec" (getNode nsig')
      let gsigma = getSig nsig
          gsigma' = getSig nsig'
      gsigma'' <- homogeneousGsigUnion (headPos pos) gsigma gsigma' 
                -- also allow different logics???
      G_sign lid'' sigma'' <- return gsigma''
      let [node] = newNodes 0 dg'
          node_contents = DGNode {
            dgn_name = name,
            dgn_sign = G_sign lid'' (empty_signature lid''),
            dgn_sens = G_l_sentence lid'' [],
            dgn_origin = DGClosed }
          link1 = (n',node,DGLink {
            dgl_morphism = inclusion gsigma' gsigma'',
            dgl_type = GlobalDef,
            dgl_origin = DGClosed })
          link2 = DGLink {
            dgl_morphism = inclusion gsigma' gsigma'',
            dgl_type = GlobalDef,
            dgl_origin = DGClosedLenv }
          insLink2 = case (getNode nsig) of
                       Nothing -> id
                       Just n -> insEdge (n,node,link2)
      return (NodeSig(node,gsigma''),
              insLink2 $
              insEdge link1 $
              insNode (node,node_contents) dg')

  Group asp pos ->
   ana_SPEC gannos genv dg nsig name (item asp)


  Spec_inst spname afitargs pos ->
   case Map.lookup spname genv of
    Nothing -> plain_error (nsig,dg) 
                 ("Specification "++pretty spname++" not found") (headPos pos)
    Just (ViewEntry _) -> 
     plain_error (nsig,dg) 
      (pretty spname++" is a view, not a specification") (headPos pos)
    Just (ArchEntry _) -> 
     plain_error (nsig,dg) 
      (pretty spname++
       " is an architectural, not a structured specification") (headPos pos)
    Just (UnitEntry _) -> 
     plain_error (nsig,dg) 
      (pretty spname++
       " is a unit specification, not a structured specification") (headPos pos)
    Just (SpecEntry gs@(imps,params,gSigmaP,body)) -> 
     case (\x y -> (x,x-y)) (length afitargs) (length params) of

      -- the case without parameters leads to a simpler dg
      (0,0) -> do
       let gsigmaB = getSig body
       gsigma <- homogeneousGsigUnion (headPos pos) (getSig nsig) gsigmaB
       G_sign lid sigma <- return gsigma
       nB <- maybeToResult (headPos pos) 
             "Internal error: empty body spec" (getNode body)
       case (getNode nsig) of
         -- the case with empty local env leads to an even simpler dg
         Nothing -> case name of
            -- if the node shall not be named, just return the body
           Nothing -> return (body,dg)
            -- if the node shall be named, we need to create a new one
           Just _ ->
            let [node] = newNodes 0 dg
                node_contents = DGNode {
                  dgn_name = name,
                  dgn_sign = G_sign lid (empty_signature lid),
                  dgn_sens = G_l_sentence lid [],
                  dgn_origin = DGSpecInst spname}
                link = (nB,node,DGLink {
                  dgl_morphism = inclusion gsigmaB gsigma,
                  dgl_type = GlobalDef,
                  dgl_origin = DGSpecInst spname})
             in return (NodeSig(node,gsigma),
                        insEdge link $
                        insNode (node,node_contents) dg)
              
         -- the case with nonempty local env 
         Just n ->
          let [node] = newNodes 0 dg
              node_contents = DGNode {
                dgn_name = name,
                dgn_sign = G_sign lid (empty_signature lid),
                dgn_sens = G_l_sentence lid [],
                dgn_origin = DGSpecInst spname}
              link1 = (n,node,DGLink {
                dgl_morphism = inclusion (getSig nsig) gsigma,
                dgl_type = GlobalDef,
                dgl_origin = DGSpecInst spname})
              link2 = (nB,node,DGLink {
                dgl_morphism = inclusion gsigmaB gsigma,
                dgl_type = GlobalDef,
                dgl_origin = DGSpecInst spname})
           in return (NodeSig(node,gsigma),
                      insEdge link1 $
                      insEdge link2 $
                      insNode (node,node_contents) dg)
       
      -- now the general case: with parameters
      (_,0) -> do
       let fitargs = map item afitargs
       (dg',args) <- foldl ana (return (dg,[])) (zip params fitargs)
       let actualargs = reverse args
       (gsigma',mor_f) <- apply_GS (headPos pos) gs actualargs
       G_sign lid' sigma' <- return gsigma'
       gsigmaRes <- homogeneousGsigUnion (headPos pos) (getSig nsig) gsigma'
       nB <- maybeToResult (headPos pos) 
             "Internal error: empty body spec" (getNode body)
       let [node] = newNodes 0 dg'
           node_contents = DGNode {
             dgn_name = name,
             dgn_sign = G_sign lid' (empty_signature lid'),
             dgn_sens = G_l_sentence lid' [],
             dgn_origin = DGSpecInst spname}
           link1 = DGLink {
             dgl_morphism = inclusion (getSig nsig) gsigma',
             dgl_type = GlobalDef,
             dgl_origin = DGSpecInst spname}
           insLink1 = case (getNode nsig) of
                        Nothing -> id
                        Just n -> insEdge (n,node,link1)
           link2 = (nB,node,DGLink {
             dgl_morphism = inclusion (getSig body) gsigma',
             dgl_type = GlobalDef,
             dgl_origin = DGSpecInst spname})
           parLinks = catMaybes (map (parLink node) actualargs)
       return (NodeSig(node,gsigma'),
               foldr insEdge
                  (insLink1 $
                   insEdge link2 $
                   insNode (node,node_contents) dg')
                parLinks)
       where
       ana res (nsig,fa) = do
         (dg,args) <- res
         (dg',arg) <- ana_FIT_ARG gannos genv dg spname imps nsig fa
         return (dg',arg:args)
       parLink node (mor_i,nsigA_i) = do
        nA_i <- getNode nsigA_i
        let link = DGLink {
             dgl_morphism = gEmbed mor_i,
             dgl_type = GlobalDef,
             dgl_origin = DGClosed }
        return (nA_i,node,link)

      -- finally the case with conflicting numbers of formal and actual parameters
      otherwise -> 
        plain_error (nsig,dg) 
          (pretty spname++" expects "++show (length params)++" arguments"
           ++" but was given "++show (length afitargs)) (headPos pos)



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
  ren' = zip ren (tail (pos ++ repeat nullPos))


-- analysis of restrictions

ana_restr1 dg (G_sign lid sigma) (GMorphism lid1 lid2 r sigma1 mor) 
           (G_symb_list (G_symb_items_list lid' sis'),pos) = do
  sis1 <- rcoerce lid1 lid' pos sis'
  rsys <- stat_symb_items lid1 sis1
  let sys = sym_of lid1 sigma1
  let sys' = filter (\sy -> any (\rsy -> matches lid1 sy rsy) rsys) 
                    (toList sys)
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
  restr' = zip restr (tail (pos ++ repeat nullPos))
ana_RESTRICTION dg gSigma@(G_sign lid sigma) gSigma'@(G_sign lid' sigma') 
     (Revealed (G_symb_map_items_list lid1 sis) pos) = 
  do let sys = sym_of lid sigma
         sys' = sym_of lid' sigma'
     sis' <- rcoerce lid1 lid' (headPos pos) sis
     rmap <- stat_symb_map_items lid' sis'
     let sys'' = 
          fromList
           [sy | sy <- toList sys', rsy <- Map.keys rmap, matches lid' sy rsy]
     sys1 <- rcoerce lid lid' (headPos pos) sys
        -- ??? this is too simple in case that local env is translated
        -- to a different logic
     if sys1 `disjoint` sys'' then return ()
      else plain_error () "attempt to hide symbols from the local environment" (headPos pos)
     mor1 <- generated_sign lid' (toList (sys1 `union` sys'')) sigma'
     mor2 <- induced_from_morphism lid' rmap (dom lid' mor1)
     return (gEmbed (G_morphism lid' mor1),
             Just (gEmbed (G_morphism lid' mor2)))



ana_FIT_ARG gannos genv dg spname nsigI nsigP (Fit_spec asp gsis pos) = do
   nP <- maybeToResult nullPos 
         "Internal error: empty parameter spec" (getNode nsigP)
   (nsigA,dg') <- ana_SPEC gannos genv dg nsigI Nothing (item asp)
   nA <- maybeToResult nullPos 
         "Internal error: empty argument spec" (getNode nsigA)
   let gsigmaP = getSig nsigP
       gsigmaA = getSig nsigA
       gsigmaI = getSig nsigI
   G_sign lidP sigmaP <- return gsigmaP
   G_sign lidA sigmaA <- return gsigmaA
   G_sign lidI sigmaI <- return gsigmaI
   G_symb_map_items_list lid sis <- return gsis
   rmap <- stat_symb_map_items lid sis
   sigmaA' <- rcoerce lidA lidP (headPos pos) sigmaA
   sigmaI' <- rcoerce lidI lidP (headPos pos) sigmaI
   rmap' <- rcoerce lid lidP (headPos pos) rmap
   mor <- induced_from_to_morphism lidP rmap' sigmaP sigmaA'
   let symI = sym_of lidP sigmaI'
       symmap_mor = symmap_of lidP mor
   -- are symbols of the imports left untouched?
  {- if setAll (\sy -> lookupFM symmap_mor sy == Just sy) symI
    then return ()
    else plain_error () "Fitting morphism must not affect import" (headPos pos)
   -} -- ??? does not work
      -- ??? also output some symbol that is affected
   let link = (nP,nA,DGLink {
         dgl_morphism = gEmbed (G_morphism lidP mor),
         dgl_type = GlobalThm False,
         dgl_origin = DGSpecInst spname})
   return (insEdge link dg',
           (G_morphism lidP mor,nsigA)
           )

ana_FIT_ARG gannos genv dg spname nsigI nsigP (Fit_view vn fas pos ans) = do
  G_sign lid sigma <- return (getSig nsigP)
  return (dg,(G_morphism lid (ide lid sigma),nsigP))
  -- ??? Needs to be implemented

extendMorphism :: Pos -> G_sign -> G_sign -> G_sign -> G_morphism
                  -> Result(G_sign,G_morphism)
extendMorphism pos gsigma gsigma' gsigmaA mor = 
  return (gsigmaA,mor) -- ??? needs to be implemented

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

ana_GENERICITY :: GlobalAnnos -> GlobalEnv -> DGraph -> AnyLogic -> GENERICITY
              -> Result (ExtGenSig,DGraph)
ana_GENERICITY gannos genv dg l@(Logic lid) 
               (Genericity (Params []) (Imported []) pos) = 
  return ((EmptyNode l,[],G_sign lid (empty_signature lid),EmptyNode l),dg)

ana_GENERICITY gannos genv dg l (Genericity (Params [asp]) imps pos) = do
  (nsigI,dg') <- ana_IMPORTS gannos genv dg l imps
  (nsigP,dg'') <- ana_SPEC gannos genv dg' nsigI Nothing (item asp)
  return ((nsigI,[nsigP],getSig nsigP,nsigP),
          dg'')

ana_GENERICITY gannos genv dg l (Genericity params imps pos) = do
  (nsigI,dg') <- ana_IMPORTS gannos genv dg l imps
  (nsigPs,dg'') <- ana_PARAMS gannos genv dg' l nsigI params
  gsigmaP <- homogeneousGsigManyUnion (headPos pos) (map getSig nsigPs)
  G_sign lidP sigmaP <- return gsigmaP
  let node_contents = DGNode {
        dgn_name = Nothing,
        dgn_sign = G_sign lidP (empty_signature lidP),
        dgn_sens = G_l_sentence lidP [],
        dgn_origin = DGFormalParams }
      [node] = newNodes 0 dg''
      dg''' = insNode (node,node_contents) dg''
      inslink dg nsig = 
        case getNode nsig of
         Nothing -> dg
         Just n -> insEdge (n,node,DGLink {
                     dgl_morphism = inclusion (getSig nsig) gsigmaP,
                     dgl_type = GlobalDef,
                     dgl_origin = DGFormalParams }) dg
  return ((nsigI,nsigPs,gsigmaP,NodeSig(node,gsigmaP)),
          foldl inslink dg''' nsigPs)

ana_PARAMS :: GlobalAnnos -> GlobalEnv -> DGraph -> AnyLogic -> NodeSig -> PARAMS
              -> Result ([NodeSig],DGraph)
ana_PARAMS gannos genv dg l nsigI (Params asps) = do
  (pars,dg') <- foldl ana (return ([],dg)) (map item asps)
  return (reverse pars,dg')
  where
  ana res sp = do
    (pars,dg) <- res
    (par,dg') <- ana_SPEC gannos genv dg nsigI Nothing sp
    return (par:pars,dg')

ana_IMPORTS :: GlobalAnnos -> GlobalEnv -> DGraph -> AnyLogic -> IMPORTED
              -> Result (NodeSig,DGraph)
ana_IMPORTS gannos genv dg l (Imported asps) = do
  let sp = Union asps (map (\_ -> nullPos) asps)
  ana_SPEC gannos genv dg (EmptyNode l) Nothing sp
   -- ??? emptyExplicit stuff needs to be added here

ana_VIEW_TYPE:: GlobalAnnos -> GlobalEnv -> DGraph -> AnyLogic 
                -> NodeSig -> VIEW_TYPE
                -> Result ((NodeSig,NodeSig),DGraph)
ana_VIEW_TYPE gannos genv dg l parSig 
              (View_type aspSrc aspTar pos) = do
  (srcNsig,dg') <- ana_SPEC gannos genv dg (EmptyNode l) Nothing (item aspSrc)
  (tarNsig,dg'') <- ana_SPEC gannos genv dg parSig Nothing (item aspTar)
  return ((srcNsig,tarNsig),dg'')


---- helpers ---------------------------------
ana_err :: String -> a
ana_err fname = 
    error ("*** Analysis of " ++ fname ++ " is not yet implemented!")

----------------------------------------------
