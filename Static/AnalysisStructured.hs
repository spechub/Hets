{- |
Module      :  $Header$
Description :  static analysis of CASL (heterogeneous) structured specifications
Copyright   :  (c) Till Mossakowski and Uni Bremen 2003-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  till@tzi.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Grothendieck)

Static analysis of CASL (heterogeneous) structured specifications
   Follows the verfication semantic rules in Chap. IV:4.7
   of the CASL Reference Manual.
-}

{-
   Todo:

   analysis of basic specs: use union of sigs
   analysis of instantiations:
     if necessary, translate body along inclusion comorphism

   Improve efficiency by storing local signature fragments only

   Name views in devgraphs?

   spec <name> not found: line number!

   Issue warning for unions of non-disjoint signatures
     (and offer tool for renaming?)

   Check that translations and reductions do not effect local env
   (Implement new semantics for revealing here)

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

   No optimization of heterogeneous unions!
     (or use heterogeneous compInclusion in Proofs/Proof.hs)
     (or perhaps abandon optimized unions at all and
      replace compHomInclusion with comp Grothendieck? is this more efficient?)

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

   local: better error message for the following

spec GenCardinality [sort Subject,Object;
                     pred predicate : Subject * Object] =
%%Nat then
local {
            Set [sort Object fit sort Elem |-> Object]
            reveal Set[Object], #__, __eps__,
                   Nat,0,1,2,3,4,5,6,7,8,9,__@@__,__>=__,__<=__
       then
            op toSet : Subject -> Set [Object]
            forall x : Subject; y : Object
            . predicate (x,y) <=> y eps toSet(x)
    }  within
           pred minCardinality(s: Subject;n: Nat) <=>
                    # toSet(s) >= n;
                maxCardinality(s: Subject;n: Nat) <=>
                    # toSet(s) <= n;
                cardinality(s: Subject;n: Nat) <=>
                    # toSet(s) = n
%%} hide Pos,toSet,Set[Object],#__,__eps__,__<=__,__>=__
end
-}

module Static.AnalysisStructured (ana_SPEC, ana_GENERICITY,
                                  ana_VIEW_TYPE, ana_err, isStructured,
                                  ana_RENAMING, ana_RESTRICTION,
                                  homogenizeGM, extendMorphism)
where

import Driver.Options
import Data.Maybe
import Logic.Logic
import Logic.Coerce
import Logic.Comorphism
import Logic.Grothendieck
import Static.DevGraph
import Syntax.AS_Structured
import Common.AS_Annotation hiding (isAxiom,isDef)
import Logic.Prover
import Common.Result
import Common.Id
import Data.Graph.Inductive.Graph
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Rel as Rel(image, setInsert)
import Data.List hiding (union)
import Common.DocUtils
import Control.Monad

getMapAndMaxIndex :: (GlobalContext -> Map.Map Int a) -> GlobalContext
                  -> (Map.Map Int a, Int)
getMapAndMaxIndex f gctx = let m = f gctx in
         (m, if Map.null m then 0 else fst $ Map.findMax m)

sigMapI :: GlobalContext -> (Map.Map Int G_sign, Int)
sigMapI = getMapAndMaxIndex sigMap

morMapI :: GlobalContext -> (Map.Map Int G_morphism, Int)
morMapI = getMapAndMaxIndex morMap

thMapI :: GlobalContext -> (Map.Map Int G_theory, Int)
thMapI = getMapAndMaxIndex thMap

insEdgeNub :: LEdge DGLinkLab -> DGraph -> DGraph
insEdgeNub (v, w, l) g =
   if (l, w) `elem` s then g
      else (p, v, l', (l, w) : s) & g'
   where (Just (p, _, l', s), g') = match v g

-- | analyze a SPEC
-- Parameters: global context, local environment,
-- the SIMPLE_ID may be a name if the specification shall be named,
-- options: here we need the info: shall only the structure be analysed?
ana_SPEC :: LogicGraph -> GlobalContext -> MaybeNode -> NODE_NAME ->
            HetcatsOpts -> SPEC -> Result (SPEC, NodeSig, GlobalContext)
ana_SPEC lg gctx nsig name opts sp =
 let dg = devGraph gctx
 in case sp of
  Basic_spec (G_basic_spec lid bspec) ->
    do G_sign lid' sigma' i1 <- return (getMaybeSig nsig)
       sigma <- coerceSign lid' lid "Analysis of basic spec" sigma'
       (bspec', sigma_complete, ax) <-
          if isStructured opts
           then return (bspec, empty_signature lid, [])
           else do b <- maybeToMonad
                          ("no basic analysis for logic "
                                         ++ language_name lid)
                          (basic_analysis lid)
                   b (bspec, sigma, globalAnnos gctx)
       let (sgMap, s) = sigMapI gctx
           (mrMap, m) = morMapI gctx
           (tMap, t) = thMapI gctx
           gsig = G_sign lid sigma_complete (s+1)
       incl <- ginclusion lg (G_sign lid sigma i1) gsig
       let gTh = G_theory lid sigma_complete (s+1) (toThSens ax) (t+1)
           node_contents =
            DGNode {
             dgn_name = name,
             dgn_theory = gTh,
                       -- no, not only the delta
             dgn_nf = Nothing,
             dgn_sigma = Nothing,
             dgn_origin = DGBasic,
             dgn_cons = None,
             dgn_cons_status = LeftOpen }
           node = getNewNode dg
           dg' = insNode (node,node_contents) dg
           incl' = updateMorIndex (m+1) incl
           link = DGLink {
                    dgl_morphism = incl',
                    dgl_type = GlobalDef,
                    dgl_origin = DGExtension }
           dg'' = case nsig of
                    EmptyNode _ -> dg'
                    JustNode (NodeSig n _) -> insEdgeNub (n,node,link) dg'
       return (Basic_spec (G_basic_spec lid bspec'),
               NodeSig node gsig,
               gctx { devGraph = dg''
                    , sigMap = Map.insert (s+1) gsig sgMap
                    , thMap = Map.insert (t+1) gTh tMap
                    , morMap = Map.insert (m+1) (toG_morphism incl') mrMap})
  Translation asp ren ->
   do let sp1 = item asp
      (sp1', NodeSig n' gsigma, gctx') <-
          ana_SPEC lg gctx nsig (inc name) opts sp1
      let (mrMap, m) = morMapI gctx'
      mor <- ana_RENAMING lg nsig gsigma opts ren
      -- ??? check that mor is identity on local env
      let gsigma' = cod Grothendieck mor
           -- ??? too simplistic for non-comorphism inter-logic translations
      G_sign lid' gsig ind <- return gsigma'
      let node_contents = DGNode {
            dgn_name = name,
            dgn_theory = G_theory lid' gsig ind noSens 0,
            dgn_nf = Nothing,
            dgn_sigma = Nothing,
            dgn_origin = DGTranslation,
            dgn_cons = None,
            dgn_cons_status = LeftOpen }
          dg' = devGraph gctx'
          node = getNewNode dg'
          mor' = updateMorIndex (m+1) mor
          link = (n',node,DGLink {
            dgl_morphism = mor',
            dgl_type = GlobalDef,
            dgl_origin = DGTranslation })
          dg'' = insNode (node,node_contents) dg'
      return (Translation (replaceAnnoted sp1' asp) ren,
              NodeSig node gsigma',
              gctx' { devGraph = insEdgeNub link dg''
                    , morMap = Map.insert (m+1) (toG_morphism mor') mrMap})
  Reduction asp restr ->
   do let sp1 = item asp
      (sp1', NodeSig n' gsigma', gctx') <-
          ana_SPEC lg gctx nsig (inc name) opts sp1
      let gsigma = getMaybeSig nsig
          dg' = devGraph gctx'
          (mrMap, m) = morMapI gctx'
      (hmor,tmor) <- ana_RESTRICTION dg gsigma gsigma' opts restr
      -- we treat hiding and revealing differently
      -- in order to keep the dg as simple as possible
      let hmor' = updateMorIndex (m+1) hmor
      case tmor of
       Nothing ->
        do let gsigma'' = dom Grothendieck hmor
           -- ??? too simplistic for non-comorphism inter-logic reductions
           G_sign lid' gsig ind <- return gsigma''
           let node_contents = DGNode {
                 dgn_name = name,
                 dgn_theory = G_theory lid' gsig ind noSens 0,
                 dgn_nf = Nothing,
                 dgn_sigma = Nothing,
                 dgn_origin = DGHiding,
                 dgn_cons = None,
                 dgn_cons_status = LeftOpen }
               node = getNewNode dg'
               link = (n',node,DGLink {
                  dgl_morphism = hmor',
                  dgl_type = HidingDef,
                  dgl_origin = DGHiding })
               dg'' = insNode (node,node_contents) dg'
           return (Reduction (replaceAnnoted sp1' asp) restr,
                   NodeSig node gsigma'',
                   gctx' { devGraph = insEdgeNub link dg''
                         , morMap = Map.insert (m+1) (toG_morphism hmor')
                                    mrMap
                         })
       Just tmor' -> do
        let gsigma1 = dom Grothendieck tmor'
            gsigma'' = cod Grothendieck tmor'
           -- ??? too simplistic for non-comorphism inter-logic reductions
        G_sign lid1 gsig ind <- return gsigma1
        G_sign lid'' gsig'' ind'' <- return gsigma''
        -- the case with identity translation leads to a simpler dg
        if tmor' == ide Grothendieck (dom Grothendieck tmor')
         then do
           let node1 = getNewNode dg'
               node_contents1 = DGNode {
                 dgn_name = name,
                 dgn_theory = G_theory lid1 gsig ind noSens 0,
                 dgn_nf = Nothing,
                 dgn_sigma = Nothing,
                 dgn_origin = DGRevealing,
                 dgn_cons = None,
                 dgn_cons_status = LeftOpen }
               link1 = (n',node1,DGLink {
                 dgl_morphism = hmor',
                 dgl_type = HidingDef,
                 dgl_origin = DGRevealing })
               dg'' = insNode (node1,node_contents1) dg'
           return (Reduction (replaceAnnoted sp1' asp) restr,
                   NodeSig node1 gsigma1,
                   gctx' { devGraph = insEdgeNub link1 dg''
                         , morMap = Map.insert (m+1) (toG_morphism hmor')
                                    mrMap
                         })
         else do
           let [node1,node''] = newNodes 2 dg'
               node_contents1 = DGNode {
                 dgn_name = extName "T" name,
                 dgn_theory = G_theory lid1 gsig ind noSens 0,
                 dgn_nf = Nothing,
                 dgn_sigma = Nothing,
                 dgn_origin = DGRevealing,
                 dgn_cons = None,
                 dgn_cons_status = LeftOpen }
               link1 = (n',node1,DGLink {
                 dgl_morphism = hmor',
                 dgl_type = HidingDef,
                 dgl_origin = DGRevealing })
               node_contents'' = DGNode {
                dgn_name = name,
                 dgn_theory = G_theory lid'' gsig'' ind'' noSens 0,
                 dgn_nf = Nothing,
                 dgn_sigma = Nothing,
                 dgn_origin = DGRevealTranslation,
                dgn_cons = None,
                dgn_cons_status = LeftOpen }
               link'' = (node1,node'',DGLink {
                 dgl_morphism = tmor',
                 dgl_type = GlobalDef,
                 dgl_origin = DGRevealTranslation })
           return (Reduction (replaceAnnoted sp1' asp) restr,
                   NodeSig node'' gsigma'',
                   gctx' { devGraph = insEdgeNub link'' $
                                      insNode (node'',node_contents'') $
                                      insEdgeNub link1 $
                                      insNode (node1,node_contents1) dg'
                         , morMap = Map.insert (m+1) (toG_morphism hmor')
                                    mrMap
                         })
  Union [] pos -> adjustPos pos $ fail $ "empty union"
  Union asps pos ->
   do let sps = map item asps
      (sps', nsigs, gctx', _) <-
          let ana r sp' = do
                (sps1,nsigs,dg',n) <- r
                (sp1,nsig',dg1) <- ana_SPEC lg dg' nsig n opts sp'
                return (sp1:sps1,nsig':nsigs,dg1,inc n)
           in foldl ana (return ([], [], gctx, extName "U" name)) sps
      let nsigs' = reverse nsigs
          dg' = devGraph gctx'
          adj = adjustPos pos
          (sgMap, s) = sigMapI gctx'
      gbigSigma <- adj $ gsigManyUnion lg (map getSig nsigs')
      G_sign lid' gsig _ <- return gbigSigma
      gbigSigma' <- return $ G_sign lid' gsig (s+1)
      let node_contents = DGNode {
            dgn_name = name,
            dgn_theory = G_theory lid' gsig (s+1) noSens 0,
            dgn_nf = Nothing,
            dgn_sigma = Nothing,
            dgn_origin = DGUnion,
            dgn_cons = None,
            dgn_cons_status = LeftOpen }
          node = getNewNode dg'
          dg1 = insNode (node, node_contents) dg'
          gctx1 = gctx' { devGraph = dg1
                        , sigMap = Map.insert (s+1) gbigSigma' sgMap }
          insE gctxres (NodeSig n gsigma) = do
            gctxl <- gctxres
            let (mrMapl, ml) = morMapI gctxl
                dgl = devGraph gctxl
            incl <- adj $ ginclusion lg gsigma gbigSigma
            let incl' = updateMorIndex (ml+1) incl
                link = DGLink {
                  dgl_morphism = incl',
                  dgl_type = GlobalDef,
                  dgl_origin = DGUnion }
            return (gctxl { devGraph = insEdgeNub (n,node,link) dgl
                          , morMap = Map.insert (ml+1)
                                     (toG_morphism incl') mrMapl})
      gctx2 <- foldl insE (return gctx1) nsigs'
      return (Union (map (uncurry replaceAnnoted)
                         (zip (reverse sps') asps))
                    pos,
              NodeSig node gbigSigma', gctx2)
  Extension asps pos -> do
   (sps',nsig1',dg1, _, _, _) <-
       foldl ana_Extension (return ([], nsig, gctx, lg, opts, pos)) namedSps
   case nsig1' of
       EmptyNode _ -> fail "empty extension"
       JustNode nsig1 -> return (Extension (map (uncurry replaceAnnoted)
                          (zip (reverse sps') asps))
                                 pos, nsig1,dg1)
   where
   namedSps = zip (reverse (name: tail (take (length asps)
                                         (iterate inc (extName "E" name)))))
                   asps

  Free_spec asp poss ->
   do let sp1 = item asp
      (sp', NodeSig n' gsigma'@(G_sign lid' gsig ind), gctx') <-
          ana_SPEC lg gctx nsig (inc name) opts sp1
      let pos = poss
          dg' = devGraph gctx'
          (mrMap, m) = morMapI gctx'
      incl <- adjustPos pos $ ginclusion lg (getMaybeSig nsig) gsigma'
      let incl' = updateMorIndex (m+1) incl
          node_contents = DGNode {
            dgn_name = name,
            dgn_theory = G_theory lid' gsig ind noSens 0, -- delta is empty
            dgn_nf = Nothing,
            dgn_sigma = Nothing,
            dgn_origin = DGFree,
            dgn_cons = None,
            dgn_cons_status = LeftOpen }
          node = getNewNode dg'
          link = (n',node,DGLink {
            dgl_morphism = incl',
            dgl_type = FreeDef nsig,
            dgl_origin = DGFree })
      return (Free_spec (replaceAnnoted sp' asp) poss,
              NodeSig node gsigma',
              gctx' { devGraph = insEdgeNub link $
                                 insNode (node,node_contents) dg'
                    , morMap = Map.insert (m+1) (toG_morphism incl') mrMap})
  Cofree_spec asp poss ->
   do let sp1 = item asp
      (sp', NodeSig n' gsigma'@(G_sign lid' gsig ind), gctx') <-
           ana_SPEC lg gctx nsig (inc name) opts sp1
      let pos = poss
          dg' = devGraph gctx'
          (mrMap, m) = morMapI gctx'
      incl <- adjustPos pos $ ginclusion lg (getMaybeSig nsig) gsigma'
      let incl' = updateMorIndex (m+1) incl
          node_contents = DGNode {
            dgn_name = name,
            dgn_theory = G_theory lid' gsig ind noSens 0, -- delta is empty
            dgn_nf = Nothing,
            dgn_sigma = Nothing,
            dgn_origin = DGCofree,
            dgn_cons = None,
            dgn_cons_status = LeftOpen }
          node = getNewNode dg'
          link = (n',node,DGLink {
            dgl_morphism = incl',
            dgl_type = CofreeDef nsig,
            dgl_origin = DGCofree })
      return (Cofree_spec (replaceAnnoted sp' asp) poss,
              NodeSig node gsigma',
              gctx' { devGraph = insEdgeNub link $
                                 insNode (node,node_contents) dg'
                    , morMap = Map.insert (m+1) (toG_morphism incl') mrMap})
  Local_spec asp asp' poss ->
   do let sp1 = item asp
          sp1' = item asp'
      (sp2, nsig'@(NodeSig _ (G_sign lid' sigma' _)), dg') <-
          ana_SPEC lg gctx nsig (extName "L" name) opts sp1
      (sp2', NodeSig n'' (G_sign lid'' sigma'' _), gctx'') <-
          ana_SPEC lg dg' (JustNode nsig') (inc name) opts sp1'
      let gsigma = getMaybeSig nsig
          dg'' = devGraph gctx''
          (sgMap, s) = sigMapI gctx''
          (mrMap, m) = morMapI gctx''
      G_sign lid sigma _<- return gsigma
      sigma1 <- coerceSign lid' lid "Analysis of local spec" sigma'
      sigma2 <- coerceSign lid'' lid "Analysis of local spec" sigma''
      let sys = sym_of lid sigma
          sys1 = sym_of lid sigma1
          sys2 = sym_of lid sigma2
          pos =  poss
      mor3 <- if isStructured opts then return (ide lid sigma2)
               else adjustPos pos $ cogenerated_sign lid
                      (sys1 `Set.difference` sys) sigma2
      let sigma3 = dom lid mor3
          -- gsigma2 = G_sign lid sigma2
          gsigma3 = G_sign lid sigma3 (s+1)
          sys3 = sym_of lid sigma3
      when (not( isStructured opts ||
                 sys2 `Set.difference` sys1 `Set.isSubsetOf` sys3))
        $ plain_error () (
          "attempt to hide the following symbols from the local environment:\n"
          ++ showDoc ((sys2 `Set.difference` sys1) `Set.difference` sys3) "")
         pos
      let node_contents = DGNode {
            dgn_name = name,
            dgn_theory = G_theory lid sigma3 (s+1) noSens 0,
            dgn_nf = Nothing,
            dgn_sigma = Nothing,
            dgn_origin = DGLocal,
            dgn_cons = None,
            dgn_cons_status = LeftOpen }
          node = getNewNode dg''
          link = (n'', node, DGLink {
            dgl_morphism = gEmbed2 gsigma3 (G_morphism lid mor3 (m+1)),
            dgl_type = HidingDef,
            dgl_origin = DGLocal })
      return (Local_spec (replaceAnnoted sp2 asp)
                         (replaceAnnoted sp2' asp')
                         poss,
              NodeSig node gsigma3,
              gctx'' { devGraph = insEdgeNub link $
                                  insNode (node,node_contents) dg''
                     , sigMap = Map.insert (s+1) gsigma3 sgMap
                     , morMap = Map.insert (m+1) (G_morphism lid mor3 (m+1)) 
                                mrMap 
                     })
  Closed_spec asp pos ->
   do let sp1 = item asp
          l = getLogic nsig
      -- analyse spec with empty local env
      (sp', NodeSig n' gsigma', gctx') <-
          ana_SPEC lg gctx (EmptyNode l) (inc name) opts sp1
      let gsigma = getMaybeSig nsig
          adj = adjustPos pos
          dg' = devGraph gctx'
          (sgMap, s) = sigMapI gctx'
          (mrMap, m) = morMapI gctx'
      gsigma'' <- adj $ gsigUnion lg gsigma gsigma'
      G_sign lid'' gsig'' _ <- return gsigma''
      gsigma2 <- return $ G_sign lid'' gsig'' (s+1)
      incl1 <- adj $ ginclusion lg gsigma gsigma2
      incl2 <- adj $ ginclusion lg gsigma' gsigma2
      let incl1' = updateMorIndex (m+1) incl1
          incl2' = updateMorIndex (m+2) incl2
          node = getNewNode dg'
          node_contents = DGNode {
            dgn_name = name,
            dgn_theory = G_theory lid'' gsig'' (s+1) noSens 0,
            dgn_nf = Nothing,
            dgn_sigma = Nothing,
            dgn_origin = DGClosed,
            dgn_cons = None,
            dgn_cons_status = LeftOpen }
          link1 = DGLink {
            dgl_morphism = incl1',
            dgl_type = GlobalDef,
            dgl_origin = DGClosedLenv }
          link2 = (n',node,DGLink {
            dgl_morphism = incl2',
            dgl_type = GlobalDef,
            dgl_origin = DGClosed })
          insLink1 = case nsig of
                       EmptyNode _ -> id
                       JustNode (NodeSig n _) -> insEdgeNub (n, node, link1)
          morMap1 = Map.insert (m+1) (toG_morphism incl1') mrMap
          morMap2 = Map.insert (m+2) (toG_morphism incl2') morMap1
      return (Closed_spec (replaceAnnoted sp' asp) pos,
              NodeSig node gsigma2,
              gctx' { devGraph = insLink1 $
                                 insEdgeNub link2 $
                                 insNode (node,node_contents) dg'
                    , sigMap = Map.insert (s+1) gsigma2 sgMap
                    , morMap = morMap2})
  Qualified_spec (Logic_name ln sublog) asp pos -> do
      l <- lookupLogic "Static analysis: " (tokStr ln) lg
      -- analyse spec with empty local env
      (sp', NodeSig n' gsigma', gctx') <-
          ana_SPEC lg gctx (EmptyNode l) (inc name) opts (item asp)
      -- construct union with local env
      let gsigma = getMaybeSig nsig
          dg' = devGraph gctx'
          adj = adjustPos pos
          (sgMap, s) = sigMapI gctx'
          (mrMap, m) = morMapI gctx'
      gsigma'' <- adj $ gsigUnion lg gsigma gsigma'
      G_sign lid'' gsig'' _ <- return gsigma''
      gsigma2 <- return $ G_sign lid'' gsig'' (s+1)
      incl1 <- adj $ ginclusion lg gsigma gsigma2
      incl2 <- adj $ ginclusion lg gsigma' gsigma2
      let incl1' = updateMorIndex (m+1) incl1
          incl2' = updateMorIndex (m+2) incl2
          node = getNewNode dg'
          node_contents = DGNode {
            dgn_name = name,
            dgn_theory = G_theory lid'' gsig'' (s+1) noSens 0,
            dgn_nf = Nothing,
            dgn_sigma = Nothing,
            dgn_origin = DGLogicQual,
            dgn_cons = None,
            dgn_cons_status = LeftOpen }
          link1 = DGLink {
            dgl_morphism = incl1',
            dgl_type = GlobalDef,
            dgl_origin = DGLogicQualLenv }
          link2 = (n',node,DGLink {
            dgl_morphism = incl2',
            dgl_type = GlobalDef,
            dgl_origin = DGLogicQual })
          insLink1 = case nsig of
                       EmptyNode _ -> id
                       JustNode (NodeSig n _) -> insEdgeNub (n, node, link1)
          morMap1 = Map.insert (m+1) (toG_morphism incl1') mrMap
          morMap2 = Map.insert (m+2) (toG_morphism incl2') morMap1
      return (Qualified_spec (Logic_name ln sublog)
                                 (replaceAnnoted sp' asp) pos,
              NodeSig node gsigma2,
              gctx' { devGraph = insLink1 $ insEdgeNub link2 $
                                 insNode (node,node_contents) dg'
                    , sigMap = Map.insert (s+1) gsigma2 sgMap
                    , morMap = morMap2})
  Group asp pos -> do
   (sp',nsig',dg') <- ana_SPEC lg gctx nsig name opts (item asp)
   return (Group (replaceAnnoted sp' asp) pos,nsig',dg')
  Spec_inst spname afitargs pos -> do
   let adj = adjustPos pos
       spstr = tokStr spname
       (sgMap, s) = sigMapI gctx
       (mrMap, m) = morMapI gctx
   case Map.lookup spname $ globalEnv gctx of
    Nothing -> fatal_error
                 ("Specification " ++ spstr ++ " not found") pos
    Just (ViewEntry _) ->
     fatal_error
      (spstr ++ " is a view, not a specification") pos
    Just (ArchEntry _) ->
     fatal_error
      (spstr ++
       " is an architectural, not a structured specification") pos
    Just (UnitEntry _) ->
     fatal_error
      (spstr ++
       " is a unit specification, not a structured specification") pos
    Just (RefEntry) ->
     fatal_error
      (spstr ++
       " is a refinement specification, not a structured specification") pos
    Just (SpecEntry gs@(imps,params,_,body@(NodeSig nB gsigmaB))) ->
     case (\x y -> (x,x-y)) (length afitargs) (length params) of
      -- the case without parameters leads to a simpler dg
      (0,0) -> do
       G_sign lid gsig _ <-
           adj $ gsigUnion lg (getMaybeSig nsig) gsigmaB
       let gsigma' = G_sign lid gsig (s+1)
       case nsig of
         -- the subcase with empty local env leads to an even simpler dg
         EmptyNode _ ->
          -- if the node shall not be named and the logic does not change,
          if isInternal name && langNameSig gsigma'==langNameSig gsigmaB
            -- then just return the body
           then return (sp, body, gctx)
            -- otherwise, we need to create a new one
           else do
             incl <- adj $ ginclusion lg gsigmaB gsigma'
             let incl' = updateMorIndex (m+1) incl
                 node = getNewNode dg
                 node_contents = DGNode {
                   dgn_name = name,
                   dgn_theory = G_theory lid gsig (s+1) noSens 0,
                   dgn_nf = Nothing,
                   dgn_sigma = Nothing,
                   dgn_origin = DGSpecInst spname,
                   dgn_cons = None,
                   dgn_cons_status = LeftOpen}
                 link = (nB,node,DGLink {
                   dgl_morphism = incl',
                   dgl_type = GlobalDef,
                   dgl_origin = DGSpecInst spname})
             return (sp,
                     NodeSig node gsigma',
                     gctx { devGraph = insEdgeNub link $
                                       insNode (node,node_contents) dg
                          , sigMap = Map.insert (s+1) gsigma' sgMap
                          , morMap = Map.insert (m+1) (toG_morphism incl') 
                                     mrMap})
         -- the subcase with nonempty local env
         JustNode (NodeSig n sigma) -> do
           incl1 <- adj $ ginclusion lg sigma gsigma'
           incl2 <- adj $ ginclusion lg gsigmaB gsigma'
           let incl1' = updateMorIndex (m+1) incl1
               incl2' = updateMorIndex (m+2) incl2
               node = getNewNode dg
               node_contents = DGNode {
                 dgn_name = name,
                 dgn_theory = G_theory lid gsig (s+1) noSens 0,
                 dgn_nf = Nothing,
                 dgn_sigma = Nothing,
                 dgn_origin = DGSpecInst spname,
                 dgn_cons = None,
                 dgn_cons_status = LeftOpen}
               link1 = (n,node,DGLink {
                 dgl_morphism = incl1',
                 dgl_type = GlobalDef,
                 dgl_origin = DGSpecInst spname})
               link2 = (nB,node,DGLink {
                 dgl_morphism = incl2',
                 dgl_type = GlobalDef,
                 dgl_origin = DGSpecInst spname})
               morMap1 = Map.insert (m+1) (toG_morphism incl1') mrMap
               morMap2 = Map.insert (m+2) (toG_morphism incl2') morMap1
           return (sp,
                   NodeSig node gsigma',
                   gctx { devGraph = insEdgeNub link1 $
                                     insEdgeNub link2 $
                                     insNode (node,node_contents) dg
                        , sigMap = Map.insert (s+1) gsigma' sgMap
                        , morMap = morMap2})
      -- now the case with parameters
      (_,0) -> do
       let fitargs = map item afitargs
       (fitargs', gctx', args, _) <-
          foldl anaFitArg (return ([], gctx, [], extName "A" name))
                          (zip params fitargs)
       let actualargs = reverse args
           dg' = devGraph gctx'
       (gsigma',morDelta) <- adj $ apply_GS lg gs actualargs
       gsigmaRes <- adj $ gsigUnion lg (getMaybeSig nsig) gsigma'
       G_sign lidRes gsigRes _ <- return gsigmaRes
       gsigmaRes' <- return $ G_sign lidRes gsigRes (s+1)
       incl1 <- adj $ ginclusion lg (getMaybeSig nsig) gsigmaRes'
       incl2 <- adj $ ginclusion lg gsigma' gsigmaRes'
       let incl1' = updateMorIndex (m+1) incl1
           incl2' = updateMorIndex (m+2) incl2
       morDelta' <- comp Grothendieck (gEmbed morDelta) incl2'
       let node = getNewNode dg'
           node_contents = DGNode {
             dgn_name = name,
             dgn_theory = G_theory lidRes gsigRes (s+1) noSens 0,
             dgn_nf = Nothing,
             dgn_sigma = Nothing,
             dgn_origin = DGSpecInst spname,
             dgn_cons = None,
             dgn_cons_status = LeftOpen}
           link1 = DGLink {
             dgl_morphism = incl1',
             dgl_type = GlobalDef,
             dgl_origin = DGSpecInst spname}
           insLink1 = case nsig of
                        EmptyNode _ -> id
                        JustNode (NodeSig n _) -> insEdgeNub (n, node, link1)
           link2 = (nB,node,DGLink {
             dgl_morphism = morDelta',
             dgl_type = GlobalDef,
             dgl_origin = DGSpecInst spname})
           parLinks = catMaybes (map (parLink gsigmaRes' node) actualargs)
           morMap1 = Map.insert (m+1) (toG_morphism incl1') mrMap
           morMap2 = Map.insert (m+2) (toG_morphism incl2') morMap1
       return (Spec_inst spname
                         (map (uncurry replaceAnnoted)
                              (zip (reverse fitargs') afitargs))
                         pos,
               NodeSig node gsigmaRes',
               gctx' { devGraph = foldr insEdgeNub
                                  (insLink1 $ insEdgeNub link2 $
                                   insNode (node,node_contents) dg')
                                  parLinks
                     , sigMap = Map.insert (s+1) gsigmaRes' sgMap
                     , morMap = morMap2})
       where
       anaFitArg res (nsig', fa) = do
         (fas', dg1, args, name') <- res
         (fa', dg', arg) <- ana_FIT_ARG lg dg1 spname imps nsig' opts name' fa
         return (fa' : fas', dg', arg : args , inc name')
       parLink gsigma' node (_mor_i, NodeSig nA_i sigA_i) = do
        incl <- maybeResult $ ginclusion lg sigA_i gsigma'
        let link = DGLink {
             dgl_morphism = incl,
             dgl_type = GlobalDef,
             dgl_origin = DGFitSpec }
        return (nA_i,node,link)
 -- finally the case with conflicting numbers of formal and actual parameters
      _ ->
        fatal_error
          (spstr ++ " expects " ++ show (length params) ++ " arguments"
           ++ " but was given " ++ show (length afitargs)) pos
  Data (Logic lidD) (Logic lidP) asp1 asp2 pos ->
   do let sp1 = item asp1
          sp2 = item asp2
          adj = adjustPos pos
      Comorphism cid <- adj $ logicInclusion lg (Logic lidD) (Logic lidP)
      let lidD' = sourceLogic cid
          lidP' = targetLogic cid
      (sp1', NodeSig n' (G_sign lid' sigma' _), gctx1) <-
         ana_SPEC lg gctx (EmptyNode (Logic lidD)) (inc name) opts sp1
      sigmaD <- adj $ coerceSign lid' lidD' "Analysis of data spec" sigma'
      (sigmaD',sensD') <- adj $ map_sign cid sigmaD
      let gsigmaD' = G_sign lidP' sigmaD' 0
          dg1 = devGraph gctx1
          node_contents = DGNode {
            dgn_name = name,
            dgn_theory = G_theory lidP' sigmaD' 0 (toThSens sensD') 0,
            dgn_nf = Nothing,
            dgn_sigma = Nothing,
            dgn_origin = DGData,
            dgn_cons = None,
            dgn_cons_status = LeftOpen }
          node = getNewNode dg1
          link = (n',node,DGLink {
            dgl_morphism = GMorphism cid sigmaD 0 (ide lidP' sigmaD') 0,
            dgl_type = GlobalDef,
            dgl_origin = DGData })
          dg2 = insEdgeNub link $
                insNode (node,node_contents) dg1
          nsig2 = NodeSig node gsigmaD'
      (sp2',nsig3,dg3) <-
         ana_SPEC lg gctx1 { devGraph = dg2 } (JustNode nsig2) name opts sp2
      return (Data (Logic lidD) (Logic lidP)
                   (replaceAnnoted sp1' asp1)
                   (replaceAnnoted sp2' asp2)
                   pos,
              nsig3, dg3)

-- analysis of renamings

ana_ren1 :: LogicGraph -> MaybeNode -> Range -> GMorphism -> G_mapping
             -> Result GMorphism
ana_ren1 _ lenv _pos (GMorphism r sigma ind1 mor ind2)
           (G_symb_map (G_symb_map_items_list lid sis)) = do
  let lid2 = targetLogic r
  sis1 <- coerceSymbMapItemsList lid lid2 "Analysis of renaming" sis
  rmap <- stat_symb_map_items lid2 sis1
  mor1 <- induced_from_morphism lid2 rmap (cod lid2 mor)
  case lenv of
    EmptyNode _ -> return ()
    JustNode (NodeSig _ (G_sign lidLenv sigmaLenv _)) -> do
    -- needs to be changed for logic translations
      sigmaLenv' <- coerceSign lidLenv lid2
        "Analysis of renaming: logic translations not yet properly handeled"
            sigmaLenv
      let sysLenv = sym_of lid2 sigmaLenv'
          m = symmap_of lid2 mor1
          isChanged sy = case Map.lookup sy m of
            Just sy' -> sy /= sy'
            Nothing -> False
          _forbiddenSys = Set.filter isChanged sysLenv
      return ()
{-      when (not (forbiddenSys == Set.empty)) $ plain_error () (
        "attempt to rename the following symbols from the local environment:\n"
             ++ showDoc forbiddenSys "") pos
-}
  mor2 <- comp lid2 mor mor1
  return $ GMorphism r sigma ind1 mor2 0

ana_ren1 lg _ _ mor (G_logic_translation (Logic_code tok src tar pos1)) = do
  let adj = adjustPos pos1
  G_sign srcLid srcSig ind<- return (cod Grothendieck mor)
  c <- adj $ case tok of
            Just ctok -> do
               Comorphism cid <- lookupComorphism (tokStr ctok) lg
               when (isJust src && getLogicStr (fromJust src) /=
                                    language_name (sourceLogic cid))
                    (fail (getLogicStr (fromJust src) ++
                           "is not the source logic of "
                           ++ language_name cid))
               when (isJust tar && getLogicStr (fromJust tar) /=
                                    language_name (targetLogic cid))
                    (fail (getLogicStr (fromJust tar) ++
                           "is not the target logic of "
                           ++ language_name cid))
               return (Comorphism cid)
            Nothing -> case tar of
               Just (Logic_name l _) -> do
                 tarL <- lookupLogic "with logic: " (tokStr l) lg
                 logicInclusion lg (Logic srcLid) tarL
               Nothing -> fail "with logic: cannot determine comorphism"
  mor1 <- adj $ gEmbedComorphism c (G_sign srcLid srcSig ind)
  adj $ comp Grothendieck mor mor1
  where getLogicStr (Logic_name l _) = tokStr l

ana_ren :: LogicGraph -> MaybeNode -> Range -> Result GMorphism -> G_mapping
            -> Result GMorphism
ana_ren lg lenv pos mor_res ren =
  do mor <- mor_res
     ana_ren1 lg lenv pos mor ren

ana_RENAMING :: LogicGraph -> MaybeNode -> G_sign -> HetcatsOpts -> RENAMING
             -> Result GMorphism
ana_RENAMING lg lenv gSigma opts (Renaming ren pos) =
  if isStructured opts
     then return (ide Grothendieck gSigma)
     else foldl (ana_ren lg lenv pos) (return (ide Grothendieck gSigma)) ren

-- analysis of restrictions

ana_restr1 :: DGraph -> G_sign -> Range -> GMorphism -> G_hiding
               -> Result GMorphism
ana_restr1 _ (G_sign lidLenv sigmaLenv _) pos
             (GMorphism cid sigma1 _ mor _)
           (G_symb_list (G_symb_items_list lid' sis')) = do
  let lid1 = sourceLogic cid
      lid2 = targetLogic cid
  sis1 <- coerceSymbItemsList lid' lid1 "Analysis of restriction" sis'
  rsys <- stat_symb_items lid1 sis1
  let sys = sym_of lid1 sigma1
      sys' = Set.filter (\sy -> any (\rsy -> matches lid1 sy rsy) rsys)
                        sys
  -- needs to be changed when logic projections are implemented
  sigmaLenv' <- coerceSign lidLenv lid1
    "Analysis of restriction: logic projections not yet properly handeled"
    sigmaLenv
  let sysLenv = sym_of lid1 sigmaLenv'
      forbiddenSys = sys' `Set.intersection` sysLenv
  when (not (forbiddenSys == Set.empty))
        $ plain_error () (
         "attempt to hide the following symbols from the local environment:\n"
         ++ showDoc forbiddenSys "") pos
  mor1 <- cogenerated_sign lid1 sys' sigma1
  mor1' <- map_morphism cid mor1
  mor2 <- comp lid2 mor1' mor
  return $ GMorphism cid (dom lid1 mor1) 0 mor2 0

ana_restr1 _dg _gSigma _mor _pos
           (G_logic_projection (Logic_code _tok _src _tar pos1)) =
  fatal_error "no analysis of logic projections yet" pos1

ana_restr :: DGraph -> G_sign -> Range -> Result GMorphism -> G_hiding
          -> Result GMorphism
ana_restr dg gSigma pos mor_res restr =
  do mor <- mor_res
     ana_restr1 dg gSigma pos mor restr

ana_RESTRICTION :: DGraph -> G_sign -> G_sign -> HetcatsOpts -> RESTRICTION
       -> Result (GMorphism, Maybe GMorphism)
ana_RESTRICTION dg gSigma gSigma' opts restr =
    ana_RESTRICTION' dg gSigma gSigma' (isStructured opts) restr

ana_RESTRICTION' :: DGraph -> G_sign -> G_sign -> Bool -> RESTRICTION
       -> Result (GMorphism, Maybe GMorphism)
ana_RESTRICTION' _ _ gSigma True _ =
  return (ide Grothendieck gSigma,Nothing)
ana_RESTRICTION' dg gSigma gSigma' False (Hidden restr pos) =
  do mor <- foldl (ana_restr dg gSigma pos)
                  (return (ide Grothendieck gSigma'))
                  restr
     return (mor,Nothing)
  -- ??? Need to check that local env is not affected !
ana_RESTRICTION' _ (G_sign lid sigma _) (G_sign lid' sigma' _)
     False (Revealed (G_symb_map_items_list lid1 sis) pos) =
  do let sys = sym_of lid sigma -- local env
         sys' = sym_of lid' sigma' -- "big" signature
         adj = adjustPos pos
     sis' <- adj $ coerceSymbMapItemsList lid1 lid'
            "Analysis of restriction" sis
     rmap <- adj $ stat_symb_map_items lid' sis'
     let sys'' =
          Set.fromList
           [sy | sy <- Set.toList sys', rsy <-
                       Map.keys rmap, matches lid' sy rsy]
          -- domain of rmap intersected with sys'
          -- domain of rmap should be checked to match symbols from sys' ???
     sys1 <- adj $ coerceSymbolSet lid lid' "Analysis of restriction" sys
        -- ??? this is too simple in case that local env is translated
        -- to a different logic
     mor1 <- adj $ generated_sign lid' (sys1 `Set.union` sys'') sigma'
     mor2 <- adj $ induced_from_morphism lid' rmap (dom lid' mor1)
     return (gEmbed (G_morphism lid' mor1 0),
             Just (gEmbed (G_morphism lid' mor2 0)))


ana_FIT_ARG :: LogicGraph -> GlobalContext -> SPEC_NAME -> MaybeNode
            -> NodeSig -> HetcatsOpts -> NODE_NAME -> FIT_ARG
            -> Result (FIT_ARG, GlobalContext, (G_morphism,NodeSig))
ana_FIT_ARG lg gctx spname nsigI
            (NodeSig nP (G_sign lidP sigmaP _)) opts name
            (Fit_spec asp gsis pos) = do
   let adj = adjustPos pos
   (sp', nsigA@(NodeSig nA (G_sign lidA sigmaA _)), dg') <-
       ana_SPEC lg gctx nsigI name opts (item asp)
   G_symb_map_items_list lid sis <- homogenizeGM (Logic lidP) gsis
   sigmaA' <- adj $ coerceSign lidA lidP "Analysis of fitting argument" sigmaA
   mor <- adj $ if isStructured opts then return (ide lidP sigmaP)
           else do
             rmap <- stat_symb_map_items lid sis
             rmap' <- if null sis then return Map.empty
                      else coerceRawSymbolMap lid lidP
                               "Analysis of fitting argument" rmap
             induced_from_to_morphism lidP rmap' sigmaP sigmaA'
   {-
   let symI = sym_of lidP sigmaI'
       symmap_mor = symmap_of lidP mor
   -- are symbols of the imports left untouched?
   if Set.all (\sy -> lookupFM symmap_mor sy == Just sy) symI
    then return ()
    else plain_error () "Fitting morphism must not affect import" pos
   -} -- ??? does not work
      -- ??? also output some symbol that is affected
   let link = (nP,nA,DGLink {
         dgl_morphism = gEmbed (G_morphism lidP mor 0),
         dgl_type = GlobalThm LeftOpen None LeftOpen,
         dgl_origin = DGSpecInst spname})
   return (Fit_spec (replaceAnnoted sp' asp) gsis pos,
           gctx { devGraph = insEdgeNub link $ devGraph dg' },
           (G_morphism lidP mor 0,nsigA)
           )

ana_FIT_ARG lg gctx spname nsigI (NodeSig nP gsigmaP)
            opts name fv@(Fit_view vn afitargs pos) = do
   let adj = adjustPos pos
       dg = devGraph gctx
       spstr = tokStr spname
   case Map.lookup vn $ globalEnv gctx of
    Nothing -> fatal_error
                 ("View " ++ tokStr vn ++ " not found") pos
    Just (SpecEntry _) ->
     fatal_error
      (spstr ++ " is a specification, not a view") pos
    Just (ArchEntry _) ->
     fatal_error
      (spstr ++
       " is an architectural specification, not a view ") pos
    Just (UnitEntry _) ->
     fatal_error
      (spstr ++
       " is a unit specification, not a view") pos
    Just (RefEntry) ->
     fatal_error
      (spstr ++
       " is a refinement specification, not a view") pos
    Just (ViewEntry (src,mor,gs@(imps,params,_,target))) -> do
     let nSrc = getNode src
         nTar = getNode target
         gsigmaS = getSig src
         gsigmaT = getSig target
         gsigmaI = getMaybeSig nsigI
     GMorphism cid _ _ morHom ind<- return mor
     let lid = targetLogic cid
     when (not (language_name (sourceLogic cid) == language_name lid))
          (fatal_error
                 "heterogeneous fitting views not yet implemented"
                 pos)
     case (\x y -> (x,x-y)) (length afitargs) (length params) of
      -- the case without parameters leads to a simpler dg
      (0,0) -> case nsigI of
         -- the subcase with empty import leads to a simpler dg
         EmptyNode _ -> do
           let link = (nP,nSrc,DGLink {
                 dgl_morphism = ide Grothendieck gsigmaP,
                 dgl_type = GlobalThm LeftOpen None LeftOpen,
                 dgl_origin = DGFitView spname})
           return (fv, gctx { devGraph = insEdgeNub link dg },
                         (G_morphism lid morHom ind, target))
         -- the subcase with nonempty import
         JustNode (NodeSig nI _) -> do
           gsigmaIS <- adj $ gsigUnion lg gsigmaI gsigmaS
           when (not (isSubGsign lg gsigmaP gsigmaIS))
             (plain_error ()
              ("Parameter does not match source of fittig view. "
               ++ "Parameter signature:\n"
               ++ showDoc gsigmaP
               "\nSource signature of fitting view (united with import):\n"
               ++ showDoc gsigmaIS "") pos)
           G_sign lidI sigI1 _<- return gsigmaI
           sigI <- adj $ coerceSign lidI lid
                    "Analysis of instantiation with import" sigI1
           mor_I <- adj $ morphism_union lid morHom $ ide lid sigI
           gsigmaA <- adj $ gsigUnion lg gsigmaI gsigmaT
           G_sign lidA gsigA indA <- return gsigmaA
           G_sign lidP gsigP indP <- return gsigmaP
           incl1 <- adj $ ginclusion lg gsigmaI gsigmaA
           incl2 <- adj $ ginclusion lg gsigmaT gsigmaA
           incl3 <- adj $ ginclusion lg gsigmaI gsigmaP
           incl4 <- adj $ ginclusion lg gsigmaS gsigmaP
           let [nA,n'] = newNodes 2 dg
               node_contentsA = DGNode {
                 dgn_name = name,
                 dgn_theory = G_theory lidA gsigA indA noSens 0,
                 dgn_nf = Nothing,
                 dgn_sigma = Nothing,
                 dgn_origin = DGFitViewA spname,
                 dgn_cons = None,
                 dgn_cons_status = LeftOpen}
               node_contents' = DGNode {
                 dgn_name = inc name,
                 dgn_theory = G_theory lidP gsigP indP noSens 0,
                 dgn_nf = Nothing,
                 dgn_sigma = Nothing,
                 dgn_origin = DGFitView spname,
                 dgn_cons = None,
                 dgn_cons_status = LeftOpen}
               link = (nP,n',DGLink {
                 dgl_morphism = ide Grothendieck gsigmaP,
                 dgl_type = GlobalThm LeftOpen None LeftOpen,
                 dgl_origin = DGFitView spname})
               link1 = (nSrc,n',DGLink {
                 dgl_morphism = incl4,
                 dgl_type = GlobalDef,
                 dgl_origin = DGFitView spname})
               link2 = (nTar,nA,DGLink {
                 dgl_morphism = incl2,
                 dgl_type = GlobalDef,
                 dgl_origin = DGFitViewA spname})
               link3 = (nI,n',DGLink {
                 dgl_morphism = incl3,
                 dgl_type = GlobalDef,
                 dgl_origin = DGFitViewImp spname})
               link4 = (nI,nA,DGLink {
                 dgl_morphism = incl1,
                 dgl_type = GlobalDef,
                 dgl_origin = DGFitViewAImp spname})
           return (fv, gctx { devGraph =
                   insEdgeNub link $
                   insEdgeNub link1 $
                   insEdgeNub link2 $
                   insEdgeNub link3 $
                   insEdgeNub link4 $
                   insNode (nA,node_contentsA) $
                   insNode (n',node_contents') dg },
                   (G_morphism lid mor_I 0, NodeSig nA gsigmaA))
      -- now the case with parameters
      (_,0) -> do
       let fitargs = map item afitargs
       (fitargs', gctx', args,_) <-
          foldl anaFitArg (return ([], gctx, [], extName "A" name))
                          (zip params fitargs)
       let actualargs = reverse args
       (gsigmaA,mor_f) <- adj $ apply_GS lg gs actualargs
       let gmor_f = gEmbed mor_f
       gsigmaRes <- adj $ gsigUnion lg gsigmaI gsigmaA
       G_sign lidRes gsigRes indRes<- return gsigmaRes
       mor1 <- adj $ comp Grothendieck mor gmor_f
       incl1 <- adj $ ginclusion lg gsigmaA gsigmaRes
       mor' <- adj $ comp Grothendieck gmor_f incl1
       GMorphism cid1 _ _ mor1Hom _<- return mor1
       let lid1 = targetLogic cid1
       when (not (language_name (sourceLogic cid1) == language_name lid1))
            (fatal_error
                   ("heterogeneous fitting views not yet implemented")
                   pos)
       G_sign lidI sigI1 _<- return gsigmaI
       sigI <- adj $ coerceSign lidI lid1
               "Analysis of instantiation with parameters" sigI1
       theta <- adj $ morphism_union lid1 mor1Hom (ide lid1 sigI)
       incl2 <- adj $ ginclusion lg gsigmaI gsigmaRes
       incl3 <- adj $ ginclusion lg gsigmaI gsigmaP
       incl4 <- adj $ ginclusion lg gsigmaS gsigmaP
       G_sign lidP gsigP indP <- return gsigmaP
       let dg' = devGraph gctx'
           [nA,n'] = newNodes 2 dg'
           node_contentsA = DGNode {
           dgn_name = name,
           dgn_theory = G_theory lidRes gsigRes indRes noSens 0,
           dgn_nf = Nothing,
           dgn_sigma = Nothing,
           dgn_origin = DGFitViewA spname,
           dgn_cons = None,
           dgn_cons_status = LeftOpen}
           node_contents' = DGNode {
             dgn_name = extName "V" name,
             dgn_theory = G_theory lidP gsigP indP noSens 0,
             dgn_nf = Nothing,
             dgn_sigma = Nothing,
             dgn_origin = DGFitView spname,
             dgn_cons = None,
             dgn_cons_status = LeftOpen}
           link = (nP,n',DGLink {
             dgl_morphism = ide Grothendieck gsigmaP,
             dgl_type = GlobalThm LeftOpen None LeftOpen,
             dgl_origin = DGFitView spname})
           link1 = (nSrc,n',DGLink {
             dgl_morphism = incl4,
             dgl_type = GlobalDef,
             dgl_origin = DGFitView spname})
           link2 = (nTar,nA,DGLink {
             dgl_morphism = mor',
             dgl_type = GlobalDef,
             dgl_origin = DGFitViewA spname})
           fitLinks = [link,link1,link2] ++ case nsigI of
                         EmptyNode _ -> []
                         JustNode (NodeSig nI _) -> let
                           link3 = (nI,n',DGLink {
                                     dgl_morphism = incl3,
                                     dgl_type = GlobalDef,
                                     dgl_origin = DGFitViewImp spname})
                           link4 = (nI,nA,DGLink {
                                     dgl_morphism = incl2,
                                     dgl_type = GlobalDef,
                                     dgl_origin = DGFitViewAImp spname})
                           in [link3,link4]
           parLinks = catMaybes (map (parLink gsigmaRes nA) actualargs)
       return (Fit_view vn
                        (map (uncurry replaceAnnoted)
                             (zip (reverse fitargs') afitargs))
                        pos,
               gctx' { devGraph = foldr insEdgeNub
                 (insNode (nA,node_contentsA) $
                  insNode (n',node_contents') dg')
                 (fitLinks ++ parLinks) },
               (G_morphism lid1 theta 0, NodeSig nA gsigmaRes))
       where
       anaFitArg res (nsig',fa) = do
         (fas',dg1,args,name') <- res
         (fa',dg',arg) <- ana_FIT_ARG lg dg1
                                  spname imps nsig' opts name' fa
         return (fa':fas',dg',arg:args,inc name')
       parLink gsigmaRes node (_mor_i,nsigA_i) = do
        let nA_i = getNode nsigA_i
        incl <- maybeResult $ ginclusion lg (getSig nsigA_i) gsigmaRes
        let link = DGLink {
             dgl_morphism = incl,
             dgl_type = GlobalDef,
             dgl_origin = DGFitView spname }
        return (nA_i,node,link)
-- finally the case with conflicting numbers of formal and actual parameters
      _ ->
        fatal_error
          (spstr ++ " expects " ++ show (length params) ++ " arguments"
           ++ " but was given " ++ show (length afitargs)) pos

-- Extension of signature morphisms (for instantitations)
-- first some auxiliary functions

mapID :: Map.Map Id (Set.Set Id) -> Id -> Result Id
mapID idmap i@(Id toks comps pos1) =
  case Map.lookup i idmap of
    Nothing -> do
      compsnew <- sequence $ map (mapID idmap) comps
      return (Id toks compsnew pos1)
    Just ids -> if Set.null ids then return i else
      case Set.lookupSingleton ids of
        Just j -> return j
        Nothing -> plain_error i
             ("Identifier component " ++ showId i
              " can be mapped in various ways:\n"
              ++ showDoc ids "") $ getRange i

extID1 :: Map.Map Id (Set.Set Id) -> Id
              -> Result (EndoMap Id) -> Result (EndoMap Id)
extID1 idmap i@(Id toks comps pos1) m = do
  m1 <- m
  compsnew <- sequence $ map (mapID idmap) comps
  if comps==compsnew
   then return m1
   else return (Map.insert i (Id toks compsnew pos1) m1)

extID :: Set.Set Id -> Map.Map Id (Set.Set Id) -> Result (EndoMap Id)
extID ids idmap = Set.fold (extID1 idmap) (return Map.empty) ids

extendMorphism :: G_sign      -- ^ formal parameter
               -> G_sign      -- ^ body
               -> G_sign      -- ^ actual parameter
               -> G_morphism  -- ^ fitting morphism
               -> Result(G_sign,G_morphism)
extendMorphism (G_sign lid sigmaP _) (G_sign lidB sigmaB1 _)
                   (G_sign lidA sigmaA1 _) (G_morphism lidM fittingMor1 _) = do
  -- for now, only homogeneous instantiations....
  sigmaB <- coerceSign lidB lid "Extension of symbol map" sigmaB1
  sigmaA <- coerceSign lidA lid "Extension of symbol map" sigmaA1
  fittingMor <- coerceMorphism lidM lid "Extension of symbol map" fittingMor1
  let symsP = sym_of lid sigmaP
      symsB = sym_of lid sigmaB
      idsB = Set.map (sym_name lid) symsB
      h = symmap_of lid fittingMor
      symbMapToRawSymbMap =
          Map.foldWithKey (\sy1 sy2 -> Map.insert (symbol_to_raw lid sy1)
                                                  (symbol_to_raw lid sy2))
                          Map.empty
      rh = symbMapToRawSymbMap h
      idh = Map.foldWithKey
             (\sy1 sy2 -> Rel.setInsert (sym_name lid sy1) (sym_name lid sy2))
             Map.empty h
  idhExt <- extID idsB idh
  let rIdExt = Map.foldWithKey (\id1 id2 -> Map.insert
                                (id_to_raw lid id1) (id_to_raw lid id2))
                Map.empty
                (foldr (\i -> Map.delete i) idhExt $ Map.keys idh)
      r = rh `Map.union` rIdExt
      -- do we need combining function catching the clashes???
  mor <- induced_from_morphism lid r sigmaB
  let hmor = symmap_of lid mor
      sigmaAD = cod lid mor
  sigma <- final_union lid sigmaA sigmaAD
  let illShared = (sym_of lid sigmaA `Set.intersection` sym_of lid sigmaAD )
                   Set.\\ Rel.image h symsP
  when (not (Set.null illShared))
   (plain_error () ("Symbols shared between actual parameter and body"
                     ++ "\nmust be in formal parameter:\n"
                     ++ showDoc illShared "") nullRange)
  let myKernel m = Set.fromDistinctAscList $ comb1 $ Map.toList m
      comb1 [] = []
      comb1 (p : qs) =
           comb2 p qs [] ++ comb1 qs
      comb2 _ [] rs = rs
      comb2 p@(a, b) ((c, d) : qs) rs =
          comb2 p qs $ if b == d then (a, c) : rs else rs
      newIdentifications = myKernel hmor Set.\\ myKernel h
  when (not (Set.null newIdentifications))
   (plain_error () (
     "Fitting morphism leads to forbidden identifications:\n"
     ++ showDoc newIdentifications "") nullRange)
  incl <- inclusion lid sigmaAD sigma
  mor1 <- comp lid mor incl
  return (G_sign lid sigma 0, G_morphism lid mor1 0)

apply_GS :: LogicGraph -> ExtGenSig -> [(G_morphism,NodeSig)]
             -> Result(G_sign,G_morphism)
apply_GS lg (nsigI,_params,gsigmaP,nsigB) args = do
  let mor_i = map fst args
      gsigmaA_i = map (getSig . snd) args
      gsigmaB = getSig nsigB
      gsigmaI = getMaybeSig nsigI
  G_sign lidI sigmaI _<- return gsigmaI
  let idI = ide lidI sigmaI
  gsigmaA <- gsigManyUnion lg gsigmaA_i
  mor_f <- homogeneousMorManyUnion (G_morphism lidI idI 0:mor_i)
  extendMorphism gsigmaP gsigmaB gsigmaA mor_f

-- | analyze a GENERICITY
-- Parameters: global context, current logic, just-structure-flag, GENERICITY
ana_GENERICITY :: LogicGraph -> GlobalContext -> AnyLogic -> HetcatsOpts
                    -> NODE_NAME -> GENERICITY
                    -> Result (GENERICITY, GenericitySig, GlobalContext)
-- zero parameters,
ana_GENERICITY _ gctx l _ _
               gen@(Genericity (Params []) (Imported imps) pos) = do
  when (not (null imps))
   (plain_error () "Parameterless specifications must not have imports"
     pos)
  return (gen,(EmptyNode l, [], EmptyNode l), gctx)
-- one parameter ...
ana_GENERICITY lg gctx l opts name
               (Genericity (Params [asp]) imps pos) = do
  (imps',nsigI,dg') <- ana_IMPORTS lg gctx l opts (extName "I" name) imps
  (sp',nsigP,dg'') <- ana_SPEC lg dg' nsigI
                      name opts (item asp)
  return (Genericity (Params [replaceAnnoted sp' asp]) imps' pos,
          (nsigI, [nsigP], JustNode nsigP), dg'')
-- ... and more parameters
ana_GENERICITY lg gctx l opts name
               (Genericity params imps pos) = do
  let adj = adjustPos pos
  (imps',nsigI,dg') <- ana_IMPORTS lg gctx l opts (extName "I" name) imps
  (params',nsigPs,gctx'') <-
      ana_PARAMS lg dg' l nsigI opts (inc name) params
  gsigmaP <- adj $ gsigManyUnion lg (map getSig nsigPs)
  G_sign lidP gsigP indP <- return gsigmaP
  let node_contents = DGNode {
        dgn_name = name,
        dgn_theory = G_theory lidP gsigP indP noSens 0,
        dgn_nf = Nothing,
        dgn_sigma = Nothing,
        dgn_origin = DGFormalParams,
        dgn_cons = None,
        dgn_cons_status = LeftOpen }
      dg'' = devGraph gctx''
      node = getNewNode dg''
      dg''' = insNode (node,node_contents) dg''
      inslink dgres (NodeSig n sigma) = do
           dg <- dgres
           incl <- adj $ ginclusion lg sigma gsigmaP
           return (insEdgeNub (n,node,DGLink {
                     dgl_morphism = incl,
                     dgl_type = GlobalDef,
                     dgl_origin = DGFormalParams }) dg)
  dg4 <- foldl inslink (return dg''') nsigPs
  return (Genericity params' imps' pos,
          (nsigI, nsigPs, JustNode $ NodeSig node gsigmaP),
           gctx { devGraph = dg4 })

ana_PARAMS :: LogicGraph -> GlobalContext -> AnyLogic -> MaybeNode
           -> HetcatsOpts -> NODE_NAME -> PARAMS
           -> Result (PARAMS, [NodeSig], GlobalContext)
ana_PARAMS lg gctx _ nsigI opts name (Params asps) = do
  (sps',pars,dg',_) <- foldl ana (return ([], [], gctx, name))
                       $ map item asps
  return (Params (map (uncurry replaceAnnoted)
                      (zip (reverse sps') asps)),
          reverse pars, dg')
  where
  ana res sp = do
    (sps',pars,dg1,n) <- res
    (sp',par,dg') <- ana_SPEC lg dg1 nsigI n opts sp
    return (sp':sps',par:pars,dg',inc n)

ana_IMPORTS ::  LogicGraph -> GlobalContext -> AnyLogic -> HetcatsOpts
                -> NODE_NAME -> IMPORTED
                -> Result (IMPORTED, MaybeNode, GlobalContext)
ana_IMPORTS lg gctx l opts name imps@(Imported asps) =
  case asps of
  [] -> return (imps, EmptyNode l, gctx)
  _ -> do
      let sp = Union asps nullRange
      (Union asps' _, nsig', dg') <-
          ana_SPEC lg gctx (EmptyNode l) name opts sp
      return (Imported asps', JustNode nsig', dg')
   -- ??? emptyExplicit stuff needs to be added here

-- | analyze a VIEW_TYPE
-- The first three arguments give the global context
-- The AnyLogic is the current logic
-- The NodeSig is the signature of the parameter of the view
-- flag, whether just the structure shall be analysed
ana_VIEW_TYPE :: LogicGraph -> GlobalContext -> AnyLogic
              -> MaybeNode -> HetcatsOpts -> NODE_NAME -> VIEW_TYPE
              -> Result (VIEW_TYPE, (NodeSig, NodeSig), GlobalContext)
ana_VIEW_TYPE lg gctx l parSig opts name
              (View_type aspSrc aspTar pos) = do
  (spSrc',srcNsig,dg') <-
     ana_SPEC lg gctx (EmptyNode l) (extName "S" name) opts (item aspSrc)
  (spTar',tarNsig,dg'') <-
     ana_SPEC lg dg' parSig
                  (extName "T" name) opts (item aspTar)
  return (View_type (replaceAnnoted spSrc' aspSrc)
                    (replaceAnnoted spTar' aspTar)
                    pos,
          (srcNsig, tarNsig), dg'')

homogenizeGM :: AnyLogic -> [Syntax.AS_Structured.G_mapping]
             -> Result G_symb_map_items_list
homogenizeGM (Logic lid) gsis =
  foldl homogenize1 (return (G_symb_map_items_list lid [])) gsis
  where
  homogenize1 res
       (Syntax.AS_Structured.G_symb_map (G_symb_map_items_list lid1 sis1)) = do
    (G_symb_map_items_list lid2 sis) <- res
    sis1' <- coerceSymbMapItemsList lid1 lid2 "" sis1
    return $ G_symb_map_items_list lid2 $ sis ++ sis1'
  homogenize1 res _ = res

-- | check if structured analysis should be performed
isStructured :: HetcatsOpts -> Bool
isStructured a = case analysis a of
                   Structured -> True
                   _ -> False

-- | Auxiliary function for not yet implemented features
ana_err :: String -> a
ana_err f = error $ "*** Analysis of " ++ f ++ " is not yet implemented!"

ana_Extension :: Result ([SPEC],MaybeNode, GlobalContext, 
                               LogicGraph, HetcatsOpts, Range)
              -> (NODE_NAME, Annoted SPEC) ->
                 Result ([SPEC], MaybeNode, GlobalContext, 
                                LogicGraph, HetcatsOpts, Range)
ana_Extension res (name',asp') = do
  (sps', nsig', dg',lg,opts, pos) <- res
  (sp1', nsig1@(NodeSig n1 sig1), gctx1) <-
     ana_SPEC lg dg' nsig' name' opts (item asp')
  let anno = find isSemanticAnno $ l_annos asp'
      dg1 = devGraph gctx1
      mrMapl = morMap gctx1
      ml = if Map.null mrMapl then 0 else fst $ Map.findMax mrMapl
  -- is the extension going between real nodes?
  gctx2 <- case (anno, nsig') of
     (Just anno0@(Semantic_anno anno1 _), JustNode (NodeSig n' sig')) -> do
         -- any other semantic annotation? that's an error
         when (any (\an -> isSemanticAnno an && an/=anno0) $ l_annos asp')
              (plain_error () "Conflicting semantic annotations"
                pos)
         -- %implied should not occur here
         when (anno1==SA_implied)
              (plain_error ()
               "Annotation %implied should come after a BASIC-ITEM"
                pos)
         if anno1==SA_implies then do
           when (not (isHomSubGsign sig1 sig')) (plain_error ()
             "Signature must not be extended in presence of %implies"
             pos)
   -- insert a theorem link according to p. 319 of the CASL Reference Manual
           return gctx1 { devGraph = insEdgeNub (n1, n', DGLink 
                              { dgl_morphism = ide Grothendieck sig1,
                                dgl_type = GlobalThm LeftOpen None LeftOpen,
                                dgl_origin = DGExtension }) dg1 }
          else do
           let anno2 = case anno1 of
                SA_cons -> Cons
                SA_def -> Def
                SA_mono -> Mono
                _ -> error "Static.AnalysisStructured: this cannot happen"
     -- insert a theorem link according to p. 319 of the CASL Reference Manual
     -- the theorem link is trivally proved by the parallel definition link,
           -- but for clarity, we leave it open here
           -- the interesting open proof obligation is anno2, of course
           incl <- ginclusion lg sig' sig1
           let incl' = updateMorIndex (ml+1) incl
           return gctx1 { devGraph = insEdgeNub (n', n1, DGLink 
                              { dgl_morphism = incl'
                              , dgl_type = GlobalThm LeftOpen anno2 LeftOpen
                              , dgl_origin = DGExtension }) dg1
                         , morMap = Map.insert (ml+1) (toG_morphism incl')
                                    mrMapl }
     _ -> return gctx1
  return (sp1' : sps', JustNode nsig1, gctx2, lg, opts, pos)
