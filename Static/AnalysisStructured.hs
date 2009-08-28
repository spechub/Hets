{- |
Module      :  $Header$
Description :  static analysis of heterogeneous structured specifications
Copyright   :  (c) Till Mossakowski and Uni Bremen 2003-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Grothendieck)

Static analysis of CASL (heterogeneous) structured specifications
   Follows the verfication semantic rules in Chap. IV:4.7
   of the CASL Reference Manual.
-}

module Static.AnalysisStructured
    ( anaSpec
    , anaSpecTop
    , getSpecAnnos
    , isStructured
    , anaRenaming
    , anaRestriction
    , homogenizeGM
    , anaGmaps
    , insGSig
    , insLink
    , extendMorphism
    , insGTheory
    ) where

import Driver.Options
import Logic.Logic
import Logic.ExtSign
import Logic.Coerce
import Logic.Comorphism
import Logic.Grothendieck
import Logic.Prover
import Static.DevGraph
import Static.GTheory
import Syntax.AS_Structured
import Common.Result
import Common.Id
import Common.ExtSign
import Common.AS_Annotation hiding (isAxiom, isDef)
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Common.Lib.Rel as Rel(image, setInsert)
import Data.Graph.Inductive.Graph as Graph (Node)
import Common.DocUtils
import Data.Maybe
import Data.List (find)
import Control.Monad

coerceMaybeNode :: LogicGraph -> DGraph -> MaybeNode -> NodeName -> AnyLogic
                -> Result (MaybeNode, DGraph)
coerceMaybeNode lg dg mn nn l2 = case mn of
  EmptyNode _ -> return (EmptyNode l2, dg)
  JustNode ns -> do
    (ms, dg2) <- coerceNode lg dg ns nn l2
    return (JustNode ms, dg2)

coerceNode :: LogicGraph -> DGraph -> NodeSig -> NodeName -> AnyLogic
           -> Result (NodeSig, DGraph)
coerceNode lg dg ns@(NodeSig n s@(G_sign lid1 _ _)) nn l2@(Logic lid2) =
    if language_name lid1 == language_name lid2 then return (ns, dg)
    else do
      c <- logicInclusion lg (Logic lid1) l2
      gmor <- gEmbedComorphism c s
      case find (\ (_, _, l) -> dgl_origin l == SeeTarget
          && dgl_type l == globalDef
          && dgl_morphism l == gmor) $ outDG dg n of
        Nothing -> do
          let (ms@(NodeSig m _), dg2) =
                insGSig dg (inc nn) DGTranslation $ cod gmor
              dg3 = insLink dg2 gmor globalDef SeeTarget n m
          return (ms, dg3)
        Just (_, t, _) ->
            return (NodeSig t $ signOf $ dgn_theory $ labDG dg t, dg)

insGTheory :: DGraph -> NodeName -> DGOrigin -> G_theory -> (NodeSig, DGraph)
insGTheory dg name orig (G_theory lid sig ind sens tind) =
    let (sgMap, s) = sigMapI dg
        (tMap, t) = thMapI dg
        nind = if ind == startSigId then succ s else ind
        tb = tind == startThId && not (Map.null sens)
        ntind = if tb then succ t else tind
        nsig = G_sign lid sig nind
        nth = G_theory lid sig nind sens ntind
        node_contents = newNodeLab name orig nth
        node = getNewNodeDG dg
    in (NodeSig node nsig,
        (if tb then setThMapDG $ Map.insert (succ t) nth tMap else id) $
        (if ind == startSigId
         then setSigMapDG $ Map.insert (succ s) nsig sgMap else id)
         $ insNodeDG (node, node_contents) dg)

insGSig :: DGraph -> NodeName -> DGOrigin -> G_sign -> (NodeSig, DGraph)
insGSig dg name orig (G_sign lid sig ind) =
    insGTheory dg name orig $ noSensGTheory lid sig ind

insLink :: DGraph -> GMorphism -> DGLinkType -> DGLinkOrigin -> Node -> Node
        -> DGraph
insLink dg (GMorphism cid sign si mor mi) ty orig n t =
    let (sgMap, s) = sigMapI dg
        (mrMap, m) = morMapI dg
        nsi = if si == startSigId then succ s else si
        nmi = if mi == startMorId then succ m else mi
        nmor = GMorphism cid sign nsi mor nmi
        link = DGLink
          { dgl_morphism = nmor
          , dgl_type = ty
          , dgl_origin = orig
          , dgl_id = defaultEdgeId }
    in (if mi == startMorId then setMorMapDG $ Map.insert (succ m)
         (toG_morphism nmor) mrMap else id) $
       (if si == startSigId then setSigMapDG $ Map.insert (succ s)
        (G_sign (sourceLogic cid) sign nsi) sgMap else id)
       $ insLEdgeNubDG (n, t, link) dg

createConsLink :: LinkKind -> Conservativity -> LogicGraph -> DGraph
  -> MaybeNode -> NodeSig -> DGLinkOrigin -> Result DGraph
createConsLink lk conser lg dg nsig (NodeSig node gsig) orig = case nsig of
    EmptyNode _ | conser == None -> return dg
    _ -> case nsig of
      JustNode (NodeSig n sig)-> do
        let Result _ mIncl = ginclusion lg sig gsig
        case mIncl of
          Just incl ->
            return $ insLink dg incl
              (ScopedLink Global lk $ mkConsStatus conser) orig n node
          Nothing -> do
            unless (conser == None) $ warning ()
                "ingoring conservativity annotation between non-subsignatures"
                nullRange
            return dg
      EmptyNode _ -> -- add conservativity to the target node
        return $ let lbl = labDG dg node
        in if isDGRef lbl then dg else
         fst $ labelNodeDG
           (node, lbl
            { nodeInfo =
               (nodeInfo lbl)
                 { node_cons_status = case getNodeConsStatus lbl of
                     ConsStatus c d th -> ConsStatus (max c conser) d th }}) dg

anaSpecTop :: Conservativity -> Bool -> LogicGraph -> DGraph -> MaybeNode
  -> NodeName -> HetcatsOpts -> SPEC -> Result (SPEC, NodeSig, DGraph)
anaSpecTop conser addSyms lg dg nsig name opts sp =
 if conser == None || case sp of
      -- for these cases def-links are re-used
    Basic_spec _ _ -> True
    Closed_spec _ _ -> True
    Spec_inst _ _ _ -> True
    Group _ _ -> True -- in this case we recurse
    _ -> False
  then anaSpecAux conser addSyms lg dg nsig name opts sp else do
  let provenThmLink =
        ThmLink $ Proven (DGRule "static analysis") emptyProofBasis
  (rsp, ns, rdg) <- anaSpec addSyms lg dg nsig name opts sp
  ndg <- createConsLink provenThmLink conser lg rdg nsig ns SeeTarget
  return (rsp, ns, ndg)

anaPlainSpec :: Bool -> LogicGraph -> HetcatsOpts -> DGraph
  -> MaybeNode -> NodeName -> DGOrigin -> DGLinkType -> Annoted SPEC -> Range
  -> Result (Annoted SPEC, NodeSig, DGraph)
anaPlainSpec addSyms lg opts dg nsig name orig dglType asp pos = do
      (sp', NodeSig n' gsigma, dg') <-
          anaSpec addSyms lg dg nsig (inc name) opts $ item asp
      let (ns@(NodeSig node gsigma'), dg2) = insGSig dg' name orig gsigma
      incl <-  adjustPos pos $ ginclusion lg gsigma gsigma'
      return (replaceAnnoted sp' asp, ns,
              insLink dg2 incl dglType SeeTarget n' node)

-- | analyze a SPEC
-- Bool Parameter determines if incoming symbols shall be ignored
-- options: here we need the info: shall only the structure be analysed?
anaSpec :: Bool -> LogicGraph -> DGraph -> MaybeNode -> NodeName
  -> HetcatsOpts -> SPEC -> Result (SPEC, NodeSig, DGraph)
anaSpec = anaSpecAux None

anaSpecAux :: Conservativity -> Bool -> LogicGraph -> DGraph -> MaybeNode
  -> NodeName -> HetcatsOpts -> SPEC -> Result (SPEC, NodeSig, DGraph)
anaSpecAux conser addSyms lg dg nsig name opts sp = case sp of
  Basic_spec (G_basic_spec lid bspec) pos ->
    do let adj = adjustPos pos
           curLogic = Logic lid
       (nsig', dg0) <- coerceMaybeNode lg dg nsig name curLogic
       G_sign lid' sigma' _ <- return $ case nsig' of
           EmptyNode cl -> emptyG_sign cl
           JustNode ns -> getSig ns
       ExtSign sig sys <-
           adj $ coerceSign lid' lid "Analysis of basic spec" sigma'
       (bspec', ExtSign sigma_complete sysd, ax) <- adj $
          if isStructured opts
           then return (bspec, mkExtSign $ empty_signature lid, [])
           else do
             b <- maybeToMonad
               ("no basic analysis for logic " ++ language_name lid)
               (basic_analysis lid)
             b (bspec, sig, globalAnnos dg0)
       let (ns, dg') = insGTheory dg0 name DGBasic
             $ G_theory lid (ExtSign sigma_complete
               $ Set.intersection
                     (if addSyms then Set.union sys sysd else sysd)
               $ sym_of lid sigma_complete) startSigId (toThSens ax) startThId
       dg'' <- createConsLink DefLink conser lg dg' nsig' ns DGLinkExtension
       return (Basic_spec (G_basic_spec lid bspec') pos, ns, dg'')
  EmptySpec pos -> case nsig of
      EmptyNode _ -> do
        warning () "empty spec" pos
        let (ns, dg') = insGSig dg name DGEmpty (getMaybeSig nsig)
        return (sp, ns, dg')
        {- anaSpec should be changed to return a MaybeNode!
           Then this duplicate dummy node could be avoided.
           Also empty unions could be treated then -}
      JustNode ns -> return (sp, ns ,dg)
  Translation asp ren ->
   do let sp1 = item asp
      (sp1', NodeSig n' gsigma, dg') <-
          anaSpec addSyms lg dg nsig (inc name) opts sp1
      mor <- anaRenaming lg nsig gsigma opts ren
      -- ??? check that mor is identity on local env
      let (ns@(NodeSig node _), dg'') =
            insGSig dg' name DGTranslation $ cod mor
           -- ??? too simplistic for non-comorphism inter-logic translations
      return (Translation (replaceAnnoted sp1' asp) ren, ns,
              insLink dg'' mor globalDef SeeTarget n' node)
  Reduction asp restr ->
   do let sp1 = item asp
      (sp1', NodeSig n' gsigma', dg') <-
          anaSpec addSyms lg dg nsig (inc name) opts sp1
      let gsigma = getMaybeSig nsig
      (hmor, tmor) <- anaRestriction gsigma gsigma' opts restr
      -- we treat hiding and revealing differently
      -- in order to keep the dg as simple as possible
      case tmor of
       Nothing ->
        do let (ns@(NodeSig node _), dg'') =
                   insGSig dg' name DGHiding $ dom hmor
           -- ??? too simplistic for non-comorphism inter-logic reductions
           return (Reduction (replaceAnnoted sp1' asp) restr, ns,
                   insLink dg'' hmor HidingDefLink SeeTarget n' node)
       Just tmor' -> do
        let gsigma1 = dom tmor'
            gsigma'' = cod tmor'
           -- ??? too simplistic for non-comorphism inter-logic reductions
        -- the case with identity translation leads to a simpler dg
        if tmor' == ide (dom tmor')
         then do
           let (ns@(NodeSig node1 _), dg'') =
                   insGSig dg' name DGRevealing gsigma1
           return (Reduction (replaceAnnoted sp1' asp) restr, ns,
                   insLink dg'' hmor HidingDefLink SeeTarget n' node1)
         else do
           let (NodeSig node1 _, dg'') =
                   insGSig dg' (extName "T" name) DGRevealing gsigma1
               (ns@(NodeSig node2 _), dg3) =
                   insGSig dg'' name DGRevealTranslation gsigma''
               dg4 = insLink dg3 hmor HidingDefLink SeeTarget n' node1
           return (Reduction (replaceAnnoted sp1' asp) restr, ns,
                   insLink dg4 tmor' globalDef SeeTarget node1 node2)
  Union [] pos -> adjustPos pos $ fail "empty union"
  Union asps pos ->
   do let sps = map item asps
      (sps', nsigs, dg', _) <-
          let ana (sps1, nsigs, dg', n) sp' = do
                (sp1, nsig', dg1) <- anaSpec addSyms lg dg' nsig n opts sp'
                return (sp1 : sps1, nsig' : nsigs, dg1, inc n)
           in foldM ana ([], [], dg, extName "U" name) sps
      let nsigs' = reverse nsigs
          adj = adjustPos pos
      gbigSigma <- adj $ gsigManyUnion lg (map getSig nsigs')
      let (ns@(NodeSig node _), dg2) = insGSig dg' name DGUnion gbigSigma
          insE dgl (NodeSig n gsigma) = do
            incl <- adj $ ginclusion lg gsigma gbigSigma
            return $ insLink dgl incl globalDef SeeTarget n node
      dg3 <- foldM insE dg2 nsigs'
      return (Union (zipWith replaceAnnoted (reverse sps') asps)
                    pos, ns, dg3)
  Extension asps pos -> do
   (sps', nsig1', dg1, _, _) <- foldM (anaExtension lg opts pos)
     ([], nsig, dg, conser, addSyms) namedSps
   case nsig1' of
       EmptyNode _ -> fail "empty extension"
       JustNode nsig1 -> return (Extension (zipWith replaceAnnoted
                          (reverse sps') asps)
                                 pos, nsig1,dg1)
   where
   namedSps = zip (reverse (name: tail (take (length asps)
                                         (iterate inc (extName "E" name)))))
                   asps
  Free_spec asp poss -> do
      (nasp, nsig', dg') <- anaPlainSpec addSyms lg opts dg nsig name
        DGFree (FreeOrCofreeDefLink Free nsig) asp poss
      return (Free_spec nasp poss, nsig', dg')
  Cofree_spec asp poss -> do
      (nasp, nsig', dg') <- anaPlainSpec addSyms lg opts dg nsig name
        DGCofree (FreeOrCofreeDefLink Cofree nsig) asp poss
      return (Cofree_spec nasp poss, nsig', dg')
  Local_spec asp asp' poss ->
   do let sp1 = item asp
          sp1' = item asp'
          adj = adjustPos poss
      (sp2, nsig'@(NodeSig _ (G_sign lid' sigma' _)), dg') <-
          anaSpec False lg dg nsig (extName "L" name) opts sp1
      (sp2', NodeSig n'' (G_sign lid'' sigma'' _), dg'') <-
          anaSpec False lg dg' (JustNode nsig') (inc name) opts sp1'
      let gsigma = getMaybeSig nsig
      G_sign lid sigma _ <- return gsigma
      sigma1 <- adj $ coerceSign lid' lid "Analysis of local spec" sigma'
      sigma2 <- adj $ coerceSign lid'' lid "Analysis of local spec" sigma''
      let sys = ext_sym_of lid sigma
          sys1 = ext_sym_of lid sigma1
          sys2 = ext_sym_of lid sigma2
      mor3 <- if isStructured opts then return (ext_ide sigma2)
               else adj $ ext_cogenerated_sign lid
                      (sys1 `Set.difference` sys) sigma2
      let sigma3 = dom mor3
          -- gsigma2 = G_sign lid sigma2
          gsigma3 = G_sign lid (makeExtSign lid sigma3) startSigId
          sys3 = sym_of lid sigma3
      unless (isStructured opts
              || sys2 `Set.difference` sys1 `Set.isSubsetOf` sys3)
        $ plain_error () (
          "illegal use of locally declared symbols: "
          ++ showDoc ((sys2 `Set.intersection` sys1) `Set.difference` sys3) "")
         poss
      let (ns@(NodeSig node _), dg2) = insGSig dg'' name DGLocal gsigma3
      return (Local_spec (replaceAnnoted sp2 asp)
                         (replaceAnnoted sp2' asp')
                         poss, ns,
              insLink dg2 (gEmbed2 gsigma3 $ mkG_morphism lid mor3)
                  HidingDefLink SeeTarget n'' node)
  Closed_spec asp pos ->
   do let sp1 = item asp
          l = getLogic nsig
      -- analyse spec with empty local env
      (sp', NodeSig n' gsigma', dg') <-
          anaSpec False lg dg (EmptyNode l) (inc name) opts sp1
      let gsigma = getMaybeSig nsig
          adj = adjustPos pos
      gsigma'' <- adj $ gsigUnion lg gsigma gsigma'
      let (ns@(NodeSig node gsigma2), dg2) = insGSig dg' name DGClosed gsigma''
      incl2 <- adj $ ginclusion lg gsigma' gsigma2
      let dg3 = insLink dg2 incl2 globalDef SeeTarget n' node
      dg4 <- createConsLink DefLink conser lg dg3 nsig ns DGLinkClosedLenv
      return (Closed_spec (replaceAnnoted sp' asp) pos, ns, dg4)
  Qualified_spec lognm@(Logic_name ln _) asp pos -> do
      let newLG = lg { currentLogic = tokStr ln }
      l <- lookupCurrentLogic "Qualified_spec" newLG
      let newNSig = case nsig of
            EmptyNode _ -> EmptyNode l
            _ -> nsig
      (nasp, nsig', dg') <-
          anaPlainSpec addSyms lg opts dg newNSig name DGLogicQual
            globalDef asp pos
      return (Qualified_spec lognm nasp pos, nsig', dg')
  Group asp pos -> do
      (sp', nsig', dg') <-
          anaSpecTop conser addSyms lg dg nsig name opts (item asp)
      return (Group (replaceAnnoted sp' asp) pos, nsig', dg')
  Spec_inst spname afitargs pos0 -> let
       pos = if null afitargs then tokPos spname else pos0
       adj = adjustPos pos
       spstr = tokStr spname
    in case lookupGlobalEnvDG spname dg of
    Just (SpecEntry gs@(ExtGenSig (GenSig imps params _)
                        body@(NodeSig nB gsigmaB))) ->
     case (\ x y -> (x , x - y)) (length afitargs) (length params) of
      -- the case without parameters leads to a simpler dg
      (0, 0) -> case nsig of
          -- if the node shall not be named and the logic does not change,
        EmptyNode _ | isInternal name -> do
          dg2 <- createConsLink DefLink conser lg dg nsig body SeeTarget
             -- then just return the body
          return (sp, body, dg2)
             -- otherwise, we need to create a new one
        _ -> do
           gsigma <- case nsig of
             EmptyNode _ -> return gsigmaB
             JustNode (NodeSig _ sig) -> adj $ gsigUnion lg sig gsigmaB
           let (fsig@(NodeSig node gsigma'), dg2) =
                 insGSig dg name (DGSpecInst spname) gsigma
           incl <- adj $ ginclusion lg gsigmaB gsigma'
           let dg3 = insLink dg2 incl globalDef SeeTarget nB node
           dg4 <- createConsLink DefLink conser lg dg3 nsig fsig SeeTarget
           return (sp, fsig, dg4)
      -- now the case with parameters
      (_, 0) -> do
       let fitargs = map item afitargs
       (fitargs', dg', args, _) <- adj $ foldM (anaFitArgs lg opts spname imps)
           ([], dg, [], extName "A" name) (zip params fitargs)
       let actualargs = reverse args
       (gsigma', morDelta@(GMorphism cid _ _ _ _)) <-
           adj $ applyGS lg gs actualargs
       gsigmaRes <- case nsig of
         EmptyNode _ -> return gsigma'
         JustNode (NodeSig _ sigma) -> adj $ gsigUnion lg sigma gsigma'
       let (ns@(NodeSig node gsigmaRes'), dg2) =
               insGSig dg' name (DGSpecInst spname) gsigmaRes
       dg3 <- foldM (parLink lg DGLinkFitSpec gsigmaRes' node) dg2
              $ map snd args
       morDelta' <- case nsig of
         EmptyNode _ -> return morDelta
         _ -> do
           incl2 <- adj $ ginclusion lg gsigma' gsigmaRes'
           comp morDelta incl2
       (_, imor) <- gSigCoerce lg gsigmaB $ Logic $ sourceLogic cid
       tmor <- gEmbedComorphism imor gsigmaB
       morDelta'' <- comp tmor morDelta'
       let dg4 = insLink dg3 morDelta'' globalDef SeeTarget nB node
       dg5 <- createConsLink DefLink conser lg dg4 nsig ns SeeTarget
       return (Spec_inst spname
                         (zipWith replaceAnnoted (reverse fitargs') afitargs)
                         pos, ns, dg5)
 -- finally the case with conflicting numbers of formal and actual parameters
      _ ->
        fatal_error
          (spstr ++ " expects " ++ show (length params) ++ " arguments"
           ++ " but was given " ++ show (length afitargs)) pos
    _ -> fatal_error
                 ("Structured specification " ++ spstr ++ " not found") pos

  -- analyse "data SPEC1 SPEC2"
  Data (Logic lidD) (Logic lidP) asp1 asp2 pos -> do
      let sp1 = item asp1
          sp2 = item asp2
          adj = adjustPos pos
      -- look for the inclusion comorphism from the current logic's data logic
      -- into the current logic itself
      Comorphism cid <- adj $ logicInclusion lg (Logic lidD) (Logic lidP)
      let lidD' = sourceLogic cid
          lidP' = targetLogic cid
          dname = inc name
      -- analyse SPEC1
      (sp1', NodeSig n' (G_sign lid' sigma' _), dg') <-
         anaSpec False lg dg (EmptyNode (Logic lidD)) dname opts sp1
      -- force the result to be in the data logic
      sigmaD <- adj $ coerceSign lid' lidD' "Analysis of data spec" sigma'
      -- translate SPEC1's signature along the comorphism
      (sigmaD', sensD') <- adj $ ext_map_sign cid sigmaD
      -- create a development graph link for this translation
      let (nsig2@(NodeSig node _), dg1) = insGTheory dg' dname DGData
            $ G_theory lidP' sigmaD' startSigId (toThSens sensD') startThId
          dg2 = insLink dg1 (GMorphism cid sigmaD startSigId
                             (ext_ide sigmaD') startMorId)
                globalDef SeeTarget n' node
      -- analyse SPEC2
      (sp2', nsig3, dg3) <-
          anaSpec addSyms lg dg2 (JustNode nsig2) name opts sp2
      return (Data (Logic lidD) (Logic lidP)
                   (replaceAnnoted sp1' asp1)
                   (replaceAnnoted sp2' asp2)
                   pos, nsig3, dg3)

anaFitArgs :: LogicGraph -> HetcatsOpts -> SPEC_NAME -> MaybeNode
  -> ([FIT_ARG], DGraph, [(G_morphism, NodeSig)], NodeName)
  -> (NodeSig, FIT_ARG)
  -> Result ([FIT_ARG], DGraph, [(G_morphism, NodeSig)], NodeName)
anaFitArgs lg opts spname imps (fas', dg1, args, name') (nsig', fa) = do
    (fa', dg', arg) <- anaFitArg lg dg1 spname imps nsig' opts name' fa
    return (fa' : fas', dg', arg : args , inc name')

parLink :: LogicGraph -> DGLinkOrigin -> G_sign -> Node -> DGraph -> NodeSig
        -> Result DGraph
parLink lg orig gsigma' node dg (NodeSig nA_i sigA_i)= do
    incl <- ginclusion lg sigA_i gsigma'
    return $ insLink dg incl globalDef orig nA_i node

-- analysis of renamings
anaRen :: LogicGraph -> HetcatsOpts -> MaybeNode -> Range -> GMorphism
  -> G_mapping -> Result GMorphism
anaRen lg opts lenv pos gmor@(GMorphism r sigma ind1 mor _) gmap =
  let adj = adjustPos pos in case gmap of
  G_symb_map (G_symb_map_items_list lid sis) ->
    let lid2 = targetLogic r in
    adj $ if language_name lid2 == language_name lid then
     if isStructured opts then return gmor else do
      sis1 <- coerceSymbMapItemsList lid lid2 "Analysis of renaming" sis
      rmap <- stat_symb_map_items lid2 sis1
      mor1 <- ext_induced_from_morphism lid2 rmap $ makeExtSign lid2 $ cod mor
      case lenv of
        EmptyNode _ -> return ()
        JustNode (NodeSig _ (G_sign lidLenv sigmaLenv _)) -> do
          -- needs to be changed for logic translations
          sigmaLenv' <- coerceSign lidLenv lid2
            "Analysis of renaming: logic translations not properly handeled"
            sigmaLenv -- see Calculi/Time/FlowOfTime.casl line 305
          let sysLenv = ext_sym_of lid2 sigmaLenv'
              m = symmap_of lid2 mor1
              isChanged sy = case Map.lookup sy m of
                Just sy' -> sy /= sy'
                Nothing -> False
              forbiddenSys = Set.filter isChanged sysLenv
          unless (Set.null forbiddenSys) $ plain_error () (
            "attempt to rename the following symbols from " ++
            "the local environment:\n" ++ showDoc forbiddenSys "") pos
      mor2 <- comp mor mor1
      return $ GMorphism r sigma ind1 mor2 startMorId
    else do
      comor <- logicInclusion lg (Logic lid2) (Logic lid)
      gmorTrans <- gEmbedComorphism comor $ cod gmor
      newMor <- comp gmor gmorTrans
      anaRen lg opts lenv pos newMor gmap
  G_logic_translation (Logic_code tok src tar pos1) ->
    let adj1 = adjustPos $ if pos1 == nullRange then pos else pos1
    in adj1 $ do
    G_sign srcLid srcSig ind <- return (cod gmor)
    c <- case tok of
            Just ctok -> do
               let getLogicStr (Logic_name l _) = tokStr l
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
               Just (Logic_name l _) ->
                 lookupLogic "with logic: " (tokStr l) lg
                 >>= logicInclusion lg (Logic srcLid)
               Nothing -> fail "with logic: cannot determine comorphism"
    mor1 <- gEmbedComorphism c (G_sign srcLid srcSig ind)
    comp gmor mor1

anaRenaming :: LogicGraph -> MaybeNode -> G_sign -> HetcatsOpts -> RENAMING
  -> Result GMorphism
anaRenaming lg lenv gSigma opts (Renaming ren pos) =
      foldM (anaRen lg opts lenv pos) (ide gSigma) ren

-- analysis of restrictions
anaRestr :: G_sign -> Range -> GMorphism -> G_hiding -> Result GMorphism
anaRestr (G_sign lidLenv sigmaLenv _) pos
              (GMorphism cid (ExtSign sigma1 sys1) _ mor _) gh =
    case gh of
      G_symb_list (G_symb_items_list lid' sis') -> do
        let lid1 = sourceLogic cid
        sis1 <- coerceSymbItemsList lid' lid1 "Analysis of restriction" sis'
        rsys <- stat_symb_items lid1 sis1
        let sys = sym_of lid1 sigma1
            sys' = Set.filter (\ sy -> any (matches lid1 sy) rsys) sys
            unmatched = filter ( \ rsy -> Set.null $ Set.filter
                                 ( \ sy -> matches lid1 sy rsy) sys') rsys
        unless (null unmatched)
          $ plain_error () ("attempt to hide unknown symbols:\n"
                          ++ showDoc unmatched "") pos
        -- needs to be changed when logic projections are implemented
        sigmaLenv' <- coerceSign lidLenv lid1
          "Analysis of restriction: logic projections not properly handeled"
          sigmaLenv
        let sysLenv = ext_sym_of lid1 sigmaLenv'
            forbiddenSys = sys' `Set.intersection` sysLenv
        unless (Set.null forbiddenSys)
          $ plain_error () (
         "attempt to hide the following symbols from the local environment:\n"
         ++ showDoc forbiddenSys "") pos
        mor1 <- cogenerated_sign lid1 sys' sigma1
        mor1' <- map_morphism cid mor1
        mor2 <- comp mor1' mor
        return $ GMorphism cid (ExtSign (dom mor1) $ Set.fold (\ sy ->
          case Map.lookup sy $ symmap_of lid1 mor1 of
            Nothing -> id
            Just sy1 -> Set.insert sy1) Set.empty sys1)
          startSigId mor2 startMorId
      G_logic_projection (Logic_code _tok _src _tar pos1) ->
        fatal_error "no analysis of logic projections yet" pos1

anaRestriction :: G_sign -> G_sign -> HetcatsOpts -> RESTRICTION
  -> Result (GMorphism, Maybe GMorphism)
anaRestriction gSigma@(G_sign lid sigma _)
    gSigma'@(G_sign lid' sigma' _) opts restr =
  if isStructured opts then return (ide gSigma, Nothing) else
  case restr of
    Hidden rstr pos -> do
      mor <- foldM (anaRestr gSigma pos) (ide gSigma') rstr
      return (mor, Nothing)
    Revealed (G_symb_map_items_list lid1 sis) pos ->
     let sys = ext_sym_of lid sigma -- local env
         sys' = ext_sym_of lid' sigma' -- "big" signature
     in adjustPos pos $ do
     sis' <- coerceSymbMapItemsList lid1 lid'
            "Analysis of restriction" sis
     rmap <- stat_symb_map_items lid' sis'
     let sys'' =
          Set.fromList
           [sy | sy <- Set.toList sys', rsy <-
                       Map.keys rmap, matches lid' sy rsy]
          -- domain of rmap intersected with sys'
          -- domain of rmap should be checked to match symbols from sys' ???
     sys1 <- coerceSymbolSet lid lid' "Analysis of restriction" sys
        -- ??? this is too simple in case that local env is translated
        -- to a different logic
     mor1 <- ext_generated_sign lid' (sys1 `Set.union` sys'') sigma'
     mor2 <- ext_induced_from_morphism lid' rmap $ makeExtSign lid' $ dom mor1
     return (gEmbed (mkG_morphism lid' mor1),
             Just (gEmbed (mkG_morphism lid' mor2)))

anaGmaps :: LogicGraph -> HetcatsOpts -> Range -> G_sign -> G_sign
  -> [G_mapping] -> Result G_morphism
anaGmaps lg opts pos psig@(G_sign lidP sigmaP _) (G_sign lidA sigmaA _) gsis
    = do
  let adj = adjustPos pos
  adj $ if isStructured opts
    then return $ mkG_morphism lidP $ ext_ide sigmaP
    else if null gsis then do
        sigmaA' <- coerceSign lidA lidP "anaGmaps" sigmaA
        fmap (mkG_morphism lidP) $
          ext_induced_from_to_morphism lidP Map.empty sigmaP sigmaA'
      else do
      cl <- lookupCurrentLogic "anaGmaps" lg
      G_symb_map_items_list lid sis <- homogenizeGM cl gsis
      rmap <- stat_symb_map_items lid sis
      let noMatch sig r = Set.null $ Set.filter
            (\ s -> matches lid s r) $ ext_sym_of lid sig
      (G_sign lidP' sigmaP'' _, _) <- gSigCoerce lg psig (Logic lid)
      sigmaP' <- coerceSign lidP' lid "anaGmaps1" sigmaP''
      sigmaA' <- coerceSign lidA lid "anaGmaps2" sigmaA
      let unknowns = filter (noMatch sigmaP') (Map.keys rmap)
            ++ filter (noMatch sigmaA') (Map.elems rmap)
      if null unknowns then fmap (mkG_morphism lid)
         $ ext_induced_from_to_morphism lid rmap sigmaP' sigmaA'
        else fatal_error ("unknown symbols " ++ showDoc unknowns "") pos
   {-
   let symI = sym_of lidP sigmaI'
       symmap_mor = symmap_of lidP mor
   -- are symbols of the imports left untouched?
   if Set.all (\sy -> lookupFM symmap_mor sy == Just sy) symI
    then return ()
    else plain_error () "Fitting morphism must not affect import" pos
   -} -- ??? does not work
      -- ??? also output some symbol that is affected

anaFitArg :: LogicGraph -> DGraph -> SPEC_NAME -> MaybeNode -> NodeSig
  -> HetcatsOpts -> NodeName -> FIT_ARG
  -> Result (FIT_ARG, DGraph, (G_morphism,NodeSig))
anaFitArg lg dg spname nsigI (NodeSig nP gsigmaP) opts name fv = case fv of
  Fit_spec asp gsis pos -> do
   (sp', nsigA@(NodeSig nA gsigA), dg') <-
       anaSpec False lg dg nsigI name opts (item asp)
   gmor <- anaGmaps lg opts pos gsigmaP gsigA gsis
   return (Fit_spec (replaceAnnoted sp' asp) gsis pos,
          insLink dg' (gEmbed gmor) globalThm
             (DGLinkSpecInst spname) nP nA, (gmor, nsigA))
  Fit_view vn afitargs pos -> let
       adj = adjustPos pos
       spstr = tokStr spname
    in case lookupGlobalEnvDG vn dg of
    Just (ViewEntry (ExtViewSig src mor
                     gs@(ExtGenSig (GenSig imps params _) target))) -> do
     let nSrc = getNode src
         nTar = getNode target
         gsigmaS = getSig src
         gsigmaT = getSig target
         gsigmaI = getMaybeSig nsigI
     GMorphism cid _ _ morHom ind <- return mor
     let lid = targetLogic cid
     case (\ x y -> (x, x - y)) (length afitargs) (length params) of
      -- the case without parameters leads to a simpler dg
      (0, 0) -> case nsigI of
         -- the subcase with empty import leads to a simpler dg
         EmptyNode _ -> do
           gmor <- ginclusion lg gsigmaP gsigmaS
           return (fv, insLink dg gmor globalThm (DGLinkFitView spname)
                   nP nSrc, (G_morphism lid morHom ind, target))
         -- the subcase with nonempty import
         JustNode (NodeSig nI _) -> do
           gsigmaIS <- adj $ gsigUnion lg gsigmaI gsigmaS
           unless (isSubGsign lg gsigmaP gsigmaIS)
             (plain_error ()
              ("Parameter does not match source of fittig view. "
               ++ "Parameter signature:\n"
               ++ showDoc gsigmaP
               "\nSource signature of fitting view (united with import):\n"
               ++ showDoc gsigmaIS "") pos)
           (G_sign lidI sigI1 _, _) <- adj $ gSigCoerce lg gsigmaI (Logic lid)
           sigI <- adj $ coerceSign lidI lid
                    "Analysis of instantiation with import" sigI1
           mor_I <- adj $ morphism_union lid morHom $ ext_ide sigI
           gsigmaA <- adj $ gsigUnion lg gsigmaI gsigmaT
           incl1 <- adj $ ginclusion lg gsigmaI gsigmaA
           incl2 <- adj $ ginclusion lg gsigmaT gsigmaA
           incl3 <- adj $ ginclusion lg gsigmaI gsigmaP
           incl4 <- adj $ ginclusion lg gsigmaS gsigmaP
           let (ns@(NodeSig nA _), dg1) =
                   insGSig dg name (DGFitViewA spname) gsigmaA
               (NodeSig n' _, dg2) =
                   insGSig dg1 (inc name) (DGFitView spname) gsigmaP
               dg3 = insLink dg2 incl1 globalDef
                     (DGLinkFitViewAImp spname) nI nA
               dg4 = insLink dg3 incl3 globalDef
                     (DGLinkFitViewImp spname) nI n'
               dg5 = insLink dg4 incl2 globalDef SeeTarget nTar nA
               dg6 = insLink dg5 incl4 globalDef SeeTarget nSrc n'
               dg7 = insLink dg6 (ide gsigmaP)
                     globalThm SeeTarget nP n'
           return (fv, dg7, (mkG_morphism lid mor_I, ns))
      -- now the case with parameters
      (_, 0) -> do
       let fitargs = map item afitargs
       (fitargs', dg', args,_) <- foldM (anaFitArgs lg opts spname imps)
           ([], dg, [], extName "A" name) (zip params fitargs)
       let actualargs = reverse args
       (gsigmaA, gmor_f) <- adj $ applyGS lg gs actualargs
       gsigmaRes <- adj $ gsigUnion lg gsigmaI gsigmaA
       mor1 <- adj $ comp mor gmor_f
       incl1 <- adj $ ginclusion lg gsigmaA gsigmaRes
       mor' <- adj $ comp gmor_f incl1
       GMorphism cid1 _ _ mor1Hom _<- return mor1
       let lid1 = targetLogic cid1
       when (language_name (sourceLogic cid1) /= language_name lid1)
            $ fatal_error "heterogeneous fitting views not yet implemented"
              pos
       G_sign lidI sigI1 _<- return gsigmaI
       sigI <- adj $ coerceSign lidI lid1
               "Analysis of instantiation with parameters" sigI1
       theta <- adj $ morphism_union lid1 mor1Hom (ext_ide sigI)
       incl2 <- adj $ ginclusion lg gsigmaI gsigmaRes
       incl3 <- adj $ ginclusion lg gsigmaI gsigmaP
       incl4 <- adj $ ginclusion lg gsigmaS gsigmaP
       let (ns@(NodeSig nA _), dg1) =
                   insGSig dg' name (DGFitViewA spname) gsigmaRes
           (NodeSig n' _, dg2) =
                   insGSig dg1 (extName "V" name) (DGFitView spname) gsigmaP
       dg3 <- foldM (parLink lg (DGLinkFitView spname) gsigmaRes nA) dg2
              $ map snd args
       let dg4 = case nsigI of
              EmptyNode _ -> dg3
              JustNode (NodeSig nI _) -> let
                dg3a = insLink dg3 incl2 globalDef
                       (DGLinkFitViewAImp spname) nI nA
                in insLink dg3a incl3 globalDef (DGLinkFitViewImp spname) nI n'
           dg5 = insLink dg4 mor' globalDef SeeTarget nTar nA
           dg6 = insLink dg5 incl4 globalDef SeeTarget nSrc n'
           dg7 = insLink dg6 (ide gsigmaP) globalThm SeeTarget nP n'
       return (Fit_view vn
                        (zipWith replaceAnnoted (reverse fitargs') afitargs)
                        pos, dg7, (mkG_morphism lid1 theta, ns))
-- finally the case with conflicting numbers of formal and actual parameters
      _ ->
        fatal_error
          (spstr ++ " expects " ++ show (length params) ++ " arguments"
           ++ " but was given " ++ show (length afitargs)) pos
    _ -> fatal_error
                 ("View " ++ tokStr vn ++ " not found") pos

-- Extension of signature morphisms (for instantitations)
-- first some auxiliary functions

mapID :: Map.Map Id (Set.Set Id) -> Id -> Result Id
mapID idmap i@(Id toks comps pos1) =
  case Map.lookup i idmap of
    Nothing -> do
      compsnew <- mapM (mapID idmap) comps
      return (Id toks compsnew pos1)
    Just ids -> if Set.null ids then return i else
      if Set.null $ Set.deleteMin ids then return $ Set.findMin ids else
         plain_error i
             ("Identifier component " ++ showId i
              " can be mapped in various ways:\n"
              ++ showDoc ids "") $ getRange i

extID1 :: Map.Map Id (Set.Set Id) -> Id
              -> Result (EndoMap Id) -> Result (EndoMap Id)
extID1 idmap i@(Id toks comps pos1) m = do
  m1 <- m
  compsnew <- mapM (mapID idmap) comps
  return $ if comps == compsnew then m1 else
    Map.insert i (Id toks compsnew pos1) m1

extID :: Set.Set Id -> Map.Map Id (Set.Set Id) -> Result (EndoMap Id)
extID ids idmap = Set.fold (extID1 idmap) (return Map.empty) ids

extendMorphism :: G_sign      -- ^ formal parameter
               -> G_sign      -- ^ body
               -> G_sign      -- ^ actual parameter
               -> G_morphism  -- ^ fitting morphism
               -> Result(G_sign, GMorphism)
extendMorphism (G_sign lid sigmaP _) (G_sign lidB sigmaB1 _)
    (G_sign lidA sigmaA1 _) (G_morphism lidM fittingMor1 _) = do
  -- for now, only homogeneous instantiations....
  sigmaB@(ExtSign _ sysB) <-
      coerceSign lidB lid "Extension of symbol map1" sigmaB1
  sigmaA <- coerceSign lidA lid "Extension of symbol map2" sigmaA1
  fittingMor <- coerceMorphism lidM lid "Extension of symbol map3" fittingMor1
  let symsP = ext_sym_of lid sigmaP
      symsB = ext_sym_of lid sigmaB
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
                (foldr Map.delete idhExt $ Map.keys idh)
      r = rh `Map.union` rIdExt
      -- do we need combining function catching the clashes???
  mor <- ext_induced_from_morphism lid r sigmaB
  let hmor = symmap_of lid mor
      sigmaAD = ExtSign (cod mor) $ Set.map (\ sy ->
        Map.findWithDefault sy sy hmor) sysB
  sigma <- ext_signature_union lid sigmaA sigmaAD
  let illShared = (ext_sym_of lid sigmaA `Set.intersection`
                              ext_sym_of lid sigmaAD )
                   Set.\\ Rel.image h symsP
  unless (Set.null illShared)
    $ plain_error () ("Symbols shared between actual parameter and body"
                     ++ "\nmust be in formal parameter:\n"
                     ++ showDoc illShared "") nullRange
  let myKernel = Set.fromDistinctAscList . comb1 . Map.toList
      comb1 [] = []
      comb1 (p : qs) =
           comb2 p qs [] ++ comb1 qs
      comb2 _ [] rs = rs
      comb2 p@(a, b) ((c, d) : qs) rs =
          comb2 p qs $ if b == d then (a, c) : rs else rs
      newIdentifications = myKernel hmor Set.\\ myKernel h
  unless (Set.null newIdentifications)
    $ warning () (
     "Fitting morphism may lead to forbidden identifications:\n"
     ++ showDoc newIdentifications "") nullRange
  incl <- ext_inclusion lid sigmaAD sigma
  mor1 <- comp mor incl
  return (G_sign lid sigma startSigId, gEmbed $ mkG_morphism lid mor1)

applyGS :: LogicGraph -> ExtGenSig -> [(G_morphism, NodeSig)]
         -> Result(G_sign, GMorphism)
applyGS lg (ExtGenSig (GenSig nsigI _ gsigmaP) nsigB) args = do
  let mor_i = map fst args
      gsigmaA_i = map (getSig . snd) args
      gsigmaB = getSig nsigB
  gsigmaA@(G_sign lidA _ _) <- gsigManyUnion lg gsigmaA_i
  (_, Comorphism uid) <- logicUnion lg (getNodeLogic nsigB) (Logic lidA)
  let cl = Logic $ targetLogic uid
  G_morphism lidG mor0 _ <- case nsigI of
    EmptyNode _ -> homogeneousMorManyUnion mor_i
    JustNode (NodeSig _ gsigmaI) -> do
      (G_sign lidI sigmaI _, _) <- gSigCoerce lg gsigmaI (Logic lidA)
      let idI = ext_ide sigmaI
      homogeneousMorManyUnion $ mkG_morphism lidI idI : mor_i
  (gsigmaP', _) <- gSigCoerce lg (getMaybeSig gsigmaP) cl
  (gsigmaB', _) <- gSigCoerce lg gsigmaB cl
  (gsigmaA', Comorphism aid) <- gSigCoerce lg gsigmaA cl
  mor1 <- coerceMorphism lidG (sourceLogic aid) "applyGS" mor0
  mor2 <- map_morphism aid mor1
  extendMorphism gsigmaP' gsigmaB' gsigmaA' $
    G_morphism (targetLogic aid) mor2 startMorId

homogenizeGM :: AnyLogic -> [Syntax.AS_Structured.G_mapping]
             -> Result G_symb_map_items_list
homogenizeGM (Logic lid) gsis =
  foldM homogenize1 (G_symb_map_items_list lid []) gsis
  where
  homogenize1 itl2@(G_symb_map_items_list lid2 sis) sm = case sm of
    Syntax.AS_Structured.G_symb_map (G_symb_map_items_list lid1 sis1) -> do
         sis1' <- coerceSymbMapItemsList lid1 lid2 "" sis1
         return $ G_symb_map_items_list lid2 $ sis ++ sis1'
    _ -> return itl2

-- | check if structured analysis should be performed
isStructured :: HetcatsOpts -> Bool
isStructured a = case analysis a of
    Structured -> True
    _ -> False

getSpecAnnos :: Range -> Annoted a -> Result (Conservativity, Bool)
getSpecAnnos pos a = do
  let sannos = filter isSemanticAnno $ l_annos a
      (sanno1, conflict, impliedA, impliesA) = case sannos of
        f@(Semantic_anno anno1 _) : r -> (case anno1 of
                SA_cons -> Cons
                SA_def -> Def
                SA_mono -> Mono
                _ -> None, any (/= f) r,
                     anno1 ==  SA_implied, anno1 == SA_implies)
        _ -> (None, False, False, False)
  when conflict $ plain_error () "Conflicting semantic annotations" pos
  when impliedA $ plain_error ()
    "Annotation %implied should come after a BASIC-ITEM" pos
  return (sanno1, impliesA)

-- only consider addSyms for the first spec
anaExtension
    :: LogicGraph -> HetcatsOpts -> Range
    -> ([SPEC], MaybeNode, DGraph, Conservativity, Bool)
    -> (NodeName, Annoted SPEC)
    -> Result ([SPEC], MaybeNode, DGraph, Conservativity, Bool)
anaExtension lg opts pos (sps', nsig', dg', conser, addSyms) (name', asp')
  = do
  (sanno1, impliesA) <- getSpecAnnos pos asp'
  -- attach conservativity to definition link
  (sp1', nsig1@(NodeSig n1 sig1), dg1) <-
     anaSpecTop (max conser sanno1) addSyms lg dg' nsig' name' opts (item asp')
  dg2 <- if impliesA then case nsig' of
    JustNode (NodeSig n' sig') -> do
      -- is the extension going between real nodes?
      unless (isHomSubGsign sig1 sig') $ plain_error ()
        "Signature must not be extended in presence of %implies" pos
    -- insert a theorem link according to p. 319 of the CASL Reference Manual
      return $ insLink dg1 (ide sig1) globalThm DGImpliesLink n1 n'
    _ -> return dg1
   else return dg1
  return (sp1' : sps', JustNode nsig1, dg2, None, True)
