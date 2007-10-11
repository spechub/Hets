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
    ( ana_SPEC
    , isStructured
    , ana_RENAMING
    , ana_RESTRICTION
    , homogenizeGM
    , extendMorphism
    ) where

import Driver.Options
import Logic.Logic
import Logic.Coerce
import Logic.Comorphism
import Logic.Grothendieck
import Logic.Prover
import Static.DevGraph
import Static.GTheory
import Syntax.AS_Structured
import Common.Result
import Common.Id
import Common.AS_Annotation hiding (isAxiom,isDef)
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Common.Lib.Rel as Rel(image, setInsert)
import Data.Graph.Inductive.Graph as Graph (Node)
import Common.DocUtils
import Data.Maybe
import Data.List hiding (union)
import Control.Monad

insGTheory :: DGraph -> NODE_NAME -> DGOrigin -> G_theory -> (NodeSig, DGraph)
insGTheory dg name orig (G_theory lid sig ind sens tind) =
    let (sgMap, s) = sigMapI dg
        (tMap, t) = thMapI dg
        nind = if ind == 0 then s + 1 else ind
        tb = tind == 0 && not (Map.null sens)
        ntind = if tb then t + 1 else tind
        nsig = G_sign lid sig nind
        nth = G_theory lid sig nind sens ntind
        node_contents = newNodeLab name orig nth
        node = getNewNodeDG dg
    in (NodeSig node nsig,
        (if tb then setThMapDG $ Map.insert (t+1) nth tMap else id) $
        (if ind == 0 then setSigMapDG $ Map.insert (s+1) nsig sgMap else id)
         $ insNodeDG (node, node_contents) dg)

insGSig :: DGraph -> NODE_NAME -> DGOrigin -> G_sign -> (NodeSig, DGraph)
insGSig dg name orig (G_sign lid sig ind) =
    insGTheory dg name orig $ noSensGTheory lid sig ind

-- | analyze a SPEC
-- Parameters: global context, local environment,
-- the SIMPLE_ID may be a name if the specification shall be named,
-- options: here we need the info: shall only the structure be analysed?
ana_SPEC :: LogicGraph -> DGraph -> MaybeNode -> NODE_NAME ->
            HetcatsOpts -> SPEC -> Result (SPEC, NodeSig, DGraph)
ana_SPEC lg dg nsig name opts sp = case sp of
  Basic_spec (G_basic_spec lid bspec) pos ->
    do G_sign lid' sigma' i1 <- return (getMaybeSig nsig)
       let adj = adjustPos pos
       sigma <- adj $ coerceSign lid' lid "Analysis of basic spec" sigma'
       (bspec', sigma_complete, ax) <- adj $
          if isStructured opts
           then return (bspec, empty_signature lid, [])
           else do b <- maybeToMonad
                          ("no basic analysis for logic "
                                         ++ language_name lid)
                          (basic_analysis lid)
                   b (bspec, sigma, globalAnnos dg)
       let (mrMap, m) = morMapI dg
           gTh = G_theory lid sigma_complete 0 (toThSens ax) 0
           (ns@(NodeSig node gsig), dg') = insGTheory dg name DGBasic gTh
       incl <- adj $ ginclusion lg (G_sign lid sigma i1) gsig
       let incl' = updateMorIndex (m+1) incl
           link = DGLink { dgl_morphism = incl'
                         , dgl_type = GlobalDef
                         , dgl_origin = DGExtension
                         , dgl_id = defaultEdgeID
                         }
           dg'' = case nsig of
                    EmptyNode _ -> dg'
                    JustNode (NodeSig n _) -> insLEdgeNubDG (n,node,link) dg'
       return (Basic_spec (G_basic_spec lid bspec') pos, ns,
               setMorMapDG (Map.insert (m+1) (toG_morphism incl') mrMap) dg'')
  EmptySpec pos -> case nsig of
      EmptyNode _ -> do
        warning () "empty spec" pos
        let (ns, dg') = insGSig dg name DGEmpty (getMaybeSig nsig)
        return (sp, ns, dg')
        {- ana_SPEC should be changed to return a MaybeNode!
           Then this duplicate dummy node could be avoided.
           Also empty unions could be treated then -}
      JustNode ns -> return (sp, ns ,dg)
  Translation asp ren ->
   do let sp1 = item asp
      (sp1', NodeSig n' gsigma, dg') <-
          ana_SPEC lg dg nsig (inc name) opts sp1
      let (mrMap, m) = morMapI dg'
      mor <- ana_RENAMING lg nsig gsigma opts ren
      -- ??? check that mor is identity on local env
      let gsigma' = cod Grothendieck mor
           -- ??? too simplistic for non-comorphism inter-logic translations
          (ns@(NodeSig node _), dg'') = insGSig dg' name DGTranslation gsigma'
          mor' = updateMorIndex (m+1) mor
          link = (n',node,DGLink
           { dgl_morphism = mor'
           , dgl_type = GlobalDef
           , dgl_origin = DGTranslation
           , dgl_id = defaultEdgeID
           })
      return (Translation (replaceAnnoted sp1' asp) ren, ns,
              setMorMapDG (Map.insert (m+1) (toG_morphism mor') mrMap)
              (insLEdgeNubDG link dg''))
  Reduction asp restr ->
   do let sp1 = item asp
      (sp1', NodeSig n' gsigma', dg') <-
          ana_SPEC lg dg nsig (inc name) opts sp1
      let gsigma = getMaybeSig nsig
          (mrMap, m) = morMapI dg'
      (hmor,tmor) <- ana_RESTRICTION dg gsigma gsigma' opts restr
      -- we treat hiding and revealing differently
      -- in order to keep the dg as simple as possible
      let hmor' = updateMorIndex (m+1) hmor
      case tmor of
       Nothing ->
        do let gsigma'' = dom Grothendieck hmor
           -- ??? too simplistic for non-comorphism inter-logic reductions
               (ns@(NodeSig node _), dg'') = insGSig dg' name DGHiding gsigma''
               link = (n',node,DGLink
                { dgl_morphism = hmor'
                , dgl_type = HidingDef
                , dgl_origin = DGHiding
                , dgl_id = defaultEdgeID
                })
           return (Reduction (replaceAnnoted sp1' asp) restr, ns,
                   setMorMapDG (Map.insert (m+1) (toG_morphism hmor') mrMap)
                   (insLEdgeNubDG link dg''))
       Just tmor' -> do
        let gsigma1 = dom Grothendieck tmor'
            gsigma'' = cod Grothendieck tmor'
           -- ??? too simplistic for non-comorphism inter-logic reductions
        -- the case with identity translation leads to a simpler dg
        if tmor' == ide Grothendieck (dom Grothendieck tmor')
         then do
           let (ns@(NodeSig node1 _), dg'') =
                   insGSig dg' name DGRevealing gsigma1
               link1 = (n',node1,DGLink
                { dgl_morphism = hmor'
                , dgl_type = HidingDef
                , dgl_origin = DGRevealing
                , dgl_id = defaultEdgeID
                })
           return (Reduction (replaceAnnoted sp1' asp) restr, ns,
                   setMorMapDG (Map.insert (m+1) (toG_morphism hmor')
                                    mrMap) (insLEdgeNubDG link1 dg''))
         else do
           let (NodeSig node1 _, dg'') =
                   insGSig dg' (extName "T" name) DGRevealing gsigma1
               (ns@(NodeSig node'' _), dg3) =
                   insGSig dg'' name DGRevealTranslation gsigma''
               link1 = (n',node1,DGLink
                { dgl_morphism = hmor'
                , dgl_type = HidingDef
                , dgl_origin = DGRevealing
                , dgl_id = defaultEdgeID
                })
               link'' = (node1, node'',DGLink
                { dgl_morphism = tmor'
                , dgl_type = GlobalDef
                , dgl_origin = DGRevealTranslation
                , dgl_id = defaultEdgeID
                })
           return (Reduction (replaceAnnoted sp1' asp) restr, ns,
                   setMorMapDG (Map.insert (m+1) (toG_morphism hmor')
                                    mrMap)
                   (insLEdgeNubDG link'' $ insLEdgeNubDG link1 dg3))
  Union [] pos -> adjustPos pos $ fail $ "empty union"
  Union asps pos ->
   do let sps = map item asps
      (sps', nsigs, dg', _) <-
          let ana r sp' = do
                (sps1,nsigs,dg',n) <- r
                (sp1,nsig',dg1) <- ana_SPEC lg dg' nsig n opts sp'
                return (sp1:sps1,nsig':nsigs,dg1,inc n)
           in foldl ana (return ([], [], dg, extName "U" name)) sps
      let nsigs' = reverse nsigs
          adj = adjustPos pos
      gbigSigma <- adj $ gsigManyUnion lg (map getSig nsigs')
      let (ns@(NodeSig node _), dg2) = insGSig dg' name DGUnion gbigSigma
          insE mdg (NodeSig n gsigma) = do
            dgl <- mdg
            let (mrMapl, ml) = morMapI dgl
            incl <- adj $ ginclusion lg gsigma gbigSigma
            let incl' = updateMorIndex (ml+1) incl
                link = DGLink
                 { dgl_morphism = incl'
                 , dgl_type = GlobalDef
                 , dgl_origin = DGUnion
                 , dgl_id = defaultEdgeID
                 }
            return $ setMorMapDG (Map.insert (ml+1)
                                     (toG_morphism incl') mrMapl)
                   (insLEdgeNubDG (n, node, link) dgl)
      dg3 <- foldl insE (return dg2) nsigs'
      return (Union (map (uncurry replaceAnnoted)
                         (zip (reverse sps') asps))
                    pos, ns, dg3)
  Extension asps pos -> do
   (sps',nsig1',dg1, _, _, _) <-
       foldl ana_Extension (return ([], nsig, dg, lg, opts, pos)) namedSps
   case nsig1' of
       EmptyNode _ -> fail "empty extension"
       JustNode nsig1 -> return (Extension (map (uncurry replaceAnnoted)
                          (zip (reverse sps') asps))
                                 pos, nsig1,dg1)
   where
   namedSps = zip (reverse (name: tail (take (length asps)
                                         (iterate inc (extName "E" name)))))
                   asps
  Free_spec asp poss -> do
      (nasp, nsig', dg') <-
          anaPlainSpec lg opts dg nsig name DGFree (FreeDef nsig) asp poss
      return (Free_spec nasp poss, nsig', dg')
  Cofree_spec asp poss -> do
      (nasp, nsig', dg') <-
          anaPlainSpec lg opts dg nsig name DGCofree (CofreeDef nsig) asp poss
      return (Cofree_spec nasp poss, nsig', dg')
  Local_spec asp asp' poss ->
   do let sp1 = item asp
          sp1' = item asp'
      (sp2, nsig'@(NodeSig _ (G_sign lid' sigma' _)), dg') <-
          ana_SPEC lg dg nsig (extName "L" name) opts sp1
      (sp2', NodeSig n'' (G_sign lid'' sigma'' _), dg'') <-
          ana_SPEC lg dg' (JustNode nsig') (inc name) opts sp1'
      let gsigma = getMaybeSig nsig
          (mrMap, m) = morMapI dg''
      G_sign lid sigma _ <- return gsigma
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
          gsigma3 = G_sign lid sigma3 0
          sys3 = sym_of lid sigma3
      when (not( isStructured opts ||
                 sys2 `Set.difference` sys1 `Set.isSubsetOf` sys3))
        $ plain_error () (
          "illegal use of locally declared symbols: "
          ++ showDoc ((sys2 `Set.intersection` sys1) `Set.difference` sys3) "")
         pos
      let (ns@(NodeSig node _), dg2) = insGSig dg'' name DGLocal gsigma3
          link = (n'', node, DGLink
           { dgl_morphism = gEmbed2 gsigma3 (G_morphism lid 0 mor3 (m+1) 0)
           , dgl_type = HidingDef
           , dgl_origin = DGLocal
           , dgl_id = defaultEdgeID
           })
      return (Local_spec (replaceAnnoted sp2 asp)
                         (replaceAnnoted sp2' asp')
                         poss, ns,
              setMorMapDG (Map.insert (m+1) (G_morphism lid 0 mor3 (m+1) 0)
                                mrMap) $ insLEdgeNubDG link dg2)
  Closed_spec asp pos ->
   do let sp1 = item asp
          l = getLogic nsig
      -- analyse spec with empty local env
      (sp', NodeSig n' gsigma', dg') <-
          ana_SPEC lg dg (EmptyNode l) (inc name) opts sp1
      let gsigma = getMaybeSig nsig
          adj = adjustPos pos
          (mrMap, m) = morMapI dg'
      gsigma'' <- adj $ gsigUnion lg gsigma gsigma'
      let (ns@(NodeSig node gsigma2), dg2) = insGSig dg' name DGClosed gsigma''
      incl1 <- adj $ ginclusion lg gsigma gsigma2
      incl2 <- adj $ ginclusion lg gsigma' gsigma2
      let incl1' = updateMorIndex (m+1) incl1
          incl2' = updateMorIndex (m+2) incl2
          link1 = DGLink
           { dgl_morphism = incl1'
           , dgl_type = GlobalDef
           , dgl_origin = DGClosedLenv
           , dgl_id = defaultEdgeID
           }
          link2 = (n',node,DGLink
           { dgl_morphism = incl2'
           , dgl_type = GlobalDef
           , dgl_origin = DGClosed
           , dgl_id = defaultEdgeID
           })
          insLink1 = case nsig of
                       EmptyNode _ -> id
                       JustNode (NodeSig n _) -> insLEdgeNubDG (n, node, link1)
          morMap1 = Map.insert (m+1) (toG_morphism incl1') mrMap
          morMap2 = Map.insert (m+2) (toG_morphism incl2') morMap1
      return (Closed_spec (replaceAnnoted sp' asp) pos, ns,
              setMorMapDG morMap2 $
              (insLink1 $ insLEdgeNubDG link2 dg2))
  Qualified_spec lognm@(Logic_name ln _) asp pos -> do
      let newLG = lg { currentLogic = tokStr ln }
      l <- lookupCurrentLogic "Qualified_spec" newLG
      let newNSig = case nsig of
            EmptyNode _ -> EmptyNode l
            _ -> nsig
      (nasp, nsig', dg') <-
          anaPlainSpec lg opts dg newNSig name DGLogicQual GlobalDef asp pos
      return (Qualified_spec lognm nasp pos, nsig', dg')
  Group asp pos -> do
      (sp',nsig',dg') <- ana_SPEC lg dg nsig name opts (item asp)
      return (Group (replaceAnnoted sp' asp) pos,nsig',dg')
  Spec_inst spname afitargs pos0 -> let
       pos = if null afitargs then tokPos spname else pos0
       adj = adjustPos pos
       spstr = tokStr spname
       (mrMap, m) = morMapI dg
    in case lookupGlobalEnvDG spname dg of
    Just (SpecEntry gs@(imps, params, _, body@(NodeSig nB gsigmaB))) ->
     case (\ x y -> (x , x - y)) (length afitargs) (length params) of
      -- the case without parameters leads to a simpler dg
      (0, 0) -> do
       gsigma <- adj $ gsigUnion lg (getMaybeSig nsig) gsigmaB
       let (fsig@(NodeSig node gsigma'), dg2) =
               insGSig dg name (DGSpecInst spname) gsigma
       incl <- adj $ ginclusion lg gsigmaB gsigma'
       let incl1 = updateMorIndex (m+1) incl
           link = (nB, node, DGLink
                  { dgl_morphism = incl1
                  , dgl_type = GlobalDef
                  , dgl_origin = DGSpecInst spname
                  , dgl_id = defaultEdgeID
                  })
           morMap1 = Map.insert (m+1) (toG_morphism incl1) mrMap
           dg3 = setMorMapDG morMap1 $ insLEdgeNubDG link dg2
       case nsig of
         -- the subcase with empty local env leads to an even simpler dg
         EmptyNode _ ->
          -- if the node shall not be named and the logic does not change,
          if isInternal name && langNameSig gsigma' == langNameSig gsigmaB
            -- then just return the body
           then return (sp, body, dg)
            -- otherwise, we need to create a new one
           else return (sp, fsig, dg3)
         -- the subcase with nonempty local env
         JustNode (NodeSig n sigma) -> do
           incl2 <- adj $ ginclusion lg sigma gsigma'
           let incl2' = updateMorIndex (m+2) incl2
               link2 = (n,node,DGLink
                { dgl_morphism = incl2'
                , dgl_type = GlobalDef
                , dgl_origin = DGSpecInst spname
                , dgl_id = defaultEdgeID
                })
               morMap2 = Map.insert (m+2) (toG_morphism incl2') morMap1
           return (sp, fsig, setMorMapDG morMap2 $ insLEdgeNubDG link2 dg3)
      -- now the case with parameters
      (_, 0) -> do
       let fitargs = map item afitargs
       (fitargs', dg', args, _) <-
          adj $ foldl (anaFitArg lg opts spname imps)
                  (return ([], dg, [], extName "A" name))
                          (zip params fitargs)
       let actualargs = reverse args
       (gsigma',morDelta) <- adj $ apply_GS lg gs actualargs
       gsigmaRes <- adj $ gsigUnion lg (getMaybeSig nsig) gsigma'
       let (ns@(NodeSig node gsigmaRes'), dg2) =
               insGSig dg' name (DGSpecInst spname) gsigmaRes
       incl1 <- adj $ ginclusion lg (getMaybeSig nsig) gsigmaRes'
       incl2 <- adj $ ginclusion lg gsigma' gsigmaRes'
       let incl1' = updateMorIndex (m+1) incl1
           incl2' = updateMorIndex (m+2) incl2
       morDelta' <- comp Grothendieck (gEmbed morDelta) incl2'
       let link1 = DGLink
            { dgl_morphism = incl1'
            , dgl_type = GlobalDef
            , dgl_origin = DGSpecInst spname
            , dgl_id = defaultEdgeID
            }
           insLink1 = case nsig of
               EmptyNode _ -> id
               JustNode (NodeSig n _) -> insLEdgeNubDG (n, node, link1)
           link2 = (nB,node,DGLink
            { dgl_morphism = morDelta'
            , dgl_type = GlobalDef
            , dgl_origin = DGSpecInst spname
            , dgl_id = defaultEdgeID
            })
           parLinks = catMaybes $
               map (parLink lg DGFitSpec gsigmaRes' node . snd) actualargs
           morMap1 = Map.insert (m+1) (toG_morphism incl1') mrMap
           morMap2 = Map.insert (m+2) (toG_morphism incl2') morMap1
       return (Spec_inst spname
                         (map (uncurry replaceAnnoted)
                              (zip (reverse fitargs') afitargs))
                         pos, ns,
               setMorMapDG morMap2 $ foldr insLEdgeNubDG
                                  (insLink1 $ insLEdgeNubDG link2 dg2)
                                  parLinks)
 -- finally the case with conflicting numbers of formal and actual parameters
      _ ->
        fatal_error
          (spstr ++ " expects " ++ show (length params) ++ " arguments"
           ++ " but was given " ++ show (length afitargs)) pos
    _ -> fatal_error
                 ("Structured specification " ++ spstr ++ " not found") pos
  Data (Logic lidD) (Logic lidP) asp1 asp2 pos -> do
      let sp1 = item asp1
          sp2 = item asp2
          adj = adjustPos pos
      Comorphism cid <- adj $ logicInclusion lg (Logic lidD) (Logic lidP)
      let lidD' = sourceLogic cid
          lidP' = targetLogic cid
      (sp1', NodeSig n' (G_sign lid' sigma' _), dg') <-
         ana_SPEC lg dg (EmptyNode (Logic lidD)) (inc name) opts sp1
      sigmaD <- adj $ coerceSign lid' lidD' "Analysis of data spec" sigma'
      (sigmaD',sensD') <- adj $ map_sign cid sigmaD
      let (nsig2@(NodeSig node _), dg1) = insGTheory dg' name DGData
            $ G_theory lidP' sigmaD' 0 (toThSens sensD') 0
          link = (n',node,DGLink
           { dgl_morphism = GMorphism cid sigmaD 0 (ide lidP' sigmaD') 0
           , dgl_type = GlobalDef
           , dgl_origin = DGData
           , dgl_id = defaultEdgeID
           })
          dg2 = insLEdgeNubDG link dg1
      (sp2',nsig3,dg3) <- ana_SPEC lg dg2 (JustNode nsig2) name opts sp2
      return (Data (Logic lidD) (Logic lidP)
                   (replaceAnnoted sp1' asp1)
                   (replaceAnnoted sp2' asp2)
                   pos,
              nsig3, dg3)

anaPlainSpec :: LogicGraph -> HetcatsOpts -> DGraph -> MaybeNode -> NODE_NAME
             -> DGOrigin -> DGLinkType -> Annoted SPEC -> Range
             -> Result (Annoted SPEC, NodeSig, DGraph)
anaPlainSpec lg opts dg nsig name orig dglType asp pos = do
      (sp', NodeSig n' gsigma, dg') <-
          ana_SPEC lg dg nsig (inc name) opts $ item asp
      let (ns@(NodeSig node gsigma'), dg2) = insGSig dg' name orig gsigma
      incl <- adjustPos pos $ ginclusion lg (getMaybeSig nsig) gsigma'
      let (mrMap, m) = morMapI dg'
          incl' = updateMorIndex (m+1) incl
          link = (n', node, DGLink
           { dgl_morphism = incl'
           , dgl_type = dglType
           , dgl_origin = orig
           , dgl_id = defaultEdgeID })
      return (replaceAnnoted sp' asp, ns,
              setMorMapDG (Map.insert (m+1) (toG_morphism incl') mrMap)
              $ insLEdgeNubDG link dg2)

anaFitArg :: LogicGraph -> HetcatsOpts -> SPEC_NAME -> MaybeNode
          -> Result ([FIT_ARG], DGraph, [(G_morphism, NodeSig)], NODE_NAME)
          -> (NodeSig, FIT_ARG)
          -> Result ([FIT_ARG], DGraph, [(G_morphism, NodeSig)], NODE_NAME)
anaFitArg lg opts spname imps res (nsig', fa) = do
    (fas', dg1, args, name') <- res
    (fa', dg', arg) <- ana_FIT_ARG lg dg1 spname imps nsig' opts name' fa
    return (fa' : fas', dg', arg : args , inc name')

parLink :: LogicGraph -> DGOrigin -> G_sign -> Node -> NodeSig
        -> Maybe (Node, Node, DGLinkLab)
parLink lg orig gsigma' node (NodeSig nA_i sigA_i) = do
    incl <- maybeResult $ ginclusion lg sigA_i gsigma'
    let link = DGLink
          { dgl_morphism = incl
          , dgl_type = GlobalDef
          , dgl_origin = orig
          , dgl_id = defaultEdgeID }
    return (nA_i, node, link)

-- analysis of renamings

ana_ren1 :: LogicGraph -> MaybeNode -> Range -> GMorphism -> G_mapping
             -> Result GMorphism
ana_ren1 _ lenv _pos (GMorphism r sigma ind1 mor _)
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
      sys' = Set.filter (\ sy -> any (matches lid1 sy) rsys) sys
      unmatched = filter ( \ rsy -> Set.null $ Set.filter
                     ( \ sy -> matches lid1 sy rsy) sys') rsys
  when (not $ null unmatched)
        $ plain_error () ("attempt to hide unknown symbols:\n"
                          ++ showDoc unmatched "") pos
  -- needs to be changed when logic projections are implemented
  sigmaLenv' <- coerceSign lidLenv lid1
    "Analysis of restriction: logic projections not yet properly handeled"
    sigmaLenv
  let sysLenv = sym_of lid1 sigmaLenv'
      forbiddenSys = sys' `Set.intersection` sysLenv
  when (not $ Set.null forbiddenSys)
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
ana_RESTRICTION' _ (G_sign lid sigma _) (G_sign lid' sigma' si')
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
     return (gEmbed (G_morphism lid' si' mor1 0 0),
             Just (gEmbed (G_morphism lid' 0 mor2 0 0)))


ana_FIT_ARG :: LogicGraph -> DGraph -> SPEC_NAME -> MaybeNode
            -> NodeSig -> HetcatsOpts -> NODE_NAME -> FIT_ARG
            -> Result (FIT_ARG, DGraph, (G_morphism,NodeSig))
ana_FIT_ARG lg dg spname nsigI
            (NodeSig nP (G_sign lidP sigmaP _)) opts name
            (Fit_spec asp gsis pos) = do
   let adj = adjustPos pos
   (sp', nsigA@(NodeSig nA (G_sign lidA sigmaA _)), dg') <-
       ana_SPEC lg dg nsigI name opts (item asp)
   G_symb_map_items_list lid sis <- homogenizeGM (Logic lidP) gsis
   sigmaA' <- adj $ coerceSign lidA lidP "Analysis of fitting argument" sigmaA
   mor <- adj $ if isStructured opts then return (ide lidP sigmaP)
           else do
             rmap <- stat_symb_map_items lid sis
             rmap' <- if null sis then return Map.empty
                      else coerceRawSymbolMap lid lidP
                               "Analysis of fitting argument" rmap
             let noMatch sig r = Set.null $ Set.filter
                   (\ s -> matches lidP s r) $ sym_of lidP sig
                 unknowns = filter (noMatch sigmaP) (Map.keys rmap')
                   ++ filter (noMatch sigmaA') (Map.elems rmap')
             if null unknowns then
               induced_from_to_morphism lidP rmap' sigmaP sigmaA'
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
   let link = (nP,nA,DGLink
        { dgl_morphism = gEmbed (G_morphism lidP 0 mor 0 0)
        , dgl_type = GlobalThm LeftOpen None LeftOpen
        , dgl_origin = DGSpecInst spname
        , dgl_id = defaultEdgeID
        })
   return (Fit_spec (replaceAnnoted sp' asp) gsis pos,
           insLEdgeNubDG link dg',
           (G_morphism lidP 0 mor 0 0,nsigA)
           )

ana_FIT_ARG lg dg spname nsigI (NodeSig nP gsigmaP)
            opts name fv@(Fit_view vn afitargs pos) = let
       adj = adjustPos pos
       spstr = tokStr spname
    in case lookupGlobalEnvDG vn dg of
    Just (ViewEntry (src, mor, gs@(imps, params, _, target))) -> do
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
     case (\ x y -> (x, x - y)) (length afitargs) (length params) of
      -- the case without parameters leads to a simpler dg
      (0, 0) -> case nsigI of
         -- the subcase with empty import leads to a simpler dg
         EmptyNode _ -> do
           let link = (nP,nSrc,DGLink
                { dgl_morphism = ide Grothendieck gsigmaP
                , dgl_type = GlobalThm LeftOpen None LeftOpen
                , dgl_origin = DGFitView spname
                , dgl_id = defaultEdgeID
                })
           return (fv, insLEdgeNubDG link dg,
                         (G_morphism lid 0 morHom ind 0, target))
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
           incl1 <- adj $ ginclusion lg gsigmaI gsigmaA
           incl2 <- adj $ ginclusion lg gsigmaT gsigmaA
           incl3 <- adj $ ginclusion lg gsigmaI gsigmaP
           incl4 <- adj $ ginclusion lg gsigmaS gsigmaP
           let (ns@(NodeSig nA _), dg1) =
                   insGSig dg name (DGFitViewA spname) gsigmaA
               (NodeSig n' _, dg2) =
                   insGSig dg1 (inc name) (DGFitView spname) gsigmaP
               link = (nP,n',DGLink
                { dgl_morphism = ide Grothendieck gsigmaP
                , dgl_type = GlobalThm LeftOpen None LeftOpen
                , dgl_origin = DGFitView spname
                , dgl_id = defaultEdgeID
                })
               link1 = (nSrc,n',DGLink
                { dgl_morphism = incl4
                , dgl_type = GlobalDef
                , dgl_origin = DGFitView spname
                , dgl_id = defaultEdgeID
                })
               link2 = (nTar,nA,DGLink
                { dgl_morphism = incl2
                , dgl_type = GlobalDef
                , dgl_origin = DGFitViewA spname
                , dgl_id = defaultEdgeID
                })
               link3 = (nI,n',DGLink
                { dgl_morphism = incl3
                , dgl_type = GlobalDef
                , dgl_origin = DGFitViewImp spname
                , dgl_id = defaultEdgeID
                })
               link4 = (nI,nA,DGLink
                { dgl_morphism = incl1
                , dgl_type = GlobalDef
                , dgl_origin = DGFitViewAImp spname
                , dgl_id = defaultEdgeID
                })
           return (fv, insLEdgeNubDG link $
                   insLEdgeNubDG link1 $
                   insLEdgeNubDG link2 $
                   insLEdgeNubDG link3 $
                   insLEdgeNubDG link4 dg2,
                   (G_morphism lid 0 mor_I 0 0, ns))
      -- now the case with parameters
      (_, 0) -> do
       let fitargs = map item afitargs
       (fitargs', dg', args,_) <-
          foldl (anaFitArg lg opts spname imps)
                    (return ([], dg, [], extName "A" name))
                          (zip params fitargs)
       let actualargs = reverse args
       (gsigmaA,mor_f) <- adj $ apply_GS lg gs actualargs
       let gmor_f = gEmbed mor_f
       gsigmaRes <- adj $ gsigUnion lg gsigmaI gsigmaA
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
       let (ns@(NodeSig nA _), dg1) =
                   insGSig dg' name (DGFitViewA spname) gsigmaRes
           (NodeSig n' _, dg2) =
                   insGSig dg1 (extName "V" name) (DGFitView spname) gsigmaP
           link = (nP,n',DGLink
            { dgl_morphism = ide Grothendieck gsigmaP
            , dgl_type = GlobalThm LeftOpen None LeftOpen
            , dgl_origin = DGFitView spname
            , dgl_id = defaultEdgeID
            })
           link1 = (nSrc,n',DGLink
            { dgl_morphism = incl4
            , dgl_type = GlobalDef
            , dgl_origin = DGFitView spname
            , dgl_id = defaultEdgeID
            })
           link2 = (nTar,nA,DGLink
            { dgl_morphism = mor'
            , dgl_type = GlobalDef
            , dgl_origin = DGFitViewA spname
            , dgl_id = defaultEdgeID
            })
           fitLinks = [link,link1,link2] ++ case nsigI of
                         EmptyNode _ -> []
                         JustNode (NodeSig nI _) -> let
                           link3 = (nI,n',DGLink
                                    { dgl_morphism = incl3
                                    , dgl_type = GlobalDef
                                    , dgl_origin = DGFitViewImp spname
                                    , dgl_id = defaultEdgeID
                                    })
                           link4 = (nI,nA,DGLink
                                    { dgl_morphism = incl2
                                    , dgl_type = GlobalDef
                                    , dgl_origin = DGFitViewAImp spname
                                    , dgl_id = defaultEdgeID
                                    })
                           in [link3,link4]
           parLinks = catMaybes $ map
               (parLink lg (DGFitView spname) gsigmaRes nA . snd) actualargs
       return (Fit_view vn
                        (map (uncurry replaceAnnoted)
                             (zip (reverse fitargs') afitargs))
                        pos,
               foldr insLEdgeNubDG dg2
                 (fitLinks ++ parLinks),
               (G_morphism lid1 0 theta 0 0, ns))

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
      compsnew <- sequence $ map (mapID idmap) comps
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
    (G_sign lidA sigmaA1 _) (G_morphism lidM _ fittingMor1 _ _) = do
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
  return (G_sign lid sigma 0, G_morphism lid 0 mor1 0 0)

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
  mor_f <- homogeneousMorManyUnion (G_morphism lidI 0 idI 0 0:mor_i)
  extendMorphism gsigmaP gsigmaB gsigmaA mor_f

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

ana_Extension :: Result ([SPEC],MaybeNode, DGraph,
                               LogicGraph, HetcatsOpts, Range)
              -> (NODE_NAME, Annoted SPEC) ->
                 Result ([SPEC], MaybeNode, DGraph,
                                LogicGraph, HetcatsOpts, Range)
ana_Extension res (name',asp') = do
  (sps', nsig', dg',lg,opts, pos) <- res
  (sp1', nsig1@(NodeSig n1 sig1), dg1) <-
     ana_SPEC lg dg' nsig' name' opts (item asp')
  let anno = find isSemanticAnno $ l_annos asp'
      mrMapl = morMap dg1
      ml = if Map.null mrMapl then 0 else fst $ Map.findMax mrMapl
  -- is the extension going between real nodes?
  dg2 <- case (anno, nsig') of
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
           return $ insLEdgeNubDG (n1, n', DGLink
                              { dgl_morphism = ide Grothendieck sig1
                              , dgl_type = GlobalThm LeftOpen None LeftOpen
                              , dgl_origin = DGExtension
                              , dgl_id = defaultEdgeID
                              }) dg1
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
           return $ setMorMapDG (Map.insert (ml+1) (toG_morphism incl')
                                    mrMapl )
                  (insLEdgeNubDG (n', n1, DGLink
                              { dgl_morphism = incl'
                              , dgl_type = GlobalThm LeftOpen anno2 LeftOpen
                              , dgl_origin = DGExtension
                              , dgl_id = defaultEdgeID
                              }) dg1)
     _ -> return dg1
  return (sp1' : sps', JustNode nsig1, dg2, lg, opts, pos)
