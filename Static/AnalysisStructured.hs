{- |
Module      :  ./Static/AnalysisStructured.hs
Description :  static analysis of DOL OMS and heterogeneous structured specifications
Copyright   :  (c) Till Mossakowski and Uni Magdeburg 2003-2016
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Grothendieck)

Static analysis of DOL OMS and networks and
       CASL (heterogeneous) structured specifications
  Follows the semantics of DOL OMS and networks,
   DOL OMG standard, clauses 10.2.2 and 10.2.3
-}

module Static.AnalysisStructured
    ( anaSpec
    , anaSpecTop
    , anaUnion
    , anaIntersect
    , anaSublogic
    , getSpecAnnos
    , anaRenaming
    , anaRestriction
    , partitionGmaps
    , homogenizeGM
    , anaGmaps
    , insGSig
    , insLink
    , extendMorphism
    , insGTheory
    , expCurie
    , expCurieR
    , expandCurieByPath
    , ExpOverrides
    , notFoundError
    , prefixErrorIRI
    , networkDiagram
    ) where

import Driver.Options

import Logic.Logic
import Logic.ExtSign
import Logic.Coerce
import Logic.Comorphism
import Logic.Grothendieck
import Logic.Prover

import Static.DevGraph
import Static.DgUtils
import Static.GTheory

import Syntax.AS_Structured
import Syntax.Print_AS_Structured

import Common.AS_Annotation hiding (isAxiom, isDef)
import Common.Consistency
import Common.DocUtils
import Common.ExtSign
import Common.GlobalAnnotations
import Common.Id
import Common.IRI
import Common.LibName
import Common.Result
import Common.Utils (number)
import Common.Lib.MapSet (imageSet, setInsert)

import Data.Graph.Inductive.Graph
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Maybe
import Data.List
import Data.Function

import Control.Monad
import Proofs.ComputeColimit (insertColimitInGraph)

import Common.Lib.Graph

import Static.ComputeTheory

-- overrides CUIRIE expansion for Download_items
type ExpOverrides = Map.Map IRI FilePath

coerceMaybeNode :: LogicGraph -> DGraph -> MaybeNode -> NodeName -> AnyLogic
                -> Result (MaybeNode, DGraph)
coerceMaybeNode lg dg mn nn l2 = case mn of
  EmptyNode _ -> return (EmptyNode l2, dg)
  JustNode ns -> do
    (ms, dg2) <- coerceNode lg dg ns nn l2
    return (JustNode ms, dg2)

coerceNode :: LogicGraph -> DGraph -> NodeSig -> NodeName -> AnyLogic
           -> Result (NodeSig, DGraph)
coerceNode lg dg ns@(NodeSig _ (G_sign lid1 _ _)) nn l2@(Logic lid2) =
    if language_name lid1 == language_name lid2 then return (ns, dg)
    else do
      c <- logicInclusion lg (Logic lid1) l2
      coerceNodeByComorph c dg ns nn

coerceNodeByComorph :: AnyComorphism -> DGraph -> NodeSig -> NodeName
           -> Result (NodeSig, DGraph)
coerceNodeByComorph c dg (NodeSig n s) nn = do
      gmor <- gEmbedComorphism c s
      case find (\ (_, _, l) -> dgl_origin l == SeeTarget
          && dgl_type l == globalDef
          && dgl_morphism l == gmor) $ outDG dg n of
        Nothing -> do
          let (ms@(NodeSig m _), dg2) =
                insGSig dg (extName "XCoerced" nn) DGLogicCoercion $ cod gmor
              dg3 = insLink dg2 gmor globalDef SeeTarget n m
          return (ms, dg3)
        Just (_, t, _) ->
            return (NodeSig t $ signOf $ dgn_theory $ labDG dg t, dg)

insGTheory :: DGraph -> NodeName -> DGOrigin -> G_theory -> (NodeSig, DGraph)
insGTheory dg name orig (G_theory lid syn sig ind sens tind) =
    let (sgMap, s) = sigMapI dg
        (tMap, t) = thMapI dg
        nind = if ind == startSigId then succ s else ind
        tb = tind == startThId && not (Map.null sens)
        ntind = if tb then succ t else tind
        nsig = G_sign lid sig nind
        nth = G_theory lid syn sig nind sens ntind
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
        link = defDGLink nmor ty orig
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
      JustNode (NodeSig n sig) -> do
        incl <- ginclusion lg sig gsig
        return $ insLink dg incl
              (ScopedLink Global lk $ mkConsStatus conser) orig n node
      EmptyNode _ -> -- add conservativity to the target node
        return $ let lbl = labDG dg node
        in if isDGRef lbl then dg else
         fst $ labelNodeDG
           (node, lbl
            { nodeInfo =
               (nodeInfo lbl)
                 { node_cons_status = case getNodeConsStatus lbl of
                     ConsStatus c d th -> ConsStatus (max c conser) d th }}) dg

getNamedSpec :: SPEC_NAME -> LibName -> DGraph -> LibEnv
  -> Result (ExtGenSig, (LibName, DGraph, LNode DGNodeLab))
getNamedSpec sp ln dg libenv = case lookupGlobalEnvDG sp dg of
          Just (SpecEntry s@(ExtGenSig (GenSig _ ps _) (NodeSig n _))) -> do
            unless (null ps)
              $ mkError "base theory must not be parameterized" sp
            let t@(refLib, refDG, (_, lbl)) = lookupRefNode libenv ln dg n
                refTok = getName $ dgn_name lbl
            unless (sp == refTok)
              $ appendDiags [mkDiag Warning "renamed base theory" sp]
            if refLib == ln then return (s, t) else
                case lookupGlobalEnvDG refTok refDG of
                  Just (SpecEntry s2) -> return (s2, t)
                  _ -> mkError "theory reference error" sp
          _ -> mkError "unknown theory" sp

anaSublogic :: HetcatsOpts -> LogicDescr -> LibName -> DGraph -> LibEnv
  -> LogicGraph
  -> Result (Maybe (ExtGenSig, (LibName, DGraph, LNode DGNodeLab)), LogicGraph)
anaSublogic _opts itm ln dg libenv lG
  = case itm of
  LogicDescr (Logic_name lt ms mt) _ _ -> do
    logN@(Logic lid) <- lookupLogic "" lt lG
    mgs <- case ms of
      Nothing -> return Nothing
      Just subL -> do
        let s = tokStr subL
        case parseSublogic lid s of
          Nothing -> fail $ "unknown sublogic of logic " ++ show logN
            ++ ": " ++ s
          Just sl ->
            if sublogicName (top_sublogic lid) == s then do
              warning () ("not a proper sublogic: " ++ s) $ tokPos subL
              return Nothing
              else return $ Just $ G_sublogics lid sl
    let logicLibN = emptyLibName "Logics"
        lG1 = setCurSublogic mgs $ setLogicName itm lG
    case mt of
      Nothing -> return (Nothing, lG1 { currentTargetBase = Nothing })
      Just sp -> do
        let ssp = iriToStringUnsecure sp
        (s, t@(libName, _, (_, lbl))) <- case Map.lookup logicLibN libenv of
          Just dg2 | logicLibN /= ln -> getNamedSpec sp logicLibN dg2 libenv
          _ -> getNamedSpec sp ln dg libenv
        case sublogicOfTh $ globOrLocTh lbl of
          gs2@(G_sublogics lid2 _) -> do
            unless (logN == Logic lid2)
              $ fail $ "the logic of '" ++ ssp
                  ++ "' is '" ++ language_name lid2
                  ++ "' and not '" ++ shows logN "'!"
            case mgs of
              Nothing -> return ()
              Just gs -> unless (isSublogic gs2 gs)
                $ fail $ "theory '" ++ ssp
                  ++ "' has sublogic '" ++ shows gs2 "' and not '"
                  ++ shows gs "'!"
            let sbMap = sublogicBasedTheories lG1
                lMap = Map.findWithDefault Map.empty logN sbMap
                nName = getDGNodeName lbl
            nMap <- case Map.lookup sp lMap of
              Nothing -> return $ Map.insert sp (libName, nName) lMap
              Just (prevLib, prevName) -> do
                unless (libName == prevLib)
                  $ fail $ "theory '" ++ ssp
                    ++ "' should come from library '"
                    ++ showDoc prevLib "' and not from '"
                    ++ showDoc libName "'!"
                unless (nName == prevName)
                  $ fail $ "the original theory name for '" ++ ssp
                    ++ "' should be '"
                    ++ prevName ++ "' and not '"
                    ++ nName ++ "'!"
                return lMap
            return (Just (s, t), lG1
              { sublogicBasedTheories = Map.insert logN nMap sbMap
              , currentTargetBase = Just (libName, nName) })
  _ -> return (Nothing, lG)

anaSpecTop :: Conservativity -> Bool -> LogicGraph -> LibEnv -> LibName -> DGraph
  -> MaybeNode -> NodeName -> HetcatsOpts -> ExpOverrides -> SPEC -> Range
  -> Result (SPEC, NodeSig, DGraph)
anaSpecTop conser addSyms lg libEnv ln dg nsig name opts eo sp pos =
 if conser == None || case sp of
      -- for these cases def-links are re-used
    Basic_spec _ _ -> True
    Closed_spec _ _ -> True
    Spec_inst {} -> True
    Group _ _ -> True -- in this case we recurse
    _ -> False
    then anaSpecAux conser addSyms lg libEnv ln dg nsig name opts eo sp pos else do
  let provenThmLink =
        ThmLink $ Proven (DGRule "static analysis") emptyProofBasis
  (rsp, ns, rdg) <- anaSpec addSyms lg libEnv ln dg nsig name opts eo sp pos
  ndg <- createConsLink provenThmLink conser lg rdg nsig ns SeeTarget
  return (rsp, ns, ndg)

anaFreeOrCofreeSpec :: Bool -> LogicGraph -> LibEnv -> HetcatsOpts -> LibName -> DGraph
  -> MaybeNode -> NodeName -> FreeOrCofree -> ExpOverrides -> Annoted SPEC
  -> Range -> Result (Annoted SPEC, NodeSig, DGraph)
anaFreeOrCofreeSpec addSyms lg libEnv opts ln dg nsig name dglType eo asp pos =
  adjustPos pos $ do
      let sp = item asp
          iPos = getRange sp
      (sp', NodeSig n' gsigma, dg') <-
          anaSpec addSyms lg libEnv ln dg nsig (extName (show dglType) name) opts eo
            sp iPos
      let (ns@(NodeSig node _), dg2) =
              insGSig dg' (setSrcRange pos name) (DGFreeOrCofree dglType) gsigma
          nsigma = case nsig of
            EmptyNode cl -> emptyG_sign cl
            JustNode nds -> getSig nds
      incl <- ginclusion lg nsigma gsigma
      return (replaceAnnoted sp' asp, ns,
              insLink dg2 incl (FreeOrCofreeDefLink dglType nsig)
              SeeTarget n' node)

{- | analyze a SPEC. The Bool Parameter determines if incoming symbols shall
be ignored. The options are needed to check: shall only the structure be
analysed? -}
anaSpec :: Bool -> LogicGraph -> LibEnv -> LibName -> DGraph -> MaybeNode -> NodeName
  -> HetcatsOpts -> ExpOverrides -> SPEC -> Range
  -> Result (SPEC, NodeSig, DGraph)
anaSpec = anaSpecAux None

anaSpecAux :: Conservativity -> Bool -> LogicGraph -> LibEnv -> LibName -> DGraph
  -> MaybeNode -> NodeName -> HetcatsOpts -> ExpOverrides -> SPEC -> Range
  -> Result (SPEC, NodeSig, DGraph)
anaSpecAux conser addSyms lg libEnv ln dg nsig name opts eo sp rg = case sp of
  Basic_spec (G_basic_spec lid bspec) pos -> adjustPos pos $ do
       let curLogic = Logic lid
           curSL = currentSublogic lg
           bsSL = G_sublogics lid $ minSublogic bspec
       when (maybe False (`isProperSublogic` bsSL) curSL)
         $ fail $ "sublogic expected: " ++ maybe "" show curSL
               ++ " found: " ++ show bsSL
       (nsig', dg0) <- coerceMaybeNode lg dg nsig name curLogic
       G_sign lid' sigma' _ <- return $ case nsig' of
           EmptyNode cl -> emptyG_sign cl
           JustNode ns -> getSig ns
       ExtSign sig sys <-
           coerceSign lid' lid "Analysis of basic spec" sigma'
       (bspec', ExtSign sigma_complete sysd, ax) <-
          if isStructured opts
           then return (bspec, mkExtSign $ empty_signature lid, [])
           else
             let res@(Result ds mb) = extBasicAnalysis lid (getName name)
                   ln bspec sig $ globalAnnos dg0
             in case mb of
               Nothing | null ds ->
                 fail "basic analysis failed without giving a reason"
               _ -> res
       diffSig <- case signatureDiff lid sigma_complete sig of
         Result _ (Just ds) -> return ds
         _ -> warning sigma_complete
           "signature difference could not be computed using full one" pos
       let gsysd = Set.map (G_symbol lid) sysd
           (ns, dg') = insGTheory dg0 (setSrcRange rg name)
             (DGBasicSpec (Just $ G_basic_spec lid bspec')
             (G_sign lid (mkExtSign diffSig) startSigId) gsysd)
               $ G_theory lid (currentSyntax lg) (ExtSign sigma_complete
               $ Set.intersection
                     (if addSyms then Set.union sys sysd else sysd)
               $ symset_of lid sigma_complete)
             startSigId (toThSens ax) startThId
       dg'' <- createConsLink DefLink conser lg dg' nsig' ns DGLinkExtension
       return (Basic_spec (G_basic_spec lid bspec') pos, ns, dg'')
  EmptySpec pos -> case nsig of
      EmptyNode _ -> do
        warning () "empty spec" pos
        let (ns, dg') = insGSig dg (setSrcRange rg name) DGEmpty
              (getMaybeSig nsig)
        return (sp, ns, dg')
        {- anaSpec should be changed to return a MaybeNode!
           Then this duplicate dummy node could be avoided.
           Also empty unions could be treated then -}
      JustNode ns -> return (sp, ns , dg)
  Translation asp ren ->
   do let sp1 = item asp
          rPos = getRange ren
      (sp1', ns'@(NodeSig n' gsigma), dg') <- anaSpec addSyms lg libEnv ln dg nsig
        (extName "Translation" name) opts eo sp1 rPos
      mor <- anaRenaming lg nsig gsigma opts ren
      -- ??? check that mor is identity on local env
      when (isIdentity mor) $ warning ()
         ("nothing renamed by:\n" ++ showDoc ren "") rPos
      (fs, dgf) <- if isIdentity mor && isInternal name then return (ns', dg')
         else do
         let (ns@(NodeSig node _), dg'') = insGSig dg' (setSrcRange rg name)
               (DGTranslation $ Renamed ren) $ cod mor
           -- ??? too simplistic for non-comorphism inter-logic translations
         return (ns, insLink dg'' mor globalDef SeeTarget n' node)
      return (Translation (replaceAnnoted sp1' asp) ren, fs, dgf)
  Extraction asp extr -> do
    let sp0 = item asp
        rname = extName "Extension" name
    (sp', nsig', dg0) <- anaSpec addSyms lg libEnv ln dg nsig rname opts eo sp0 rg
    (ns', dg1) <- anaExtraction lg libEnv dg0 nsig' name rg extr
    return (Extraction (replaceAnnoted sp' asp) extr, ns', dg1)
  Reduction asp restr ->
   do let sp1 = item asp
          rname = extName "Restriction" name
      (sp1', ns0, dg0) <- anaSpec addSyms lg libEnv ln dg nsig rname opts eo sp1 rg
      rLid <- getRestrLogic restr
      p1@(NodeSig n' gsigma', dg') <- coerceNode lg dg0 ns0 rname rLid
      (hmor, tmor) <- anaRestriction lg (getMaybeSig nsig) gsigma' opts restr
      let noRename = maybe True isIdentity tmor
          noHide = isIdentity hmor
      when noHide $ (if noRename then warning else hint) ()
        ("nothing hidden by:\n" ++ showDoc restr "") $ getRange restr
      p2@(NodeSig node1 _, dg2) <- if noHide && isInternal name then return p1
          else do
           let trgSg = dom hmor
               hidSyms = Set.difference (symsOfGsign gsigma')
                 $ symsOfGsign trgSg
               orig = DGRestriction (Restricted restr) hidSyms
               (ns@(NodeSig node _), dg'') = insGSig dg'
                 (if noRename then name else extName "Hiding" name)
                 orig trgSg
           -- ??? too simplistic for non-comorphism inter-logic reductions
           return (ns, insLink dg'' hmor HidingDefLink SeeTarget n' node)
      {- we treat hiding and revealing differently
      in order to keep the dg as simple as possible -}
      (fs, dgf) <- case tmor of
        Just tmor' | not noRename -> do
          let (ns@(NodeSig node2 _), dg3) =
                   insGSig dg2 name DGRevealTranslation $ cod tmor'
          return (ns, insLink dg3 tmor' globalDef SeeTarget node1 node2)
        Nothing -> return p2
        _ -> hint p2 ("nothing renamed by:\n" ++ showDoc restr "")
            $ getRange restr
      return (Reduction (replaceAnnoted sp1' asp) restr, fs, dgf)
  Filtering asp filtering -> do
       let sp1 = item asp
           rname = extName "Filtering" name
       (sp', nsig', dg') <- anaSpec addSyms lg libEnv ln dg nsig rname opts eo sp1 rg
       (nf, dgF) <- anaFiltering lg libEnv dg' nsig' name filtering
       return (Filtering (replaceAnnoted sp' asp) filtering, nf, dgF)
       -- error "analysis of filterings not yet implemented"
  Minimization asp (Mini kw cm cv poss) -> do
      (nasp, nsig', dg') <- anaFreeOrCofreeSpec addSyms lg libEnv opts ln dg nsig
        name Minimize eo asp poss
      return (Minimization nasp (Mini kw cm cv poss), nsig', dg')
  Union asps pos -> do
    (newAsps, _, ns, dg') <- adjustPos pos $ anaUnion addSyms lg libEnv ln dg nsig
      name opts eo asps rg
    return (Union newAsps pos, ns, dg')
  Intersection asps pos -> do
    (newAsps, _, ns, dg') <- adjustPos pos $ anaIntersect addSyms lg libEnv ln dg nsig
      name opts eo asps rg
    return (Intersection newAsps pos, ns, dg')
  Extension asps pos -> do
   let namedSps = map (\ (asp, n) ->
         let nn = incBy n (extName "Extension" name) in
         if n < length asps then (nn, asp)
         else (name { xpath = xpath nn }, asp)) $ number asps
   (sps', nsig1', dg1, _, _) <- foldM (anaExtension lg libEnv opts eo ln pos)
     ([], nsig, dg, conser, addSyms) namedSps
   case nsig1' of
       EmptyNode _ -> fail "empty extension"
       JustNode nsig1 -> return (Extension (zipWith replaceAnnoted
                          (reverse sps') asps)
                                 pos, nsig1, dg1)
  Free_spec asp poss -> do
      (nasp, nsig', dg') <- anaFreeOrCofreeSpec addSyms lg libEnv opts ln dg nsig
        name Free eo asp poss
      return (Free_spec nasp poss, nsig', dg')
  Cofree_spec asp poss -> do
      (nasp, nsig', dg') <- anaFreeOrCofreeSpec addSyms lg libEnv opts ln dg nsig
        name Cofree eo asp poss
      return (Cofree_spec nasp poss, nsig', dg')
  Minimize_spec asp poss -> do
      (nasp, nsig', dg') <- anaFreeOrCofreeSpec addSyms lg libEnv opts ln dg nsig
          name Minimize eo asp poss
      return (Minimize_spec nasp poss, nsig', dg')
  Local_spec asp asp' poss -> adjustPos poss $ do
      let sp1 = item asp
          pos1 = getRange sp1
          sp1' = item asp'
          pos1' = getRange sp1'
          lname = extName "Local" name
      (sp2, nsig'@(NodeSig _ gsig1), dg') <-
        anaSpec False lg libEnv ln dg nsig (extName "Spec" lname) opts eo sp1 pos1
      (sp2', NodeSig n'' gsig2@(G_sign lid2 sigma2 _), dg'') <- anaSpec False lg
        libEnv ln dg' (JustNode nsig') (extName "Within" lname) opts eo sp1' pos1'
      let gSigN = getMaybeSig nsig
      (G_sign lid sigmaN _, _) <- gSigCoerce lg gSigN (Logic lid2)
      sigma <- coerceSign lid lid2 "Analysis of local spec1" sigmaN
      (G_sign lid' sigma' _, _) <- gSigCoerce lg gsig1 (Logic lid2)
      sigma1 <- coerceSign lid' lid2 "Analysis of local spec2" sigma'
      let sys = ext_sym_of lid2 sigma
          sys1 = ext_sym_of lid2 sigma1
          sys2 = ext_sym_of lid2 sigma2
      mor3 <- if isStructured opts then return (ext_ide sigma2)
               else ext_cogenerated_sign lid2
                      (sys1 `Set.difference` sys) sigma2
      let sigma3 = dom mor3
          gsigma3 = G_sign lid2 (makeExtSign lid2 sigma3) startSigId
          sys3 = symset_of lid2 sigma3
      unless (isStructured opts
              || sys2 `Set.difference` sys1 `Set.isSubsetOf` sys3)
        $ plain_error () (
          "illegal use of locally declared symbols: "
          ++ showDoc ((sys2 `Set.intersection` sys1) `Set.difference` sys3) "")
         poss
      let hidSyms = Set.difference (symsOfGsign gsig2) $ symsOfGsign gsigma3
          orig = DGRestriction NoRestriction hidSyms
          (ns@(NodeSig node _), dg2) = insGSig dg'' name orig gsigma3
      return (Local_spec (replaceAnnoted sp2 asp)
                         (replaceAnnoted sp2' asp')
                         poss, ns,
              insLink dg2 (gEmbed2 gsigma3 $ mkG_morphism lid2 mor3)
                  HidingDefLink SeeTarget n'' node)
  Closed_spec asp pos -> adjustPos pos $ do
      let sp1 = item asp
          pos1 = getRange sp1
          l = getLogic nsig
      -- analyse spec with empty local env
      (sp', NodeSig n' gsigma', dg') <- anaSpec False lg libEnv ln dg
        (EmptyNode l) (extName "Closed" name) opts eo sp1 pos1
      gsigma2 <- gsigUnionMaybe lg addSyms nsig gsigma'
      let (ns@(NodeSig node _), dg2) = insGSig dg' name DGClosed gsigma2
      incl2 <- ginclusion lg gsigma' gsigma2
      let dg3 = insLink dg2 incl2 globalDef SeeTarget n' node
      dg4 <- createConsLink DefLink conser lg dg3 nsig ns DGLinkClosedLenv
      return (Closed_spec (replaceAnnoted sp' asp) pos, ns, dg4)
  Qualified_spec lognm asp pos -> adjustPos pos $ do
      let newLG = setLogicName lognm lg
      l <- lookupCurrentLogic "Qualified_spec" newLG
      let newNSig = case nsig of
            EmptyNode _ -> EmptyNode l
            _ -> nsig
          qname = extName "Qualified" name
      (sp', ns', dg') <- anaSpec addSyms newLG libEnv ln dg newNSig qname opts eo
        (item asp) pos
      (ns, dg2) <- coerceNode lg dg' ns' qname l
      return (Qualified_spec lognm asp { item = sp' } pos, ns, dg2)
  Group asp pos -> do
      (sp', nsig', dg') <-
          anaSpecTop conser addSyms lg libEnv ln dg nsig name opts eo (item asp) rg
      return (Group (replaceAnnoted sp' asp) pos, nsig', dg')
  Spec_inst spname' afitargs mImp pos0 -> do
   spname <- expCurieR (globalAnnos dg) eo spname'
   let pos = if null afitargs then iriPos spname else pos0
   adjustPos pos $ case lookupGlobalEnvDG spname dg of
    Just (SpecEntry gs@(ExtGenSig (GenSig _ params _)
                        body@(NodeSig nB gsigmaB))) ->
     case (length afitargs, length params) of
      -- the case without parameters leads to a simpler dg
      (0, 0) -> case nsig of
          -- if the node shall not be named and the logic does not change,
        EmptyNode _ | isInternal name -> do
          dg2 <- createConsLink DefLink conser lg dg nsig body SeeTarget
             -- then just return the body
          return (sp, body, dg2)
             -- otherwise, we need to create a new one
        _ -> do
           gsigma <- gsigUnionMaybe lg addSyms nsig gsigmaB
           let (fsig@(NodeSig node _), dg2) =
                 insGSig dg name (DGInst spname) gsigma
           incl <- ginclusion lg gsigmaB gsigma
           let dg3 = case nsig of
                 JustNode (NodeSig nI _) | nI == nB -> dg2
                 _ -> insLink dg2 incl globalDef (DGLinkMorph spname) nB node
           dg4 <- createConsLink DefLink conser lg dg3 nsig fsig SeeTarget
           return (sp, fsig, dg4)
      -- now the case with parameters
      (la, lp) | la == lp -> do
       (ffitargs, dg', (morDelta, gsigmaA, ns@(NodeSig nA gsigmaRes))) <-
               anaAllFitArgs lg libEnv opts eo ln dg nsig name spname gs afitargs
       GMorphism cid _ _ _ _ <- return morDelta
       morDelta' <- case nsig of
         EmptyNode _
           | logicOfGsign gsigmaA == logicOfGsign gsigmaRes
             -> return morDelta
         _ -> ginclusion lg gsigmaA gsigmaRes >>= comp morDelta
       (_, imor) <- gSigCoerce lg gsigmaB $ Logic $ sourceLogic cid
       tmor <- gEmbedComorphism imor gsigmaB
       morDelta'' <- comp tmor morDelta'
       let dg4 = case nsig of
             JustNode (NodeSig nI _) | nI == nB -> dg'
             _ -> insLink dg' morDelta'' globalDef (DGLinkMorph spname) nB nA
       dg5 <- createConsLink DefLink conser lg dg4 nsig ns SeeTarget
       return (Spec_inst spname ffitargs mImp pos, ns, dg5)
       | otherwise -> instMismatchError spname lp la pos
    _ | null afitargs -> do
     warning () ("ignoring missing spec " ++ showDoc spname' "") pos
     case nsig of
      EmptyNode _ -> do -- copied from EmptySpec case
        let (ns, dg') = insGSig dg name DGEmpty (getMaybeSig nsig)
        return (sp, ns, dg')
      JustNode ns -> return (sp, ns , dg)
    _ -> notFoundError "structured spec" spname

  -- analyse "data SPEC1 SPEC2"
  Data lD@(Logic lidD) lP asp1 asp2 pos -> adjustPos pos $ do
      let sp1 = item asp1
          pos1 = getRange sp1
          sp2 = item asp2
      {- look for the inclusion comorphism from the current logic's data logic
      into the current logic itself -}
      c <- logicInclusion lg lD lP
      let dname = extName "Data" name
      -- analyse SPEC1
      (sp1', ns', dg') <- anaSpec False (setCurLogic (language_name lidD) lg)
         libEnv ln dg (EmptyNode lD) dname opts eo sp1 pos1
      -- force the result to be in the data logic
      (ns'', dg'') <- coerceNode lg dg' ns' (extName "Qualified" dname) lD
      -- translate SPEC1's signature along the comorphism
      (nsig2@(NodeSig node gsigmaD), dg2) <-
         coerceNodeByComorph c dg'' ns'' dname
      (usig, udg) <- case nsig of
        EmptyNode _ -> return (nsig2, dg2)
        JustNode ns2 -> do
          gsigma2 <- gsigUnion lg addSyms (getSig ns2) gsigmaD
          let (ns@(NodeSig node2a _), dg2a) =
                insGSig dg2 (extName "Union" name) DGUnion gsigma2
          incl2 <- ginclusion lg gsigmaD gsigma2
          let dg3 = insLink dg2a incl2 globalDef SeeTarget node node2a
          dg4 <- createConsLink DefLink conser lg dg3 nsig ns SeeTarget
          return (ns, dg4)
      -- analyse SPEC2
      (sp2', nsig3, udg3) <-
          anaSpec addSyms lg libEnv ln udg (JustNode usig) name opts eo sp2 rg
      return (Data lD lP
                   (replaceAnnoted sp1' asp1)
                   (replaceAnnoted sp2' asp2)
                   pos, nsig3, udg3)
  Combination (Network cItems eItems _) pos -> adjustPos pos $ do
    let (cNodes', cEdges') = networkDiagram dg cItems eItems
    (ns, dg') <- insertColimitInGraph libEnv dg cNodes' cEdges' name
    return (sp, ns, dg')
  _ -> fail $ "AnalysisStructured: " ++ show (prettyLG lg sp)


-- | build the diagram of a network specified as a list of network elements to be added
-- | and a list of network elements to be removed

networkDiagram :: DGraph
                        -> [LABELED_ONTO_OR_INTPR_REF]
                        -> [IRI]
                        -> ([Node], [(Node, Node, DGLinkLab)])
networkDiagram dg cItems eItems = let 
        -- add to/remove from a list of nodes and a list of edges
        -- the graph of a network element
        -- if remove is true, nElem gets removed 
        getNodes remove (cN, cE) nElem = let
            cEntry = fromMaybe (error $ "No entry for " ++ show nElem)
                     $ lookupGlobalEnvDG nElem dg
            bgraph = dgBody dg
            lEdge x y m = case filter (\ (_, z, l) -> (z == y) &&
                                         (dgl_morphism l == m) ) $
                               out bgraph x of
                             [] -> error $ "No edge found:\n x:" ++ show x ++ "\n y: " ++ show y
                             lE : _ -> lE
           in case cEntry of
               SpecEntry extGenSig -> let
                   n = getNode $ extGenBody extGenSig
                  in if remove then
                     (n:cN, nub $ cE ++ out bgraph n ++ inn bgraph n) 
                     -- remove all incoming and outgoing edges of n 
                     else if elem n cN then (cN, cE) else (n : cN, cE)
               ViewOrStructEntry True (ExtViewSig ns gm eGS) -> let
                   s = getNode ns
                   t = getNode $ extGenBody eGS
                 in if remove 
                     then (cN, lEdge s t gm : cE) 
                     -- keep the nodes and remove just the edge 
                     else(nub $ s : t : cN, lEdge s t gm : cE)
               AlignEntry asig ->
                  case asig of
                   AlignMor src gmor tar ->  let
                     s = getNode src
                     t = getNode tar
                    in (nub $ s : t : cN, lEdge s t gmor : cE)
                   AlignSpan src phi1 tar1 phi2 tar2 ->  let
                     s = getNode src
                     t1 = getNode tar1
                     t2 = getNode tar2
                    in (nub $ [s, t1, t2] ++ cN,
                              [lEdge s t1 phi1, lEdge s t2 phi2] ++ cE)
                   WAlign src1 i1 sig1 src2 i2 sig2 tar1 tar2 bri -> let
                      s1 = getNode src1
                      s2 = getNode src2
                      t1 = getNode tar1
                      t2 = getNode tar2
                      b = getNode bri
                     in if remove then
                         (nub $ s1 : s2 : b : cN,
                         [lEdge s1 b i1, lEdge s1 t1 sig1,
                          lEdge s2 b i2, lEdge s2 t2 sig2] ++ cE) 
                        else (nub $ s1 : s2 : t1 : t2 : b : cN,
                         [lEdge s1 b i1, lEdge s1 t1 sig1,
                          lEdge s2 b i2, lEdge s2 t2 sig2] ++ cE)
               NetworkEntry diag -> let
                    dnodes = nodes diag
                    ledges = labEdges diag
                    dgedges = map (\(x,y, (_, m)) -> lEdge x y m) ledges
                   in (dnodes, dgedges)
               _ -> error $ show nElem
                    ++ " is not an OMS, a view, a network or an alignment"
        -- also add the implicit elements: paths of global def. links,
        -- hiding def. links, inclusions of DOL intersections
        addGDefLinks (cN, iN, cE) n = let
           g = dgBody dg
           allGDef = all $ \ (_, _, l) -> isGlobalDef $ dgl_type l
           gDefPaths x y = filter allGDef $ getPathsTo x y g
           nPaths = concat $ concatMap (gDefPaths n) cN
           nNodes = concatMap (\ (x, y, _) -> [x, y]) nPaths
           hideLinks = filter (\ (_, _, l) -> dgl_type l == HidingDefLink)
              $ concatMap (inn g) $ cN ++ nNodes
           hNodes = map (\ (x, _, _) -> x) hideLinks
           implicitNodes = nub $ iN ++ nNodes ++ hNodes
           intersectLinks = filter (\ (_, _, l) -> dgl_origin l == DGLinkIntersect)
                            $ concatMap (inn g) $ cN ++ implicitNodes
           in (cN, implicitNodes
              , nub $ nPaths ++ cE ++ hideLinks ++ intersectLinks)
        addLinks (cN, cE) = foldl addGDefLinks (cN, [], cE) cN
        (cNodes, iNodes, cEdges) =
           addLinks . foldl (getNodes False) ([], []) $ getItems cItems
        (eNodes, eEdges) = foldl (getNodes True) ([], []) eItems
        (cNodes', cEdges') = (nub (cNodes ++ iNodes) \\ eNodes,
                              cEdges \\ eEdges)
 in (cNodes', cEdges')
  
getItems :: [LABELED_ONTO_OR_INTPR_REF] -> [IRI]
getItems [] = []
getItems (Labeled _ i : r) = i : getItems r

instMismatchError :: IRI -> Int -> Int -> Range -> Result a
instMismatchError spname lp la = fatal_error $ iriToStringUnsecure spname
    ++ " expects " ++ show lp ++ " arguments" ++ " but was given " ++ show la

notFoundError :: String -> IRI -> Result a
notFoundError str sid = fatal_error (str ++ " '" ++ iriToStringUnsecure sid
    ++ "' or '" ++ iriToStringShortUnsecure sid ++ "' not found") $ iriPos sid

gsigUnionMaybe :: LogicGraph -> Bool -> MaybeNode -> G_sign -> Result G_sign
gsigUnionMaybe lg both mn gsig = case mn of
  EmptyNode _ -> return gsig
  JustNode ns -> gsigUnion lg both (getSig ns) gsig

anaExtraction :: LogicGraph -> LibEnv -> DGraph -> NodeSig -> NodeName -> Range ->
              EXTRACTION -> Result (NodeSig, DGraph)
anaExtraction lg libEnv dg nsig name rg (ExtractOrRemove b iris _) = if not b then
  fail "analysis of remove not implemented yet"
 else do
  let dg0 = markHiding libEnv dg
      n = getNode nsig
  if labelHasHiding $ labDG dg0 n then
    fail "cannot extract module from a non-flattenable OMS"
   else do
    let dgThm = computeDGraphTheories libEnv dg0
        gth = case (globalTheory . labDG dgThm) n  of
               Nothing -> error "not able to compute theory"
               Just th -> th
    mTh <- case gth of
        G_theory lid syntax (ExtSign sig _) _ gsens _ -> do
          let nsens = toNamedList gsens
          (msig, msens) <- extract_module lid iris (sig, nsens)
          return $ G_theory lid syntax
                            (ExtSign msig $ foldl Set.union Set.empty $ sym_of lid msig) startSigId
                            (toThSens msens) startThId
    let (nsig', dg') = insGTheory dg (setSrcRange rg name) DGExtract mTh
    incl <- ginclusion lg (getSig nsig') (getSig nsig)
    let  dg'' = insLink dg' incl globalThm SeeSource (getNode nsig') n
    return (nsig', dg'')

anaUnion :: Bool -> LogicGraph -> LibEnv -> LibName -> DGraph -> MaybeNode -> NodeName
  -> HetcatsOpts -> ExpOverrides -> [Annoted SPEC] -> Range
  -> Result ([Annoted SPEC], [NodeSig], NodeSig, DGraph)
anaUnion addSyms lg libEnv ln dg nsig name opts eo asps rg = case asps of
  [] -> fail "empty union"
  _ -> do
      let sps = map item asps
      (sps', nsigs, dg', _) <-
          let ana (sps1, nsigs, dg', n) sp' = do
                let n1 = inc n
                (sp1, nsig', dg1) <-
                  anaSpec addSyms lg libEnv ln dg' nsig n1 opts eo sp' $ getRange sp'
                return (sp1 : sps1, nsig' : nsigs, dg1, n1)
           in foldM ana ([], [], dg, extName "Union" name) sps
      let newAsps = zipWith replaceAnnoted (reverse sps') asps
      case nsigs of
        [ns] -> return (newAsps, nsigs, ns, dg')
        _ -> do
          let nsigs' = reverse nsigs
          gbigSigma <- gsigManyUnion lg (map getSig nsigs')
          let (ns@(NodeSig node _), dg2) = insGSig dg' (setSrcRange rg name)
                DGUnion gbigSigma
              insE dgl (NodeSig n gsigma) = do
                incl <- ginclusion lg gsigma gbigSigma
                return $ insLink dgl incl globalDef SeeTarget n node
          dg3 <- foldM insE dg2 nsigs'
          return (newAsps, nsigs', ns, dg3)

anaIntersect :: Bool -> LogicGraph -> LibEnv -> LibName -> DGraph -> MaybeNode -> NodeName
  -> HetcatsOpts -> ExpOverrides -> [Annoted SPEC] -> Range
  -> Result ([Annoted SPEC], [NodeSig], NodeSig, DGraph)
anaIntersect addSyms lg libEnv ln dg nsig name opts eo asps rg = case asps of
  [] -> fail "empty intersection"
  _ -> do
      let sps = map item asps
          ana (sps1, nsigs, dg', n) sp' = do
                let n1 = inc n
                (sp1, nsig', dg1) <-
                  anaSpec addSyms lg libEnv ln dg' nsig n1 opts eo sp' $
                          getRange sp'
                return (sp1 : sps1, nsig' : nsigs, dg1, n1)
      (sps', nsigs, dg', _) <-
        foldM ana ([], [], dg, extName "Intersect" name) sps
      let newAsps = zipWith replaceAnnoted (reverse sps') asps
      case nsigs of
        [ns] -> return (newAsps, nsigs, ns, dg')
        _ -> do
          let nsigs' = reverse nsigs
              labelHidings = map labelHasHiding $ map (\n -> labDG (markHiding libEnv dg) $ getNode n) nsigs'
              hasHiding = foldl (\x y -> x || y) False labelHidings
          case hasHiding of
            True -> fail "Intersection is defined only for flattenable theories"
            False -> do
             let dgThm = computeDGraphTheories libEnv dg
                 theo:theos = map (\x -> case (globalTheory . labDG dgThm . getNode) x of
                                            Nothing -> error $ "not able to compute theory of node" ++ (show $ getNode x)
                                            Just th -> th) nsigs'
             gbigSigma <- gsigManyIntersect lg (map getSig nsigs')
             gth <- foldM (intersectG_sentences gbigSigma) theo theos
             let (ns@(NodeSig node _), dg2) = insGTheory dg' (setSrcRange rg name)
                    DGIntersect gth
                 insE dgl (NodeSig n gsigma) = do
                   incl <- ginclusion lg gbigSigma gsigma
                   return $ insLink dgl incl globalThm DGLinkIntersect node n
             dg3 <- foldM insE dg2 nsigs'
             return (newAsps, nsigs', ns, dg3)

anaFiltering :: LogicGraph -> LibEnv -> DGraph -> NodeSig -> NodeName-> FILTERING
   -> Result (NodeSig, DGraph)
anaFiltering lg libEnv dg nsig nname filtering = case filtering of
  FilterSymbolList selectOrReject (G_symb_items_list lidS sItems) _ ->
   if not selectOrReject then do
     let strs = concatMap (symb_items_name lidS) sItems
         dgThm = computeDGraphTheories libEnv dg
         th =
            case (globalTheory . labDG dgThm . getNode) nsig of
                  Nothing -> error "error computing theory"
                  Just t -> t
     case th of
      G_theory l1 ser1 sig1 ind1 sens1 ind1' -> do
         let gth' = G_theory l1 ser1 sig1 ind1
                    (foldl (\m x -> Map.delete x m) sens1 strs) ind1'
         let (ns@(NodeSig node gsigma), dg') = insGTheory dg nname DGEmpty gth'
         gmor <- ginclusion lg gsigma $ getSig nsig
         let dg2 = insLink dg' gmor globalThm SeeSource node $ getNode nsig
         return (ns, dg2)
    else error "analysis of select not implemented yet"
  FilterBasicSpec _ _ _ -> error "filtering a basic spec not implemented yet"


-- analysis of renamings
anaRen :: LogicGraph -> HetcatsOpts -> MaybeNode -> Range -> GMorphism
  -> G_mapping -> Result GMorphism
anaRen lg opts lenv pos gmor@(GMorphism r sigma ind1 mor _) gMapping =
  adjustPos pos $ case gMapping of
  G_symb_map (G_symb_map_items_list lid sis) ->
    let lid2 = targetLogic r in
    if language_name lid2 == language_name lid then
     if isStructured opts then return gmor else do
      sis1 <- coerceSymbMapItemsList lid lid2 "Analysis of renaming" sis
      src@(ExtSign sig _) <- return $ makeExtSign lid2 $ cod mor
      rmap <- stat_symb_map_items lid2 sig Nothing sis1
      mor1 <- ext_induced_from_morphism lid2 rmap src
      case lenv of
        EmptyNode _ -> return ()
        JustNode (NodeSig _ sigLenv) -> do
          -- needs to be changed for logic translations
          (G_sign lid1 sigmaLenv1 _, _) <-
              gSigCoerce lg sigLenv (Logic lid2)
          sigmaLenv' <- coerceSign lid1 lid2 "" sigmaLenv1
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
      anaRen lg opts lenv pos newMor gMapping
  G_logic_translation (Logic_code tok src tar pos1) ->
    let pos2 = if pos1 == nullRange then pos else pos1
        adj1 = adjustPos pos2
    in adj1 $ do
    G_sign srcLid srcSig ind <- return (cod gmor)
    c <- case tok of
            Just c -> lookupComorphism c lg
            Nothing -> case tar of
               Just (Logic_name l _ _) ->
                 lookupLogic "with logic: " l lg
                 >>= logicInclusion lg (Logic srcLid)
               Nothing -> fail "with logic: cannot determine comorphism"
    checkSrcOrTarLogic pos2 True c src
    checkSrcOrTarLogic pos2 False c tar
    mor1 <- gEmbedComorphism c (G_sign srcLid srcSig ind)
    comp gmor mor1

checkSrcOrTarLogic :: Range -> Bool -> AnyComorphism -> Maybe Logic_name
                      -> Result ()
checkSrcOrTarLogic pos b (Comorphism cid) ml = case ml of
  Nothing -> return ()
  Just (Logic_name s _ _) ->
      when (s /= if b then language_name $ sourceLogic cid
                 else language_name $ targetLogic cid)
        $ plain_error () (s ++ " is is not the "
           ++ (if b then "source" else "target") ++ " logic of "
           ++ language_name cid) pos

anaRenaming :: LogicGraph -> MaybeNode -> G_sign -> HetcatsOpts -> RENAMING
  -> Result GMorphism
anaRenaming lg lenv gSigma opts (Renaming ren pos) =
      foldM (anaRen lg opts lenv pos) (ide gSigma) ren

getRestrLogic :: RESTRICTION -> Result AnyLogic
getRestrLogic restr = case restr of
  Revealed (G_symb_map_items_list lid _) _ -> return $ Logic lid
  Hidden l _ -> case l of
    [] -> error "getRestrLogic"
    h : _ -> case h of
      G_symb_list (G_symb_items_list lid _) -> return $ Logic lid
      G_logic_projection (Logic_code _ _ _ pos1) ->
        fatal_error "no analysis of logic projections yet" pos1

-- analysis of restrictions
anaRestr :: LogicGraph -> G_sign -> Range -> GMorphism -> G_hiding
  -> Result GMorphism
anaRestr lg sigEnv pos (GMorphism cid (ExtSign sigma1 sys1) _ mor _) gh =
    case gh of
      G_symb_list (G_symb_items_list lid' sis') -> do
        let lid1 = sourceLogic cid
        sis1 <- coerceSymbItemsList lid' lid1 "Analysis of restriction1" sis'
        rsys <- stat_symb_items lid1 sigma1 sis1
        let sys = symset_of lid1 sigma1
            sys' = Set.filter (\ sy -> any (matches lid1 sy) rsys) sys
            unmatched = filter ( \ rsy -> Set.null $ Set.filter
                                 ( \ sy -> matches lid1 sy rsy) sys') rsys
        unless (null unmatched)
          $ plain_error () ("attempt to hide unknown symbols:\n"
                          ++ showDoc unmatched "") pos
        -- needs to be changed when logic projections are implemented
        (G_sign lidE sigmaLenv0 _, _) <- gSigCoerce lg sigEnv (Logic lid1)
        sigmaLenv' <- coerceSign lidE lid1 "" sigmaLenv0
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
      G_logic_projection (Logic_code _ _ _ pos1) ->
        fatal_error "no analysis of logic projections yet" pos1

anaRestriction :: LogicGraph -> G_sign -> G_sign -> HetcatsOpts -> RESTRICTION
  -> Result (GMorphism, Maybe GMorphism)
anaRestriction lg gSigma gSigma'@(G_sign lid0 sig0 _) opts restr =
  if isStructured opts then return (ide gSigma, Nothing) else
  case restr of
    Hidden rstr pos -> do
      mor <- foldM (anaRestr lg gSigma pos) (ide gSigma') rstr
      return (mor, Nothing)
    Revealed (G_symb_map_items_list lid1 sis) pos -> adjustPos pos $ do
      (G_sign lid sigma _, _) <- gSigCoerce lg gSigma (Logic lid1)
      sigma0 <- coerceSign lid lid1 "reveal1" sigma
      sigma1 <- coerceSign lid0 lid1 "reveal2" sig0
      let sys = ext_sym_of lid1 sigma0 -- local env
          sys' = ext_sym_of lid1 sigma1 -- "big" signature
      rmap <- stat_symb_map_items lid1 (plainSign sigma1) Nothing sis
      let sys'' = Set.fromList
           [sy | sy <- Set.toList sys', rsy <-
                       Map.keys rmap, matches lid1 sy rsy]
          {- domain of rmap intersected with sys'
          rmap is checked by ext_induced_from_morphism below -}
      mor1 <- ext_generated_sign lid1 (sys `Set.union` sys'') sigma1
      let extsig1 = makeExtSign lid1 $ dom mor1
      mor2 <- ext_induced_from_morphism lid1 rmap extsig1
      return (gEmbed2 (G_sign lid1 extsig1 startSigId)
                      $ G_morphism lid1 mor1 startMorId
             , Just $ gEmbed $ mkG_morphism lid1 mor2)

partitionGmaps :: [G_mapping] -> ([G_mapping], [G_mapping])
partitionGmaps l = let
  (hs, rs) = span (\ sm -> case sm of
    G_symb_map _ -> True
    G_logic_translation _ -> False) $ reverse l
  in (reverse rs, reverse hs)

anaGmaps :: LogicGraph -> HetcatsOpts -> Range -> G_sign -> G_sign
  -> [G_mapping] -> Result G_morphism
anaGmaps lg opts pos psig@(G_sign lidP sigmaP _) asig@(G_sign lidA sigmaA _)
  gsis = adjustPos pos $ if isStructured opts
    then return $ mkG_morphism lidP $ ext_ide sigmaP
    else if null gsis then do
        (G_sign lidP' sigmaP' _, _) <- gSigCoerce lg psig (Logic lidA)
        sigmaA' <- coerceSign lidA lidP' "anaGmaps" sigmaA
        fmap (mkG_morphism lidP') $
          ext_induced_from_to_morphism lidP' Map.empty sigmaP' sigmaA'
      else do
      cl <- lookupCurrentLogic "anaGmaps" lg
      G_symb_map_items_list lid sis <- homogenizeGM cl gsis
      (G_sign lidP' sigmaP'' _, _) <- gSigCoerce lg psig (Logic lid)
      sigmaP' <- coerceSign lidP' lid "anaGmaps1" sigmaP''
      (G_sign lidA' sigmaA'' _, _) <- gSigCoerce lg asig (Logic lid)
      sigmaA' <- coerceSign lidA' lid "anaGmaps2" sigmaA''
      rmap <- stat_symb_map_items lid (plainSign sigmaP')
        (Just $ plainSign sigmaA') sis
      fmap (mkG_morphism lid)
        $ ext_induced_from_to_morphism lid rmap sigmaP' sigmaA'

   {-
   let symI = sym_of lidP sigmaI'
       symmap_mor = symmap_of lidP mor
   -- are symbols of the imports left untouched?
   if Set.all (\sy -> lookupFM symmap_mor sy == Just sy) symI
    then return ()
    else plain_error () "Fitting morphism must not affect import" pos
      -- does not work
      -- also output symbols that are affected
   -}

anaFitArg :: LogicGraph -> LibEnv -> LibName -> DGraph -> IRI -> MaybeNode
  -> NodeSig -> HetcatsOpts -> NodeName -> ExpOverrides -> FIT_ARG
  -> Result (FIT_ARG, DGraph, (G_morphism, NodeSig))
anaFitArg lg libEnv ln dg spname nsigI nsigP@(NodeSig nP gsigmaP) opts name eo fv =
  let ga = globalAnnos dg in
  case fv of
  Fit_spec asp gsis pos -> do
   (sp', nsigA, dg') <- anaSpec False lg libEnv ln dg nsigI name opts eo (item asp) pos
   (_, Comorphism aid) <-
       logicUnion lg (getNodeLogic nsigP) (getNodeLogic nsigA)
   let tl = Logic $ targetLogic aid
   (nsigA'@(NodeSig nA' gsigA'), dg'') <- coerceNode lg dg' nsigA name tl
   (gsigmaP', pmor) <- gSigCoerce lg gsigmaP tl
   tmor <- gEmbedComorphism pmor gsigmaP
   gmor <- anaGmaps lg opts pos gsigmaP' gsigA' gsis
   eGmor <- comp tmor $ gEmbed gmor
   return ( Fit_spec (replaceAnnoted sp' asp) gsis pos
          , if nP == nA' && isInclusion eGmor then dg'' else
                insLink dg'' eGmor globalThm
                   (DGLinkInst spname $ Fitted gsis) nP nA'
          , (gmor, nsigA'))
  Fit_view vn' afitargs pos -> do
   vn <- expCurieR ga eo vn'
   case lookupGlobalEnvDG vn dg of
    Just (ViewOrStructEntry _ (ExtViewSig (NodeSig nSrc gsigmaS) mor
      gs@(ExtGenSig (GenSig _ params _) target@(NodeSig nTar _))))
        -> adjustPos pos $ do
      GMorphism cid _ _ morHom ind <- return mor
      let lid = targetLogic cid
          pname = dgn_name $ labDG dg nP
          gsigmaI = getMaybeSig nsigI
      dg5 <- do
        gsigmaIS <- gsigUnionMaybe lg True nsigI gsigmaS
        unless (isSubGsign lg gsigmaP gsigmaIS
                && isSubGsign lg gsigmaIS gsigmaP)
             (plain_error ()
              ("Parameter does not match source of fittig view. "
               ++ "Parameter signature:\n"
               ++ showDoc gsigmaP
               "\nSource signature of fitting view (united with import):\n"
               ++ showDoc gsigmaIS "") pos)
        (dg4, iSrc) <- case nsigI of
          EmptyNode _ -> return (dg, nSrc)
          JustNode (NodeSig nI _) -> do
            inclI <- ginclusion lg gsigmaI gsigmaIS
            inclS <- ginclusion lg gsigmaS gsigmaIS
            let (NodeSig n' _, dg1) = insGSig dg (extName "View" name)
                  {xpath = xpath pname} (DGFitView vn) gsigmaIS
                dg2 = insLink dg1 inclI globalDef
                      (DGLinkFitViewImp vn) nI n'
            return (insLink dg2 inclS globalDef
                    (DGLinkFitViewImp vn) nSrc n', n')
        if nP == iSrc then return dg4 else do
          gmor <- ginclusion lg gsigmaP gsigmaIS
          return $ insLink dg4 gmor globalThm (DGLinkFitView vn) nP iSrc
      case (length afitargs, length params) of
      -- the case without parameters leads to a simpler dg
        (0, 0) -> return (fv, dg5, (G_morphism lid morHom ind, target))
        -- now the case with parameters
        (la, lp) | la == lp -> do
          (ffitargs, dg', (gmor_f, _, ns@(NodeSig nA _))) <-
            anaAllFitArgs lg libEnv opts eo ln dg5 (EmptyNode $ Logic lid)
              name vn gs afitargs
          mor1 <- comp mor gmor_f
          GMorphism cid1 _ _ theta _ <- return mor1
          let lid1 = targetLogic cid1
          when (language_name (sourceLogic cid1) /= language_name lid1)
            $ fatal_error "heterogeneous fitting views not yet implemented"
              pos
          let dg9 = insLink dg' gmor_f globalDef (DGLinkMorph vn) nTar nA
          return (Fit_view vn ffitargs pos, dg9, (mkG_morphism lid1 theta, ns))
         | otherwise -> instMismatchError spname lp la pos
    _ -> notFoundError "view" vn

anaFitArgs :: LogicGraph -> LibEnv -> HetcatsOpts -> ExpOverrides -> LibName -> IRI
  -> MaybeNode
  -> ([FIT_ARG], DGraph, [(G_morphism, NodeSig)], NodeName)
  -> (NodeSig, FIT_ARG)
  -> Result ([FIT_ARG], DGraph, [(G_morphism, NodeSig)], NodeName)
anaFitArgs lg libEnv opts eo ln spname imps (fas', dg1, args, name') (nsig', fa) = do
    let n1 = inc name'
    (fa', dg', arg) <- anaFitArg lg libEnv ln dg1 spname imps nsig' opts n1 eo fa
    return (fa' : fas', dg', arg : args, n1)

anaAllFitArgs :: LogicGraph -> LibEnv -> HetcatsOpts -> ExpOverrides -> LibName -> DGraph
  -> MaybeNode
  -> NodeName -> IRI -> ExtGenSig -> [Annoted FIT_ARG]
  -> Result ([Annoted FIT_ARG], DGraph, (GMorphism, G_sign, NodeSig))
anaAllFitArgs lg libEnv opts eo ln dg nsig name spname
  gs@(ExtGenSig (GenSig imps params _) _)
  afitargs = do
  let fitargs = map item afitargs
  (fitargs', dg', args, _) <- foldM (anaFitArgs lg libEnv opts eo ln spname imps)
           ([], dg, [], extName "Actuals" name) (zip params fitargs)
  let actualargs = reverse args
  (gsigma', morDelta) <- applyGS lg gs actualargs
  gsigmaRes <- gsigUnionMaybe lg True nsig gsigma'
  let (ns, dg2) = insGSig dg' name (DGInst spname) gsigmaRes
  dg3 <- foldM (parLink lg nsig (DGLinkInstArg spname) ns) dg2
    $ map snd actualargs
  return ( zipWith replaceAnnoted (reverse fitargs') afitargs, dg3
         , (morDelta, gsigma', ns))

parLink :: LogicGraph -> MaybeNode -> DGLinkOrigin -> NodeSig -> DGraph
           -> NodeSig -> Result DGraph
parLink lg nsig orig (NodeSig node gsigma') dg (NodeSig nA_i sigA_i) =
  case nsig of
    JustNode (NodeSig nI _) | nI == nA_i -> return dg
      -- actual parameter will be included via import
    _ -> do
      incl <- ginclusion lg sigA_i gsigma'
      return $ insLink dg incl globalDef orig nA_i node

{- Extension of signature morphisms (for instantitations)
first some auxiliary functions -}

mapID :: Map.Map Id (Set.Set Id) -> Id -> Result Id
mapID idmap i@(Id toks comps pos1) =
  case Map.lookup i idmap of
    Nothing -> do
      compsnew <- mapM (mapID idmap) comps
      return (Id toks compsnew pos1)
    Just ids -> case Set.toList ids of
      [] -> return i
      [h] -> return h
      _ -> plain_error i
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

extendMorphism :: Bool -- ^ check sharing (False for lambda expressions)
               -> G_sign      -- ^ formal parameter
               -> G_sign      -- ^ body
               -> G_sign      -- ^ actual parameter
               -> G_morphism  -- ^ fitting morphism
               -> Result (G_sign, G_morphism)
extendMorphism sharing (G_sign lid sigmaP _) (G_sign lidB sigmaB1 _)
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
      symbMapToRawSymbMap = Map.foldWithKey
          (on Map.insert $ symbol_to_raw lid) Map.empty
      rh = symbMapToRawSymbMap h
      idh = Map.foldWithKey (on setInsert $ sym_name lid) Map.empty h
  idhExt <- extID idsB idh
  let rIdExt = Map.foldWithKey (on Map.insert $ id_to_raw lid) Map.empty
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
                   Set.\\ imageSet h symsP
  unless (Set.null illShared || not sharing)
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
  return (G_sign lid sigma startSigId, mkG_morphism lid mor1)

applyGS :: LogicGraph -> ExtGenSig -> [(G_morphism, NodeSig)]
         -> Result (G_sign, GMorphism)
applyGS lg (ExtGenSig (GenSig nsigI _ gsigmaP) nsigB) args = do
  let mor_i = map fst args
      gsigmaA_i = map (getSig . snd) args
      gsigmaB = getSig nsigB
  gsigmaA@(G_sign lidA _ _) <- gsigManyUnion lg gsigmaA_i
  (Comorphism bid, Comorphism uid) <-
    logicUnion lg (getNodeLogic nsigB) (Logic lidA)
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
  (gsig, G_morphism gid mor3 mId) <- extendMorphism True gsigmaP' gsigmaB'
    gsigmaA' $ G_morphism (targetLogic aid) mor2 startMorId
  case gsigmaB of
    G_sign lidB sigB indB -> do
      sigB' <- coerceSign lidB (sourceLogic bid) "applyGS2" sigB
      mor4 <- coerceMorphism gid (targetLogic bid) "applyGS3" mor3
      return (gsig, GMorphism bid sigB' indB mor4 mId)

homogenizeGM :: AnyLogic -> [G_mapping] -> Result G_symb_map_items_list
homogenizeGM (Logic lid) =
  foldM homogenize1 (G_symb_map_items_list lid [])
  where
  homogenize1 (G_symb_map_items_list lid2 sis) sm = case sm of
    G_symb_map (G_symb_map_items_list lid1 sis1) -> do
         sis1' <- coerceSymbMapItemsList lid1 lid2 "homogenizeGM" sis1
         return $ G_symb_map_items_list lid2 $ sis ++ sis1'
    G_logic_translation lc ->
         fail $ "translation not supported by " ++ showDoc lc ""

getSpecAnnos :: Range -> Annoted a -> Result (Conservativity, Bool)
getSpecAnnos pos a = do
  let sannos = filter isSemanticAnno $ l_annos a
      (sanno1, conflict, impliesA) = case sannos of
        f@(Semantic_anno anno1 _) : r -> (case anno1 of
                SA_cons -> Cons
                SA_def -> Def
                SA_mono -> Mono
                _ -> None, any (/= f) r,
                     anno1 == SA_implies || anno1 == SA_implied)
        _ -> (None, False, False)
  when conflict $ plain_error () "Conflicting semantic annotations" pos
  return (sanno1, impliesA)

-- only consider addSyms for the first spec
anaExtension :: LogicGraph -> LibEnv -> HetcatsOpts -> ExpOverrides -> LibName -> Range
    -> ([SPEC], MaybeNode, DGraph, Conservativity, Bool)
    -> (NodeName, Annoted SPEC)
    -> Result ([SPEC], MaybeNode, DGraph, Conservativity, Bool)
anaExtension lg libEnv opts eo ln pos (sps', nsig', dg', conser, addSyms) (name', asp')
  = do
  (sanno1, impliesA) <- getSpecAnnos pos asp'
  -- attach conservativity to definition link
  let sp = item asp'
  (sp1', nsig1@(NodeSig n1 sig1), dg1) <- anaSpecTop (max conser sanno1)
    addSyms lg libEnv ln dg' nsig' name' opts eo sp $ getRange sp
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


-- BEGIN CURIE expansion

expCurieR :: GlobalAnnos -> ExpOverrides -> IRI -> Result IRI
expCurieR ga eo i = maybe (prefixErrorIRI i) return $ expCurie ga eo i

expCurie :: GlobalAnnos -> ExpOverrides -> IRI -> Maybe IRI
expCurie ga eo i =
  let pm = prefix_map ga
  in case Map.lookup i eo of
        Nothing -> expandCurie pm i
        Just path -> expandCurieByPath path i

expandCurieByPath :: FilePath -> IRI -> Maybe IRI
expandCurieByPath path i = case parseIRIReference $ path ++ "?" of
          Nothing -> Nothing
          Just p -> expandCurie (Map.singleton "" p) i

prefixErrorIRI :: IRI -> Result a
prefixErrorIRI i = fatal_error ("No prefix found for CURIE " ++
    iriToStringUnsecure i ++ " or expansion does not yield a valid IRI.")
    $ iriPos i

-- END CURIE expansion
