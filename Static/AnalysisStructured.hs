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
import Syntax.AS_Library

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
import qualified Common.OrderedMap as OMap

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
import Static.History

import Debug.Trace

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
    then anaSpecAux conser addSyms True lg libEnv ln 
                    dg nsig name opts eo sp pos 
    else do
  let provenThmLink =
        ThmLink $ Proven (DGRule "static analysis") emptyProofBasis
  (rsp, ns, rdg) <- anaSpec addSyms True lg libEnv ln 
                            dg nsig name opts eo sp pos
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
          anaSpec addSyms True lg libEnv ln 
                  dg nsig (extName (show dglType) name) opts eo
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

{- | analyze a SPEC. The first Bool Parameter determines if incoming symbols shall
be ignored while the second determines if the nodes should be optimized away for specifications without parameters. The options are needed to check: shall only the structure be
analysed? -}
anaSpec :: Bool -> Bool-> LogicGraph -> LibEnv -> LibName -> DGraph -> MaybeNode -> NodeName
  -> HetcatsOpts -> ExpOverrides -> SPEC -> Range
  -> Result (SPEC, NodeSig, DGraph)
anaSpec = anaSpecAux None

anaSpecAux :: Conservativity -> Bool -> Bool 
  -> LogicGraph -> LibEnv -> LibName -> DGraph
  -> MaybeNode -> NodeName -> HetcatsOpts -> ExpOverrides -> SPEC -> Range
  -> Result (SPEC, NodeSig, DGraph)
anaSpecAux conser addSyms optNodes lg 
           libEnv ln dg nsig name opts eo sp rg = case sp of
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
             let res@(Result ds mb) = -- trace ("sig in extBasicAnalysis:" ++ show sig ++ " bspec:" ++ show bspec) $ 
                                      extBasicAnalysis lid (getName name)
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
       dg'' <- -- trace ("gsysd:" ++ show gsysd) $ 
               createConsLink DefLink conser lg dg' nsig' ns DGLinkExtension
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
      (sp1', ns'@(NodeSig n' gsigma), dg') <- 
        anaSpec addSyms optNodes lg libEnv ln dg nsig
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
    (sp', nsig', dg0) <- anaSpec addSyms optNodes lg libEnv 
                                 ln dg nsig rname opts eo sp0 rg
    (ns', dg1) <- anaExtraction lg libEnv ln dg0 nsig' name rg extr
    return (Extraction (replaceAnnoted sp' asp) extr, ns', dg1)
  Reduction asp restr ->
   do let sp1 = item asp
          rname = extName "Restriction" name
      (sp1', ns0, dg0) <- anaSpec addSyms optNodes lg libEnv 
                           ln dg nsig rname opts eo sp1 rg
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
       (sp', nsig', dg') <- anaSpec addSyms optNodes lg libEnv ln dg 
                                    nsig rname opts eo sp1 rg
       (nf, dgF) <- anaFiltering lg libEnv ln dg' nsig' name filtering
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
        anaSpec False True lg libEnv ln 
                dg nsig (extName "Spec" lname) opts eo sp1 pos1
      (sp2', NodeSig n'' gsig2@(G_sign lid2 sigma2 _), dg'') <- 
          anaSpec False True lg libEnv ln 
                dg' (JustNode nsig') (extName "Within" lname) opts eo sp1' pos1'
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
      (sp', NodeSig n' gsigma', dg') <- anaSpec False True lg libEnv ln dg
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
      (sp', ns', dg') <- anaSpec addSyms optNodes newLG libEnv ln 
                                 dg newNSig qname opts eo
        (item asp) pos
      (ns, dg2) <- coerceNode lg dg' ns' qname l
      return (Qualified_spec lognm asp { item = sp' } pos, ns, dg2)
  Group asp pos -> do
      (sp', nsig', dg') <-
          anaSpecTop conser addSyms lg libEnv ln 
                     dg nsig name opts eo (item asp) rg
      return (Group (replaceAnnoted sp' asp) pos, nsig', dg')
  Spec_inst spname' afitargs mImp pos0 -> do -- trace ("\n\n**** ana spec inst *** " ++ show spname' ++ " afitargs:" ++ show afitargs ++ "nsig:" ++ show nsig) $ do
   spname <- expCurieR (globalAnnos dg) eo spname'
   let pos = if null afitargs then iriPos spname else pos0
   adjustPos pos $ case lookupGlobalEnvDG spname dg of
    Just (PatternEntry patSig@(PatternSig _local imp params vMap _body)) -> -- trace ("patSig:" ++ show patSig) $
     -- 1. solve afitargs using params and imp
     case (length afitargs, length params) of
      (la, lp) -> do
       if (la == lp) && la > 0 then do
         (afitargs', patSig'@(PatternSig _local _imp' _params' vMap' bodySig), dg', nsig', gm', subst) <- anaPatternInstArgs lg libEnv opts eo ln dg imp nsig name spname patSig afitargs
         -- let body' = getBody bodySig
         (Logic cl) <- lookupCurrentLogic "anaGmaps" lg
         (dg2, lastParamAndNewNodes, spB) <- trace ("calling instMacro on "  ++ show spname' ++ "[" ++ show afitargs ++ "] subst:" ++ show subst) $ 
                       instantiateMacro lg libEnv opts eo ln dg' imp (JustNode nsig') name spname subst vMap' gm' bodySig
         (dgI, allPrevDefs) <- unionNodes lg dg2 (makeName $ mkIRI "TESTNAME") $ nub lastParamAndNewNodes
         --the body should extend the last argument
         (sp', nsig'', dg3) <-  trace ("spB:" ++ show spB) $ 
                                anaSpecTop conser addSyms lg libEnv ln dgI (JustNode allPrevDefs) (makeName $ addSuffixToIRI "_source" $ getName name) opts eo (item spB) nullRange
                                -- TODO: nsig' should be the node of instantiateMacro!!!
         --incl <- ginclusion lg (getSig nsig') (getSig nsig'')
         --let dg3 = insLink dg'' incl globalDef SeeTarget (getNode nsig') (getNode nsig'')
         -- trace ("sp':" ++ show sp' ++ " nsig'':" ++ show nsig'' ++ "dg3:"++ show (labEdges $ dgBody dg3)) $ 
         return (Spec_inst spname' afitargs' mImp pos0, nsig'', dg3) -- was nsig''
        else if la == 0 then error "arguments missing in instantiation"
             else if lp == 0 then error "pattern without arguments"
                  else error "mismatch in length of arguments" 
     -- 2. generate fitting morphisms and theorem links from the params to the nodes of fitargs
     -- 3. substitute vars in body using the fitting morphisms -> a structured DOL spec, Body
     --    here is also where the missing arguments induce rejections in the body
     -- 4. replace the P[A1; ... An] with (Imp then A1) and ... and (Imp then An) then Body 
    Just (SpecEntry gs@(ExtGenSig (GenSig _ params _)
                        body@(NodeSig nB gsigmaB))) ->
     case (length afitargs, length params) of
      -- the case without parameters leads to a simpler dg
      (0, 0) -> case nsig of
          -- if the node shall not be named and the logic does not change,
        EmptyNode _ | isInternal name && optNodes -> do
          dg2 <- createConsLink DefLink conser lg dg nsig body SeeTarget
             -- then just return the body
          return (sp, body, dg2)
             -- otherwise, we need to create a new one
        _ -> do
           gsigma <- gsigUnionMaybe lg addSyms nsig gsigmaB
           let (fsig@(NodeSig node _), dg2) =
                 insGSig dg name (DGInst spname) gsigma
           incl <- -- trace ("gsigmaB:" ++ show gsigmaB ++ " gsigma:" ++ show gsigma) $  
                   ginclusion lg gsigmaB gsigma
           let dg3 = case nsig of
                 JustNode (NodeSig nI _) | nI == nB -> dg2
                 _ -> insLink dg2 incl globalDef (DGLinkMorph spname) nB node
           dg4 <- -- trace ("nsig:" ++ show nsig ++ " fsig:" ++ show fsig) $ 
                  createConsLink DefLink conser lg dg3 nsig fsig SeeTarget
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
      (sp1', ns', dg') <- anaSpec False True (setCurLogic (language_name lidD) lg)
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
          anaSpec addSyms optNodes lg libEnv ln 
                  udg (JustNode usig) name opts eo sp2 rg
      return (Data lD lP
                   (replaceAnnoted sp1' asp1)
                   (replaceAnnoted sp2' asp2)
                   pos, nsig3, udg3)
  Combination (Network cItems eItems _) pos -> adjustPos pos $ do
    let (cNodes', cEdges') = networkDiagram dg cItems eItems
    (ns, dg') <- insertColimitInGraph libEnv ln dg cNodes' cEdges' name
    return (sp, ns, dg')
  UnsolvedName x pos -> -- this should not happen, but when it does, solve as spec_inst
    anaSpecAux conser addSyms optNodes lg 
           libEnv ln dg nsig name opts eo (Spec_inst x [] Nothing pos) rg
  _ -> fail $ "in AnalysisStructured: " ++ show (prettyLG lg sp)


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

anaExtraction :: LogicGraph -> LibEnv -> LibName -> DGraph -> NodeSig -> NodeName -> Range ->
              EXTRACTION -> Result (NodeSig, DGraph)
anaExtraction lg libEnv ln dg nsig name rg (ExtractOrRemove b iris _) = if not b then
  fail "analysis of remove not implemented yet"
 else do
  let dg0 = markHiding libEnv dg
      n = getNode nsig
  if labelHasHiding $ labDG dg0 n then
    fail "cannot extract module from a non-flattenable OMS"
   else do
    let dgThm = computeDGraphTheories libEnv ln dg0
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

unionNodes :: LogicGraph -> DGraph -> NodeName -> [NodeSig] -> Result (DGraph, NodeSig)
unionNodes lg dg name nsigs = 
   case nsigs of
    [ns] -> return (dg, ns)
    _ -> do
      let nsigs' = reverse nsigs
      gbigSigma <- gsigManyUnion lg (map getSig nsigs')
      let (ns@(NodeSig node _), dg2) = insGSig dg name
                                       DGUnion gbigSigma
          insE dgl (NodeSig n gsigma) = do
                incl <- ginclusion lg gsigma gbigSigma
                return $ insLink dgl incl globalDef SeeTarget n node
      dg3 <- foldM insE dg2 nsigs'
      return (dg3, ns)
 
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
                  anaSpec addSyms True lg libEnv ln 
                          dg' nsig n1 opts eo sp' $ getRange sp'
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
                  anaSpec addSyms True lg libEnv ln dg' nsig n1 opts eo sp' $
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
             let dgThm = computeDGraphTheories libEnv ln dg
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

anaFiltering :: LogicGraph -> LibEnv -> LibName -> DGraph -> NodeSig -> NodeName-> FILTERING
   -> Result (NodeSig, DGraph)
anaFiltering lg libEnv ln dg nsig nname filtering = case filtering of
  FilterSymbolList selectOrReject (G_symb_items_list lidS sItems) _ ->
   if not selectOrReject then do
     let strs = concatMap (symb_items_name lidS) sItems
         dgThm = computeDGraphTheories libEnv ln dg
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

anaGmaps :: LogicGraph -> HetcatsOpts -> Range -> G_sign -> G_sign -> Maybe G_morphism
  -> [G_mapping] -> Result G_morphism
anaGmaps lg opts pos psig@(G_sign lidP sigmaP _) asig@(G_sign lidA sigmaA _) mgm
  gsis = adjustPos pos $ if isStructured opts
    then return $ mkG_morphism lidP $ ext_ide sigmaP
    else do 
      if null gsis then do -- trace ("gsis is null psig:" ++ show psig ++ " asig:" ++ show asig) $ do
        (G_sign lidP' sigmaP' _, _) <- gSigCoerce lg psig (Logic lidA)
        sigmaA' <- coerceSign lidA lidP' "anaGmaps" sigmaA
        prevMap <- case mgm of 
                   Nothing -> return Map.empty
                   Just prevGMor ->
                    case prevGMor of 
                      G_morphism prevLid prevMor _ -> do
                        prevMor' <- coerceMorphism prevLid lidP' "anaGmaps:coerceMorphism" prevMor
                        let symMap = symmap_of lidP' prevMor'
                        return $ Map.mapKeys (symbol_to_raw lidP') $ Map.map (symbol_to_raw lidP') symMap 
        fmap (mkG_morphism lidP') $
          ext_induced_from_to_morphism lidP' prevMap sigmaP' sigmaA'
      else do
      cl <- lookupCurrentLogic "anaGmaps" lg
      G_symb_map_items_list lid sis <- homogenizeGM cl gsis
      (G_sign lidP' sigmaP'' _, _) <- gSigCoerce lg psig (Logic lid)
      sigmaP' <- coerceSign lidP' lid "anaGmaps1" sigmaP''
      (G_sign lidA' sigmaA'' _, _) <- gSigCoerce lg asig (Logic lid)
      sigmaA' <- coerceSign lidA' lid "anaGmaps2" sigmaA''
      rMap <- stat_symb_map_items lid (plainSign sigmaP')
        (Just $ plainSign sigmaA') sis
      prevMap <- case mgm of 
                   Nothing -> return Map.empty
                   Just prevGMor ->
                    case prevGMor of 
                      G_morphism prevLid prevMor _ -> do
                        prevMor' <- coerceMorphism prevLid lid "anaFitArg:coerceMorphism" prevMor
                        let symMap = symmap_of lid prevMor'
                        return $ Map.mapKeys (symbol_to_raw lid) $ Map.map (symbol_to_raw lid) symMap 
      let crtMap = if Map.intersection rMap prevMap == Map.empty 
                     then Map.union rMap prevMap
                     else error $ "trying to map previously mapped symbol:" ++ (show $ Map.intersection rMap prevMap) -- TODO: don't fail if the symbols are mapped in the same way                 
      fmap (mkG_morphism lid)
        $ ext_induced_from_to_morphism lid crtMap sigmaP' sigmaA'

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

-- TODO: analysis of fit args must be different for non-local patterns
-- the signature morphism will not expand the previous definitions
-- different argument in the call in spec_inst!!!! 

anaFitArg :: LogicGraph -> LibEnv -> LibName -> DGraph -> IRI -> MaybeNode
  -> NodeSig -> HetcatsOpts -> NodeName -> ExpOverrides 
  -> MaybeNode -> MaybeNode -> Maybe G_morphism -> FIT_ARG
  -> Result (FIT_ARG, DGraph, (G_morphism, NodeSig))
anaFitArg lg libEnv ln dg spname nsigI nsigP@(NodeSig nP gsigmaP) opts name eo csig prevSig mgm fv =
  let ga = globalAnnos dg in
  case fv of
  Fit_string s _ -> error $ "nyi for " ++ (show s)
  Fit_spec asp gsis pos -> do
   (sp', nsigA', dg0) <- -- trace ("calling ana spec:" ++ show asp ++ " nsigI:"++ show nsigI ++ "nsigP:" ++ show nsigP)$ 
                        anaSpec False True lg libEnv ln
                                dg nsigI name opts eo (item asp) pos
   -- if the context and the previous argument are both not EmptyNodes
   -- unite the argument, the context and the previous argument
   (nsigA, dg') <- 
      case (prevSig, csig) of
       (EmptyNode _, EmptyNode _) -> return (nsigA', dg0)
       _ -> do 
        let pN = case prevSig of
                  EmptyNode _ -> []
                  JustNode x -> [x]
            cN = case csig of 
                  EmptyNode _ -> []
                  JustNode x -> [x]
        gbigSigma <- gsigManyUnion lg $ map getSig $ 
                      pN ++ cN ++ [nsigA'] 
        let (uSig@(NodeSig unode _), dg1) = insGSig dg0 (extName "Union" name)
                                             DGUnion gbigSigma
            insE dgl (NodeSig n gs) = do
             incl <- ginclusion lg gs gbigSigma
             -- trace ("inclusion for:" ++ show gs ++ " is " ++ show incl ) $ 
             return $ insLink dgl incl globalDef SeeTarget n unode
        dg2 <- foldM insE dg1 $ pN ++ cN ++ [nsigA']
        return (uSig, dg2)
   (_, Comorphism aid) <- -- trace ("nsigA:" ++ show nsigA) $ 
       logicUnion lg (getNodeLogic nsigP) (getNodeLogic nsigA)
   let tl = Logic $ targetLogic aid
   (nsigA''@(NodeSig nA' gsigA'), dg'') <- coerceNode lg dg' nsigA name tl
   (gsigmaP', pmor) <- gSigCoerce lg gsigmaP tl
   tmor <- gEmbedComorphism pmor gsigmaP
   gmor <- -- trace ("gsis:" ++ show gsis ++ " gsigmaP':" ++ show gsigmaP' ++ " gsigA':" ++ show gsigA' ++ " mgm:" ++ show mgm) $ 
           anaGmaps lg opts pos gsigmaP' gsigA' mgm gsis
   eGmor <- comp tmor $ gEmbed gmor
   return ( Fit_spec (replaceAnnoted sp' asp) gsis pos
          , if nP == nA' && isInclusion eGmor then dg'' else
                insLink dg'' eGmor globalThm
                   (DGLinkInst spname $ Fitted gsis) nP nA'
          , (gmor, nsigA''))
  Fit_ctx (G_symbol slid ssym) (G_symbol tlid tsym) pos -> do
    let tRSym = symbol_to_raw slid $ coerceSymbol tlid slid tsym
        sRSym = symbol_to_raw slid ssym
    case csig of 
      EmptyNode _ -> error "anaFitArg: empty context" -- should never happen
      JustNode c -> do 
        (nsigA@(NodeSig na sigA), dg') <- 
                       case (prevSig, nsigI) of
                         (EmptyNode _, EmptyNode _) -> return (c, dg)
                         (EmptyNode _, JustNode i) -> do -- first argument is an abbreviation, unite i and c
                           gUnionSig <- gsigManyUnion lg $ map getSig [c, i]
                           let (usig@(NodeSig unode _), dg0) =
                                insGSig dg (extName "Union" name) DGUnion gUnionSig
                               insE dgl (NodeSig n gs) = do
                                 incl <- ginclusion lg gs gUnionSig
                                 return $ insLink dgl incl globalDef SeeTarget n unode
                           dg1 <- foldM insE dg0 [c, i]
                           return (usig, dg1)
                         (JustNode x, _) -> do -- isig should be already in prevSig, don't add another link
                           gUnionSig <- gsigManyUnion lg $ map getSig [c, x]
                           let (usig@(NodeSig unode _), dg0) =
                                insGSig dg (extName "Union" name) DGUnion gUnionSig
                               insE dgl (NodeSig n gs) = do
                                 incl <- ginclusion lg gs gUnionSig
                                 return $ insLink dgl incl globalDef SeeTarget n unode
                           dg1 <- foldM insE dg0 [c, x]
                           return (usig, dg1)
        ssig <- case gsigmaP of 
                 G_sign plid psig _ -> coerceSign plid slid "anaFitArg:coercePlainSign" psig
        tsig <- case sigA of 
                 G_sign plid psig _ -> coerceSign plid slid "anaFitArg:coercePlainSign" psig
        prevMap <- case mgm of 
                   Nothing -> return Map.empty
                   Just prevGMor ->
                    case prevGMor of 
                      G_morphism prevLid prevMor _ -> do
                        prevMor' <- coerceMorphism prevLid slid "anaFitArg:coerceMorphism" prevMor
                        let symMap = symmap_of slid prevMor'
                            isysms = case nsigI of 
                                      EmptyNode _ -> Set.empty
                                      JustNode inode -> case getSig inode of
                                                         G_sign ilid (ExtSign isig _) _ -> Set.map (\x -> coerceSymbol ilid slid x) $ symset_of ilid isig 
                        -- trace ("***isysms:" ++ show isysms) $ 
                        return $ Map.mapKeys (symbol_to_raw slid) $ Map.map (symbol_to_raw slid) $ 
                                 Map.filterWithKey (\x _ -> not $ Set.member x isysms) symMap  -- TODO: dont map the symbols in imports!
        let crtMapAux = Map.fromList [(sRSym, tRSym)]
            crtMap = if Map.intersection crtMapAux prevMap == Map.empty 
                     then Map.union prevMap crtMapAux
                     else error $ "trying to map previously mapped symbol:" ++ (show $ Map.intersection crtMapAux prevMap) -- TODO: don't fail if the symbols are mapped in the same way                 
        mor <-  -- trace ("\n***********************\ninduced:" ++ show crtMap ++ " ssig:" ++ show ssig ++ " tsig:" ++ show tsig) $ 
               induced_from_to_morphism slid crtMap ssig tsig
        let gmor = mkG_morphism slid mor
            dg'' = insLink dg' (gEmbed gmor) globalThm (DGLinkInstArg spname) nP na
        return (fv, dg'', (gmor, nsigA))   
  Fit_new (G_symbol slid ssym) (G_symbol tlid tsym) pos -> do
   -- trace ("_________________________mgm in fit_new:" ++ show mgm ++ "\n_________nsigP:" ++ show nsigP ++ "\n_____prevSig:" ++ show prevSig) $ do
    let tRSym = symbol_to_raw slid $ coerceSymbol tlid slid tsym
        sRSym = symbol_to_raw slid ssym
    sigA <- add_symb_to_sign tlid (empty_signature tlid) tsym
    let extSigA = ExtSign sigA (Set.singleton tsym)
        (asig@(NodeSig a gA), dg0) = insGSig dg (extName "Actual" name) (DGInst spname) $ G_sign tlid extSigA startSigId
        uNodes = (case csig of 
                   EmptyNode _ -> []
                   JustNode x -> [x]) ++
                 (case prevSig of
                   EmptyNode _ -> case nsigI of
                                    EmptyNode _ -> []
                                    JustNode x -> [x]
                   JustNode x -> [x])
    gUnionSig <- -- trace ("asig:" ++ show asig) $ 
                 gsigManyUnion lg $ [gA] ++ map getSig uNodes
    let (usig@(NodeSig unode _), dg1) =
               insGSig dg0 (extName "Union" name) DGUnion gUnionSig
        insE dgl (NodeSig n gs) = do
          incl <-  -- trace ("\n=============\ninclusion from " ++ show gs ++ "\n\nto " ++ show gUnionSig) $ 
                  ginclusion lg gs gUnionSig
          return $ insLink dgl incl globalDef SeeTarget n unode
    dg2 <- foldM insE dg1 $ asig:uNodes
    ssig <- case gsigmaP of 
                 G_sign plid psig _ -> coerceSign plid slid "anaFitArg:coercePlainSign" psig
    tsig <- case gUnionSig of 
                 G_sign plid psig _ -> coerceSign plid slid "anaFitArg:coercePlainSign" psig
    prevMap <- -- trace ("\n=============\nmgm:"++ show mgm ++ "\nssig:"++show ssig ++ "\ntsig:"++ show tsig) $ 
               case mgm of 
                   Nothing -> return Map.empty
                   Just prevGMor ->
                    case prevGMor of 
                      G_morphism prevLid prevMor _ -> do
                        prevMor' <- coerceMorphism prevLid slid "anaFitArg:coerceMorphism" prevMor
                        let symMap = symmap_of slid prevMor'
                            isysms = case nsigI of 
                                      EmptyNode _ -> Set.empty
                                      JustNode inode -> case getSig inode of
                                                         G_sign ilid (ExtSign isig _) _ -> Set.map (\x -> coerceSymbol ilid slid x) $ symset_of ilid isig
                        -- trace ("symMap:" ++ show symMap) $ 
                        return $ Map.mapKeys (symbol_to_raw slid) $ Map.map (symbol_to_raw slid) $ 
                                  Map.filterWithKey (\x _ -> not $ Set.member x isysms) symMap 
    let crtMapAux = Map.fromList [(sRSym, tRSym)]
        crtMap = if Map.intersection crtMapAux prevMap == Map.empty 
                  then Map.union prevMap crtMapAux
                  else -- don't fail if the symbols are mapped in the same way   
                    let intersMapKeys = Map.keys $ Map.intersection crtMapAux prevMap
                        allMappedSameWay = foldl (\b k -> let v1 = Map.findWithDefault (error "not in crt") k crtMapAux
                                                              v2 = Map.findWithDefault (error "not in prev") k prevMap
                                                          in (v1 == v2) && b ) True intersMapKeys
                    in if allMappedSameWay then  Map.union prevMap crtMapAux 
                       else 
                         error $ "trying to map previously mapped symbol:" ++ (show $ Map.intersection crtMapAux prevMap)               
    mor <- -- trace ("\n=============\nssig:"++ show ssig ++ "\n tsig:" ++ show tsig ++ "\n prevMap:" ++ show prevMap ) $ 
           induced_from_to_morphism slid crtMap ssig tsig
    let gmor = mkG_morphism slid mor
        dg'' = -- trace ("gmor after induced:" ++ show gmor) $ 
               insLink dg2 (gEmbed gmor) globalThm (DGLinkInstArg spname) nP unode
    return (fv, dg'', (gmor, usig))                     
    -- trace ("sigA:" ++ show usig) $ error "fit_new nyi" 
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
    (fa', dg', arg) <- anaFitArg lg libEnv ln dg1 spname imps nsig' opts n1 eo imps imps Nothing fa -- TODO: this is wrong!
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

anaPatternInstArgs :: LogicGraph -> LibEnv -> HetcatsOpts -> ExpOverrides -> LibName -> DGraph
  -> MaybeNode -> MaybeNode 
  -> NodeName -> IRI -> PatternSig -> [Annoted FIT_ARG]
  -> Result ([Annoted FIT_ARG], PatternSig, DGraph, NodeSig, Maybe G_morphism, GSubst)
anaPatternInstArgs lg libEnv opts eo ln dg isig csig name spname psig@(PatternSig local imps params vMap body) afitargs = do
   l@(Logic crtLid) <- lookupCurrentLogic "anaPatternInstArgs" lg
   -- before the arguments are analysed, we have to go through their list
   -- and check if any Missing_arg nullRange appears
   -- if it does, check that it occurs on the position of an optional parameter
   -- if it doesn't give an error
   -- else construct a new PatternSig that keeps only the present parameters and has a new body
   -- add it temporarily to globalEnv and proceed, then restore the old definition
   let zipped = zip params afitargs
   idImps <- case isig of
                  EmptyNode _ -> return Nothing
                  JustNode (NodeSig _ gisig) -> 
                    case gisig of
                      G_sign ilid (ExtSign esig _) _ -> do  
                         esig' <- coercePlainSign ilid crtLid "coerceSign in anaPatternInstArgs" esig
                         let emor = ide esig'
                         return $ Just $ G_morphism crtLid emor startMorId
   (missingNodes, zipped', _, dgP) <- 
              foldM (\(ns, ls, lastParam, dg0) (p,a) -> 
                                   case item a of 
                                     Missing_arg _ -> -- trace ("p:" ++ show p) $ 
                                       case p of
                                        SingleParamInfo True parSig -> return (ns ++ [parSig], ls, lastParam, dg0)
                                        _ -> fail $ "unexpected missing argument for non-optional parameter:" ++ show p 
                                     _ -> do --TODO: remove missing symbols only! if there were missing arguments before!
                                         (dg1, newParam, p') <- removeMissingSymbolsParam lg libEnv ln dg0 lastParam ns p
                                         -- don't return p, add a new node in the DG extending the previous argument that removes all symbols and sentences from dgn_theory p
                                         -- that include symbols from ns
                                         return $ (ns, ls ++ [(p',a)], newParam, dg1) ) 
                    ([], [], isig, dg) zipped
   (afitargs', dg', nsig', subst, gm') <- --trace ("zipped':" ++ (show $ map (\x -> case x of 
                                          --                                    SingleParamInfo _ xs -> dgn_theory $ labDG dgP $ getNode xs
                                            --                                  _ -> error "nyi") $  map fst zipped')) $ 
         foldM (\(args0, dg0, nsig0, subst0, gm0) (par0, arg0) -> do
                   (arg1, dg1, nsig1, subst1, gm1) <- -- trace ("subst0:" ++ show subst0) $ 
                                                 anaPatternInstArg lg libEnv opts eo ln dg0 isig csig nsig0 name spname subst0 gm0 par0 arg0
                   let nsig2 = case nsig1 of -- this is a trick to make lists work!
                                EmptyNode _ -> nsig0
                                _ -> nsig1
                   return (args0 ++ [arg1], dg1, nsig2, subst1, gm1))
               ([], dgP, EmptyNode l, Map.empty, idImps) $ zipped'
   let lastParamSig = case nsig' of
                           EmptyNode _ -> error "should not happen"
                           JustNode x -> x
   case missingNodes of
    [] -> return (afitargs', psig, dg', lastParamSig, gm', subst)
    _ -> do
     (vMap', body') <- removeMissingOptionalSymbols lg libEnv ln missingNodes vMap body 
     return (afitargs', PatternSig local imps (map fst zipped') vMap' body', dg', lastParamSig, gm', subst)

removeMissingSymbolsParam :: LogicGraph -> LibEnv -> LibName -> DGraph -> MaybeNode -> [NodeSig] -> PatternParamInfo -> Result (DGraph, MaybeNode, PatternParamInfo)
removeMissingSymbolsParam lg libEnv ln dg lastParam ns p = do
 case p of
  SingleParamInfo optFlag psig -> do
   let gth = dgn_theory $ labDG dg $ getNode psig
   case gth of
    G_theory lid syn (ExtSign sig nIsyms) sid sens tid -> do
      let delSyms = concatMap (\n -> let gs = getSig n in 
                                     case gs of
                                      G_sign slid (ExtSign _ syms) _ -> map (\x -> coerceSymbol slid lid x) $ Set.toList syms ) ns
      mor <- cogenerated_sign lid (Set.fromList delSyms) sig
      let sens' = OMap.fromList $ filter (\(_, y) -> Set.null $ Set.intersection (Set.fromList delSyms) $ Set.fromList $ symsOfSen lid sig $ sentence y) $ OMap.toList sens
          gth' = G_theory lid syn (ExtSign (dom mor) nIsyms) sid sens' tid
          newNode = newInfoNodeLab (makeName $ mkIRI "NewParam")
                               (newNodeInfo DGFormalParams) gth'
          newNodeNr = getNewNodeDG dg
          dg' = changesDGH dg [InsertNode (newNodeNr, newNode)]
          newParNode = NodeSig newNodeNr $ signOf gth'
      dg'' <- case lastParam of
                EmptyNode _ -> return dg'
                JustNode prevSig -> do 
                 incl <- ginclusion lg (getSig prevSig) $ signOf gth'
                 return $ insLink dg' incl
                            globalDef DGLinkImports (getNode prevSig) newNodeNr
      -- trace ("newParNode:" ++ show newParNode) $ 
      return (dg'', JustNode newParNode, SingleParamInfo optFlag newParNode)
  _ -> return (dg, lastParam, p) -- don't remove from lists yet

removeMissingOptionalSymbols :: LogicGraph -> LibEnv -> LibName -> [NodeSig] -> PatternVarMap -> LocalOrSpecSig
                             -> Result (PatternVarMap, LocalOrSpecSig)
removeMissingOptionalSymbols lg libEnv ln missingNodes vMap bodySig = do
 Logic lid <- lookupCurrentLogic "removeMissingOptionalSymbols" lg
 let delSyms = concatMap (\n -> let gs = getSig n in 
                                     case gs of
                                      G_sign slid (ExtSign _ syms) _ -> map (\x -> coerceSymbol slid lid x) $ Set.toList syms ) missingNodes
     removeSymbolsFromSpec sp = 
      case sp of 
       Basic_spec (G_basic_spec blid bsp) rg -> do
        let delSyms' = map (coerceSymbol lid blid) delSyms
        bsp' <- delete_symbols_macro blid (Set.fromList delSyms') bsp
        return $ Basic_spec (G_basic_spec blid bsp') rg
       _ -> error "only basic specs for now"
     vMap' = foldl (\f s -> Map.delete ( idToIRI $ sym_name lid s) f) vMap delSyms
 bodySig' <- case getBody bodySig of
           Spec_pattern asp -> do
             sp' <- removeSymbolsFromSpec $ item asp
             return $ SpecSig $ Spec_pattern $ asp{item = sp'}
           Local_pattern locals asp -> error "2" 
 -- trace ("body:" ++ show bodySig ++" body':"++ show bodySig') $ 
 return (vMap', bodySig')

anaPatternInstArg :: LogicGraph -> LibEnv -> HetcatsOpts -> ExpOverrides -> LibName -> DGraph
  -> MaybeNode -> MaybeNode -> MaybeNode
  -> NodeName -> IRI -> GSubst -> Maybe G_morphism -> PatternParamInfo -> Annoted FIT_ARG
  -> Result (Annoted FIT_ARG, DGraph, MaybeNode, GSubst, Maybe G_morphism)
anaPatternInstArg lg libEnv opts eo ln dg0 isig csig prevSig name spname subst0 mgm0 par0 arg0 = -- trace ("***** arg0 in argInst:" ++ show arg0 ++ " subst0:" ++ show subst0 ++ " par0 in argInst:" ++ show par0) $ 
 case item arg0 of 
  Fit_string s r -> 
   case par0 of
    StringParamInfo i -> do
      l <- lookupCurrentLogic "fit string" lg
      return (arg0, dg0, EmptyNode l, Map.insert (i, "String") (PlainVal s) subst0, mgm0)
    _ -> error $ "parameter mismatch, got a string when expecting a " ++ show par0
  Fit_spec asp gm r -> 
   case item asp of
    UnsolvedName i rg -> -- trace ("solving an unsolved name in inst arg:" ++ show i) $ 
     -- TODO: here we must also pass the parameter, so we can check its symbols
     -- 1. if i is the name of a spec entry in globalEnv
     --    solve to Spec_inst i [] Nothing nullRange
     -- and the substitution should be inducedFrom<nodeOfParam>To<nodeOfI>
     if i `elem` Map.keys (globalEnv dg0) then
      case (par0, Map.findWithDefault (error "anaPatternInstArg: already checked") i (globalEnv dg0)) of
       (SingleParamInfo b pSig, SpecEntry eGSig) -> do
         let arg1 = Fit_spec (emptyAnno $ Spec_inst i [] Nothing nullRange) [] nullRange
         l <- lookupCurrentLogic "fit string" lg
         -- empty node was isig in next line
         (arg2, dg1, (gmor, nsigA)) <- anaFitArg lg libEnv ln dg0 spname isig pSig opts (extName "Arg" name) eo csig prevSig mgm0 arg1
         case gmor of
          G_morphism lid mor _ -> do -- trace ("arg2:"++ show arg2 ++ " gmor:" ++ show gmor ++ " nsigA:"++ show nsigA) $ do
            let smap = symmap_of lid mor
                isyms = case isig of 
                                EmptyNode _ -> Set.empty
                                JustNode inode -> case getSig inode of 
                                               G_sign ilid (ExtSign sigI _) _ -> Set.map (coerceSymbol ilid lid) $ symset_of ilid sigI
                subst1 = foldl (\f (ssym, tsym) -> 
                                     let (sn, sk) = (idToIRI $ sym_name lid ssym, symKind lid ssym)
                                         tn = idToIRI $ sym_name lid tsym
                                     in Map.insert (sn, sk) (PlainVal tn) f) subst0 $ filter (\(x,_) -> not $ Set.member x isyms) $ Map.toList smap
            -- TODO: any compatibility checks must be done here
            return (arg0{item=arg2}, dg1, JustNode nsigA, subst1, Just gmor)
       _ -> error $ "argument mismatch in instantiation. parameter: " ++ show par0 ++ "\n argument: " ++ show arg0  
     else do
      case par0 of
       SingleParamInfo b pNSig ->  
        case getSig pNSig of
         G_sign lid (ExtSign _ newDecls) _ -> 
           case Set.toList newDecls of
            [sym] -> do
              let noCtxOrNoMatch = do 
                   let arg1 = Fit_new (G_symbol lid sym) (G_symbol lid (rename_symbol lid sym (stringToId $ show $ instParamName subst0 i))) nullRange
                   (arg2, dg1, (gmor, nsigA)) <- -- trace ("================ calling anaFitArg. prevSig:" ++ show prevSig ++ " arg1:" ++ show arg1) $ 
                                                 anaFitArg lg libEnv ln dg0 spname isig pNSig opts (extName "Arg" name) eo csig prevSig mgm0 arg1
                                                 -- try: only extend previous morphism if the pattern is local!
                   case gmor of
                    G_morphism glid mor _ -> do
                      let smap = symmap_of glid mor
                          isyms = case isig of 
                                EmptyNode _ -> Set.empty
                                JustNode inode -> case getSig inode of 
                                               G_sign ilid (ExtSign sigI _) _ -> Set.map (coerceSymbol ilid glid) $ symset_of ilid sigI
                          subst1 = foldl (\f (ssym, tsym) -> 
                                     let (sn, sk) = (idToIRI $ sym_name glid ssym, symKind glid ssym)
                                         tn = idToIRI $ sym_name glid tsym
                                     in Map.insert (sn, sk) (PlainVal tn) f) 
                                   subst0 $ filter (\(x,_) -> not $ Set.member x isyms) $ Map.toList smap
                      -- TODO: any compatibility checks must be done here
                      return (arg0{item=arg2}, dg1, JustNode nsigA, subst1, Just gmor)
              case csig of
               EmptyNode _ -> noCtxOrNoMatch
               JustNode c -> 
                case getSig c of
                 G_sign lid1 (ExtSign ctx _) _ -> do
                  let ctxSyms = filter (\csym -> ((idToIRI $ sym_name lid1 csym) == i) && (symKind lid1 csym == symKind lid sym)) $ Set.toList $ symset_of lid1 ctx
                  case ctxSyms of
                    [] -> trace "err2" $ 
                          noCtxOrNoMatch
                    [ctxSym] -> trace "symbol in ctx" $ do
                        let arg1 = Fit_ctx (G_symbol lid sym) (G_symbol lid1 ctxSym) nullRange
                        (arg2, dg1, (gmor, nsigA)) <- anaFitArg lg libEnv ln dg0 spname isig pNSig 
                                                                                               opts (extName "Arg" name) eo csig 
                                                                                               prevSig mgm0 arg1
                        case gmor of
                          G_morphism glid mor _ -> do
                            let smap = symmap_of glid mor
                                isyms = case isig of 
                                         EmptyNode _ -> Set.empty
                                         JustNode inode -> case getSig inode of 
                                                        G_sign ilid (ExtSign sigI _) _ -> 
                                                         Set.map (coerceSymbol ilid glid) $ symset_of ilid sigI
                                subst1 = foldl (\f (ssym, tsym) -> 
                                            let (sn, sk) = (idToIRI $ sym_name glid ssym, symKind glid ssym)
                                                tn = idToIRI $ sym_name glid tsym
                                            in Map.insert (sn, sk) (PlainVal tn) f)
                                          subst0 $ filter (\(x,_) -> not $ Set.member x isyms) $ Map.toList smap
                            -- TODO: any compatibility checks must be done here
                            trace ("++++++ computed subst1:"++ show subst1) $ return (arg0{item=arg2}, dg1, JustNode nsigA, subst1, Just gmor)
                    _ -> fail $ "multiple occurences of abbreviated name in the context:" ++ show ctxSyms
            _ -> fail "ambiguity in use of abbreviation notation, parameter has more than one symbol" 
       _ -> fail $ "abbreviation notation can be used only for single ontology arguments, not for lists: " ++ show i
     -- 2. if i is a symbol from the context (nsig)
     --    solve to context fit x |-> i
     -- and the substitution maps x to i
     -- where x is the unique symbol declared in the param
     -- 3. otherwise, i is a new symbol of same kind as x 
     -- and the substitution maps x to i
    OntoList aspecs -> do 
      -- 1. generate a temporary param for the template node of the param list
      --  SingleParamInfo False n where the signature of the head of the param list is JustNode n
      let (par1, tailName) = case par0 of
                  SingleParamInfo _ _ -> error $ "expecting single argument: " ++ show par0 ++ " but got a list: " ++ show aspecs
                  ListParamInfo _ _ (JustNode n) tn -> let x = case tn of
                                                                 Nothing -> nullIRI
                                                                 Just y -> y
                                                       in (SingleParamInfo False n, x) -- TODO: not safe for empty, do it right!!!!
                  _ -> error $ "instantiating empty list pattern:" ++ show par0 ++ " with non-empty argument:" ++ show aspecs
      -- 2. analyze each elem of aspecs as a single argument for this param 
      -- use anaPatternInstArg lg libEnv opts eo ln dg0 isig csig prevSig name spname subst0 mgm0 par0 arg0
      -- it returns the analysed arg, the dgraph, justnode node of argument, substitution, generated morphism
      -- but update prevSig name spname subst0 mgm0 par0 arg0; fold the dgs; store the nodes of args
      (aspecs', aNodes, subst1, dg1) <- 
         foldM (\(anaSpecs, specNodes, substI, aDg) crtSp -> do
                   (crtSp', aDg', argNode, aSubst, aMor) <- 
                      anaPatternInstArg lg libEnv opts eo ln
                                        aDg isig csig prevSig -- TODO: check that prevSig is fine here
                                        name spname -- TODO: give proper names
                                        subst0 mgm0 -- TODO: check that this is ok
                                        par1 $ 
                                        emptyAnno $ Fit_spec crtSp [] nullRange
                   return (anaSpecs ++ [crtSp'], 
                           specNodes ++ [argNode],
                           if substI == Map.empty then aSubst else substI, -- only interested in the first substitution
                           aDg')
               ) ([], [], Map.empty, dg0) aspecs 
      -- 3. unite the resulting nodes
      (dg2, argUnion) <- unionNodes lg dg1 (makeName $ mkIRI "UnionNode") $ concatMap (\aN -> case aN of 
                                                                      JustNode x -> [x]
                                                                      _ -> []) aNodes      
      -- 4. generate a substitution: subst of the first argument plus list variable to tail of analyzed args
      let subst2 = case aspecs' of
                    _:asps -> 
                       let (k, iriList) = foldl (\(_k0, iris0) as0 -> case item as0 of
                                                                       Fit_new gsym1 gsym2 _ -> 
                                                                        case gsym1 of
                                                                         G_symbol lid1 sym1 ->
                                                                          case gsym2 of
                                                                           G_symbol lid2 sym2 -> 
                                                                            let -- name1 = idToIRI $ sym_name lid1 sym1
                                                                                kind1 = symKind lid1 sym1
                                                                                name2 = idToIRI $ sym_name lid2 sym2 
                                                                            in (kind1, iris0 ++ [name2]) 
                                                                       Fit_ctx gsym1 gsym2 _ -> 
                                                                        case gsym1 of
                                                                         G_symbol lid1 sym1 ->
                                                                          case gsym2 of
                                                                           G_symbol lid2 sym2 -> 
                                                                            let -- name1 = idToIRI $ sym_name lid1 sym1
                                                                                kind1 = symKind lid1 sym1
                                                                                name2 = idToIRI $ sym_name lid2 sym2 
                                                                            in (kind1, iris0 ++ [name2]) 
                                                                       _ -> error "only fit new/ctx for now!"
                                                )
                                                                        
                                                  ("", []) asps
                       in Map.insert (tailName, "list") (ListVal k iriList) subst1
                                  
                    _ -> subst1
      return (arg0, dg2, JustNode argUnion, subst2, mgm0)
      -- 5. instantiate the body with the substitution and add a link from the united arguments to the body 
      -- this should happen elsewhere! 
    _ -> -- trace ("itm:" ++ (show $ item arg0) ) $ 
         error "only unsolved names for now"
  _ -> -- trace ("itm:" ++ (show $ item arg0)) $ 
       error "only fit_spec for now"

instantiateMacro :: LogicGraph -> LibEnv ->HetcatsOpts -> ExpOverrides -> LibName -> 
                    DGraph -> MaybeNode -> MaybeNode 
                    -> NodeName -> IRI -> GSubst -> PatternVarMap -> Maybe G_morphism -> LocalOrSpecSig -> Result (DGraph, [NodeSig], Annoted SPEC)
instantiateMacro lg libEnv opts eo ln dg imp nsig name spname subst vars mgmPrev macro = 
 --trace ("~~~~~~~~~~~~~~~~instantiateMacro:" ++ show macro ++ "\nsubst:" ++ show subst ++
 --       "\nnsig:" ++ show nsig ++ "\nimp:"++ show imp ++ "\nmgmPrev:"++ show mgmPrev ++ "\nvars:" ++ show vars) $
 {- (Logic lid)  <- lookupCurrentLogic "macro" lg
 let th = (empty_signature lid, [])
     bsp = case convertTheory lid of
             Just f -> f th
             _ -> error "cannot convert theory"
 return (dg, emptyAnno $ Basic_spec (G_basic_spec lid bsp) nullRange) -}
 case macro of
   LocalSig localVarMaps (Local_pattern _ localBody) -> do
    let gEnv' = foldl (\g (n, s) -> Map.insert n (PatternEntry s) g) (globalEnv dg) $ Map.toList localVarMaps
        dg' = dg {globalEnv = gEnv'}
    instantiateMacro lg libEnv opts eo ln dg' imp nsig name spname subst vars mgmPrev (SpecSig $ Spec_pattern localBody) -- TODO: will this be enough?
    -- trace ("known:" ++ show (Map.keys gEnv')) $ error "local patterns nyi"
   SpecSig (Spec_pattern asp) ->
    instMacroAux lg libEnv opts eo ln dg imp nsig name spname subst vars mgmPrev asp
   _ -> fail $ "illegal pattern signature:" ++ show macro


instMacroAux :: LogicGraph -> LibEnv ->HetcatsOpts -> ExpOverrides -> LibName -> 
                DGraph -> MaybeNode -> MaybeNode 
                -> NodeName -> IRI -> GSubst -> PatternVarMap -> Maybe G_morphism
                -> Annoted SPEC -> Result (DGraph, [NodeSig], Annoted SPEC)
instMacroAux lg libEnv opts eo ln crtDG imp crtNSig name spname crtSubst vars crtGM asp0 =  -- trace ("+++++ instMacroAux for " ++ show asp0) $
      case item asp0 of
       Basic_spec gbsp rg -> 
        case gbsp of
         G_basic_spec lid bsp -> do 
           bsp'<- instantiate_macro lid vars crtSubst bsp
           let lastNode = case crtNSig of
                            JustNode x -> x
                            _ -> error "no last param of a pattern, should not happend"
           -- trace ("bsp':" ++ show bsp') $ 
           return (crtDG, [lastNode], asp0{item = Basic_spec (G_basic_spec lid bsp') rg})
       Group asp1 rg -> do 
         (dg2, ns2, asp2) <- instMacroAux lg libEnv opts eo ln crtDG imp crtNSig name spname crtSubst vars crtGM asp1
         return (dg2, ns2, asp0{item = Group asp2 rg}) 
       Extension asps rg -> do
         (dg1, ns1, asps1) <- foldM (\(aDg, ns, as) a -> do 
                                  (dg', ns', a') <- instMacroAux lg libEnv opts eo ln aDg imp crtNSig name spname crtSubst vars crtGM a
                                  return (dg', ns ++ ns', as ++ [a'])  ) (crtDG, [], []) asps
         return (dg1, ns1, asp0{item = Extension asps1 rg})
       Union asps rg -> do
         (dg1, ns1, asps1)<- foldM (\(aDg, ns, as) a -> do 
                                  (dg',ns',a') <- instMacroAux lg libEnv opts eo ln aDg imp crtNSig name spname crtSubst vars crtGM a
                                  return (dg', ns ++ ns', as ++ [a'])  ) (crtDG, [], []) asps
         -- trace ("ns1:" ++ show ns1) $
         return (dg1, ns1, asp0{item = Union asps1 rg})
       Spec_inst sn afitargs _ _ -> trace ("\n\nspec_inst:" ++ show (item asp0)) $ 
                                    do -- here afitargs must be instantiated if they are variables!!!
        let snEntry = Map.findWithDefault (error $ "unknown pattern:" ++ show sn) sn $ globalEnv crtDG
        case snEntry of
         PatternEntry patSig@(PatternSig isLocal _ pParams pMap pBody) -> do
          l@(Logic crtLid) <- lookupCurrentLogic "anaPatternInstArgs" lg
          idImps <- case imp of
                     EmptyNode _ -> return Nothing
                     JustNode (NodeSig _ gisig) -> 
                       case gisig of
                        G_sign ilid (ExtSign esig _) _ -> do  
                          esig' <- coercePlainSign ilid crtLid "coerceSign in anaPatternInstArgs" esig
                          let emor = ide esig'
                          return $ Just $ G_morphism crtLid emor startMorId
          let solveVars aFitArg = 
               case item aFitArg of 
                 Fit_spec asp1 gm rg ->
                   case item asp1 of
                     UnsolvedName i _ -> 
                       if i == mkIRI "empty" then error "empty list as argument in instantiation of pattern nyi"
                       else ([], aFitArg)
                     NormalVariable i -> trace ("normal variable: " ++ show i ++ " crtSubst:" ++ show crtSubst ++ " vars:" ++ show vars ++ " pMap:" ++ show pMap) $
                       if i `elem` Map.keys vars then
                         let (b, k) = Map.findWithDefault (error "notPossible") i vars
                             val = Map.findWithDefault (error "variable not mapped") (i,k) crtSubst
                             valIRI = case val of
                                       PlainVal valiri -> valiri
                                       _ -> error "normal variable mapped to list"
                         in ([((i,k), (valIRI,k))], aFitArg{item = Fit_spec asp1{item= UnsolvedName valIRI nullRange} gm rg})
                       else 
                         case filter (\(x,_y) -> x == i) $ Map.keys crtSubst of
                               [(a, k)] -> 
                                 let 
                                  val = Map.findWithDefault (error "variable not mapped") (i,k) crtSubst
                                  valIRI = case val of
                                           PlainVal valiri -> valiri
                                           _ -> error "normal variable mapped to list"
                                 in ([((i,k), (valIRI,k))], aFitArg{item = Fit_spec asp1{item= UnsolvedName valIRI nullRange} gm rg})
                               _ -> error $ "unknown variable:" ++ show i ++ " in " ++ show vars
                     ListVariable i -> 
                       if i `elem` Map.keys vars then
                          let (b, k) = Map.findWithDefault (error "not possible") i vars
                          in if k == "list" then 
                              let val = Map.findWithDefault (error "variable not mapped") (i, k) crtSubst
                              in case val of 
                                   ListVal k' vals -> 
                                     let genItem = Fit_spec asp1{item= OntoList $ map (\v -> emptyAnno $ UnsolvedName v nullRange) vals} gm rg
                                     in if not $ null vals then ([], aFitArg{item = genItem}) -- error $ "genItem:" ++ show genItem
                                        else ([], aFitArg{item = Fit_spec asp1{item = UnsolvedName (mkIRI "empty") nullRange} gm rg})
                                             -- TODO: this does not suffice, we need to generate empty ontology here already!
                                   _ -> error $ "expected list argument but got single element"
                             else error $ "expected list but got " ++ k
                       else error $ "unknown list variable:" ++ show i
                     _ -> ([], aFitArg)
                 _ -> ([], aFitArg)
              solved = map solveVars afitargs
              afitargs0 = map snd solved
              aitems = filter (\x -> case item x of
                                      Fit_spec y _ _ -> case item y of 
                                                         UnsolvedName anIRI _ -> anIRI == mkIRI "empty"
                                                         _ -> False) afitargs0
              newVars = concatMap fst solved
              zipped = -- trace ("~~~~~~~~~~~~~newVars:"++ show newVars) $  
                       zip pParams afitargs0 -- TODO: allow optionals in locals!!!!
                                            -- TODO: if isLocal start with subst1 else start with empty subst? 
          (Logic lid)  <- lookupCurrentLogic "macro" lg
          let th = (empty_signature lid, [])
              bsp = case convertTheory lid of
                      Just f -> f th
                      _ -> error "cannot convert theory"
          if not $ null aitems then 
            instMacroAux lg libEnv opts eo ln crtDG imp crtNSig name spname crtSubst vars crtGM $ asp0{item = Basic_spec (G_basic_spec lid bsp) nullRange} -- error "empty list as argument, not yet done"
          else do 
           gmor' <- -- trace ("~~~~~~~~~~~~~zipped:"++ show zipped) $ 
                   if isLocal then 
                    case crtGM of
                     Nothing -> extendWithSubst l idImps newVars
                     Just agm -> return $ Just agm
                    else return idImps -- TODO: old variant: extendWithSubst l idImps newVars
           (afitargs', dg', nsig', subst', gm') <- -- trace ("~~~~~~~~~~~~~gmor':"++ show gmor') $
            foldM (\(args0, dg0, nsig0, subst0, gm0) (par0, arg0) -> do
                    (arg1, dg1, nsig1, subst1, gm1) <- -- strace ("subst0 in spec_inst:" ++ show subst0 ++ " nsig0:" ++ show nsig0) $ 
                      anaPatternInstArg lg libEnv opts eo ln dg0 
                                        imp (EmptyNode l) nsig0 -- TODO: context is always empty now
                                        name spname subst0 gm0 par0 arg0 
                    --trace ("$$$after analysis nsig':" ++ show nsig1 ++ " gm1:" ++ show gm1) $ 
                    return (args0 ++ [arg1], dg1, nsig1, subst1, gm1))
                 ([], crtDG, crtNSig, crtSubst, gmor') -- the last argument node should not be EmptyNode, but the target of gmor'. Try with nsig?
                 zipped
          -- (afitargs', patSig'@(PatternSig _local _imp' _params' vMap' bodySig), dg', nsig', subst') <- anaPatternInstArgs lg libEnv opts eo ln dg imp nsig name spname patSig afitargs
           --trace ("\n\n\n recursive call:" ++ show subst' ++ " nsig':" ++ show nsig') $ 
           instantiateMacro lg libEnv opts eo ln dg' imp nsig' name spname (Map.union subst' crtSubst) vars gm' pBody
            -- instantiateMacro lg libEnv opts eo ln dg' imp nsig' name spname (Map.union subst' subst) vars gm' pBody
          -- error $ "spec_inst:" ++ show sn ++ " args:" ++ show afitargs ++ " vars:" ++ show vars ++ " subst:" ++ show subst
          -- 1. afitargs should give raise to signature morphisms from the nodes of the params to the nodes of the args
          -- 2.                        and to a subst'
          -- 3. the body of sn should be instantiated in the new dgraph, with the union of subst and subst', with the varmap taken from the signature of sn in the globalEnv
         _ -> fail $ "expected a pattern entry but found:" ++ show snEntry
       _ -> fail $ "only non-structured bodies for now:" ++ show (globalEnv crtDG)
    -- instMacroAux dg nsig subst mgmPrev asp
   -- _ -> fail $ "illegal pattern signature:" ++ show macro

extendWithSubst :: AnyLogic -> Maybe G_morphism -> [((IRI, String),(IRI, String))] -> Result (Maybe G_morphism)
extendWithSubst (Logic l) mgm newVars = do
 case mgm of 
  Nothing -> return Nothing -- TODO: wrong, should still generate a morphism!
  Just gm ->
   case gm of
    G_morphism crtLid emor _ -> do
     let 
         ssyms = map (\(x,y) -> new_symbol crtLid x y) $ map fst newVars
         tsyms = map (\(x,y) -> new_symbol crtLid x y) $ map snd newVars 
         crtMap = Map.fromList $ map (\(x, y) -> (symbol_to_raw crtLid x, symbol_to_raw crtLid y)) $ zip ssyms tsyms
     ssig <- foldM (add_symb_to_sign crtLid) (empty_signature crtLid) ssyms
     tsig <- foldM (add_symb_to_sign crtLid) (empty_signature crtLid) tsyms
     mor <- induced_from_to_morphism crtLid crtMap (ExtSign ssig Set.empty) (ExtSign tsig Set.empty)
     rmor <- morphism_union crtLid emor mor
     -- trace ("ssig:" ++ show ssig ++ "tsig:" ++ show tsig ++ "rmor:" ++ show rmor) $ 
     return $ Just $ G_morphism crtLid rmor startMorId
 
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
