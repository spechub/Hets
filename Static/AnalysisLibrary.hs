{- |
Module      :  $Header$
Description :  static analysis of CASL specification libraries
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable(Logic)

Static analysis of CASL specification libraries
   Follows the verification semantics sketched in Chap. IV:6
   of the CASL Reference Manual.
-}

module Static.AnalysisLibrary
    ( anaLib
    , anaLibExt
    , ana_LIB_DEFN
    ) where

import Proofs.Automatic
import Logic.Logic
import Logic.Coerce
import Logic.Grothendieck
import Data.Graph.Inductive.Graph
import Syntax.AS_Structured
import Syntax.AS_Library
import Static.GTheory
import Static.DevGraph
import Static.AnalysisStructured
import Static.AnalysisArchitecture
import Comorphisms.LogicGraph
import Common.AS_Annotation hiding (isAxiom, isDef)
import Common.GlobalAnnotations
import Common.ConvertGlobalAnnos
import Common.AnalyseAnnos
import Common.Result
import Common.ResultT
import Common.Keywords
import Common.Id
import Common.DocUtils
import qualified Data.Map as Map
import Driver.Options
import Driver.ReadFn
import Driver.WriteFn
import Data.List
import Control.Monad
import Control.Monad.Trans
import System.Directory
import System.Time

-- | lookup an env or read and analyze a file
anaLib :: HetcatsOpts -> FilePath -> IO (Maybe (LIB_NAME, LibEnv))
anaLib opts fname = do
  fname' <- existsAnSource opts {intype = GuessIn} $ rmSuffix fname
  case fname' of
    Nothing -> anaLibExt opts fname emptyLibEnv
    Just file ->
        if isSuffixOf prfSuffix file then do
            putIfVerbose opts 0 $ "a matching source file for proof history '"
                             ++ file ++ "' not found."
            return Nothing
        else anaLibExt opts file emptyLibEnv

-- | read a file and extended the current library environment
anaLibExt :: HetcatsOpts -> FilePath -> LibEnv -> IO (Maybe (LIB_NAME, LibEnv))
anaLibExt opts file libEnv = do
    defl <- lookupLogic "logic from command line: "
                  (defLogic opts) logicGraph
    Result ds res <- runResultT $ anaLibFileOrGetEnv logicGraph defl opts
                     libEnv (fileToLibName opts file) file
    showDiags opts ds
    case res of
        Nothing -> return Nothing
        Just (ln, lenv) -> do
            let nEnv = if hasPrfOut opts then automatic ln lenv else lenv
                dg = lookupDGraph ln nEnv
                ga = globalAnnos dg
            writeSpecFiles opts file nEnv ga (ln, globalEnv dg)
            putIfVerbose opts 3 $ showGlobalDoc ga ga ""
            return $ Just (ln, nEnv)

-- | parsing and static analysis for files
-- Parameters: logic graph, default logic, file name
anaSourceFile :: LogicGraph -> AnyLogic -> HetcatsOpts -> LibEnv -> FilePath
              -> ResultT IO (LIB_NAME, LibEnv)
anaSourceFile lgraph defl opts libenv fname = ResultT $ do
  fname' <- existsAnSource opts {intype = GuessIn} fname
  case fname' of
    Nothing -> do
        return $ fail $ "a file for input '" ++ fname ++ "' not found."
    Just file ->
        if any (flip isSuffixOf file) [envSuffix, prfSuffix] then
            fail $ "a matching source file for '" ++ fname ++ "' not found."
        else do
        curDir <- getCurrentDirectory
        input <- readFile file
        mt <- getModificationTime file
        -- when switching to ghc 6.6.1 with System.FilePath use:
        -- combine curDir file
        let absolutePath = if "/" `isPrefixOf` file
                           then file
                           else curDir ++ '/':file
        putIfVerbose opts 2 $ "Reading file " ++ absolutePath
        runResultT $ anaString lgraph defl opts libenv input absolutePath mt

-- | parsing and static analysis for string (=contents of file)
-- Parameters: logic graph, default logic, contents of file, filename
anaString :: LogicGraph -> AnyLogic -> HetcatsOpts -> LibEnv -> String
          -> FilePath -> ClockTime -> ResultT IO (LIB_NAME, LibEnv)
anaString lgraph defl opts libenv input file mt =
  let Result ds mast = read_LIB_DEFN_M lgraph defl opts file input mt
  in case mast of
  Just ast@(Lib_defn ln _ _ ans) -> case analysis opts of
      Skip  -> do
          lift $ putIfVerbose opts 1 $
                  "Skipping static analysis of library " ++ show ln
          ga <- liftR $ addGlobalAnnos emptyGlobalAnnos ans
          case gui opts of
                      Only -> return ()
                      _ -> lift $ write_LIB_DEFN ga file opts ast
          liftR $ Result ds Nothing
      _ -> do
          let libstring = show $ getLIB_ID ln
          if libstring == libraryS then return ()
             else do
               if isSuffixOf libstring (rmSuffix file) then return () else
                   lift $ putIfVerbose opts 1 $
                       "### file name '" ++ file
                       ++ "' does not match library name '" ++
                          libstring ++ "'"
               lift $ putIfVerbose opts 1 $ "Analyzing library " ++ show ln
          (_,ld, _, lenv) <- ana_LIB_DEFN lgraph defl opts libenv ast
          case Map.lookup ln lenv of
              Nothing -> error $ "anaString: missing library: " ++ show ln
              Just dg -> lift $ do
                  case gui opts of
                      Only -> return ()
                      _ -> write_LIB_DEFN (globalAnnos dg) file opts ld
                  when (hasEnvOut opts)
                        (writeFileInfo opts ln file ld dg)
                  return (ln, lenv)
  Nothing -> liftR $ Result ds Nothing

-- lookup/read a library
anaLibFile :: LogicGraph -> AnyLogic -> HetcatsOpts -> LibEnv -> LIB_NAME
              -> ResultT IO (LIB_NAME, LibEnv)
anaLibFile lgraph defl opts libenv ln =
    let lnstr = show ln in case Map.lookup ln libenv of
    Just _ -> do
        analyzing opts $ "from " ++ lnstr
        return (ln, libenv)
    Nothing -> do
        putMessageIORes opts 1 $ "Downloading " ++ lnstr ++ " ..."
        res <- anaLibFileOrGetEnv lgraph defl
            (if recurse opts then opts else opts { outtypes = [] })
                  libenv ln $ libNameToFile opts ln
        putMessageIORes opts 1 $ "... loaded " ++ lnstr
        return res

-- lookup/read a library
anaLibFileOrGetEnv :: LogicGraph -> AnyLogic -> HetcatsOpts -> LibEnv
              -> LIB_NAME -> FilePath -> ResultT IO (LIB_NAME, LibEnv)
anaLibFileOrGetEnv lgraph defl opts libenv libname file = ResultT $ do
     let env_file = rmSuffix file ++ envSuffix
     recent_env_file <- checkRecentEnv opts env_file file
     if recent_env_file
        then do
             mgc <- readVerbose opts libname env_file
             case mgc of
                 Nothing -> runResultT $ do
                     lift $ putIfVerbose opts 1 $ "Deleting " ++ env_file
                     anaSourceFile lgraph defl opts libenv file
                 Just (ld, gc) -> do
                     write_LIB_DEFN (globalAnnos gc) file opts ld
                          -- get all DGRefs from DGraph
                     Result ds mEnv <- runResultT $ foldl
                         ( \ ioLibEnv labOfDG -> let node = snd labOfDG in
                               if isDGRef node then do
                                 let ln = dgn_libname node
                                 p_libEnv <- ioLibEnv
                                 if Map.member ln p_libEnv then
                                    return p_libEnv
                                    else fmap snd $ anaLibFile lgraph defl
                                         opts p_libEnv ln
                               else ioLibEnv)
                         (return $ Map.insert libname gc libenv)
                         $ labNodesDG gc
                     return $ Result ds $ fmap
                                ( \ rEnv -> (libname, rEnv)) mEnv
        else runResultT $ anaSourceFile lgraph defl opts libenv file

-- | analyze a LIB_DEFN
-- Parameters: logic graph, default logic, opts, library env, LIB_DEFN
-- call this function as follows:
-- do Result diags res <- runResultT (ana_LIB_DEFN ...)
--    mapM_ (putStrLn . show) diags
ana_LIB_DEFN :: LogicGraph -> AnyLogic -> HetcatsOpts
                 -> LibEnv -> LIB_DEFN
                 -> ResultT IO (LIB_NAME,LIB_DEFN,DGraph,LibEnv)

ana_LIB_DEFN lgraph defl opts libenv (Lib_defn ln alibItems pos ans) = do
  gannos <- showDiags1 opts $ liftR $ addGlobalAnnos emptyGlobalAnnos ans
  (libItems', dg, _, libenv') <-
     foldl ana (do
                  dg <- lift $ emptyDGwithMVar
                  return ([], dg { globalAnnos = gannos }, defl, libenv))
               (map item alibItems)

  return (ln,
          Lib_defn ln
                   (map (uncurry replaceAnnoted)
                        (zip (reverse libItems') alibItems))
                   pos
                   ans,
                   dg,
          Map.insert ln dg libenv')

  where
  ana res1 libItem = do
    (libItems',dg1,l1,libenv1) <- res1

    ResultT (do
      Result diags2 res <-
         runResultT $ ana_LIB_ITEM lgraph defl opts libenv1 dg1 l1 libItem
      runResultT $ showDiags1 opts (liftR (Result diags2 res))
      if outputToStdout opts then
         if hasErrors diags2 then
            fail "Stopped due to errors"
            else case res of
              Just (libItem',dg1',l1',libenv1') ->
                  return (return (libItem':libItems',dg1',l1',libenv1'))
              Nothing -> fail "Stopped. No result available"
         else do
              --result1 <- runResultT res1
              --let diags1 = diags result1
              if hasErrors diags2 then
                 runResultT $ liftR (Result (diags2) Nothing)
                 else case res of
                 Just (libItem',dg1',l1',libenv1') ->
                     return ((return (libItem':libItems',dg1',l1',libenv1'))
                             {diags = diags2})
                 Nothing -> return $ fail "Stopped. No result available"
             )

putMessageIORes :: HetcatsOpts -> Int -> String -> ResultT IO ()
putMessageIORes opts i msg =
   if outputToStdout opts
   then lift $ putIfVerbose opts i msg
   else liftR $ message () msg

analyzing :: HetcatsOpts -> String -> ResultT IO ()
analyzing opts msg = putMessageIORes opts 1 $ "Analyzing " ++ msg

alreadyDefined :: String -> String
alreadyDefined str = "Name " ++ str ++ " already defined"

-- | analyze a GENERICITY
ana_GENERICITY :: LogicGraph -> DGraph -> AnyLogic -> HetcatsOpts
                    -> NODE_NAME -> GENERICITY
                    -> Result (GENERICITY, GenericitySig, DGraph)
ana_GENERICITY lg dg l opts name
    gen@(Genericity params@(Params psps) imps@(Imported isps) pos) =
  case psps of
  [] -> do -- no parameter ...
    when (not (null isps))
      (plain_error () "Parameterless specifications must not have imports"
       pos)
    return (gen, (EmptyNode l, [], EmptyNode l), dg)
  _ -> do
   (imps',nsigI,dg') <- ana_IMPORTS lg dg l opts (extName "I" name) imps
   case psps of
     [asp] -> do -- one parameter ...
       (sp', nsigP, dg'') <- ana_SPEC lg dg' nsigI name opts (item asp)
       return (Genericity (Params [replaceAnnoted sp' asp]) imps' pos,
          (nsigI, [nsigP], JustNode nsigP), dg'')
     _ -> do -- ... and more parameters
       (params',nsigPs,dg'') <-
           ana_PARAMS lg dg' nsigI opts (inc name) params
       let adj = adjustPos pos
       gsigmaP <- adj $ gsigManyUnion lg (map getSig nsigPs)
       G_sign lidP gsigP indP <- return gsigmaP
       let node_contents = newNodeLab name DGFormalParams
             $ noSensGTheory lidP gsigP indP
           node = getNewNodeDG dg''
           dg''' = insNodeDG (node,node_contents) dg''
           inslink dgres (NodeSig n sigma) = do
             dgl <- dgres
             incl <- adj $ ginclusion lg sigma gsigmaP
             return (insLEdgeNubDG (n,node,DGLink
                    { dgl_morphism = incl
                    , dgl_type = GlobalDef
                    , dgl_origin = DGFormalParams
                    , dgl_id = defaultEdgeID
                    }) dgl)
       dg4 <- foldl inslink (return dg''') nsigPs
       return (Genericity params' imps' pos,
          (nsigI, nsigPs, JustNode $ NodeSig node gsigmaP), dg4)

ana_PARAMS :: LogicGraph -> DGraph -> MaybeNode
           -> HetcatsOpts -> NODE_NAME -> PARAMS
           -> Result (PARAMS, [NodeSig], DGraph)
ana_PARAMS lg dg nsigI opts name (Params asps) = do
  (sps',pars,dg',_) <- foldl ana (return ([], [], dg, name))
                       $ map item asps
  return (Params (map (uncurry replaceAnnoted)
                      (zip (reverse sps') asps)),
          reverse pars, dg')
  where
  ana res sp = do
    (sps',pars,dg1,n) <- res
    (sp',par,dg') <- ana_SPEC lg dg1 nsigI n opts sp
    return (sp':sps',par:pars,dg',inc n)

ana_IMPORTS ::  LogicGraph -> DGraph -> AnyLogic -> HetcatsOpts
                -> NODE_NAME -> IMPORTED
                -> Result (IMPORTED, MaybeNode, DGraph)
ana_IMPORTS lg dg l opts name imps@(Imported asps) = case asps of
  [] -> return (imps, EmptyNode l, dg)
  _ -> do
      let sp = Union asps nullRange
      (Union asps' _, nsig', dg') <-
          ana_SPEC lg dg (EmptyNode l) name opts sp
      return (Imported asps', JustNode nsig', dg')
   -- ??? emptyExplicit stuff needs to be added here

-- | analyse a LIB_ITEM
ana_LIB_ITEM :: LogicGraph -> AnyLogic -> HetcatsOpts
                 -> LibEnv -> DGraph -> AnyLogic
                 -> LIB_ITEM
                 -> ResultT IO (LIB_ITEM, DGraph, AnyLogic, LibEnv)
ana_LIB_ITEM lgraph defl opts libenv dg l itm = case itm of
  Spec_defn spn gen asp pos -> do
    let spstr = tokStr spn
    analyzing opts $ "spec " ++ spstr
    (gen', (imp, params, allparams), dg') <-
      liftR (ana_GENERICITY lgraph dg l opts
             (extName "P" (makeName spn)) gen)
    (sp', body, dg'') <-
      liftR (ana_SPEC lgraph dg'
             allparams (makeName spn) opts (item asp))
    let libItem' = Spec_defn spn gen' (replaceAnnoted sp' asp) pos
        genv = globalEnv dg
    if Map.member spn genv
      then liftR (plain_error (libItem', dg'', l, libenv)
                  (alreadyDefined spstr) pos)
      else return (libItem',
                dg'' { globalEnv = Map.insert spn (SpecEntry
                            (imp, params, getMaybeSig allparams, body)) genv }
                     , l, libenv)
  View_defn vn gen vt gsis pos -> do
    analyzing opts $ "view " ++ tokStr vn
    liftR (ana_VIEW_DEFN lgraph defl libenv dg l opts vn gen vt gsis pos)
  Arch_spec_defn asn asp pos -> do
    let asstr = tokStr asn
    analyzing opts $ "arch spec " ++ asstr
    (archSig, dg', asp') <-
      liftR (ana_ARCH_SPEC lgraph defl dg l opts (item asp))
    let asd' = Arch_spec_defn asn (replaceAnnoted asp' asp) pos
        genv = globalEnv dg'
    if Map.member asn genv
      then liftR (plain_error (asd', dg', l, libenv)
                  (alreadyDefined asstr) pos)
      else return (asd', dg'
             { globalEnv = Map.insert asn (ArchEntry archSig) genv },
             l, libenv)
  Unit_spec_defn usn usp pos -> do
    let usstr = tokStr usn
    analyzing opts $ "unit spec " ++ usstr
    (unitSig, dg', usp') <- liftR (ana_UNIT_SPEC lgraph defl dg l opts
                                      (EmptyNode defl) usp)
    let usd' = Unit_spec_defn usn usp' pos
        genv = globalEnv dg'
    if Map.member usn genv
      then liftR (plain_error (itm, dg', l, libenv)
                  (alreadyDefined usstr) pos)
      else return (usd', dg'
             { globalEnv = Map.insert usn (UnitEntry unitSig) genv },
             l, libenv)
  Ref_spec_defn rn _ pos -> do
    let rnstr = tokStr rn
    analyzing opts $ "refinement "
      ++ rnstr ++ "\n  (refinement analysis not implemented yet)"
    let genv = globalEnv dg
    if Map.member rn genv
      then liftR (plain_error (itm, dg, l, libenv)
                             (alreadyDefined rnstr)
                             pos)
      else return ( itm, dg { globalEnv = Map.insert rn (RefEntry) genv }
                  , l, libenv)
  Logic_decl ln@(Logic_name logTok _) pos -> do
    logNm <- lookupLogic "LOGIC DECLARATION:" (tokStr logTok) lgraph
    putMessageIORes opts 1 $ "logic " ++ show logNm
    return (Logic_decl ln pos, dg, logNm, libenv)
  Download_items ln items _ -> do
  -- we take as the default logic for imported libs
  -- the global default logic
    (ln', libenv') <- anaLibFile lgraph defl opts libenv ln
    if ln == ln' then case Map.lookup ln libenv' of
      Nothing -> error $ "Internal error: did not find library " ++
                     show ln ++ " available: " ++ show (Map.keys libenv')
      Just dg' -> do
        (genv1,dg1) <- liftR (foldl (ana_ITEM_NAME_OR_MAP libenv' ln
                                       $ globalEnv dg')
                                       (return (globalEnv dg, dg))
                                       items)
        gannos'' <- liftR $ globalAnnos dg `mergeGlobalAnnos` globalAnnos dg'
        return (itm, dg1
              { globalAnnos = gannos''
              , globalEnv = genv1 }, l, libenv')
      else liftR $ fail $ "downloaded library '" ++ show ln'
            ++ "' does not match library name '" ++ shows ln "'"

-- ??? Needs to be generalized to views between different logics
ana_VIEW_DEFN :: LogicGraph -> AnyLogic -> LibEnv -> DGraph
              -> AnyLogic -> HetcatsOpts -> SIMPLE_ID
              -> GENERICITY -> VIEW_TYPE -> [G_mapping] -> Range
              -> Result (LIB_ITEM, DGraph, AnyLogic, LibEnv)
ana_VIEW_DEFN lgraph _defl libenv dg l opts
              vn gen vt gsis pos = do
  let adj = adjustPos pos
  (gen',(imp,params,allparams),dg') <-
       ana_GENERICITY lgraph dg l opts (extName "VG" (makeName vn)) gen
  (vt', (src,tar), dg'') <-
       ana_VIEW_TYPE lgraph dg' l allparams opts
                         (makeName vn) vt
  let gsigmaS = getSig src
      gsigmaT = getSig tar
  G_sign lidS sigmaS _ <- return gsigmaS
  G_sign lidT sigmaT _ <- return gsigmaT
  gsis1 <- adj $ homogenizeGM (Logic lidS) gsis
  G_symb_map_items_list lid sis <- return gsis1
  sigmaS' <- adj $ coerceSign lidS lid "" sigmaS
  sigmaT' <- adj $ coerceSign lidT lid "" sigmaT
  mor <- if isStructured opts then return (ide lid sigmaS')
           else do
             rmap <- adj $ stat_symb_map_items lid sis
             adj $ induced_from_to_morphism lid rmap sigmaS' sigmaT'
  let nodeS = getNode src
      nodeT = getNode tar
      gmor = gEmbed (G_morphism lid 0 mor 0 0)
      link = (nodeS,nodeT,DGLink {
               dgl_morphism = gmor,
               dgl_type = GlobalThm LeftOpen None LeftOpen,
                   -- 'LeftOpen' for conserv correct?
               dgl_origin = DGView vn,
               dgl_id = [getNewEdgeID dg'']})
      vsig = (src,gmor,(imp,params,getMaybeSig allparams,tar))
      genv = globalEnv dg''
  if Map.member vn genv
   then plain_error (View_defn vn gen' vt' gsis pos, dg'', l, libenv)
                    (alreadyDefined $ tokStr vn)
                    pos
   else return (View_defn vn gen' vt' gsis pos,
                (insEdgeDG link dg'')
                { globalEnv = Map.insert vn (ViewEntry vsig) genv }
               , l
               , libenv)

ana_ITEM_NAME_OR_MAP :: LibEnv -> LIB_NAME -> GlobalEnv
                     -> Result (GlobalEnv, DGraph) -> ITEM_NAME_OR_MAP
                     -> Result (GlobalEnv, DGraph)
ana_ITEM_NAME_OR_MAP libenv ln genv' res itm =
   ana_ITEM_NAME_OR_MAP1 libenv ln genv' res $ case itm of
     Item_name name -> (name, name)
     Item_name_map old new _ -> (old, new)

ana_ITEM_NAME_OR_MAP1 :: LibEnv -> LIB_NAME -> GlobalEnv
                      -> Result (GlobalEnv, DGraph) -> (SIMPLE_ID, SIMPLE_ID)
                      -> Result (GlobalEnv, DGraph)
ana_ITEM_NAME_OR_MAP1 libenv ln genv' res (old, new) = do
  (genv,dg) <- res
  entry <- maybeToResult nullRange
            (tokStr old ++ " not found") (Map.lookup old genv')
  case Map.lookup new genv of
    Nothing -> return ()
    Just _ -> fail (tokStr new ++ " already used")
  case entry of
    SpecEntry extsig ->
      let (dg1,extsig1) = refExtsig libenv ln dg (Just new) extsig
          genv1 = Map.insert new (SpecEntry extsig1) genv
       in return (genv1,dg1)
    ViewEntry vsig ->
      let (dg1,vsig1) = refViewsig libenv ln dg vsig
          genv1 = Map.insert new (ViewEntry vsig1) genv
      in return (genv1,dg1)
    ArchEntry _asig -> ana_err "arch spec download"
    UnitEntry _usig -> ana_err "unit spec download"
    RefEntry -> ana_err "ref spec download"

refNodesig :: LibEnv -> LIB_NAME -> DGraph -> (Maybe SIMPLE_ID, NodeSig)
           -> (DGraph, NodeSig)
refNodesig libenv refln dg (name, NodeSig refn sigma@(G_sign lid sig ind)) =
  let (ln, n) = getActualParent libenv refln refn
      node_contents = newInfoNodeLab (makeMaybeName name)
           (newRefInfo ln n) $ noSensGTheory lid sig ind
      node = getNewNodeDG dg
   in
   --(insNode (node,node_contents) dg, NodeSig node sigma)
   case (lookupInAllRefNodesDG (ln, n) dg) of
        Just existNode -> (dg, NodeSig existNode sigma)
        Nothing -> (addToRefNodesDG (node, ln, n)
                                    $ insNodeDG (node,node_contents) dg
                    , NodeSig node sigma)

{- | get to the actual parent which is not a referenced node, so that
     the small chains between nodes in different library can be advoided.
     (details see ticket 5)
-}
getActualParent :: LibEnv -> LIB_NAME -> Node -> (LIB_NAME, Node)
getActualParent libenv ln n =
   let
   dg = lookupDGraph ln libenv
   refLab =
        lab' $ safeContextDG "Static.AnalysisLibrary.getActualParent" dg n
   in
   case isDGRef refLab of
        -- recursively goes to parent of the current node, but
        -- it actually would only be done once
        True -> getActualParent libenv (dgn_libname refLab) (dgn_node refLab)
        False -> (ln, n)

refNodesigs :: LibEnv -> LIB_NAME -> DGraph -> [(Maybe SIMPLE_ID, NodeSig)]
            -> (DGraph, [NodeSig])
refNodesigs libenv ln = mapAccumR (refNodesig libenv ln)

refExtsig :: LibEnv -> LIB_NAME -> DGraph -> Maybe SIMPLE_ID -> ExtGenSig
          -> (DGraph, ExtGenSig)
refExtsig libenv ln dg name (imps,params,gsigmaP,body) =
  let
  params' = map (\x -> (Nothing,x)) params
  (dg0, body1) = refNodesig libenv ln dg (name, body)
  (dg1, params1) = refNodesigs libenv ln dg0 params'
  (dg2, imps1) = case imps of
                 EmptyNode _ -> (dg1, imps)
                 JustNode ns -> let
                     (dg3, nns) = refNodesig libenv ln dg1 (Nothing, ns)
                     in (dg3, JustNode nns)
  in (dg2,(imps1,params1,gsigmaP,body1))

refViewsig :: LibEnv -> LIB_NAME -> DGraph -> (NodeSig, t1, ExtGenSig)
           -> (DGraph, (NodeSig, t1, ExtGenSig))
refViewsig libenv ln dg (src,mor,extsig) =
  (dg2,(src1,mor,extsig1))
  where
  (_,[src1]) = refNodesigs libenv ln dg [(Nothing,src)]
  (dg2,extsig1) = refExtsig libenv ln dg Nothing extsig
