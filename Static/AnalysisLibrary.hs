{- |
Module      :  $Header$
Description :  static analysis of CASL specification libraries
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  till@tzi.de
Stability   :  provisional
Portability :  non-portable(Logic)

Static analysis of CASL specification libraries
   Follows the verification semantics sketched in Chap. IV:6
   of the CASL Reference Manual.
-}

{-
   Todo:
   Generalization to heterogeneous views
   check that libname coincides with filename (otherwise internal error occurs)
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
import Logic.Prover
import Data.Graph.Inductive.Graph
import Syntax.AS_Structured
import Syntax.AS_Library
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
import Common.Id
import Common.DocUtils
import qualified Data.Map as Map
import Driver.Options
import Driver.ReadFn
import Driver.WriteFn
import Data.List
import Control.Monad
import Control.Monad.Trans

-- | lookup an env or read and analyze a file
anaLib :: HetcatsOpts -> FilePath -> IO (Maybe (LIB_NAME, LibEnv))
anaLib opts file = anaLibExt opts file emptyLibEnv

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
                gctx = lookupGlobalContext ln nEnv
                ga = globalAnnos gctx
            writeSpecFiles opts file nEnv ga (ln, globalEnv gctx)
            putIfVerbose opts 3 $ showGlobalDoc ga ga ""
            return $ Just (ln, nEnv)

-- | parsing and static analysis for files
-- Parameters: logic graph, default logic, file name
anaSourceFile :: LogicGraph -> AnyLogic -> HetcatsOpts -> LibEnv -> FilePath
              -> ResultT IO (LIB_NAME, LibEnv)
anaSourceFile lgraph defl opts libenv fname = ResultT $ do
  fname' <- existsAnSource opts fname
  case fname' of
    Nothing -> do
        return $ fail $ "a file for input '" ++ fname ++ "' not found."
    Just file ->
        if any (flip isSuffixOf file) [envSuffix, prfSuffix] then
            let file' = rmSuffix file in
            runResultT $ anaLibFileOrGetEnv lgraph defl opts libenv
                   (fileToLibName opts file') file'
        else do
        input <- readFile file
        putIfVerbose opts 2 $ "Reading file " ++ file
        runResultT $ anaString lgraph defl opts libenv input file

-- | parsing and static analysis for string (=contents of file)
-- Parameters: logic graph, default logic, contents of file, filename
anaString :: LogicGraph -> AnyLogic -> HetcatsOpts -> LibEnv -> String
          -> FilePath -> ResultT IO (LIB_NAME, LibEnv)
anaString lgraph defl opts libenv input file =
  let Result ds mast = read_LIB_DEFN_M lgraph defl opts file input
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
          if ln == fileToLibName opts file
             then return ()
             else showDiags1 opts $ liftR $ Result [mkDiag Warning
                      ("file name '" ++ file
                       ++ "' does not match library name") $ getLIB_ID ln]
                       $ Just ()
          lift $ putIfVerbose opts 1 $ "Analyzing library " ++ show ln
          (_,ld,_,lenv) <-
              ana_LIB_DEFN lgraph defl opts libenv ast
          case Map.lookup ln lenv of
              Nothing -> error $ "anaString: missing library: " ++ show ln
              Just gctx -> lift $ do
                  case gui opts of
                      Only -> return ()
                      _ -> write_LIB_DEFN (globalAnnos gctx) file opts ld
                  when (hasEnvOut opts)
                        (writeFileInfo opts ln file ld gctx)
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
                         ( \ ioLibEnv labDG -> case snd labDG of
                             DGRef { dgn_libname = ln } -> do
                                 p_libEnv <- ioLibEnv
                                 if Map.member ln p_libEnv then
                                    return p_libEnv
                                    else fmap snd $ anaLibFile lgraph defl
                                         opts p_libEnv ln
                             _ -> ioLibEnv)
                         (return $ Map.insert libname gc libenv)
                         $ labNodes $ devGraph gc
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
  (libItems', gctx, _, libenv') <-
     foldl ana (return ([], emptyGlobalContext { globalAnnos = gannos }
                       , defl, libenv))
               (map item alibItems)

  return (ln,
          Lib_defn ln
                   (map (uncurry replaceAnnoted)
                        (zip (reverse libItems') alibItems))
                   pos
                   ans,
          devGraph gctx,
          Map.insert ln gctx libenv')

  where
  ana res1 libItem = do
    (libItems',gctx1,l1,libenv1) <- res1

    ResultT (do
      Result diags2 res <-
         runResultT $ ana_LIB_ITEM lgraph defl opts libenv1 gctx1 l1 libItem
      runResultT $ showDiags1 opts (liftR (Result diags2 res))
      if outputToStdout opts then
         if hasErrors diags2 then
            fail "Stopped due to errors"
            else case res of
              Just (libItem',gctx1',l1',libenv1') ->
                  return (return (libItem':libItems',gctx1',l1',libenv1'))
              Nothing -> fail "Stopped. No result available"
         else do
              --result1 <- runResultT res1
              --let diags1 = diags result1
              if hasErrors diags2 then
                 runResultT $ liftR (Result (diags2) Nothing)
                 else case res of
                 Just (libItem',gctx1',l1',libenv1') ->
                     return ((return (libItem':libItems',gctx1',l1',libenv1'))
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

-- analyse a LIB_ITEM
-- Parameters: logic graph, default logic, opts, library env
-- global context, current logic, LIB_ITEM
ana_LIB_ITEM :: LogicGraph -> AnyLogic -> HetcatsOpts
                 -> LibEnv -> GlobalContext -> AnyLogic
                 -> LIB_ITEM
                 -> ResultT IO (LIB_ITEM,GlobalContext,AnyLogic,LibEnv)
ana_LIB_ITEM lgraph _defl opts libenv gctx l
             (Spec_defn spn gen asp pos) = do
  let spstr = tokStr spn
  analyzing opts $ "spec " ++ spstr
  (gen',(imp,params,allparams),dg') <-
     liftR (ana_GENERICITY lgraph gctx l opts
                 (extName "P" (makeName spn)) gen)
  (sp',body,dg'') <-
     liftR (ana_SPEC lgraph dg'
                          allparams (makeName spn) opts (item asp))
  let libItem' = Spec_defn spn gen' (replaceAnnoted sp' asp) pos
      genv = globalEnv gctx
  if Map.member spn genv
   then liftR (plain_error (libItem', dg'', l, libenv)
                                (alreadyDefined spstr)
                                pos)
   else return (libItem',
                dg'' { globalEnv = Map.insert spn (SpecEntry
                            (imp, params, getMaybeSig allparams, body)) genv }
                     , l, libenv)

ana_LIB_ITEM lgraph defl opts libenv gctx l
             (View_defn vn gen vt gsis pos) = do
  analyzing opts $ "view " ++ tokStr vn
  liftR (ana_VIEW_DEFN lgraph defl libenv gctx l opts
                            vn gen vt gsis pos)

-- architectural specification
ana_LIB_ITEM lgraph defl opts libenv gctx l
             (Arch_spec_defn asn asp pos) = do
  let asstr = tokStr asn 
  analyzing opts $ "arch spec " ++ asstr
  (archSig, gctx', asp') <- liftR (ana_ARCH_SPEC lgraph defl gctx l opts
                                      (item asp))
  let asd' = Arch_spec_defn asn (replaceAnnoted asp' asp) pos
      genv = globalEnv gctx'
  if Map.member asn genv
     then
     liftR (plain_error (asd', gctx', l, libenv)
                             (alreadyDefined asstr)
                             pos)
     else
     return (asd', gctx'
             { globalEnv = Map.insert asn (ArchEntry archSig) genv },
             l, libenv)

-- unit specification
ana_LIB_ITEM lgraph defl opts libenv gctx l
             usd@(Unit_spec_defn usn usp pos) = do
  let usstr = tokStr usn
  analyzing opts $ "unit spec " ++ usstr
  (unitSig, gctx', usp') <- liftR (ana_UNIT_SPEC lgraph defl gctx l opts
                                      (EmptyNode defl) usp)
  let usd' = Unit_spec_defn usn usp' pos
      genv = globalEnv gctx'
  if Map.member usn genv
     then
     liftR (plain_error (usd, gctx', l, libenv)
                             (alreadyDefined usstr)
                             pos)
     else
     return (usd', gctx'
             { globalEnv = Map.insert usn (UnitEntry unitSig) genv },
             l, libenv)

-- refinement specification
ana_LIB_ITEM _lgraph _defl opts libenv gctx l
             rd@(Ref_spec_defn rn _ pos) = do
  let rnstr = tokStr rn
  analyzing opts $ "refinement "
      ++ rnstr ++ "\n  (refinement analysis not implemented yet)"
  let rd' = rd
      genv = globalEnv gctx
  if Map.member rn genv
     then
     liftR (plain_error (rd, gctx, l, libenv)
                             (alreadyDefined rnstr)
                             pos)
     else
     return (rd', gctx { globalEnv = Map.insert rn (RefEntry) genv }
            , l, libenv)

-- logic declaration
ana_LIB_ITEM lgraph _defl opts libenv gctx _l
             (Logic_decl ln@(Logic_name logTok _) pos) = do
  logNm <- lookupLogic "LOGIC DECLARATION:" (tokStr logTok) lgraph
  putMessageIORes opts 1 $ "logic " ++ show logNm
  return (Logic_decl ln pos,gctx,logNm,libenv)

ana_LIB_ITEM lgraph defl opts libenv gctx l
             libItem@(Download_items ln items _) = do
  -- we take as the default logic for imported libs
  -- the global default logic
  (ln', libenv') <- anaLibFile lgraph defl opts libenv ln
  if ln == ln' then case Map.lookup ln libenv' of
    Nothing -> error $ "Internal error: did not find library " ++
                     show ln ++ " available: " ++ show (Map.keys libenv')
    Just gctx' -> do
      (genv1,dg1) <- liftR (foldl (ana_ITEM_NAME_OR_MAP ln
                                       $ globalEnv gctx')
                                       (return (globalEnv gctx, devGraph gctx))
                                       items)
      gannos'' <- liftR $
                  globalAnnos gctx `mergeGlobalAnnos` globalAnnos gctx'
      return (libItem, gctx
              { globalAnnos = gannos''
              , globalEnv = genv1
              , devGraph = dg1 }, l, libenv')
   else liftR $ fail $ "downloaded library '" ++ show ln'
           ++ "' does not match library name '" ++ shows ln "'"

-- ??? Needs to be generalized to views between different logics
ana_VIEW_DEFN :: LogicGraph -> AnyLogic -> LibEnv -> GlobalContext
              -> AnyLogic -> HetcatsOpts -> SIMPLE_ID
              -> GENERICITY -> VIEW_TYPE -> [G_mapping] -> Range
              -> Result (LIB_ITEM, GlobalContext, AnyLogic, LibEnv)
ana_VIEW_DEFN lgraph _defl libenv gctx l opts
              vn gen vt gsis pos = do
  let adj = adjustPos pos
  (gen',(imp,params,allparams),dg') <-
       ana_GENERICITY lgraph gctx l opts (extName "VG" (makeName vn)) gen
  (vt', (src,tar), gctx'') <-
       ana_VIEW_TYPE lgraph dg' l allparams opts
                         (makeName vn) vt
  let gsigmaS = getSig src
      gsigmaT = getSig tar
      dg'' = devGraph gctx''
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
      gmor = gEmbed (G_morphism lid mor 0)
      link = (nodeS,nodeT,DGLink {
               dgl_morphism = gmor,
               dgl_type = GlobalThm LeftOpen None LeftOpen,
                   -- 'LeftOpen' for conserv correct?
               dgl_origin = DGView vn})
      vsig = (src,gmor,(imp,params,getMaybeSig allparams,tar))
      genv = globalEnv gctx''
  if Map.member vn genv
   then plain_error (View_defn vn gen' vt' gsis pos, gctx'', l, libenv)
                    (alreadyDefined $ tokStr vn)
                    pos
   else return (View_defn vn gen' vt' gsis pos,
                gctx'' { globalEnv = Map.insert vn (ViewEntry vsig) genv
                       , devGraph = insEdge link dg''}, l, libenv)

ana_ITEM_NAME_OR_MAP :: LIB_NAME -> GlobalEnv -> Result (GlobalEnv, DGraph)
                     -> ITEM_NAME_OR_MAP -> Result (GlobalEnv, DGraph)
ana_ITEM_NAME_OR_MAP ln genv' res (Item_name name) =
  ana_ITEM_NAME_OR_MAP1 ln genv' res name name
ana_ITEM_NAME_OR_MAP ln genv' res (Item_name_map old new _) =
  ana_ITEM_NAME_OR_MAP1 ln genv' res old new

ana_ITEM_NAME_OR_MAP1 :: LIB_NAME -> GlobalEnv -> Result (GlobalEnv, DGraph)
                      -> SIMPLE_ID -> SIMPLE_ID
                      -> Result (GlobalEnv, DGraph)
ana_ITEM_NAME_OR_MAP1 ln genv' res old new = do
  (genv,dg) <- res
  entry <- maybeToResult nullRange
            (tokStr old ++ " not found") (Map.lookup old genv')
  case Map.lookup new genv of
    Nothing -> return ()
    Just _ -> fail (tokStr new ++ " already used")
  case entry of
    SpecEntry extsig ->
      let (dg1,extsig1) = refExtsig ln dg (Just new) extsig
          genv1 = Map.insert new (SpecEntry extsig1) genv
       in return (genv1,dg1)
    ViewEntry vsig ->
      let (dg1,vsig1) = refViewsig ln dg vsig
          genv1 = Map.insert new (ViewEntry vsig1) genv
      in return (genv1,dg1)
    ArchEntry _asig -> ana_err "arch spec download"
    UnitEntry _usig -> ana_err "unit spec download"
    RefEntry -> ana_err "ref spec download"

refNodesig :: LIB_NAME -> DGraph -> (Maybe SIMPLE_ID, NodeSig)
           -> (DGraph, NodeSig)
refNodesig ln dg (name, NodeSig n sigma@(G_sign lid sig ind)) =
  let node_contents = DGRef {
        dgn_name = makeMaybeName name,
        dgn_libname = ln,
        dgn_node = n,
        dgn_theory = G_theory lid sig ind noSens 0,
        dgn_nf = Nothing,
        dgn_sigma = Nothing
        }
      node = getNewNode dg
   in (insNode (node,node_contents) dg, NodeSig node sigma)

refNodesigs :: LIB_NAME -> DGraph -> [(Maybe SIMPLE_ID, NodeSig)]
            -> (DGraph, [NodeSig])
refNodesigs ln = mapAccumR (refNodesig ln)

refExtsig :: LIB_NAME -> DGraph -> Maybe SIMPLE_ID -> ExtGenSig
          -> (DGraph, ExtGenSig)
refExtsig ln dg name (imps,params,gsigmaP,body) =
  let
  params' = map (\x -> (Nothing,x)) params
  (dg0, body1) = refNodesig ln dg (name, body)
  (dg1, params1) = refNodesigs ln dg0 params'
  (dg2, imps1) = case imps of
                 EmptyNode _ -> (dg1, imps)
                 JustNode ns -> let
                     (dg3, nns) = refNodesig ln dg1 (Nothing, ns)
                     in (dg3, JustNode nns)
  in (dg2,(imps1,params1,gsigmaP,body1))

refViewsig :: LIB_NAME -> DGraph -> (NodeSig, t1, ExtGenSig)
           -> (DGraph, (NodeSig, t1, ExtGenSig))
refViewsig ln dg (src,mor,extsig) =
  (dg2,(src1,mor,extsig1))
  where
  (_,[src1]) = refNodesigs ln dg [(Nothing,src)]
  (dg2,extsig1) = refExtsig ln dg Nothing extsig
