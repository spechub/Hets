{-|
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  till@tzi.de
Stability   :  provisional
Portability :  non-portable(Logic)

Analysis of libraries
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
    , ana_LIB_DEFN
    ) where

import Logic.Logic
import Logic.Coerce
import Logic.Grothendieck
import Logic.Prover
import Data.Graph.Inductive.Graph
import Syntax.AS_Structured hiding (View_defn, Spec_defn)
import Syntax.AS_Library
import Static.DevGraph
import Static.PrintDevGraph
import Static.AnalysisStructured
import Static.AnalysisArchitecture
import Comorphisms.LogicGraph
import Common.AS_Annotation hiding (isAxiom, isDef)
import Common.GlobalAnnotations
import Common.ConvertGlobalAnnos
import Common.AnalyseAnnos
import Common.Result
import Common.Id
import qualified Common.Lib.Map as Map
import Common.PrettyPrint
import Driver.Options
import Driver.ReadFn
import Driver.WriteFn
import Data.List
import Control.Monad

-- | lookup an env or read and analyze a file
anaLib :: HetcatsOpts -> FilePath -> IO (Maybe (LIB_NAME, LibEnv))
anaLib opts file = do
    defl <- lookupLogic "logic from command line: "
                  (defLogic opts) logicGraph
    Result ds res <- ioresToIO $ anaLibFileOrGetEnv logicGraph defl opts 
                     emptyLibEnv (fileToLibName opts file) file
    showDiags opts ds 
    case res of 
        Nothing -> return res
        Just (ln, lenv) -> case Map.lookup ln lenv of
              Nothing -> return res
              Just gctx@(ga, ge, _) -> do
                  writeSpecFiles opts file lenv ga (ln, ge)
                  putIfVerbose opts 5 $ show $
                                printLibrary lenv (ln, gctx)
                  putIfVerbose opts 3 $ showPretty ga ""
                  return res

-- | parsing and static analysis for files
-- Parameters: logic graph, default logic, file name
anaSourceFile :: LogicGraph -> AnyLogic -> HetcatsOpts -> LibEnv -> FilePath
              -> IOResult (LIB_NAME, LibEnv)
anaSourceFile lgraph defl opts libenv fname = IOResult $ do
  fname' <- existsAnSource opts fname
  case fname' of
    Nothing -> do
        return $ fail $ "a file for input '" ++ fname ++ "' not found."
    Just fname'' -> do
        input <- readFile fname''
        putIfVerbose opts 1 $ "Reading file " ++ fname''
        ioresToIO $ anaString lgraph defl opts libenv input fname''

-- | parsing and static analysis for string (=contents of file)
-- Parameters: logic graph, default logic, contents of file, filename
anaString :: LogicGraph -> AnyLogic -> HetcatsOpts -> LibEnv -> String
              -> FilePath -> IOResult (LIB_NAME, LibEnv)
anaString lgraph defl opts libenv input file =
  let Result ds mast = read_LIB_DEFN_M lgraph defl opts file input
  in case mast of
  Just ast@(Lib_defn ln _ _ ans) -> case analysis opts of
      Skip  -> do
          ioToIORes $ putIfVerbose opts 1 $
                  "Skipping static analysis of library " ++ show ln
          ga <- resToIORes $ addGlobalAnnos emptyGlobalAnnos ans
          case gui opts of
                      Only -> return ()
                      _ -> ioToIORes $ write_LIB_DEFN ga file opts ast
          resToIORes $ Result ds Nothing
      _ -> do
          if ln == fileToLibName opts file
             then return ()
             else showDiags1 opts $ resToIORes $ Result [mkDiag Warning
                      ("file name '" ++ file 
                       ++ "' does not match library name") $ getLIB_ID ln] 
                       $ Just () 
          ioToIORes $ putIfVerbose opts 1 $ "Analyzing library " ++ show ln
          (_,ld,_,lenv) <-
              ana_LIB_DEFN lgraph defl opts libenv ast
          case Map.lookup ln lenv of
              Nothing -> error $ "anaString: missing library: " ++ show ln
              Just gctx@(ga, _, _) -> ioToIORes $ do
                  case gui opts of
                      Only -> return ()
                      _ -> write_LIB_DEFN ga file opts ld
                  when (hasEnvOut opts)
                        (writeFileInfo opts file gctx)
                  return (ln, lenv)
  Nothing -> resToIORes $ Result ds Nothing

-- lookup/read a library
anaLibFile :: LogicGraph -> AnyLogic -> HetcatsOpts -> LibEnv -> LIB_NAME
              -> IOResult (LIB_NAME, LibEnv)
anaLibFile lgraph defl opts libenv ln = 
    let lnstr = showPretty ln "" in case Map.lookup ln libenv of
    Just _ -> do 
        putMessageIORes opts 1 $ "Analyzing from " ++ lnstr
        return (ln, libenv)
    Nothing -> do 
        putMessageIORes opts 1 $ "Downloading " ++ lnstr ++ " ..."
        res <- anaLibFileOrGetEnv lgraph defl opts libenv ln 
            $ libNameToFile opts ln
        putMessageIORes opts 1 $ "... loaded " ++ lnstr
        return res

-- | convert a file name that may have a suffix to a library name
fileToLibName :: HetcatsOpts -> FilePath -> LIB_NAME
fileToLibName opts efile =
    let path = libdir opts
        file = rmSuffix efile -- cut of extension
        nfile = dropWhile (== '/') $         -- cut off leading slashes
                if isPrefixOf path file
                then drop (length path) file -- cut off libdir prefix
                else file
    in Lib_id $ Indirect_link nfile nullRange

-- | create a file name without suffix from a library name
libNameToFile :: HetcatsOpts -> LIB_NAME -> FilePath
libNameToFile opts libname =
           case getLIB_ID libname of
                Indirect_link file _ ->
                  let path = libdir opts
                     -- add trailing "/" if necessary
                  in pathAndBase path file
                Direct_link _ _ -> error "libNameToFile"

-- lookup/read a library
anaLibFileOrGetEnv :: LogicGraph -> AnyLogic -> HetcatsOpts -> LibEnv
              -> LIB_NAME -> FilePath -> IOResult (LIB_NAME, LibEnv)
anaLibFileOrGetEnv lgraph defl opts libenv libname file = IOResult $ do
     let env_file = rmSuffix file ++ ".env"
     recent_env_file <- checkRecentEnv opts env_file file
     if recent_env_file
        then do
             putIfVerbose opts 1 $ "Reading " ++ env_file
             Result dias mgc <- globalContextfromShATerm env_file
             case mgc of
                 Nothing -> ioresToIO $ do
                     showDiags1 opts $ resToIORes $ Result dias $ Just ()
                     ioToIORes $ putIfVerbose opts 1 $ "Deleting " ++ env_file
                     anaSourceFile lgraph defl opts libenv file
                 Just gc@(_,_,dgraph) -> do
                          -- get all DGRefs from DGraph
                     Result ds mEnv <- ioresToIO $ foldl 
                         ( \ ioLibEnv labDG -> case snd labDG of
                             DGRef { dgn_libname = ln } -> do
                                 p_libEnv <- ioLibEnv
                                 if Map.member ln p_libEnv then 
                                    return p_libEnv
                                    else fmap snd $ anaLibFile lgraph defl
                                         opts p_libEnv ln
                             _ -> ioLibEnv) 
                         (return $ Map.insert libname gc libenv) 
                         $ labNodes dgraph
                     return $ Result ds $ fmap
                                ( \ rEnv -> (libname, rEnv)) mEnv
        else ioresToIO $ anaSourceFile lgraph defl opts libenv file

-- | analyze a LIB_DEFN
-- Parameters: logic graph, default logic, opts, library env, LIB_DEFN
-- call this function as follows:
-- do Result diags res <- ioresToIO (ana_LIB_DEFN ...)
--    mapM_ (putStrLn . show) diags
ana_LIB_DEFN :: LogicGraph -> AnyLogic -> HetcatsOpts
                 -> LibEnv -> LIB_DEFN
                 -> IOResult (LIB_NAME,LIB_DEFN,DGraph,LibEnv)

ana_LIB_DEFN lgraph defl opts libenv (Lib_defn ln alibItems pos ans) = do
  gannos <- showDiags1 opts $ resToIORes $ addGlobalAnnos emptyGlobalAnnos ans
  (libItems',gctx@(_,_,dg),_,libenv') <-
     foldl ana (return ([],(gannos,Map.empty,empty),defl,libenv))
               (map item alibItems)

  return (ln,
          Lib_defn ln
                   (map (uncurry replaceAnnoted)
                        (zip (reverse libItems') alibItems))
                   pos
                   ans,
          dg,
          Map.insert ln gctx libenv')

  where
  ana res1 libItem = do
    (libItems',gctx1,l1,libenv1) <- res1

    IOResult (do
      Result diags2 res <-
         ioresToIO $ ana_LIB_ITEM lgraph defl opts libenv1 gctx1 l1 libItem
      ioresToIO $ showDiags1 opts (resToIORes (Result diags2 res))
      if outputToStdout opts then
         if hasErrors diags2 then
            fail "Stopped due to errors"
            else case res of
              Just (libItem',gctx1',l1',libenv1') ->
                  return (return (libItem':libItems',gctx1',l1',libenv1'))
              Nothing -> fail "Stopped. No result available"
         else do
              --result1 <- ioresToIO res1
              --let diags1 = diags result1
              if hasErrors diags2 then
                 ioresToIO $ resToIORes (Result (diags2) Nothing)
                 else case res of
                 Just (libItem',gctx1',l1',libenv1') ->
                     return ((return (libItem':libItems',gctx1',l1',libenv1'))
                             {diags = diags2})
                 Nothing -> return $ fail "Stopped. No result available"
             )

putMessageIORes :: HetcatsOpts -> Int -> String -> IOResult ()
putMessageIORes opts i msg =
   if outputToStdout opts
   then ioToIORes $ putIfVerbose opts i msg
   else resToIORes $ message () msg

-- analyse a LIB_ITEM
-- Parameters: logic graph, default logic, opts, library env
-- global context, current logic, LIB_ITEM
ana_LIB_ITEM :: LogicGraph -> AnyLogic -> HetcatsOpts
                 -> LibEnv -> GlobalContext -> AnyLogic
                 -> LIB_ITEM
                 -> IOResult (LIB_ITEM,GlobalContext,AnyLogic,LibEnv)
ana_LIB_ITEM lgraph _defl opts libenv gctx@(gannos, genv, _) l
             (Spec_defn spn gen asp pos) = do
  putMessageIORes opts 1 $ "Analyzing spec " ++ showPretty spn ""
  (gen',(imp,params,allparams),dg') <-
     resToIORes (ana_GENERICITY lgraph gctx l opts 
                 (extName "P" (makeName spn)) gen)
  (sp',body,dg'') <-
     resToIORes (ana_SPEC lgraph (gannos,genv,dg')
                          allparams (makeName spn) opts (item asp))
  let libItem' = Spec_defn spn gen' (replaceAnnoted sp' asp) pos
  if Map.member spn genv
   then resToIORes (plain_error (libItem',gctx,l,libenv)
                                ("Name "++ showPretty spn " already defined")
                                pos)
   else return (libItem',
                (gannos, Map.insert spn 
                 (SpecEntry 
                  (imp, params, getMaybeSig allparams, body)) genv,
                 dg''), l, libenv)

ana_LIB_ITEM lgraph defl opts libenv gctx l
             (View_defn vn gen vt gsis pos) = do
  putMessageIORes opts 1 $ "Analyzing view " ++ showPretty vn ""
  resToIORes (ana_VIEW_DEFN lgraph defl libenv gctx l opts
                            vn gen vt gsis pos)

-- architectural specification
ana_LIB_ITEM lgraph defl opts libenv gctx@(gannos, genv, _) l
             (Arch_spec_defn asn asp pos) = do
  putMessageIORes opts 1 $ "Analyzing arch spec " ++ showPretty asn ""
  (archSig, dg', asp') <- resToIORes (ana_ARCH_SPEC lgraph defl gctx l opts
                                      (item asp))
  let asd' = Arch_spec_defn asn (replaceAnnoted asp' asp) pos
      gctx' = (gannos, genv, dg')
  if Map.member asn genv
     then
     resToIORes (plain_error (asd', gctx', l, libenv)
                             ("Name " ++ showPretty asn " already defined")
                             pos)
     else
     return (asd',
             (gannos,
              Map.insert asn (ArchEntry archSig) genv,
              dg'),
             l,
             libenv)

-- unit specification
ana_LIB_ITEM lgraph defl opts libenv gctx@(gannos, genv, _) l
             usd@(Unit_spec_defn usn usp pos) = do
  putMessageIORes opts 1 $ "Analyzing unit spec " ++ showPretty usn ""
  (unitSig, dg', usp') <- resToIORes (ana_UNIT_SPEC lgraph defl gctx l opts
                                      (EmptyNode defl) usp)
  let usd' = Unit_spec_defn usn usp' pos
  if Map.member usn genv
     then
     resToIORes (plain_error (usd, (gannos, genv, dg'), l, libenv)
                             ("Name " ++ showPretty usn " already defined")
                             pos)
     else
     return (usd',
             (gannos,
              Map.insert usn (UnitEntry unitSig) genv,
              dg'),
             l,
             libenv)

-- refinement specification
ana_LIB_ITEM _lgraph _defl opts libenv (gannos, genv, dg) l
             rd@(Ref_spec_defn rn _ pos) = do
  putMessageIORes opts 1 $ "Analyzing refinement "
      ++ showPretty rn "\n  (refinement analysis not implemented yet)"
  let rd' = rd
      dg' = dg
  if Map.member rn genv
     then
     resToIORes (plain_error (rd, (gannos, genv, dg), l, libenv)
                             ("Name " ++ showPretty rn " already defined")
                             pos)
     else
     return (rd',
             (gannos,
              Map.insert rn (RefEntry) genv,
              dg'),
             l,
             libenv)

-- logic declaration
ana_LIB_ITEM lgraph _defl opts libenv gctx _l
             (Logic_decl ln@(Logic_name logTok _) pos) = do
  logNm <- lookupLogic "LOGIC DECLARATION:" (tokStr logTok) lgraph
  putMessageIORes opts 1 $ "logic " ++ show logNm
  return (Logic_decl ln pos,gctx,logNm,libenv)

ana_LIB_ITEM lgraph defl opts libenv (gannos,genv,dg) l
             libItem@(Download_items ln items _) = do
  -- we take as the default logic for imported libs
  -- the global default logic
  (ln', libenv') <- anaLibFile lgraph defl opts libenv ln
  if ln == ln' then case Map.lookup ln libenv' of
    Nothing -> error $ "Internal error: did not find library " ++
                     show ln ++ " available: " ++ show (Map.keys libenv')
    Just (gannos', genv', _dg') -> do
      (genv1,dg1) <- resToIORes (foldl (ana_ITEM_NAME_OR_MAP ln genv')
                                       (return (genv,dg)) items
                                 )
      gannos'' <- resToIORes $ gannos `mergeGlobalAnnos` gannos'
      return (libItem,(gannos'',genv1,dg1),l,libenv')
   else resToIORes $ fail $ "downloaded library '" ++ show ln'
           ++ "' does not match library name '" ++ shows ln "'"

-- ??? Needs to be generalized to views between different logics
ana_VIEW_DEFN :: LogicGraph -> AnyLogic -> LibEnv -> GlobalContext
              -> AnyLogic -> HetcatsOpts -> SIMPLE_ID
              -> GENERICITY -> VIEW_TYPE -> [G_mapping] -> Range
              -> Result (LIB_ITEM, GlobalContext, AnyLogic, LibEnv)
ana_VIEW_DEFN lgraph _defl libenv gctx@(gannos, genv, _) l opts
              vn gen vt gsis pos = do
  let adj = adjustPos pos
  (gen',(imp,params,allparams),dg') <-
       ana_GENERICITY lgraph gctx l opts (extName "VG" (makeName vn)) gen
  (vt',(src,tar),dg'') <-
       ana_VIEW_TYPE lgraph (gannos,genv,dg') l allparams opts (makeName vn) vt
  let gsigmaS = getSig src
      gsigmaT = getSig tar
  G_sign lidS sigmaS <- return gsigmaS
  G_sign lidT sigmaT <- return gsigmaT
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
      gmor = gEmbed (G_morphism lid mor)
      link = (nodeS,nodeT,DGLink {
               dgl_morphism = gmor,
               dgl_type = GlobalThm LeftOpen None LeftOpen,
                   -- 'LeftOpen' for conserv correct?
               dgl_origin = DGView vn})
      vsig = (src,gmor,(imp,params,getMaybeSig allparams,tar))
  if Map.member vn genv
   then plain_error (View_defn vn gen' vt' gsis pos,gctx,l,libenv)
                    ("Name "++showPretty vn " already defined")
                    pos
   else return (View_defn vn gen' vt' gsis pos,
                (gannos,
                 Map.insert vn (ViewEntry vsig) genv,
                 insEdge link dg''),
                l,
                libenv)


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
            (showPretty old " not found") (Map.lookup old genv')
  case Map.lookup new genv of
    Nothing -> return ()
    Just _ -> fail (showPretty new " already used")
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
refNodesig ln dg (name, NodeSig n sigma@(G_sign lid sig)) =
  let node_contents = DGRef {
        dgn_name = makeMaybeName name,
        dgn_libname = ln,
        dgn_node = n,
        dgn_theory = G_theory lid sig noSens,
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
