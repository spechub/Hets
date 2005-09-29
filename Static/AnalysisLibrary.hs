{-| 
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2004
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

module Static.AnalysisLibrary (anaFile, ana_LIB_DEFN, anaString) where

import Logic.Logic
import Logic.Coerce
import Logic.Grothendieck
import Data.Graph.Inductive.Graph
import Static.DevGraph
import Syntax.AS_Structured hiding (View_defn, Spec_defn)
import Syntax.AS_Library
import Static.AnalysisStructured
import Static.AnalysisArchitecture
import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.ConvertGlobalAnnos
import Common.AnalyseAnnos
import Common.Result
import Common.Id
import qualified Common.Lib.Map as Map
import Common.PrettyPrint
import Driver.Options
import Driver.ReadFn
import Driver.WriteFn (writeFileInfo)
import Data.List
import System.Environment(getEnv)

-- | parsing and static analysis for files
-- Parameters: logic graph, default logic, file name
anaFile :: LogicGraph -> AnyLogic -> HetcatsOpts -> LibEnv -> String
              -> IO (Maybe (LIB_NAME,LIB_DEFN,DGraph,LibEnv))
anaFile logicGraph defaultLogic opts libenv fname = do
  putIfVerbose opts 1  ("Reading " ++ fname)
  fname' <- existsAnSource fname
  case fname' of
    Nothing -> do
     if outputToStdout opts then
      putStrLn (fname++" not found.")
      else return ()
     return Nothing
    Just fname'' -> do
      input <- readFile fname''
      anaString logicGraph defaultLogic opts libenv input (Just fname'')

-- | parsing and static analysis for string (=contents of file)
-- Parameters: logic graph, default logic, contents of file, filename (if any)
anaString :: LogicGraph -> AnyLogic -> HetcatsOpts -> LibEnv -> String
              -> Maybe String -> IO (Maybe (LIB_NAME,LIB_DEFN,DGraph,LibEnv))
anaString logicGraph defaultLogic opts libenv input fname = do
  let fname' = case fname of
        Nothing -> "<stdin>"
        Just n -> n
  ast <- read_LIB_DEFN_M defaultLogic fname' input
  Result ds res <-
        ioresToIO (ana_LIB_DEFN logicGraph defaultLogic opts
                                libenv ast)
      -- no diags expected here, since these are handled in ana_LIB_DEFN
      -- sequence (map (putStrLn . show) diags)
  case (res,fname) of 
        (Just (ln,_,_,lenv), Just n) ->
          writeFileInfo opts ds n ln lenv
        _ -> return ()
  return res

-- lookup/read a library
anaLibFile :: LogicGraph -> AnyLogic -> HetcatsOpts -> LibEnv -> LIB_NAME 
              -> IO ([Diagnosis], LibEnv)
anaLibFile logicGraph defaultLogic opts libenv libname = do
  -- is the library already in memory?
  case Map.lookup libname libenv of
   Just _ -> return ([],libenv)
   Nothing -> do
     -- if not compute the filename,
     fname <- case getLIB_ID libname of
                Indirect_link file _ -> do
                  path <- case libdir opts of
                            "" -> catch (getEnv "HETS_LIB") 
                                        (\ _ -> return "")
                            p -> return p
                  -- add trailing "/" if necessary
                  let path1 = case path of
                       "" -> ""
                       p -> case last p of
                              '/' -> p
                              _ -> p++"/"
                  return (path1++file)
                Direct_link _ _ -> 
                    if outputToStdout opts then
                       error "No direct links implemented yet"
                       else return (error "No direct links implemented yet")
     -- check if and env file is there and read it if it is recent
     let env_fname = fname++".env"
                     -- fname is sufficient here, because anaFile
                     -- trys all possible suffices with this basename
     recent_env_file <- checkRecentEnv env_fname fname
     if recent_env_file 
        then do 
             putIfVerbose opts 1 ("Reading "++env_fname)
             (Result dias mgc) <- globalContextfromShATerm env_fname
             -- the conversion/reading might yield an error that
             -- should be caught here
             (dias2, mLibEnv) <- 
                   maybe (do ioresToIO $ showDiags1 opts 
                                         (resToIORes (Result dias mgc))
                             anaLibFile' fname dias)
                       (\ gc@(_,_,dgraph) -> do 
                          putIfVerbose opts 1 ""
                          -- get all DGRefs from DGraph
                          let libEnv' = (Map.insert libname gc libenv)
                              nodesDGRef =
                                 filter (\ labDG -> case labDG of 
                                                      DGRef _ _ _ _ _ -> True
                                                      _ -> False)
                                        (map snd (labNodes dgraph))
                       -- and call anaLibFile with each of the dgn_libname
                       -- of the DGRefs
                              refLibs = nub $ map dgn_libname nodesDGRef
                              newRefLibs = 
                                 filter (\ ln -> 
                                          not (ln `elem` Map.keys libEnv'))
                                   refLibs
                          foldl (\ioLibEnv tlibname ->
                                do (dias3 ,p_libEnv) <- ioLibEnv
                                   putIfVerbose opts 1 
                                             ("Analyzing from " ++ 
                                              showPretty tlibname "\n")
                                   (dias4, libEnvF) <- 
                                       anaLibFile logicGraph defaultLogic
                                           opts p_libEnv tlibname
                                   return ((dias3 ++ dias4),libEnvF)
                                ) (return ([], libEnv')) newRefLibs
                       )
                      mgc
             if outputToStdout opts then
                return ([], mLibEnv)  
                else return( dias ++ dias2 , mLibEnv)
             else anaLibFile' fname []
                 
 where anaLibFile' :: FilePath -> [Diagnosis] -> IO ([Diagnosis], LibEnv)
       anaLibFile' fname diags'=
         do
         -- read and analyze the library,
         if outputToStdout opts then
            do
            res <- anaFile logicGraph defaultLogic opts libenv fname    
            putIfVerbose opts 1 ""
            -- and just return the libenv
            return (case res of 
                       Just (_,_,_,libenv') -> (diags', libenv')
                       Nothing -> (diags', libenv)
                   )
            else do
                 (dias, res) <- anaFileW logicGraph defaultLogic opts 
                                libenv fname
                 return (case res of
                         Just (_,_,_,libenv') -> (diags'++dias, libenv')
                         Nothing -> ((diags $ message () 
                                      (fname ++" not found.")) 
                                     ++ diags',libenv))
                            
       anaFileW :: LogicGraph -> AnyLogic -> HetcatsOpts -> LibEnv -> String
                  -> IO ([Diagnosis], Maybe (LIB_NAME,LIB_DEFN,DGraph,LibEnv))
       anaFileW logicGraph' defLogic' opts' libenv' fname = do
                fname' <- existsAnSource fname
                case fname' of
                     Nothing -> return ([], Nothing)
                     Just fname'' -> do
                         input <- readFile fname''
                         anaStringW logicGraph' defLogic' opts' libenv' input 
                                        (Just fname'')

       anaStringW :: LogicGraph -> AnyLogic -> HetcatsOpts -> LibEnv -> String
                  -> Maybe String 
                  -> IO ([Diagnosis], Maybe (LIB_NAME,LIB_DEFN,DGraph,LibEnv))
       anaStringW logicGraph' defLogic' opts' libenv' input fname = do
                let fname' = case fname of
                                  Nothing -> "<stdin>"
                                  Just n -> n
                (_, ast) <- read_LIB_DEFN_M_WI defLogic' fname' input
                Result ds res <-
                    ioresToIO (ana_LIB_DEFN logicGraph' defLogic' opts'
                                libenv' ast)
                case (res,fname) of 
                                 (Just (ln,_,_,lenv), Just n) ->
                                     writeFileInfo opts' ds n ln lenv
                                 _ -> return ()
                return (ds, res)

-- | analyze a LIB_DEFN
-- Parameters: logic graph, default logic, opts, library env, LIB_DEFN
-- call this function as follows:
-- do Result diags res <- ioresToIO (ana_LIB_DEFN ...)
--    sequence (map (putStrLn . show) diags)
ana_LIB_DEFN :: LogicGraph -> AnyLogic -> HetcatsOpts
                 -> LibEnv -> LIB_DEFN
                 -> IOResult (LIB_NAME,LIB_DEFN,DGraph,LibEnv)

ana_LIB_DEFN lgraph defl opts libenv (Lib_defn ln alibItems pos ans) = do
  gannos <- resToIORes $ addGlobalAnnos emptyGlobalAnnos ans
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

-- analyse a LIB_ITEM
-- Parameters: logic graph, default logic, opts, library env
-- global context, current logic, LIB_ITEM
ana_LIB_ITEM :: LogicGraph -> AnyLogic -> HetcatsOpts
                 -> LibEnv -> GlobalContext -> AnyLogic
                 -> LIB_ITEM
                 -> IOResult (LIB_ITEM,GlobalContext,AnyLogic,LibEnv)
ana_LIB_ITEM lgraph _defl opts libenv gctx@(gannos, genv, _) l  
             (Spec_defn spn gen asp pos) = do
  let analyseMessage = "Analyzing spec " ++ showPretty spn ""
  ioToIORes (putIfVerbose opts 1  analyseMessage)
  if outputToStdout opts then
     return()
     else
     resToIORes $ message () analyseMessage
  (gen',(imp,params,allparams),dg') <- 
     resToIORes (ana_GENERICITY lgraph gctx l opts (extName "P" (makeName spn)) gen)
  (sp',body,dg'') <- 
     resToIORes (ana_SPEC lgraph (gannos,genv,dg') 
                          allparams (makeName spn) opts (item asp))
  let libItem' = Spec_defn spn gen' (replaceAnnoted sp' asp) pos
  if Map.member spn genv 
   then resToIORes (plain_error (libItem',gctx,l,libenv)
                                ("Name "++ showPretty spn " already defined")
                                pos)
   else return (libItem',
                (gannos,
                 Map.insert spn (SpecEntry (imp,params,getMaybeSig allparams,body)) genv,
                 dg''),
                l,
                libenv)

ana_LIB_ITEM lgraph defl opts libenv gctx l
             (View_defn vn gen vt gsis pos) = do
  let analyseMessage = "Analyzing view " ++ showPretty vn ""
  ioToIORes (putIfVerbose opts 1  analyseMessage)
  if outputToStdout opts then
     return()
     else
     resToIORes $ message () analyseMessage
  resToIORes (ana_VIEW_DEFN lgraph defl libenv gctx l opts
                            vn gen vt gsis pos)

-- architectural specification
ana_LIB_ITEM lgraph defl opts libenv gctx@(gannos, genv, _) l 
             (Arch_spec_defn asn asp pos) = do
  let analyseMessage = "Analyzing arch spec " ++ showPretty asn ""
  ioToIORes (putIfVerbose opts 1 analyseMessage )
  if outputToStdout opts then
     return()
     else
     resToIORes $ message () analyseMessage
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
  let analyseMessage = "Analyzing unit spec " ++ showPretty usn ""
  ioToIORes (putIfVerbose opts 1 analyseMessage)
  if outputToStdout opts then
     return()
     else
     resToIORes $ message () analyseMessage
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
ana_LIB_ITEM lgraph defl opts libenv gctx@(gannos, genv, dg) l 
             rd@(Ref_spec_defn rn ref pos) = do
  let analyseMessage = "Analyzing refinement " ++ showPretty rn "\n  (refinement analysis not implemented yet)"
  ioToIORes (putIfVerbose opts 1 analyseMessage )
  if outputToStdout opts then
     return()
     else
     resToIORes $ message () analyseMessage
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
  let  analyseMessage = "logic " ++ show logNm
  ioToIORes (putIfVerbose opts 1  analyseMessage)
  if outputToStdout opts then
     return()
     else
     resToIORes $ message () analyseMessage
  return (Logic_decl ln pos,gctx,logNm,libenv)

ana_LIB_ITEM lgraph defl opts libenv gctx@(gannos,genv,dg) l 
             libItem@(Download_items ln items pos) = do
  -- we take as the default logic for imported libs 
  -- the global default logic
  
  let analyseMessage = "Analyzing from " ++ showPretty ln "\n"
  ioToIORes (putIfVerbose opts 1 analyseMessage)
  if outputToStdout opts then
     return()
     else
     resToIORes $ message () analyseMessage

  (diags', libenv') <- ioToIORes (anaLibFile lgraph defl opts libenv ln)
  resToIORes $ Result diags' $ Just ()

  -- let libMsg = unlines $ map show diags'
  -- resToIORes $ message () libMsg

  case Map.lookup ln libenv' of
    Nothing -> do 
     if outputToStdout opts then
        do 
          ioToIORes (putStrLn ("Internal error: did not find library "++
                     show ln++" available: "++show (Map.keys libenv')))
          return (libItem,gctx,l,libenv')
       else 
          resToIORes $ (fatal_error ("Internal error: did not find library "
                ++show ln++" available: "++show (Map.keys libenv')) nullRange)
    Just (gannos', genv', _dg') -> do
      (genv1,dg1) <- resToIORes (foldl (ana_ITEM_NAME_OR_MAP ln genv') 
                                       (return (genv,dg)) items
                                 )
      gannos'' <- resToIORes $ gannos `mergeGlobalAnnos` gannos'
      return (libItem,(gannos'',genv1,dg1),l,libenv')


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

refNodesig :: LIB_NAME -> DGraph -> (Maybe SIMPLE_ID, NodeSig) 
           -> (DGraph, NodeSig)
refNodesig ln dg (name, NodeSig n sigma) =
  let node_contents = DGRef {
        dgn_renamed = makeMaybeName name,
        dgn_libname = ln,
        dgn_node = n,
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
