{-| 
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
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


module Static.AnalysisLibrary (anaFile, ana_LIB_DEFN) where

import Logic.Logic
import Logic.Grothendieck
import Common.Lib.Graph
import Static.DevGraph
import qualified Syntax.AS_Structured
import Syntax.Parse_AS_Structured (lookupLogicName)
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
import Options
import System
import List

import ReadFn
import WriteFn (writeFileInfo)

-- | parsing and static analysis for files
-- Parameters: logic graph, default logic, file name
anaFile :: LogicGraph -> AnyLogic -> HetcatsOpts -> LibEnv -> String
              -> IO (Maybe (LIB_NAME,LIB_DEFN,DGraph,LibEnv))
anaFile logicGraph defaultLogic opts libenv fname = do
  putIfVerbose opts 1  ("Reading " ++ fname)
  fname' <- existsAnSource fname
  case fname' of
    Nothing -> do
      putStrLn (fname++" not found.")
      return Nothing
    Just fname'' -> do
      input <- readFile fname''
      ast <- read_LIB_DEFN_M defaultLogic fname'' input
      Result diags res <-
            ioresToIO (ana_LIB_DEFN logicGraph defaultLogic opts
                                    libenv ast)
          -- no diags expected here, since these are handled in ana_LIB_DEFN
          -- sequence (map (putStrLn . show) diags)
      case res of 
            Nothing -> return()
            Just (ln,_,_,lenv) ->
              writeFileInfo opts diags fname'' ln lenv
      return res

-- lookup/read a library
anaLibFile :: LogicGraph -> AnyLogic -> HetcatsOpts -> LibEnv -> LIB_NAME 
              -> IO LibEnv
anaLibFile logicGraph defaultLogic opts libenv libname = do
  -- is the library already in memory?
  case Map.lookup libname libenv of
   Just _ -> return libenv
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
                Direct_link _ _ -> error "No direct links implemented yet"
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
	     maybe (do showDiags opts dias
		       anaLibFile' fname)
                   (\ gc@(_,_,dgraph) -> do 
		       putStrLn ""
		       -- get all DGRefs from DGraph
		       let libEnv' = (Map.insert libname gc libenv)
		           nodesDGRef =
		              filter (\ labDG -> case labDG of 
				                  DGRef _ _ _ -> True
				                  _ -> False)
		                    (map snd (labNodes dgraph))
		       -- and call anaLibFile with each of the dgn_libname
		       -- of the DGRefs
		           refLibs = nub $ map dgn_libname nodesDGRef
		       --putStrLn ("Referenced Libs: " ++ 
			--	 (concat $ map (\ ln -> showPretty ln "; ")
                          --                 refLibs))
		       let newRefLibs = 
		              filter (\ ln -> 
				       not (ln `elem` Map.keys libEnv'))
		                refLibs
	               foldl (\ ioLibEnv tlibname ->
                                do p_libEnv <- ioLibEnv
		            --       putStrLn ("Available Libs: " ++
				--	     (concat $ map 
					--       (\ ln -> showPretty ln "; ")
                                          --     (Map.keys p_libEnv)))
			           putIfVerbose opts 1 
			                     ("Analyzing from " ++ 
					      showPretty tlibname "\n")
			           anaLibFile logicGraph defaultLogic 
                                              opts p_libEnv tlibname)
		           (return libEnv') 
		           newRefLibs )
		      mgc
	else anaLibFile' fname
 where anaLibFile' :: FilePath -> IO LibEnv
       anaLibFile' fname =
         do
         -- read and analyze the library,
         res <- anaFile logicGraph defaultLogic opts libenv fname
	 putStrLn ""
	 -- and just return the libenv
	 return (case res of 
               Just (_,_,_,libenv') -> libenv'
               Nothing -> libenv) 
  
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
  ana res libItem = do 
    (libItems',gctx1,l1,libenv1) <- res
    IOResult (do
      Result diags res <-
         ioresToIO (ana_LIB_ITEM lgraph defl opts libenv1 gctx1 l1 libItem)
      showDiags opts diags
      if hasErrors diags then fail "Stopped due to errors"
       else case res of
         Just (libItem',gctx1',l1',libenv1') -> 
           return (return (libItem':libItems',gctx1',l1',libenv1'))
         Nothing -> fail "Stopped. No result available"
      )

-- analyse a LIB_ITEM
-- Parameters: logic graph, default logic, opts, library env
-- global context, current logic, LIB_ITEM
ana_LIB_ITEM :: LogicGraph -> AnyLogic -> HetcatsOpts
                 -> LibEnv -> GlobalContext -> AnyLogic
                 -> LIB_ITEM
                 -> IOResult (LIB_ITEM,GlobalContext,AnyLogic,LibEnv)

ana_LIB_ITEM lgraph defl opts libenv gctx@(gannos,genv,dg) l  
             (Spec_defn spn gen asp pos) = do
  let just_struct = analysis opts == Structured
  ioToIORes (putIfVerbose opts 1  ("Analyzing spec " ++ showPretty spn ""))
  (gen',(imp,params,parsig,allparams),dg') <- 
     resToIORes (ana_GENERICITY lgraph gctx l just_struct gen)
  (sp',body,dg'') <- 
     resToIORes (ana_SPEC lgraph (gannos,genv,dg') 
                          allparams (Just spn) just_struct (item asp))
  let libItem' = Spec_defn spn gen' (replaceAnnoted sp' asp) pos
  if Map.member spn genv 
   then resToIORes (plain_error (libItem',gctx,l,libenv)
                                ("Name "++ showPretty spn " already defined")
                                (headPos pos))
   else return (libItem',
                (gannos,
                 Map.insert spn (SpecEntry (imp,params,parsig,body)) genv,
                 dg''),
                l,
                libenv)


ana_LIB_ITEM lgraph defl opts libenv gctx l
             (View_defn vn gen vt gsis pos) = do
  let just_struct = analysis opts == Structured
  ioToIORes (putIfVerbose opts 1  ("Analyzing view " ++ showPretty vn ""))
  resToIORes (ana_VIEW_DEFN lgraph defl libenv gctx l just_struct
                            vn gen vt gsis pos)

-- architectural specification
ana_LIB_ITEM lgraph defl opts libenv gctx@(gannos, genv, dg) l 
             asd@(Arch_spec_defn asn asp pos) = do
  let just_struct = analysis opts == Structured
  ioToIORes (putIfVerbose opts 1  ("Analyzing arch spec " ++ showPretty asn ""))
  (archSig, dg', asp') <- resToIORes (ana_ARCH_SPEC lgraph defl gctx l just_struct (item asp))
  let asd' = Arch_spec_defn asn (replaceAnnoted asp' asp) pos
      gctx' = (gannos, genv, dg')
  if Map.member asn genv 
     then
     resToIORes (plain_error (asd', gctx', l, libenv)
		             ("Name " ++ showPretty asn " already defined")
		             (headPos pos))
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
  let just_struct = analysis opts == Structured
  ioToIORes (putIfVerbose opts 1 ("Analyzing unit spec " ++ showPretty usn ""))
  (unitSig, dg', usp') <- resToIORes (ana_UNIT_SPEC lgraph defl gctx l just_struct (EmptyNode defl) usp)
  let usd' = Unit_spec_defn usn usp' pos
  if Map.member usn genv 
     then
     resToIORes (plain_error (usd, (gannos, genv, dg'), l, libenv)
		             ("Name " ++ showPretty usn " already defined")
		             (headPos pos))
     else
     return (usd', 
	     (gannos,
	      Map.insert usn (UnitEntry unitSig) genv,
	      dg'),
	     l,
	     libenv)

ana_LIB_ITEM lgraph defl opts libenv gctx l 
             (Logic_decl ln pos) = do
  log <- lookupLogicName ln lgraph
  ioToIORes (putIfVerbose opts 1  ("logic "++show log))
  return (Logic_decl ln pos,gctx,log,libenv)

ana_LIB_ITEM lgraph defl opts libenv gctx@(gannos,genv,dg) l 
             libItem@(Download_items ln items pos) = do
  -- we take as the default logic for imported libs 
  -- the global default logic
  ioToIORes (putIfVerbose opts 1 ("Analyzing from " ++ showPretty ln "\n"))
  let items' = zip items (drop 2 (pos ++ repeat nullPos))
  libenv' <- ioToIORes (anaLibFile lgraph defl opts libenv ln)
  case Map.lookup ln libenv' of
    Nothing -> do
       ioToIORes (putStrLn ("Internal error: did not find library "++show ln++" available: "++show (Map.keys libenv')))
       return (libItem,gctx,l,libenv')
    Just (gannos',genv',dg') -> do
      (genv1,dg1) <- resToIORes (foldl (ana_ITEM_NAME_OR_MAP ln genv') 
                                       (return (genv,dg)) items'
                                 )
      gannos'' <- resToIORes $ gannos `mergeGlobalAnnos` gannos'
      return (libItem,(gannos'',genv1,dg1),l,libenv')


-- ??? Needs to be generalized to views between different logics
ana_VIEW_DEFN lgraph defl libenv gctx@(gannos,genv,dg) l just_struct
              vn gen vt gsis pos = do
  let adj = adjustPos (headPos pos)
  (gen',(imp,params,parsig,allparams),dg') <- 
       ana_GENERICITY lgraph gctx l just_struct gen
  (vt',(src,tar),dg'') <- 
       ana_VIEW_TYPE lgraph (gannos,genv,dg') l allparams just_struct vt
  let gsigmaS = getSig src
      gsigmaT = getSig tar
  G_sign lidS sigmaS <- return gsigmaS
  G_sign lidT sigmaT <- return gsigmaT
  gsis1 <- adj $ Syntax.AS_Structured.homogenizeGM (Logic lidS) gsis
  G_symb_map_items_list lid sis <- return gsis1
  sigmaS' <- rcoerce lid lidS (headPos pos) sigmaS
  sigmaT' <- rcoerce lid lidT (headPos pos) sigmaT
  mor <- if just_struct then return (ide lid sigmaS')
           else do
             rmap <- adj $ stat_symb_map_items lid sis
             adj $ induced_from_to_morphism lid rmap sigmaS' sigmaT'
  nodeS <- maybeToResult (headPos pos) 
         "Internal error: empty source spec of view" (getNode src)
  nodeT <- maybeToResult (headPos pos) 
         "Internal error: empty source spec of view" (getNode tar)
  let gmor = gEmbed (G_morphism lid mor)
      link = (nodeS,nodeT,DGLink {
               dgl_morphism = gmor,
               dgl_type = GlobalThm Open None Open,
	           -- 'Open' for conserv correct?
               dgl_origin = DGView vn})
      vsig = (src,gmor,(imp,params,parsig,tar))
  if Map.member vn genv 
   then plain_error (View_defn vn gen' vt' gsis pos,gctx,l,libenv)
                    ("Name "++showPretty vn " already defined")
                    (headPos pos)
   else return (View_defn vn gen' vt' gsis pos,
                (gannos,
                 Map.insert vn (ViewEntry vsig) genv,
                 insEdge link dg''),
                l,
                libenv)


ana_ITEM_NAME_OR_MAP ln genv' res (Item_name name,pos) = 
  ana_ITEM_NAME_OR_MAP1 ln genv' res name name pos
ana_ITEM_NAME_OR_MAP ln genv' res (Item_name_map old new _, pos) = 
  ana_ITEM_NAME_OR_MAP1 ln genv' res old new pos

ana_ITEM_NAME_OR_MAP1 ln genv' res old new pos = do
  (genv,dg) <- res
  entry <- maybeToResult pos 
            (showPretty old " not found") (Map.lookup old genv')
  case Map.lookup new genv of
    Nothing -> return ()
    Just _ -> fatal_error (showPretty new " already used") pos 
  case entry of
    SpecEntry extsig ->
      let (dg1,extsig1) = refExtsig ln dg (Just new) extsig
          genv1 = Map.insert new (SpecEntry extsig1) genv
       in return (genv1,dg1)
    ViewEntry vsig -> 
      let (dg1,vsig1) = refViewsig ln dg vsig
          genv1 = Map.insert new (ViewEntry vsig1) genv
      in return (genv1,dg1)
    ArchEntry asig -> ana_err "arch spec download"
    UnitEntry usig -> ana_err "unit spec download"

refNodesig ln (dg,refdNodes) (name,NodeSig(n,sigma)) =
  let node_contents = DGRef {
        dgn_renamed = name,
        dgn_libname = ln,
        dgn_node = n }
      [node] = newNodes 0 dg
   in (insNode (node,node_contents) dg, NodeSig(node,sigma) : refdNodes)
refNodesig ln (dg,refdNodes) (_,EmptyNode l) =
  (dg,EmptyNode l : refdNodes)

refNodesigs ln dg nodes =
  (dg',reverse nodes')
  where (dg', nodes') = foldl (refNodesig ln) (dg,[]) nodes

refExtsig ln dg name (imps,params,gsigmaP,body) =
  (dg1,(imps1,params1,gsigmaP,body1))
  where
  params' = map (\x -> (Nothing,x)) params
  (dg1,imps1:body1:params1) =  
    refNodesigs ln dg
       ((Nothing,imps):(name,body):params')

refViewsig ln dg (src,mor,extsig) =
  (dg2,(src1,mor,extsig1))
  where
  (_,[src1]) = refNodesigs ln dg [(Nothing,src)]
  (dg2,extsig1) = refExtsig ln dg Nothing extsig


