{- HetCATS/Static/AnalysisLibrary.hs
   $Id$
   Till Mossakowski

   Analysis of libraries

   Follows the extended static semantic rules in:

   T. Mossakowski, S. Autexier, D. Hutter, P. Hoffman:
   CASL Proof calculus.
   Available from http://www.informatik.uni-bremen.de/~till/calculus.ps
   To appear in the CASL book.

   Todo:

-}


module Static.AnalysisLibrary (anaFile, ana_LIB_DEFN)
where

import Logic.Logic
import Logic.Grothendieck
import Common.Lib.Graph
import Static.DevGraph
import qualified Syntax.AS_Structured
import Syntax.Parse_AS_Structured (lookupLogicName,library)
import Common.Lib.Parsec
import Syntax.AS_Library
import Static.AnalysisStructured
import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.AnalyseAnnos
import Common.Result
import Common.Id
import qualified Common.Lib.Map as Map
import Common.Result
import Common.PrettyPrint
import Common.AnnoState
import Options
import System
import List
import Directory

-- | parsing and static analysis for files
-- Parameters: logic graph, default logic, file name
anaFile :: LogicGraph -> AnyLogic -> HetcatsOpts -> String
              -> IO (Maybe (LIB_NAME,LIB_DEFN,DGraph,LibEnv))
anaFile logicGraph defaultLogic opts fname = do
  putIfVerbose opts 1  ("Reading " ++ fname)
  let names = [fname,fname++".spec",fname++".casl"]
  -- look for the first existing file
  existFlags <- sequence (map doesFileExist names)
  let fname' = find fst (zip existFlags names) >>= (return . snd)
  case fname' of
    Nothing -> do
      putStrLn (fname++" not found.")
      return Nothing
    Just fname'' -> do
      input <- readFile fname''
      case runParser (library (defaultLogic,logicGraph)) emptyAnnos
	   fname'' input of
        Left err -> do putStrLn (show err)
                       return Nothing
        Right ast -> do
          Result diags res <-
            ioresToIO (ana_LIB_DEFN logicGraph defaultLogic opts
                                    emptyLibEnv ast)
          -- no diags expected here, since these are handled in ana_LIB_DEFN
          -- sequence (map (putStrLn . show) diags)
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
     -- read and analyze the library,
     res <- anaFile logicGraph defaultLogic opts fname
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

ana_LIB_DEFN lgraph l opts libenv (Lib_defn ln alibItems pos ans) = do
  gannos <- resToIORes $ addGlobalAnnos emptyGlobalAnnos ans
  (libItems',gctx@(_,_,dg),_,libenv') <- 
     foldl ana (return ([],(gannos,Map.empty,empty),l,libenv))
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
         ioresToIO (ana_LIB_ITEM lgraph l1 opts libenv1 gctx1 l1 libItem)
      sequence (map (putStrLn . show) diags)
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

ana_LIB_ITEM lgraph defl opts libenv gctx@(gannos,genv,dg) l 
             (Arch_spec_defn asn asp pos) = do
  ioToIORes (putIfVerbose opts 1  ("Analyzing arch spec "++showPretty asn ""))
  ana_err "arch spec"

ana_LIB_ITEM lgraph defl opts libenv gctx@(gannos,genv,dg) l
             (Unit_spec_defn usn usp pos) = do
  ioToIORes (putIfVerbose opts 1  ("Analyzing unit spec "++showPretty usn ""))
  ana_err "unit spec"

ana_LIB_ITEM lgraph defl opts libenv gctx l 
             (Logic_decl ln pos) = do
  let log = lookupLogicName ln lgraph
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
                    -- ??? what to do with gannos' ?
      (genv1,dg1) <- resToIORes (foldl (ana_ITEM_NAME_OR_MAP ln genv') 
                                       (return (genv,dg)) items'
                                 )
      return (libItem,(gannos,genv1,dg1),l,libenv')


-- ??? Needs to be generalized to views between different logics
ana_VIEW_DEFN lgraph defl libenv gctx@(gannos,genv,dg) l just_struct
              vn gen vt gsis pos = do
  (gen',(imp,params,parsig,allparams),dg') <- 
       ana_GENERICITY lgraph gctx l just_struct gen
  (vt',(src,tar),dg'') <- 
       ana_VIEW_TYPE lgraph (gannos,genv,dg') l allparams just_struct vt
  let gsigmaS = getSig src
      gsigmaT = getSig tar
  G_sign lidS sigmaS <- return gsigmaS
  G_sign lidT sigmaT <- return gsigmaT
  gsis1 <- homogenize (Logic lidS) gsis
  G_symb_map_items_list lid sis <- return gsis1
  sigmaS' <- rcoerce lid lidS (headPos pos) sigmaS
  sigmaT' <- rcoerce lid lidT (headPos pos) sigmaT
  mor <- if just_struct then return (ide lid sigmaS')
           else do
             rmap <- stat_symb_map_items lid sis
             induced_from_to_morphism lid rmap sigmaS' sigmaT'
  nodeS <- maybeToResult nullPos 
         "Internal error: empty source spec of view" (getNode src)
  nodeT <- maybeToResult nullPos 
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
      let (dg1,extsig1) = refExtsig ln dg new extsig
          genv1 = Map.insert new (SpecEntry extsig1) genv
       in return (genv1,dg1)
    ViewEntry vsig -> ana_err "view download"
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
       ((Nothing,imps):(Just name,body):params')


homogenize1 res 
     (Syntax.AS_Structured.G_symb_map (G_symb_map_items_list lid1 sis1)) = do
  (G_symb_map_items_list lid sis) <- res
  sis1' <- rcoerce lid1 lid nullPos sis1
  return (G_symb_map_items_list lid (sis++sis1'))
homogenize1 res _ = res 

homogenize (Logic lid) gsis = 
  foldl homogenize1 (return (G_symb_map_items_list lid [])) gsis 
