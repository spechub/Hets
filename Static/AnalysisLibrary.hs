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
import Common.GlobalAnnotationsFunctions
import Common.Result
import Common.Id
import qualified Common.Lib.Map as Map
import Common.Result
import Common.PrettyPrint
import Options

-- | parsing and static analysis for files
-- Parameters: logic graph, default logic, file name
anaFile :: LogicGraph -> AnyLogic -> HetcatsOpts -> String
              -> IO (Maybe (LIB_NAME,DGraph,LibEnv))
anaFile logicGraph defaultLogic opts fname = do
  putIfVerbose opts 1  ("Reading " ++ fname)
  input <- readFile fname
  let ast = case runParser (library logicGraph) defaultLogic fname input of
              Left err -> error (show err)
              Right ast -> ast
  Result diags res <- ioresToIO (ana_LIB_DEFN logicGraph defaultLogic emptyLibEnv opts ast)
  sequence (map (putStrLn . show) diags)
  return res


ana_file1 :: LogicGraph -> AnyLogic -> LibEnv -> HetcatsOpts -> LIB_NAME -> IO LibEnv
ana_file1 logicGraph defaultLogic libenv opts libname = do
  case Map.lookup libname libenv of
   Just _ -> return libenv
   Nothing -> do
    let fname = case getLIB_ID libname of
                 Indirect_link p _ -> p
                 Direct_link _ _ -> error "No direct links implemented yet"
    putIfVerbose opts 1  ("Reading " ++ (fname++".casl"))
    input <- readFile (fname++".casl")
    let ast = case runParser (library logicGraph) defaultLogic fname input of
                Left err -> error (show err)
                Right ast -> ast
    Result diags res <- ioresToIO (ana_LIB_DEFN logicGraph defaultLogic libenv opts ast)
    sequence (map (putStrLn . show) diags)
    return (case res of 
               Just (ln,dg,libenv') -> libenv'
               Nothing -> libenv) 
  

-- | analyze a LIB_DEFN
-- Parameters: logic graph, default logic, library env, opts, LIB_DEFN
-- call this function as follows:
-- do Result diags res <- ioresToIO (ana_LIB_DEFN ...)
--    sequence (map (putStrLn . show) diags)
ana_LIB_DEFN :: LogicGraph -> AnyLogic 
                 -> LibEnv -> HetcatsOpts -> LIB_DEFN
                 -> IOResult (LIB_NAME,DGraph,LibEnv)

ana_LIB_DEFN lgraph l libenv opts (Lib_defn ln libItems pos ans) = do
  (gctx@(_,_,dg),_,libenv') <- 
     foldl ana (return ((gannos,Map.empty,empty),l,libenv))
               (map item libItems)
  return (ln,dg,Map.insert ln gctx libenv')
  where
  gannos = addGlobalAnnos emptyGlobalAnnos ans
  ana res libItem = do
    (gctx1,l1,libenv1) <- res
    ana_LIB_ITEM lgraph l1 libenv1 gctx1 l1 opts libItem

-- analyse a LIB_ITEM
-- Parameters: logic graph, default logic, library env
-- global context, current logic, opts, LIB_ITEM
ana_LIB_ITEM :: LogicGraph -> AnyLogic -> LibEnv
                 -> GlobalContext -> AnyLogic -> HetcatsOpts
                 -> LIB_ITEM
                 -> IOResult (GlobalContext,AnyLogic,LibEnv)

ana_LIB_ITEM lgraph defl libenv gctx@(gannos,genv,dg) l opts (Spec_defn spn gen asp pos) = do
  let just_struct = False -- justStruct opts
  ioToIORes (putIfVerbose opts 1  ("Analyzing spec " ++ showPretty spn ""))
  ((imp,params,parsig,allparams),dg') <- resToIORes (ana_GENERICITY gctx l just_struct gen)
  (body,dg'') <- resToIORes (ana_SPEC (gannos,genv,dg') allparams (Just spn) just_struct (item asp))
  if Map.member spn genv 
   then resToIORes (plain_error (gctx,l,libenv)
                                ("Name "++ showPretty spn " already defined")
                                (headPos pos))
   else return ((gannos,
                 Map.insert spn (SpecEntry (imp,params,parsig,body)) genv,
                 dg''),
                l,
                libenv)

ana_LIB_ITEM lgraph defl libenv gctx l opts
             (View_defn vn gen vt gsis pos) = do
  let just_struct = False -- justStruct opts
  ioToIORes (putIfVerbose opts 1  ("Analyzing view " ++ showPretty vn ""))
  resToIORes (ana_VIEW_DEFN lgraph defl libenv gctx l just_struct
                            vn gen vt gsis pos)

ana_LIB_ITEM lgraph defl libenv gctx@(gannos,genv,dg) l opts 
             (Arch_spec_defn asn asp pos) = do
  ioToIORes (putIfVerbose opts 1  ("Analyzing arch spec "++showPretty asn ""))
  ana_err "arch spec"

ana_LIB_ITEM lgraph defl libenv gctx@(gannos,genv,dg) l opts
             (Unit_spec_defn usn usp pos) = do
  ioToIORes (putIfVerbose opts 1  ("Analyzing unit spec "++showPretty usn ""))
  ana_err "unit spec"

ana_LIB_ITEM lgraph defl libenv gctx l opts 
             (Logic_decl ln pos) = do
  let log = lookupLogicName ln lgraph
  ioToIORes (putIfVerbose opts 1  ("logic "++show log))
  return (gctx,log,libenv)

ana_LIB_ITEM lgraph defl libenv gctx@(gannos,genv,dg) l opts 
             (Download_items ln items pos) = do
  -- we take as the default logic for imported libs 
  -- the global default logic
  ioToIORes (putIfVerbose opts 1 ("Analyzing from " ++ showPretty ln "\n"))
  let items' = zip items (drop 2 (pos ++ repeat nullPos))
  libenv' <- ioToIORes (ana_file1 lgraph defl libenv opts ln)
  case Map.lookup ln libenv' of
    Nothing -> do
       ioToIORes (putStrLn ("Internal error: did not find library "++show ln++" available:"++show (Map.keys libenv')))
       return (gctx,l,libenv')
    Just (gannos',genv',dg') -> do
                    -- ??? what to do with gannos' ?
      (genv1,dg1) <- resToIORes (foldl (ana_ITEM_NAME_OR_MAP ln genv') 
                                       (return (genv,dg)) items'
                                 )
      return ((gannos,genv1,dg1),l,libenv')


-- ??? Needs to be generalized to views between different logics
ana_VIEW_DEFN lgraph defl libenv gctx@(gannos,genv,dg) l just_struct
              vn gen vt gsis pos = do
  ((imp,params,parsig,allparams),dg') <- ana_GENERICITY gctx l just_struct gen
  ((src,tar),dg'') <- ana_VIEW_TYPE (gannos,genv,dg') l allparams just_struct vt
  let gsigmaS = getSig src
      gsigmaT = getSig tar
  G_sign lidS sigmaS <- return gsigmaS
  G_sign lidT sigmaT <- return gsigmaT
  gsis1 <- homogenize (Logic lidS) gsis
  G_symb_map_items_list lid sis <- return gsis1
  rmap <- stat_symb_map_items lid sis
  sigmaS' <- rcoerce lid lidS (headPos pos) sigmaS
  sigmaT' <- rcoerce lid lidT (headPos pos) sigmaT
  mor <- induced_from_to_morphism lid rmap sigmaS' sigmaT'
  nodeS <- maybeToResult nullPos 
         "Internal error: empty source spec of view" (getNode src)
  nodeT <- maybeToResult nullPos 
         "Internal error: empty source spec of view" (getNode tar)
  let gmor = gEmbed (G_morphism lid mor)
      link = (nodeS,nodeT,DGLink {
               dgl_morphism = gmor,
               dgl_type = GlobalThm False,
               dgl_origin = DGView vn})
      vsig = (src,gmor,(imp,params,parsig,tar))
  if Map.member vn genv 
   then plain_error (gctx,l,libenv)
                    ("Name "++showPretty vn " already defined")
                    (headPos pos)
   else return ((gannos,
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
