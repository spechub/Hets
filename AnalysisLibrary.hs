{- HetCATS/AnalysisLibrary.hs
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


module AnalysisLibrary
where

import Logic
import LogicRepr
import Grothendieck
import Graph
import DevGraph
import qualified AS_Structured
import Parse_AS_Structured (lookupLogic, library)
import Parsec
import AS_Library
import AnalysisStructured
import AS_Annotation
import GlobalAnnotations
import GlobalAnnotationsFunctions
import Result
import Id
import FiniteMap
import Result


-- for testing
ana_file1 :: LogicGraph -> AnyLogic -> String -> IO DGraph
ana_file1 logicGraph defaultLogic fname = do
  putStrLn ("Reading " ++ fname)
  input <- readFile fname
  let ast = case runParser (library logicGraph) defaultLogic fname input of
              Left err -> error (show err)
              Right ast -> ast
  Result diags res <- ioresToIO (ana_LIB_DEFN logicGraph defaultLogic emptyLibEnv ast)
  sequence (map (putStrLn . show) diags)
  
  return (case res of 
             Just (ln,dg,libenv) -> dg
             Nothing -> empty) 


ana_file :: LogicGraph -> AnyLogic -> LibEnv -> LIB_NAME -> IO LibEnv
ana_file logicGraph defaultLogic libenv libname = do
  let fname = case getLIB_ID libname of
               Indirect_link p _ -> p
               Direct_link _ _ -> error "No direct links implemented yet"
  putStrLn ("Reading " ++ (fname++".casl"))
  input <- readFile (fname++".casl")
  let ast = case runParser (library logicGraph) defaultLogic fname input of
              Left err -> error (show err)
              Right ast -> ast
  Result diags res <- ioresToIO (ana_LIB_DEFN logicGraph defaultLogic libenv ast)
  sequence (map (putStrLn . show) diags)
  return (case res of 
             Just (ln,dg,libenv') -> libenv'
             Nothing -> libenv) 
  

ana_LIB_DEFN :: LogicGraph -> AnyLogic 
                 -> LibEnv -> LIB_DEFN
                 -> IOResult (LIB_NAME,DGraph,LibEnv)

ana_LIB_DEFN lgraph l libenv (Lib_defn ln libItems pos ans) = do
  (gannos',genv,dg,_,libenv') <- foldl ana (return (gannos,emptyFM,empty,l,libenv))
                                   (map item libItems)
  return (ln,dg,addToFM libenv' ln (genv,dg,gannos'))
  where
  gannos = addGlobalAnnos emptyGlobalAnnos ans
  ana res libItem = do
    (gannos1,genv1,dg1,l1,libenv1) <- res
    ana_LIB_ITEM_with_download lgraph l1 libenv1 gannos1 genv1 dg1 l1 libItem

ana_LIB_ITEM_with_download :: LogicGraph -> AnyLogic -> LibEnv -> GlobalAnnos 
                 -> GlobalEnv -> DGraph -> AnyLogic 
                 -> LIB_ITEM
                 -> IOResult (GlobalAnnos,GlobalEnv,DGraph,AnyLogic,LibEnv)

ana_LIB_ITEM_with_download lgraph defl libenv 
           gannos genv dg l (Download_items ln items pos) = do
  -- we take as the default logic for imported libs 
  -- the global default logic
  let items' = zip items (drop 2 pos ++ nullPosList)
  libenv' <- ioToIORes (ana_file lgraph defl libenv ln)
  case lookupFM libenv' ln of
    Nothing -> do
       ioToIORes (putStrLn "Internal error: did not find library")
       return (gannos,genv,dg,l,libenv')
    Just (genv',dg',gannos') -> do
                    -- ??? what to do with gannos' ?
      (genv1,dg1) <- resToIORes (foldl (ana_ITEM_NAME_OR_MAP ln genv') 
                                       (return (genv,dg)) items'
                                 )
      return (gannos,genv1,dg1,l,libenv')

ana_LIB_ITEM_with_download lgraph defl libenv 
   gannos genv dg l libItem =
  IOResult (return (ana_LIB_ITEM lgraph defl libenv gannos genv dg l libItem))

ana_ITEM_NAME_OR_MAP ln genv' res (Item_name name,pos) = 
  ana_ITEM_NAME_OR_MAP1 ln genv' res name name pos
ana_ITEM_NAME_OR_MAP ln genv' res (Item_name_map old new _, pos) = 
  ana_ITEM_NAME_OR_MAP1 ln genv' res old new pos

ana_ITEM_NAME_OR_MAP1 ln genv' res old new pos = do
  (genv,dg) <- res
  entry <- maybeToResult pos 
            (pretty old++" not found") (lookupFM genv' old)
  case lookupFM genv new of
    Nothing -> return ()
    Just _ -> fatal_error (pretty new++" already used") pos 
  case entry of
    SpecEntry extsig ->
      let (dg1,extsig1) = refExtsig ln dg new extsig
          genv1 = addToFM genv new (SpecEntry extsig1)
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

refExtsig ln dg name (imps,params,body) =
  (dg1,(imps1,params1,body1))
  where
  params' = map (\x -> (Nothing,x)) params
  (dg1,imps1:body1:params1) =  
    refNodesigs ln dg
       ((Nothing,imps):(Just name,body):params')

ana_LIB_ITEM :: LogicGraph -> AnyLogic -> LibEnv -> GlobalAnnos 
                 -> GlobalEnv -> DGraph -> AnyLogic 
                 -> LIB_ITEM
                 -> Result (GlobalAnnos,GlobalEnv,DGraph,AnyLogic,LibEnv)

ana_LIB_ITEM lgraph defl libenv gannos genv dg l (Spec_defn spn gen asp pos) = do
  ((imp,params,allparams),dg') <- ana_GENERICITY gannos genv dg l gen
  (body,dg'') <- ana_SPEC gannos genv dg' allparams (Just spn) (item asp)
  if elemFM spn genv 
   then plain_error (gannos,genv,dg,l,libenv)
                    ("Name "++pretty spn++" already defined")
                    (head (pos++nullPosList))
   else return (gannos,addToFM genv spn (SpecEntry (imp,params,body)),dg'',l,libenv)

ana_LIB_ITEM lgraph defl libenv gannos genv dg l (View_defn vn gen vt symmap pos) =
  ana_err "views"

ana_LIB_ITEM lgraph defl libenv gannos genv dg l (Arch_spec_defn asn asp pos) = 
  ana_err "arch spec"

ana_LIB_ITEM lgraph defl libenv gannos genv dg l (Unit_spec_defn usn usp pos) =
  ana_err "unit spec"

ana_LIB_ITEM lgraph defl libenv gannos genv dg l (Download_items ln items pos) =
  ana_err "download"

ana_LIB_ITEM lgraph defl libenv gannos genv dg l (Logic_decl ln pos) = do
  let log = lookupLogic ln lgraph
  return (gannos,genv,dg,log,libenv)
