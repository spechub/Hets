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
    ( anaLibFileOrGetEnv
    , ana_LIB_DEFN
    , anaSourceFile
    ) where

import Logic.Logic
import Logic.Grothendieck

import Syntax.AS_Structured
import Syntax.AS_Library

import Static.GTheory
import Static.DevGraph
import Static.AnalysisStructured
import Static.AnalysisArchitecture

import Common.AS_Annotation hiding (isAxiom, isDef)
import Common.GlobalAnnotations
import Common.ConvertGlobalAnnos
import Common.AnalyseAnnos
import Common.Result
import Common.ResultT
import Common.LibName
import Common.Keywords
import Common.Id

import Driver.Options
import Driver.ReadFn
import Driver.WriteLibDefn

import Data.Graph.Inductive.Graph
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List

import Control.Monad
import Control.Monad.Trans

import System.Directory
import System.Time

-- a set of library names to check for cyclic imports
type LNS = Set.Set LIB_NAME

-- | parsing and static analysis for files
-- Parameters: logic graph, default logic, file name
anaSourceFile :: LogicGraph -> HetcatsOpts -> LNS -> LibEnv -> FilePath
              -> ResultT IO (LIB_NAME, LibEnv)
anaSourceFile lgraph opts topLns libenv fname = ResultT $ do
  fname' <- existsAnSource opts {intype = GuessIn} fname
  case fname' of
    Nothing ->
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
        runResultT $ anaString lgraph opts topLns libenv input absolutePath mt

-- | parsing and static analysis for string (=contents of file)
-- Parameters: logic graph, default logic, contents of file, filename
anaString :: LogicGraph -> HetcatsOpts -> LNS -> LibEnv -> String
          -> FilePath -> ClockTime -> ResultT IO (LIB_NAME, LibEnv)
anaString lgraph opts topLns libenv input file mt = do
  let Result ds mast = read_LIB_DEFN_M lgraph opts file input mt
  case mast of
    Just ast@(Lib_defn ln _ _ ans) -> case analysis opts of
      Skip  -> do
          lift $ putIfVerbose opts 1 $
                  "Skipping static analysis of library " ++ show ln
          ga <- liftR $ addGlobalAnnos emptyGlobalAnnos ans
          lift $ write_LIB_DEFN ga file opts ast
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
          (_,ld, _, lenv0) <- ana_LIB_DEFN lgraph opts topLns libenv ast
          let lenv = markAllHiding lenv0
          case Map.lookup ln lenv of
              Nothing -> error $ "anaString: missing library: " ++ show ln
              Just dg -> lift $ do
                  write_LIB_DEFN (globalAnnos dg) file opts ld
                  when (hasEnvOut opts)
                        (writeFileInfo opts ln file ld dg)
                  return (ln, lenv)
    Nothing -> liftR $ Result ds Nothing

-- lookup or read a library
anaLibFile :: LogicGraph -> HetcatsOpts -> LNS -> LibEnv -> LIB_NAME
           -> ResultT IO (LIB_NAME, LibEnv)
anaLibFile lgraph opts topLns libenv ln =
    let lnstr = show ln in case Map.lookup ln libenv of
    Just _ -> do
        analyzing opts $ "from " ++ lnstr
        return (ln, libenv)
    Nothing -> do
        putMessageIORes opts 1 $ "Downloading " ++ lnstr ++ " ..."
        res <- anaLibFileOrGetEnv lgraph
            (if recurse opts then opts else opts { outtypes = [] })
            (Set.insert ln topLns) libenv ln $ libNameToFile opts ln
        putMessageIORes opts 1 $ "... loaded " ++ lnstr
        return res

-- | lookup or read a library
anaLibFileOrGetEnv :: LogicGraph -> HetcatsOpts -> LNS -> LibEnv
                   -> LIB_NAME -> FilePath -> ResultT IO (LIB_NAME, LibEnv)
anaLibFileOrGetEnv lgraph opts topLns libenv libname file = ResultT $ do
     let envFile = rmSuffix file ++ envSuffix
     recent_envFile <- checkRecentEnv opts envFile file
     if recent_envFile
        then do
             mgc <- readVerbose opts libname envFile
             case mgc of
                 Nothing -> runResultT $ do
                     lift $ putIfVerbose opts 1 $ "Deleting " ++ envFile
                     lift $ removeFile envFile
                     anaSourceFile lgraph opts topLns libenv file
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
                                    else fmap snd $ anaLibFile lgraph
                                         opts topLns p_libEnv ln
                               else ioLibEnv)
                         (return $ Map.insert libname gc libenv)
                         $ labNodesDG gc
                     return $ Result ds $ fmap
                                ( \ rEnv -> (libname, rEnv)) mEnv
        else runResultT $ anaSourceFile lgraph opts topLns libenv file

-- | analyze a LIB_DEFN
-- Parameters: logic graph, default logic, opts, library env, LIB_DEFN
-- call this function as follows:
-- do Result diags res <- runResultT (ana_LIB_DEFN ...)
--    mapM_ (putStrLn . show) diags
ana_LIB_DEFN :: LogicGraph -> HetcatsOpts -> LNS -> LibEnv -> LIB_DEFN
             -> ResultT IO (LIB_NAME, LIB_DEFN, DGraph, LibEnv)
ana_LIB_DEFN lgraph opts topLns libenv (Lib_defn ln alibItems pos ans) = do
  gannos <- showDiags1 opts $ liftR $ addGlobalAnnos emptyGlobalAnnos ans
  let dg = emptyDG
  (libItems', dg1, libenv', _) <- foldM ana
      ([], dg { globalAnnos = gannos }, libenv, lgraph) (map item alibItems)
  return (ln, Lib_defn ln
      (map (uncurry replaceAnnoted) (zip (reverse libItems') alibItems))
      pos ans, dg1, Map.insert ln dg1 libenv')
  where
  ana (libItems', dg1, libenv1, lG) libItem =
    let newLG = case libItems' of
          [] -> lG { currentLogic = defLogic opts }
          Logic_decl (Logic_name logTok _) _ : _ ->
              lG { currentLogic = tokStr logTok }
          _ -> lG
    in ResultT (do
      Result diags2 res <-
         runResultT $ ana_LIB_ITEM newLG opts topLns libenv1 dg1 libItem
      runResultT $ showDiags1 opts (liftR (Result diags2 res))
      let mRes = case res of
             Just (libItem', dg1', libenv1') ->
                 Just (libItem' : libItems', dg1', libenv1', newLG)
             Nothing -> Nothing
      if outputToStdout opts then
         if hasErrors diags2 then
            fail "Stopped due to errors"
            else runResultT $ liftR $ Result [] mRes
         else runResultT $ liftR $ Result diags2 mRes)

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
ana_GENERICITY :: LogicGraph -> DGraph -> HetcatsOpts -> NodeName
               -> GENERICITY -> Result (GENERICITY, GenericitySig, DGraph)
ana_GENERICITY lg dg opts name
    gen@(Genericity params@(Params psps) imps@(Imported isps) pos) =
  case psps of
  [] -> do -- no parameter ...
    unless (null isps) $ plain_error ()
      "Parameterless specifications must not have imports" pos
    l <- lookupCurrentLogic "GENERICITY" lg
    return (gen, GenericitySig (EmptyNode l) [] $ EmptyNode l, dg)
  _ -> do
   (imps', nsigI, dg') <- ana_IMPORTS lg dg opts (extName "I" name) imps
   case psps of
     [asp] -> do -- one parameter ...
       (sp', nsigP, dg'') <- ana_SPEC False lg dg' nsigI name opts (item asp)
       return (Genericity (Params [replaceAnnoted sp' asp]) imps' pos,
          GenericitySig nsigI [nsigP] $ JustNode nsigP, dg'')
     _ -> do -- ... and more parameters
       (params',nsigPs,dg'') <-
           ana_PARAMS lg dg' nsigI opts (inc name) params
       let adj = adjustPos pos
       gsigmaP <- adj $ gsigManyUnion lg (map getSig nsigPs)
       let (NodeSig node _, dg3) = insGSig dg'' name DGFormalParams gsigmaP
           inslink dgl (NodeSig n sigma) = do
             incl <- adj $ ginclusion lg sigma gsigmaP
             return $ insLink dgl incl globalDef SeeTarget n node
       dg4 <- foldM inslink dg3 nsigPs
       return (Genericity params' imps' pos,
         GenericitySig nsigI nsigPs $ JustNode $ NodeSig node gsigmaP, dg4)

ana_PARAMS :: LogicGraph -> DGraph -> MaybeNode
           -> HetcatsOpts -> NodeName -> PARAMS
           -> Result (PARAMS, [NodeSig], DGraph)
ana_PARAMS lg dg nsigI opts name (Params asps) = do
  (sps', pars, dg', _) <- foldM ana ([], [], dg, name) $ map item asps
  return (Params (map (uncurry replaceAnnoted)
                      (zip (reverse sps') asps)),
          reverse pars, dg')
  where
  ana (sps', pars, dg1, n) sp = do
    (sp', par, dg') <- ana_SPEC False lg dg1 nsigI n opts sp
    return (sp' : sps', par : pars, dg', inc n)

ana_IMPORTS :: LogicGraph -> DGraph -> HetcatsOpts -> NodeName -> IMPORTED
            -> Result (IMPORTED, MaybeNode, DGraph)
ana_IMPORTS lg dg opts name imps@(Imported asps) = do
  l <- lookupCurrentLogic "IMPORTS" lg
  case asps of
    [] -> return (imps, EmptyNode l, dg)
    _ -> do
      let sp = Union asps nullRange
      (Union asps' _, nsig', dg') <-
          ana_SPEC False lg dg (EmptyNode l) name opts sp
      return (Imported asps', JustNode nsig', dg')
    -- ??? emptyExplicit stuff needs to be added here

-- | analyse a LIB_ITEM
ana_LIB_ITEM :: LogicGraph -> HetcatsOpts -> LNS -> LibEnv -> DGraph
             -> LIB_ITEM -> ResultT IO (LIB_ITEM, DGraph, LibEnv)
ana_LIB_ITEM lgraph opts topLns libenv dg itm = case itm of
  Spec_defn spn gen asp pos -> do
    let spstr = tokStr spn
    analyzing opts $ "spec " ++ spstr
    (gen', GenericitySig imp params allparams, dg') <-
      liftR $ ana_GENERICITY lgraph dg opts (extName "P" (makeName spn)) gen
    (sanno1, impliesA) <- liftR $ getSpecAnnos pos asp
    when impliesA $ liftR $ plain_error ()
       "unexpected initial %implies in spec-defn" pos
    (sp', body, dg'') <-
      liftR (anaSpecTop sanno1 True lgraph dg'
             allparams (makeName spn) opts (item asp))
    let libItem' = Spec_defn spn gen' (replaceAnnoted sp' asp) pos
        genv = globalEnv dg
    if Map.member spn genv
      then liftR $ plain_error (libItem', dg'', libenv)
               (alreadyDefined spstr) pos
      else return
        ( libItem'
        , dg'' { globalEnv = Map.insert spn (SpecEntry
                 $ ExtGenSig imp params (getMaybeSig allparams) body) genv }
        , libenv)
  View_defn vn gen vt gsis pos -> do
    analyzing opts $ "view " ++ tokStr vn
    liftR $ ana_VIEW_DEFN lgraph libenv dg opts vn gen vt gsis pos
  Arch_spec_defn asn asp pos -> do
    let asstr = tokStr asn
    analyzing opts $ "arch spec " ++ asstr
    (archSig, dg', asp') <- liftR $ ana_ARCH_SPEC lgraph dg opts $ item asp
    let asd' = Arch_spec_defn asn (replaceAnnoted asp' asp) pos
        genv = globalEnv dg'
    if Map.member asn genv
      then liftR $ plain_error (asd', dg', libenv) (alreadyDefined asstr) pos
      else return (asd', dg'
             { globalEnv = Map.insert asn (ArchEntry archSig) genv },
             libenv)
  Unit_spec_defn usn usp pos -> do
    let usstr = tokStr usn
    analyzing opts $ "unit spec " ++ usstr
    l <- lookupCurrentLogic "Unit_spec_defn" lgraph
    (unitSig, dg', usp') <-
        liftR $ ana_UNIT_SPEC lgraph dg opts (EmptyNode l) usp
    let usd' = Unit_spec_defn usn usp' pos
        genv = globalEnv dg'
    if Map.member usn genv
      then liftR $ plain_error (itm, dg', libenv) (alreadyDefined usstr) pos
      else return (usd', dg'
             { globalEnv = Map.insert usn (UnitEntry unitSig) genv },
             libenv)
  Ref_spec_defn rn _ pos -> do
    let rnstr = tokStr rn
    analyzing opts $ "refinement "
      ++ rnstr ++ "\n  (refinement analysis not implemented yet)"
    let genv = globalEnv dg
    if Map.member rn genv
      then liftR $ plain_error (itm, dg, libenv) (alreadyDefined rnstr) pos
      else return ( itm, dg { globalEnv = Map.insert rn RefEntry genv }
                  , libenv)
  Logic_decl (Logic_name logTok _) _ -> do
    logNm <- lookupLogic "LOGIC DECLARATION:" (tokStr logTok) lgraph
    putMessageIORes opts 1 $ "logic " ++ show logNm
    return (itm, dg, libenv)
  Download_items ln items _ -> if Set.member ln topLns then
    liftR $ mkError "illegal cyclic library import"
      $ Set.map getLIB_ID topLns
    else do
        (ln', libenv') <- anaLibFile lgraph opts topLns libenv ln
        if ln == ln' then case Map.lookup ln libenv' of
          Nothing -> error $ "Internal error: did not find library "
            ++ show ln ++ " available: " ++ show (Map.keys libenv')
          Just dg' -> do
            dg1 <- liftR $ anaItemNamesOrMaps libenv' ln dg' dg items
            return (itm, dg1, libenv')
          else liftR $ mkError ("downloaded library '" ++ show ln'
            ++ "' does not match library name") $ getLIB_ID ln

-- the first DGraph dg' is that of the imported library
anaItemNamesOrMaps :: LibEnv -> LIB_NAME -> DGraph -> DGraph
                   -> [ITEM_NAME_OR_MAP] -> Result DGraph
anaItemNamesOrMaps libenv' ln dg' dg items = do
  (genv1, dg1) <- foldM
    (ana_ITEM_NAME_OR_MAP libenv' ln $ globalEnv dg') (globalEnv dg, dg) items
  gannos'' <- globalAnnos dg `mergeGlobalAnnos` globalAnnos dg'
  return dg1
    { globalAnnos = gannos''
    , globalEnv = genv1 }

-- | analyse genericity and view type and construct gmorphism
ana_VIEW_DEFN :: LogicGraph -> LibEnv -> DGraph -> HetcatsOpts -> SIMPLE_ID
              -> GENERICITY -> VIEW_TYPE -> [G_mapping] -> Range
              -> Result (LIB_ITEM, DGraph, LibEnv)
ana_VIEW_DEFN lgraph libenv dg opts vn gen vt gsis pos = do
  (gen', GenericitySig imp params allparams, dg') <-
       ana_GENERICITY lgraph dg opts (extName "VG" (makeName vn)) gen
  (vt', (src@(NodeSig nodeS gsigmaS)
        , tar@(NodeSig nodeT gsigmaT@(G_sign lidT _ _))), dg'') <-
       ana_VIEW_TYPE lgraph dg' allparams opts (makeName vn) vt
  let genv = globalEnv dg''
  if Map.member vn genv
    then plain_error (View_defn vn gen' vt' gsis pos, dg'', libenv)
                    (alreadyDefined $ tokStr vn) pos
    else do
      (gsigmaS', imor) <- gSigCoerce lgraph gsigmaS (Logic lidT)
      tmor <- gEmbedComorphism imor gsigmaS
      emor <- fmap gEmbed $ ana_Gmaps lgraph opts pos gsigmaS' gsigmaT gsis
      gmor <- comp tmor emor
      let vsig = ExtViewSig src gmor
             $ ExtGenSig imp params (getMaybeSig allparams) tar
      return (View_defn vn gen' vt' gsis pos,
                (insLink dg'' gmor globalThm
                 (DGLinkView vn) nodeS nodeT)
                -- 'LeftOpen' for conserv correct?
                { globalEnv = Map.insert vn (ViewEntry vsig) genv }
               , libenv)

-- | analyze a VIEW_TYPE
-- The first three arguments give the global context
-- The AnyLogic is the current logic
-- The NodeSig is the signature of the parameter of the view
-- flag, whether just the structure shall be analysed
ana_VIEW_TYPE :: LogicGraph -> DGraph -> MaybeNode -> HetcatsOpts
              -> NodeName -> VIEW_TYPE
              -> Result (VIEW_TYPE, (NodeSig, NodeSig), DGraph)
ana_VIEW_TYPE lg dg parSig opts name
              (View_type aspSrc aspTar pos) = do
  l <- lookupCurrentLogic "VIEW_TYPE" lg
  (spSrc', srcNsig, dg') <- adjustPos pos $
     ana_SPEC False lg dg (EmptyNode l) (extName "S" name) opts (item aspSrc)
  (spTar', tarNsig, dg'') <- adjustPos pos $
     ana_SPEC True lg dg' parSig (extName "T" name) opts (item aspTar)
  return (View_type (replaceAnnoted spSrc' aspSrc)
                    (replaceAnnoted spTar' aspTar)
                    pos,
          (srcNsig, tarNsig), dg'')

ana_ITEM_NAME_OR_MAP :: LibEnv -> LIB_NAME -> GlobalEnv
                     -> (GlobalEnv, DGraph) -> ITEM_NAME_OR_MAP
                     -> Result (GlobalEnv, DGraph)
ana_ITEM_NAME_OR_MAP libenv ln genv' res itm =
   ana_ITEM_NAME_OR_MAP1 libenv ln genv' res $ case itm of
     Item_name name -> (name, name)
     Item_name_map old new _ -> (old, new)

-- | Auxiliary function for not yet implemented features
ana_err :: String -> a
ana_err f = error $ "*** Analysis of " ++ f ++ " is not yet implemented!"

ana_ITEM_NAME_OR_MAP1 :: LibEnv -> LIB_NAME -> GlobalEnv
                      -> (GlobalEnv, DGraph) -> (SIMPLE_ID, SIMPLE_ID)
                      -> Result (GlobalEnv, DGraph)
ana_ITEM_NAME_OR_MAP1 libenv ln genv' (genv, dg) (old, new) = do
  entry <- maybeToResult (tokPos old)
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
      refInfo = newRefInfo ln n
      node_contents = newInfoNodeLab (makeMaybeName name) refInfo
        $ noSensGTheory lid sig ind
      node = getNewNodeDG dg
   in case lookupInAllRefNodesDG refInfo dg of
        Just existNode -> (dg, NodeSig existNode sigma)
        Nothing ->
          ( addToRefNodesDG node refInfo $ insNodeDG (node, node_contents) dg
          , NodeSig node sigma)

{- | get to the actual parent which is not a referenced node, so that
     the small chains between nodes in different library can be advoided.
     (details see ticket 5)
-}
getActualParent :: LibEnv -> LIB_NAME -> Node -> (LIB_NAME, Node)
getActualParent libenv ln n =
   let refLab = labDG (lookupDGraph ln libenv) n in
   if isDGRef refLab then
        -- recursively goes to parent of the current node, but
        -- it actually would only be done once
        getActualParent libenv (dgn_libname refLab) (dgn_node refLab)
   else (ln, n)

refNodesigs :: LibEnv -> LIB_NAME -> DGraph -> [(Maybe SIMPLE_ID, NodeSig)]
            -> (DGraph, [NodeSig])
refNodesigs libenv = mapAccumR . refNodesig libenv

refExtsig :: LibEnv -> LIB_NAME -> DGraph -> Maybe SIMPLE_ID -> ExtGenSig
          -> (DGraph, ExtGenSig)
refExtsig libenv ln dg name (ExtGenSig imps params gsigmaP body) = let
  params' = map (\x -> (Nothing,x)) params
  (dg0, body1) = refNodesig libenv ln dg (name, body)
  (dg1, params1) = refNodesigs libenv ln dg0 params'
  (dg2, imps1) = case imps of
                 EmptyNode _ -> (dg1, imps)
                 JustNode ns -> let
                     (dg3, nns) = refNodesig libenv ln dg1 (Nothing, ns)
                     in (dg3, JustNode nns)
  in (dg2, ExtGenSig imps1 params1 gsigmaP body1)

refViewsig :: LibEnv -> LIB_NAME -> DGraph -> ExtViewSig
           -> (DGraph, ExtViewSig)
refViewsig libenv ln dg (ExtViewSig src mor extsig) = let
  (_,[src1]) = refNodesigs libenv ln dg [(Nothing, src)]
  (dg2, extsig1) = refExtsig libenv ln dg Nothing extsig
  in (dg2, ExtViewSig src1 mor extsig1)
