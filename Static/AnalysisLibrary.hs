{- |
Module      :  ./Static/AnalysisLibrary.hs
Description :  static analysis of DOL documents and CASL specification libraries
Copyright   :  (c) Till Mossakowski, Uni Magdeburg 2002-2016
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable(Logic)

Static analysis of DOL documents and CASL specification libraries
   Follows the verification semantics sketched in Chap. IV:6
   of the CASL Reference Manual.
   Follows the semantics of DOL documents, DOL OMG standard, clause 10.2.1
-}

module Static.AnalysisLibrary
    ( anaLibFileOrGetEnv
    , anaLibDefn
    , anaSourceFile
    , anaLibItem
    , anaViewDefn
    , LNS
    ) where

import Logic.Logic
import Logic.Grothendieck
import Logic.Coerce
import Logic.Prover

import Syntax.AS_Structured
import Syntax.Print_AS_Structured
import Syntax.Print_AS_Library ()
import Syntax.AS_Library

import Static.GTheory
import Static.DevGraph
import Static.DgUtils
import Static.ComputeTheory
import Static.AnalysisStructured
import Static.AnalysisArchitecture
import Static.ArchDiagram (emptyExtStUnitCtx)

import Common.AS_Annotation hiding (isAxiom, isDef)
import Common.Consistency
import Common.GlobalAnnotations
import Common.ConvertGlobalAnnos
import Common.AnalyseAnnos
import Common.ExtSign
import Common.Result
import Common.ResultT
import Common.LibName
import Common.Id
import Common.IRI
import Common.DocUtils
import qualified Common.Unlit as Unlit
import Common.Utils

import Driver.Options
import Driver.ReadFn
import Driver.ReadLibDefn
import Driver.WriteLibDefn

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Either (lefts, rights)
import Data.List
import Data.Maybe

import Control.Monad
import Control.Monad.Trans

import System.Directory
import System.FilePath

import LF.Twelf2DG
import Framework.Analysis

import GenHyb.WriteFile

import MMT.Hets2mmt (mmtRes)
import Proofs.ComputeColimit

-- a set of library names to check for cyclic imports
type LNS = Set.Set LibName

{- | parsing and static analysis for files
Parameters: logic graph, default logic, file name -}
anaSourceFile :: LogicGraph -> HetcatsOpts -> LNS -> LibEnv -> DGraph
  -> FilePath -> ResultT IO (LibName, LibEnv)
anaSourceFile = anaSource Nothing

anaSource :: Maybe LibName -- ^ suggested library name
  -> LogicGraph -> HetcatsOpts -> LNS -> LibEnv -> DGraph
  -> FilePath -> ResultT IO (LibName, LibEnv)
anaSource mln lg opts topLns libenv initDG origName = ResultT $ do
  let mName = useCatalogURL opts origName
      fname = tryToStripPrefix "file://" mName
      syn = case defSyntax opts of
        "" -> Nothing
        s -> Just $ simpleIdToIRI $ mkSimpleId s
      lgraph = setSyntax syn $ setCurLogic (defLogic opts) lg
  fname' <- getContentAndFileType opts fname
  dir <- getCurrentDirectory
  case fname' of
    Left err -> return $ fail err
    Right (mr, _, file, inputLit) ->
        if any (`isSuffixOf` file) [envSuffix, prfSuffix] then
          return . fail $ "no matching source file for '" ++ fname ++ "' found."
        else let
        input = (if unlit opts then Unlit.unlit else id) inputLit
        libStr = if isAbsolute fname
              then convertFileToLibStr fname
              else dropExtensions fname
        nLn = case mln of
              Nothing | useLibPos opts && not (checkUri fname) ->
                Just $ emptyLibName libStr
              _ -> mln
        fn2 = keepOrigClifName opts origName file
        fnAbs = if isAbsolute fn2 then fn2 else dir </> fn2
        url = if checkUri fn2 then fn2 else "file://" ++ fnAbs
        in
        if runMMT opts then mmtRes fname else
            if takeExtension file /= ('.' : show TwelfIn)
            then runResultT $
                 anaString nLn lgraph opts topLns libenv initDG input url mr
            else do
              res <- anaTwelfFile opts file
              return $ case res of
                Nothing -> fail $ "failed to analyse file: " ++ file
                Just (lname, lenv) -> return (lname, Map.union lenv libenv)

-- | parsing of input string (content of file)
anaString :: Maybe LibName -- ^ suggested library name
  -> LogicGraph -> HetcatsOpts -> LNS -> LibEnv -> DGraph -> String
  -> FilePath -> Maybe String -- ^ mime-type of file
  -> ResultT IO (LibName, LibEnv)
anaString mln lgraph opts topLns libenv initDG input file mr = do
  curDir <- lift getCurrentDirectory -- get full path for parser positions
  let realFileName = curDir </> file
      posFileName = case mln of
          Just gLn | useLibPos opts -> libToFileName gLn
          _ -> if checkUri file then file else realFileName
  lift $ putIfVerbose opts 2 $ "Reading file " ++ file
  libdefns <- readLibDefn lgraph opts mr file posFileName input
  when (null libdefns) . fail $ "failed to read contents of file: " ++ file
  foldM (anaStringAux mln lgraph opts topLns initDG mr file posFileName)
        (error "Static.AnalysisLibrary.anaString", libenv)
    $ case analysis opts of
      Skip -> [last libdefns]
      _ -> libdefns

-- | calling static analysis for parsed library-defn
anaStringAux :: Maybe LibName -- ^ suggested library name
  -> LogicGraph -> HetcatsOpts -> LNS -> DGraph -> Maybe String -> FilePath
  -> FilePath -> (LibName, LibEnv) -> LIB_DEFN -> ResultT IO (LibName, LibEnv)
anaStringAux mln lgraph opts topLns initDG mt file posFileName (_, libenv)
             (Lib_defn pln is' ps ans) = do
  let pm = fst $ partPrefixes ans
      expnd i = fromMaybe i $ expandCurie pm i
      spNs = Set.unions . map (Set.map expnd . getSpecNames)
        $ concatMap (getSpecDef . item) is'
      declNs = Set.fromList . map expnd
        $ concatMap (getDeclSpecNames . item) is'
      missNames = Set.toList $ spNs Set.\\ declNs
      unDecls = map (addDownload True) $ filter
          (isNothing . (`lookupGlobalEnvDG` initDG)) missNames
      is = unDecls ++ is'
      spN = convertFileToLibStr file
      noLibName = getLibId pln == nullIRI
      nIs = case is of
        [Annoted (Spec_defn spn gn as qs) rs [] []]
            | noLibName && null (iriToStringUnsecure spn)
                -> [Annoted (Spec_defn (simpleIdToIRI $ mkSimpleId spN)
                             gn as qs) rs [] []]
        _ -> is
      emptyFilePath = null $ getFilePath pln
      ln = setMimeType mt $ if emptyFilePath then setFilePath posFileName
            $ if noLibName then fromMaybe (emptyLibName spN) mln else pln
           else pln
      ast = Lib_defn ln nIs ps ans
  case analysis opts of
      Skip -> do
          lift $ putIfVerbose opts 1 $
                  "Skipping static analysis of library " ++ show ln
          ga <- liftR $ addGlobalAnnos emptyGlobalAnnos ans
          lift $ writeLibDefn lgraph ga file opts ast
          liftR mzero
      _ -> do
          let libstring = libToFileName ln
          unless (isSuffixOf libstring (dropExtension file)
              || not emptyFilePath) . lift . putIfVerbose opts 1
              $ "### file name '" ++ file ++ "' does not match library name '"
              ++ libstring ++ "'"
          lift $ putIfVerbose opts 1 $ "Analyzing "
              ++ (if noLibName then "file " ++ file ++ " as " else "")
              ++ "library " ++ show ln
          (lnFinal, ld, ga, lenv) <-
              anaLibDefn lgraph opts topLns libenv initDG ast file
          case Map.lookup lnFinal lenv of
              Nothing -> error $ "anaString: missing library: " ++ show lnFinal
              Just dg -> lift $ do
                  writeLibDefn lgraph ga file opts ld
                  when (hasEnvOut opts)
                        (writeFileInfo opts lnFinal file ld dg)
                  return (lnFinal, lenv)

-- lookup or read a library
anaLibFile :: LogicGraph -> HetcatsOpts -> LNS -> LibEnv -> DGraph -> LibName
           -> ResultT IO (LibName, LibEnv)
anaLibFile lgraph opts topLns libenv initDG ln =
    let lnstr = show ln in case find (== ln) $ Map.keys libenv of
    Just ln' -> do
        analyzing opts $ "from " ++ lnstr
        return (ln', libenv)
    Nothing ->
            do
            putMessageIORes opts 1 $ "Downloading " ++ lnstr ++ " ..."
            res <- anaLibFileOrGetEnv lgraph
              (if recurse opts then opts else opts
                      { outtypes = []
                      , unlit = False })
              (Set.insert ln topLns) libenv initDG (Just ln) $ libNameToFile ln
            putMessageIORes opts 1 $ "... loaded " ++ lnstr
            return res

-- | lookup or read a library
anaLibFileOrGetEnv :: LogicGraph -> HetcatsOpts -> LNS -> LibEnv -> DGraph
                   -> Maybe LibName -> FilePath -> ResultT IO (LibName, LibEnv)
anaLibFileOrGetEnv lgraph opts topLns libenv initDG mln file = do
     let envFile = rmSuffix file ++ envSuffix
     recent_envFile <- lift $ checkRecentEnv opts envFile file
     if recent_envFile
        then do
             mgc <- lift $ readVerbose lgraph opts mln envFile
             case mgc of
                 Nothing -> do
                     lift $ putIfVerbose opts 1 $ "Deleting " ++ envFile
                     lift $ removeFile envFile
                     anaSource mln lgraph opts topLns libenv initDG file
                 Just (ld@(Lib_defn ln _ _ _), gc) -> do
                     lift $ writeLibDefn lgraph (globalAnnos gc) file opts ld
                          -- get all DGRefs from DGraph
                     mEnv <- foldl
                         ( \ ioLibEnv labOfDG -> let node = snd labOfDG in
                               if isDGRef node then do
                                 let ln2 = dgn_libname node
                                 p_libEnv <- ioLibEnv
                                 if Map.member ln2 p_libEnv then
                                    return p_libEnv
                                    else fmap snd $ anaLibFile lgraph
                                         opts topLns p_libEnv initDG ln2
                               else ioLibEnv)
                         (return $ Map.insert ln gc libenv)
                         $ labNodesDG gc
                     return (ln, mEnv)
        else anaSource mln lgraph opts topLns libenv initDG file

{- | analyze a LIB_DEFN.
  Parameters: logic graph, default logic, opts, library env, LIB_DEFN.
  Call this function as follows:

>    do Result diags res <- runResultT (anaLibDefn ...)
>       mapM_ (putStrLn . show) diags
-}
anaLibDefn :: LogicGraph -> HetcatsOpts -> LNS -> LibEnv -> DGraph -> LIB_DEFN
  -> FilePath -> ResultT IO (LibName, LIB_DEFN, GlobalAnnos, LibEnv)
anaLibDefn lgraph opts topLns libenv dg (Lib_defn ln alibItems pos ans) file
  = do
  let libStr = libToFileName ln
      isDOLlib = elem ':' libStr
  gannos <- showDiags1 opts $ liftR $ addGlobalAnnos
    (defPrefixGlobalAnnos $ if isDOLlib then file else libStr) ans
  allAnnos <- liftR $ mergeGlobalAnnos (globalAnnos dg) gannos
  (libItems', dg', libenv', _, _) <- foldM (anaLibItemAux opts topLns ln)
      ([], dg { globalAnnos = allAnnos }, libenv
      , lgraph, Map.empty) (map item alibItems)
  let dg1 = computeDGraphTheories libenv' $ markFree libenv'
        $ markHiding libenv' $ fromMaybe dg' $ maybeResult
        $ shortcutUnions dg'
      newLD = Lib_defn ln
        (zipWith replaceAnnoted (reverse libItems') alibItems) pos ans
      dg2 = dg1 { optLibDefn = Just newLD }
  return (ln, newLD, globalAnnos dg2, Map.insert ln dg2 libenv')

shortcutUnions :: DGraph -> Result DGraph
shortcutUnions dgraph = let spNs = getGlobNodes $ globalEnv dgraph in
  foldM (\ dg (n, nl) -> let
  locTh = dgn_theory nl
  innNs = innDG dg n
  in case outDG dg n of
       [(_, t, et@DGLink {dgl_type = lt})]
         | Set.notMember n spNs && null (getThSens locTh) && isGlobalDef lt
           && not (hasOutgoingFreeEdge dg t)
           && length innNs > 1
           && all (\ (_, _, el) -> case dgl_type el of
                ScopedLink Global DefLink (ConsStatus cs None LeftOpen)
                  | cs == getCons lt -> True
                _ -> False) innNs
           && case nodeInfo nl of
                DGNode DGUnion _ -> True
                _ -> False
         -> foldM (\ dg' (s, _, el) -> do
             newMor <- composeMorphisms (dgl_morphism el) $ dgl_morphism et
             return $ insLink dg' newMor
              (dgl_type el) (dgl_origin el) s t) (delNodeDG n dg) innNs
       _ -> return dg) dgraph $ topsortedNodes dgraph

defPrefixGlobalAnnos :: FilePath -> GlobalAnnos
defPrefixGlobalAnnos file = emptyGlobalAnnos
  { prefix_map = Map.singleton ""
    $ fromMaybe nullIRI $ parseIRIReference $ file ++ "?" }

anaLibItemAux :: HetcatsOpts -> LNS -> LibName
  -> ([LIB_ITEM], DGraph, LibEnv, LogicGraph, ExpOverrides) -> LIB_ITEM
  -> ResultT IO ([LIB_ITEM], DGraph, LibEnv, LogicGraph, ExpOverrides)
anaLibItemAux opts topLns ln q@(libItems', dg1, libenv1, lg, eo) libItem = let
  currLog = currentLogic lg
  newOpts = if elem currLog ["DMU", "Framework"] then
              opts { defLogic = currLog } else opts
  in ResultT $ do
      res2@(Result diags2 res) <- runResultT
        $ anaLibItem lg newOpts topLns ln libenv1 dg1 eo libItem
      runResultT $ showDiags1 opts (liftR res2)
      let mRes = case res of
             Just (libItem', dg1', libenv1', newLG, eo') ->
                 Just (libItem' : libItems', dg1', libenv1', newLG, eo')
             Nothing -> Just q
      if outputToStdout opts then
         if hasErrors diags2 then
            fail "Stopped due to errors"
            else runResultT $ liftR $ Result [] mRes
         else runResultT $ liftR $ Result diags2 mRes

putMessageIORes :: HetcatsOpts -> Int -> String -> ResultT IO ()
putMessageIORes opts i msg =
   if outputToStdout opts
   then lift $ putIfVerbose opts i msg
   else liftR $ message () msg

analyzing :: HetcatsOpts -> String -> ResultT IO ()
analyzing opts = putMessageIORes opts 1 . ("Analyzing " ++)

alreadyDefined :: String -> String
alreadyDefined str = "Name " ++ str ++ " already defined"

-- | analyze a GENERICITY
anaGenericity :: LogicGraph -> LibEnv -> LibName -> DGraph -> HetcatsOpts
  -> ExpOverrides -> NodeName -> GENERICITY
  -> Result (GENERICITY, GenSig, DGraph)
anaGenericity lg libEnv ln dg opts eo name
    gen@(Genericity (Params psps) (Imported isps) pos) =
  let ms = currentBaseTheory dg in
  adjustPos pos $ case psps of
  [] -> do -- no parameter ...
    unless (null isps) $ plain_error ()
      "Parameterless specifications must not have imports" pos
    l <- lookupCurrentLogic "GENERICITY" lg
    return (gen, GenSig (EmptyNode l) []
      $ maybe (EmptyNode l) JustNode ms, dg)
  _ -> do
   l <- lookupCurrentLogic "IMPORTS" lg
   let baseNode = maybe (EmptyNode l) JustNode ms
   (imps', nsigI, dg') <- case isps of
     [] -> return ([], baseNode, dg)
     _ -> do
      (is', _, nsig', dgI) <- anaUnion False lg libEnv ln dg baseNode
          (extName "Imports" name) opts eo isps $ getRange isps
      return (is', JustNode nsig', dgI)
   (ps', nsigPs, ns, dg'') <- anaUnion False lg libEnv ln dg' nsigI
          (extName "Parameters" name) opts eo psps $ getRange psps
   return (Genericity (Params ps') (Imported imps') pos,
     GenSig nsigI nsigPs $ JustNode ns, dg'')

expCurieT :: GlobalAnnos -> ExpOverrides -> IRI -> ResultT IO IRI
expCurieT ga eo = liftR . expCurieR ga eo

-- | analyse a LIB_ITEM
anaLibItem :: LogicGraph -> HetcatsOpts -> LNS -> LibName -> LibEnv -> DGraph
  -> ExpOverrides -> LIB_ITEM
  -> ResultT IO (LIB_ITEM, DGraph, LibEnv, LogicGraph, ExpOverrides)
anaLibItem lg opts topLns currLn libenv dg eo itm =
 case itm of
  Spec_defn spn2 gen asp pos -> do
    let spn' = if null (iriToStringUnsecure spn2) then
         simpleIdToIRI $ mkSimpleId "Spec" else spn2
    spn <- expCurieT (globalAnnos dg) eo spn'
    let spstr = iriToStringUnsecure spn
        nName = makeName spn
    analyzing opts $ "spec " ++ spstr
    (gen', gsig@(GenSig _ _args allparams), dg') <-
      liftR $ anaGenericity lg libenv currLn dg opts eo nName gen
    (sanno1, impliesA) <- liftR $ getSpecAnnos pos asp
    when impliesA $ liftR $ plain_error ()
      "unexpected initial %implies in spec-defn" pos
    (sp', body, dg'') <-
      liftR (anaSpecTop sanno1 True lg libenv currLn dg'
            allparams nName opts eo (item asp) pos)
    let libItem' = Spec_defn spn gen' (replaceAnnoted sp' asp) pos
        genv = globalEnv dg
    if Map.member spn genv
      then liftR $ plain_error (libItem', dg'', libenv, lg, eo)
              (alreadyDefined spstr) pos
      else
        -- let (_n, dg''') = addSpecNodeRT dg'' (UnitSig args body) $ show spn
        return
        ( libItem'
        , dg'' { globalEnv = Map.insert spn (SpecEntry
                  $ ExtGenSig gsig body) genv }
        , libenv, lg, eo)
  Entail_defn en' etype pos -> do
    en <- expCurieT (globalAnnos dg) eo en'
    analyzing opts $ "entailment " ++ iriToStringUnsecure en
    liftR $ anaEntailmentDefn lg currLn libenv dg opts eo en etype pos
  View_defn vn' gen vt gsis pos -> do
    vn <- expCurieT (globalAnnos dg) eo vn'
    analyzing opts $ "view " ++ iriToStringUnsecure vn
    liftR $ anaViewDefn lg currLn libenv dg opts eo vn gen vt gsis pos
  Align_defn an' arities atype acorresps _ pos -> do
    an <- expCurieT (globalAnnos dg) eo an'
    analyzing opts $ "alignment " ++ iriToStringUnsecure an
    anaAlignDefn lg currLn libenv dg opts eo an arities atype acorresps pos
  Arch_spec_defn asn' asp pos -> do
    asn <- expCurieT (globalAnnos dg) eo asn'
    let asstr = iriToStringUnsecure asn
    analyzing opts $ "arch spec " ++ asstr
    (_, _, diag, archSig, dg', asp') <- liftR $ anaArchSpec lg libenv currLn dg
      opts eo emptyExtStUnitCtx Nothing $ item asp
    let asd' = Arch_spec_defn asn (replaceAnnoted asp' asp) pos
        genv = globalEnv dg'
    if Map.member asn genv
      then liftR $ plain_error (asd', dg', libenv, lg, eo)
               (alreadyDefined asstr) pos
      else do
            let aName = show asn
                dg'' = updateNodeNameRT dg'
                       (refSource $ getPointerFromRef archSig)
                       True aName
                dg3 = dg'' { archSpecDiags =
                           Map.insert aName diag
                           $ archSpecDiags dg''}
            return (asd', dg3
              { globalEnv = Map.insert asn
                            (ArchOrRefEntry True archSig) genv }
              , libenv, lg, eo)
  Unit_spec_defn usn' usp pos -> do
    usn <- expCurieT (globalAnnos dg) eo usn'
    let usstr = iriToStringUnsecure usn
    analyzing opts $ "unit spec " ++ usstr
    l <- lookupCurrentLogic "Unit_spec_defn" lg
    (rSig, dg', usp') <-
      liftR $ anaUnitSpec lg libenv currLn dg opts eo 
                          usn' (EmptyNode l) Nothing usp
    unitSig <- liftR $ getUnitSigFromRef rSig
    let usd' = Unit_spec_defn usn usp' pos
        genv = globalEnv dg'
    if Map.member usn genv
      then liftR $ plain_error (itm, dg', libenv, lg, eo)
               (alreadyDefined usstr) pos
      else return (usd', dg'
             { globalEnv = Map.insert usn (UnitEntry unitSig) genv },
             libenv, lg, eo)
  Ref_spec_defn rn' rsp pos -> do
    rn <- expCurieT (globalAnnos dg) eo rn'
    let rnstr = iriToStringUnsecure rn
    l <- lookupCurrentLogic "Ref_spec_defn" lg
    (_, _, _, rsig, dg', rsp') <- liftR $ 
        anaRefSpec True lg libenv currLn dg opts eo
      (EmptyNode l) rn emptyExtStUnitCtx Nothing rsp
    analyzing opts $ "ref spec " ++ rnstr
    let rsd' = Ref_spec_defn rn rsp' pos
        genv = globalEnv dg'
    if Map.member rn genv
      then liftR $ plain_error (itm, dg', libenv, lg, eo)
               (alreadyDefined rnstr) pos
      else return ( rsd', dg'
        { globalEnv = Map.insert rn (ArchOrRefEntry False rsig) genv }
        , libenv, lg, eo)
  Logic_decl logN pos -> do
    putMessageIORes opts 1 . show $ prettyLG lg itm
    (mth, newLg) <- liftR
      $ adjustPos pos $ anaSublogic opts logN currLn dg libenv lg
    case mth of
      Nothing ->
        return (itm, dg { currentBaseTheory = Nothing }, libenv, newLg, eo)
      Just (s, (libName, refDG, (_, lbl))) -> do
            -- store th-lbl in newDG
        let dg2 = if libName /= currLn then
              let (s2, (genv, newDG)) = refExtsigAndInsert libenv libName refDG
                    (globalEnv dg, dg) (getName $ dgn_name lbl) s
              in newDG { globalEnv = genv
                       , currentBaseTheory = Just $ extGenBody s2 }
              else dg { currentBaseTheory = Just $ extGenBody s }
        return (itm, dg2, libenv, newLg, eo)
  Network_defn anIri (Network cItems eItems _) pos -> do
    nn <- expCurieT (globalAnnos dg) eo anIri
    let nnstr = iriToStringUnsecure nn
    analyzing opts $ "network " ++ nnstr
    let (cNodes, cEdges) = networkDiagram dg cItems eItems
        diag = makeDiagram dg cNodes cEdges
        genv = globalEnv dg
    if Map.member nn genv 
       then
        liftR $ plain_error (itm, dg, libenv, lg, eo)
               (alreadyDefined nnstr) pos
       else
        return (itm, dg{globalEnv = Map.insert nn (NetworkEntry diag) genv},
                libenv, lg, eo)
  Download_items ln items pos ->
    if Set.member ln topLns then
     liftR $ mkError "illegal cyclic library import"
       $ Set.map getLibId topLns
    else do
        let newOpts = opts { intype = GuessIn }
        (ln', libenv') <- anaLibFile lg newOpts topLns libenv
          (cpIndexMaps dg emptyDG { globalAnnos =
            emptyGlobalAnnos { prefix_map = prefix_map $ globalAnnos dg }}) ln
        unless (ln == ln')
          $ liftR $ warning ()
              (shows ln " does not match internal name " ++ shows ln' "")
              pos
        case Map.lookup ln' libenv' of
          Nothing -> error $ "Internal error: did not find library "
            ++ show ln' ++ " available: " ++ show (Map.keys libenv')
          Just dg' -> do
            let dg0 = cpIndexMaps dg' dg
                fn = libToFileName ln'
                currFn = libToFileName currLn
                (realItems, errs, origItems) = case items of
                  ItemMaps rawIms ->
                    let (ims, warns) = foldr (\ im@(ItemNameMap i mi)
                          (is, ws) -> if Just i == mi then
                            (ItemNameMap i Nothing : is
                            , warning () (show i ++ " item no renamed")
                              (getRange mi) : ws)
                            else (im : is, ws)) ([], []) rawIms
                        expIms = map (expandCurieItemNameMap fn currFn) ims
                        leftExpIms = lefts expIms
                    in if not $ null leftExpIms
                        then ([], leftExpIms, itemNameMapsToIRIs ims)
                        else (rights expIms, warns, itemNameMapsToIRIs ims)
                  UniqueItem i ->
                    let is = Map.keys $ globalEnv dg'
                        ks = case is of
                               [_] -> is
                               _ -> filter (== getLibId ln') is
                    in case ks of
                    [j] -> case expCurie (globalAnnos dg) eo i of
                      Nothing -> ([], [prefixErrorIRI i], [i])
                      Just expI -> case expCurie (globalAnnos dg) eo j of
                        Nothing -> ([], [prefixErrorIRI j], [i, j])
                        Just expJ ->
                            ([ItemNameMap expJ (Just expI)], [], [i, j])
                    _ ->
                     ( []
                     , [ mkError ("non-unique name within imported library: "
                                  ++ intercalate ", " (map show is))
                         ln'], [])
                additionalEo = Map.fromList $ map (\ o -> (o, fn)) origItems
                eo' = Map.unionWith (\ _ p2 -> p2) eo additionalEo
            mapM_ liftR errs
            dg1 <- liftR $ anaItemNamesOrMaps libenv' ln' dg' dg0 realItems
            return (itm, dg1, libenv', lg, eo')
  Newlogic_defn ld _ -> ResultT $ do
    dg' <- anaLogicDef ld dg
    return $ Result [] $ Just (itm, dg', libenv, lg, eo)
  Hlogic_defn hld _ -> ResultT $ do
    dg' <- anaHLogicDef hld dg lg
    return $ Result [] $ Just (itm, dg', libenv, lg, eo)
  Newcomorphism_defn com _ -> ResultT $ do
    dg' <- anaComorphismDef com dg
    return $ Result [] $ Just (itm, dg', libenv, lg, eo)
  _ -> return (itm, dg, libenv, lg, eo)

symbolsOf :: LogicGraph -> G_sign -> G_sign -> [CORRESPONDENCE]
  -> Result (Set.Set (G_symbol, G_symbol))
symbolsOf lg gs1@(G_sign l1 (ExtSign sig1 sys1) _)
 gs2@(G_sign l2 (ExtSign sig2 sys2) _) corresps =
 case corresps of
  [] -> return Set.empty
  c : corresps' -> case c of
    Default_correspondence -> symbolsOf lg gs1 gs2 corresps' -- TO DO
    Correspondence_block _ _ cs -> do
      sPs1 <- symbolsOf lg gs1 gs2 cs
      sPs2 <- symbolsOf lg gs1 gs2 corresps'
      return $ Set.union sPs1 sPs2
    Single_correspondence _ (G_symb_items_list lid1 sis1)
        (G_symb_items_list lid2 sis2) _ _ -> do
      ss1 <- coerceSymbItemsList lid1 l1 "symbolsOf1" sis1
      rs1 <- stat_symb_items l1 sig1 ss1
      ss2 <- coerceSymbItemsList lid2 l2 "symbolsOf2" sis2
      rs2 <- stat_symb_items l2 sig2 ss2
      p <- case (rs1, rs2) of
        ([r1], [r2]) ->
         case
            ( filter (\ sy -> matches l1 sy r1) $ Set.toList sys1
            , filter (\ sy -> matches l2 sy r2) $ Set.toList sys2) of
          ([s1], [s2]) ->
            return (G_symbol l1 s1, G_symbol l2 s2)
          (ll1, ll2) -> 
                 plain_error (G_symbol l1 $ head ll1, G_symbol l2 $ head ll2) -- this is a hack!
                  ("Missing or non-unique symbol match " ++ 
                   "for correspondence\nMatches for first symbol: " ++ 
                   showDoc rs1 "\n" ++
                   showDoc ll1 "\nMatches for second symbol: " ++ 
                   showDoc rs2 "\n" ++
                   showDoc ll2 "\n") 
                  nullRange
        _ -> fail $ "non-unique raw symbols"
      ps <- symbolsOf lg gs1 gs2 corresps'
      return $ Set.insert p ps

-- | analyse an entailment type
-- | analyse genericity and view type and construct gmorphism
anaEntailmentDefn :: LogicGraph -> LibName -> LibEnv -> DGraph -> HetcatsOpts
  -> ExpOverrides -> IRI -> ENTAIL_TYPE -> Range
  -> Result (LIB_ITEM, DGraph, LibEnv, LogicGraph, ExpOverrides)
anaEntailmentDefn lg ln libEnv dg opts eo en et pos = do
  case et of
   Entail_type on1 on2 _ -> do
     case (on1, on2) of
      (MkOms asp1, MkOms asp2) -> do
        let spS = item asp1
            spT = item asp2
            name = makeName en
        l <- lookupCurrentLogic "ENTAIL_DEFN" lg
        (_spSrc', srcNsig, dg') <- anaSpec False True lg libEnv ln 
                          dg (EmptyNode l) (extName "Source" name)
                          opts eo spS $ getRange spS
        (_spTgt', tgtNsig, dg'') <- anaSpec True True lg libEnv ln 
                          dg' (EmptyNode l)
                          (extName "Target" name) opts eo spT $ getRange spT
        incl <- ginclusion lg (getSig tgtNsig) (getSig srcNsig)
        let  dg3 = insLink dg'' incl globalThm SeeSource
                   (getNode tgtNsig) (getNode srcNsig)
             gsig = GenSig (EmptyNode l) [] (EmptyNode l)
        let vsig = ExtViewSig srcNsig incl $ ExtGenSig gsig tgtNsig
        return (Entail_defn en et pos, dg3{
                  globalEnv = Map.insert en (ViewOrStructEntry True vsig)
                              $ globalEnv dg3},
                libEnv, lg, eo)
      _ -> fail "entailment between networks not supported yet"
   _ -> fail "omsinnetwork entailment not supported yet"


-- | analyse genericity and view type and construct gmorphism
anaViewDefn :: LogicGraph -> LibName -> LibEnv -> DGraph -> HetcatsOpts
  -> ExpOverrides -> IRI -> GENERICITY -> VIEW_TYPE
  -> [G_mapping] -> Range
  -> Result (LIB_ITEM, DGraph, LibEnv, LogicGraph, ExpOverrides)
anaViewDefn lg ln libenv dg opts eo vn gen vt gsis pos = do
  let vName = makeName vn
  (gen', gsig@(GenSig _ _ allparams), dg') <-
       anaGenericity lg libenv ln dg opts eo vName gen
  (vt', (src@(NodeSig nodeS gsigmaS)
        , tar@(NodeSig nodeT gsigmaT@(G_sign lidT _ _))), dg'') <-
       anaViewType lg libenv ln dg' allparams opts eo vName vt
  let genv = globalEnv dg''
  if Map.member vn genv
    then plain_error (View_defn vn gen' vt' gsis pos, dg'', libenv, lg, eo)
                    (alreadyDefined $ iriToStringUnsecure vn) pos
    else do
      let (tsis, hsis) = partitionGmaps gsis
      (gsigmaS', tmor) <- if null tsis then do
          (gsigmaS', imor) <- gSigCoerce lg gsigmaS (Logic lidT)
          tmor <- gEmbedComorphism imor gsigmaS
          return (gsigmaS', tmor)
        else do
          mor <- anaRenaming lg allparams gsigmaS opts (Renaming tsis pos)
          let gsigmaS'' = cod mor
          (gsigmaS', imor) <- gSigCoerce lg gsigmaS'' (Logic lidT)
          tmor <- gEmbedComorphism imor gsigmaS''
          fmor <- comp mor tmor
          return (gsigmaS', fmor)
      emor <- fmap gEmbed $ anaGmaps lg opts pos gsigmaS' gsigmaT hsis
      gmor <- comp tmor emor
      let vsig = ExtViewSig src gmor $ ExtGenSig gsig tar
          voidView = nodeS == nodeT && isInclusion gmor
      when voidView $ warning ()
        ("identity mapping of source to same target for view: " ++
            iriToStringUnsecure vn) pos
      return (View_defn vn gen' vt' gsis pos,
                (if voidView then dg'' else insLink dg'' gmor globalThm
                 (DGLinkView vn $ Fitted gsis) nodeS nodeT)
                -- 'LeftOpen' for conserv correct?
                { globalEnv = Map.insert vn (ViewOrStructEntry True vsig) genv }
               , libenv, lg, eo)

{- | analyze a VIEW_TYPE
The first four arguments give the global context
The AnyLogic is the current logic
The NodeSig is the signature of the parameter of the view
flag, whether just the structure shall be analysed -}
anaViewType :: LogicGraph -> LibEnv -> LibName -> DGraph -> MaybeNode -> HetcatsOpts
  -> ExpOverrides
  -> NodeName -> VIEW_TYPE -> Result (VIEW_TYPE, (NodeSig, NodeSig), DGraph)
anaViewType lg libEnv ln dg parSig opts eo name (View_type aspSrc aspTar pos) = do
  -- trace "called anaViewType" $ do
  l <- lookupCurrentLogic "VIEW_TYPE" lg
  let spS = item aspSrc
      spT = item aspTar
  (spSrc', srcNsig, dg') <- anaSpec False True lg libEnv ln dg (EmptyNode l)
    (extName "Source" name) opts eo spS $ getRange spS
  (spTar', tarNsig, dg'') <- anaSpec True True lg libEnv ln dg' parSig
    (extName "Target" name) opts eo spT $ getRange spT
  return (View_type (replaceAnnoted spSrc' aspSrc)
                    (replaceAnnoted spTar' aspTar)
                    pos,
          (srcNsig, tarNsig), dg'')

anaAlignDefn :: LogicGraph -> LibName -> LibEnv -> DGraph -> HetcatsOpts
  -> ExpOverrides -> IRI -> Maybe ALIGN_ARITIES -> VIEW_TYPE
  -> [CORRESPONDENCE] -> Range
  -> ResultT IO (LIB_ITEM, DGraph, LibEnv, LogicGraph, ExpOverrides)
anaAlignDefn lg ln libenv dg opts eo an arities atype acorresps pos = do
     l <- lookupCurrentLogic "Align_defn" lg
     (atype', (src, tar), dg') <- liftR
       $ anaViewType lg libenv ln dg (EmptyNode l) opts eo (makeName an) atype
     let gsig1 = getSig src
         gsig2 = getSig tar
     case (gsig1, gsig2) of
      (G_sign lid1 _ _, G_sign lid2 _ _) ->
       if Logic lid1 == Logic lid2 then do
        -- arities TO DO
        pairsSet <- liftR $ symbolsOf lg gsig1 gsig2 acorresps
        let leftList = map fst $ Set.toList pairsSet
            rightList = map snd $ Set.toList pairsSet
            isTotal gsig sList = Set.fromList sList == symsOfGsign gsig
            isInjective sList = length sList == length (nub sList)
            checkArity sList1 sList2 gsig arity = case arity of
              AA_InjectiveAndTotal -> isTotal gsig sList1 &&
                                      isInjective sList2
              AA_Injective -> isInjective sList2
              AA_Total -> isTotal gsig sList1
              _ -> True
            aCheck = case arities of
                      Nothing -> True
                      Just (Align_arities aleft aright) ->
                       checkArity leftList rightList gsig1 aleft &&
                       checkArity rightList leftList gsig2 aright
        if not aCheck then
          liftR $ mkError "Arities do not check" arities
         else do
         newDg <- do
            -- (A_source, A_target, A_bridge,
            --  A_source -> O1, A_target -> O2)
            (gt1, gt2, gt, gmor1, gmor2) <- liftR $
                generateWAlign an gsig1 gsig2 acorresps
            -- A_source
            let n1 = getNewNodeDG dg'
                labN1 = newInfoNodeLab
                         (makeName $ addSuffixToIRI "_source" an)
                         (newNodeInfo DGAlignment)
                         gt1
                dg1 = insLNodeDG (n1, labN1) dg'
            -- A_target
                n2 = getNewNodeDG dg1
                labN2 = newInfoNodeLab
                         (makeName $ addSuffixToIRI "_target" an)
                         (newNodeInfo DGAlignment)
                         gt2
                dg2 = insLNodeDG (n2, labN2) dg1
             -- A_bridge
                n = getNewNodeDG dg2
                labN = newInfoNodeLab
                         (makeName $ addSuffixToIRI "_bridge" an)
                         (newNodeInfo DGAlignment)
                         gt
                dg3 = insLNodeDG (n, labN) dg2
             -- A_target-> O2
                (_, dg4) = insLEdgeDG
                         (n2, getNode tar, globDefLink gmor2 $ DGLinkAlign an)
                         dg3
             -- A_source -> O1
                (_, dg5) = insLEdgeDG
                        (n1, getNode src, globDefLink gmor1 $ DGLinkAlign an)
                        dg4
             -- inclusion of A_source in A_bridge
            incl1 <- liftR $ ginclusion lg (signOf gt1) $ signOf gt
             -- inclusion of A_target in A_bridge
            incl2 <- liftR $ ginclusion lg (signOf gt2) $ signOf gt
             -- add the inclusions to the dg
            let (_, dg6) = insLEdgeDG
                             (n1, n,
                               globDefLink incl1 $ DGLinkAlign an) dg5
                (_, dg7) = insLEdgeDG
                             (n2, n,
                               globDefLink incl2 $ DGLinkAlign an) dg6
                -- store the alignment in the global env
                asign = WAlign (NodeSig n1 $ signOf gt1) incl1 gmor1
                              (NodeSig n2 $ signOf gt2) incl2 gmor2
                              src tar (NodeSig n $ signOf gt)
            return dg7 {globalEnv = Map.insert an (AlignEntry asign)
                            $ globalEnv dg7}
         let itm = Align_defn an arities atype' acorresps SingleDomain pos
             anstr = iriToStringUnsecure an
         if Map.member an $ globalEnv dg
          then liftR $ plain_error (itm, dg, libenv, lg, eo)
                (alreadyDefined anstr) pos
          else return (itm, newDg, libenv, lg, eo)
       else liftR $ fatal_error
         ("Alignments only work between ontologies in the same logic\n"
         ++ show (prettyLG lg atype)) pos

generateWAlign :: IRI -> G_sign -> G_sign -> [CORRESPONDENCE]
               -> Result (G_theory, G_theory, G_theory, GMorphism, GMorphism)
generateWAlign an
               (G_sign lid1 (ExtSign ssig _) _)
               (G_sign lid2 (ExtSign tsig _) _)
               corrs = do
 tsig' <- coercePlainSign lid2 lid1 "coercePlainSign" tsig
 -- 1. initialize
 let
     sig1 = empty_signature lid1
     sig2 = empty_signature lid1
     sig = empty_signature lid1
     phi1 = Map.empty
     phi2 = Map.empty
 -- 2. for each correspondence (e1,e2,r),
 --    build the bridge ontology (s', sens')
 --    the signatures s1'' and s2'' of the involved symbols
 --    together with the maps (aname:e1 -> e1) and (aname:e2 -> e2)
 -- This is done by corresp2th, in a logic dependent way.
 -- first we check if we must disambiguate names in the bridge ontology
 let flag = let insNames aSet aLid aSItems = foldl (\s n -> Set.insert n s) aSet $
                                              map (symb_items_name aLid) aSItems
                (syms1, syms2) =
                 foldl (\ (set1, set2) c -> case c of
                               Single_correspondence _ (G_symb_items_list lidS1 sitems1)
                                                       (G_symb_items_list lidS2 sitems2) _ _ ->
                                   (insNames set1 lidS1 sitems1,
                                    insNames set2 lidS2 sitems2)
                               _ -> error "only single corrs")
                       (Set.empty, Set.empty) corrs
             in not $ Set.null $ Set.intersection syms1 syms2
 -- then we set a flag in addCorresp to True if disambiguation is needed
 let addCorresp (s1, s2, s, sens, p1, p2) (G_symb_items_list lids1 l1,
                            G_symb_items_list lids2 l2, rrel) = do
       l1' <- coerceSymbItemsList lids1 lid1 "coerceSymbItemsList" l1
       l2' <- coerceSymbItemsList lids2 lid1 "coerceSymbItemsList" l2
       (sigb, senb, s1', s2', eMap1, eMap2) <-
           corresp2th lid1 (iriToStringUnsecure an) flag
                           ssig tsig'
                           l1' l2' p1 p2 rrel
       s1'' <- signature_union lid1 s1 s1'
       s2'' <- signature_union lid1 s2 s2'
       s' <- signature_union lid1 s sigb
       let p1' = Map.union eMap1 p1
           p2' = Map.union eMap2 p2
           sens' = sens ++ senb
       return (s1'', s2'', s', sens', p1', p2')
 (sig1'', sig2'', sig'', sens'', sMap1, sMap2) <- foldM addCorresp
       (sig1, sig2, sig, [], phi1, phi2) $
       map (\c -> case c of
                   Single_correspondence _ s1 s2 (Just rref) _ ->
                     (s1, s2, refToRel rref)
                   _ -> error "only single correspondences for now")
       corrs
 -- 3. make G_ results
 -- gth1 is A_source
 let gth1 = noSensGTheory lid1 (mkExtSign sig1'') startSigId
 -- gth2 is A_target
     gth2 = noSensGTheory lid1 (mkExtSign sig2'') startSigId
 -- gth is A_bridge
     gth = G_theory lid1 Nothing (mkExtSign sig'') startSigId
                                 (toThSens sens'') startThId
 -- prepare the maps for morphism generation
     rsMap1 = Map.mapKeys (symbol_to_raw lid1) $
              Map.map (symbol_to_raw lid1) sMap1
     rsMap2 = Map.mapKeys (symbol_to_raw lid1) $
              Map.map (symbol_to_raw lid1) sMap2
 -- mor1 should go from A_source to O1: sig1'' to ssig
 mor1 <- induced_from_to_morphism
            lid1 rsMap1 (mkExtSign sig1'') (mkExtSign ssig)
 let gmor1 = gEmbed2 (signOf gth1) $ mkG_morphism lid1 mor1
 -- mor2 should go from A_target to O2: sig2'' to tsig'
 mor2 <- {- trace "mor2:" $
         trace ("source: " ++ (show sig2'')) $
         trace ("target: " ++ (show tsig'))  $ -}
         induced_from_to_morphism
            lid1 rsMap2 (mkExtSign sig2'') (mkExtSign tsig')
 let gmor2 = gEmbed2 (signOf gth2) $ mkG_morphism lid1 mor2
 return (gth1, gth2, gth, gmor1, gmor2)

-- the first DGraph dg' is that of the imported library
anaItemNamesOrMaps :: LibEnv -> LibName -> DGraph -> DGraph
  -> [ItemNameMap] -> Result DGraph
anaItemNamesOrMaps libenv' ln refDG dg items = do
  (genv1, dg1) <- foldM
    (anaItemNameOrMap libenv' ln refDG) (globalEnv dg, dg) items
  gannos'' <- mergeGlobalAnnos (globalAnnos refDG) $ globalAnnos dg
  return dg1
    { globalAnnos = gannos''
    , globalEnv = genv1 }

anaItemNameOrMap :: LibEnv -> LibName -> DGraph -> (GlobalEnv, DGraph)
  -> ItemNameMap -> Result (GlobalEnv, DGraph)
anaItemNameOrMap libenv ln refDG res (ItemNameMap old m) =
   anaItemNameOrMap1 libenv ln refDG res (old, fromMaybe old m)

-- | Auxiliary function for not yet implemented features
anaErr :: String -> a
anaErr f = error $ "*** Analysis of " ++ f ++ " is not yet implemented!"

anaItemNameOrMap1 :: LibEnv -> LibName -> DGraph -> (GlobalEnv, DGraph)
  -> (IRI, IRI) -> Result (GlobalEnv, DGraph)
anaItemNameOrMap1 libenv ln refDG (genv, dg) (old, new) = do
  entry <- maybe (notFoundError "item" old) return
            $ lookupGlobalEnvDG old refDG
  maybeToResult (iriPos new) (iriToStringUnsecure new ++ " already used")
    $ case Map.lookup new genv of
    Nothing -> Just ()
    Just _ -> Nothing
  case entry of
    SpecEntry extsig ->
      return $ snd $ refExtsigAndInsert libenv ln refDG (genv, dg) new extsig
    ViewOrStructEntry b vsig ->
      let (dg1, vsig1) = refViewsig libenv ln refDG dg (makeName new) vsig
          genv1 = Map.insert new (ViewOrStructEntry b vsig1) genv
      in return (genv1, dg1)
    UnitEntry _usig -> anaErr "unit spec download"
    AlignEntry _asig -> anaErr "alignment download"
    ArchOrRefEntry b _rsig -> anaErr $ (if b then "arch" else "ref")
      ++ " spec download"
    NetworkEntry _gdiag -> anaErr "network download"

refNodesig :: LibEnv -> LibName -> DGraph -> DGraph -> (NodeName, NodeSig)
           -> (DGraph, NodeSig)
refNodesig libenv refln refDG dg
  (name, NodeSig refn sigma@(G_sign lid sig ind)) =
  let (ln, _, (n, lbl)) =
         lookupRefNode libenv refln refDG refn
      refInfo = newRefInfo ln n
      new = newInfoNodeLab name refInfo
        $ noSensGTheory lid sig ind
      nodeCont = new { globalTheory = globalTheory lbl }
      node = getNewNodeDG dg
   in case lookupInAllRefNodesDG refInfo dg of
        Just existNode -> (dg, NodeSig existNode sigma)
        Nothing ->
          ( insNodeDG (node, nodeCont) dg
          , NodeSig node sigma)

refNodesigs :: LibEnv -> LibName -> DGraph -> DGraph -> [(NodeName, NodeSig)]
            -> (DGraph, [NodeSig])
refNodesigs libenv ln = mapAccumR . refNodesig libenv ln

refExtsigAndInsert :: LibEnv -> LibName -> DGraph -> (GlobalEnv, DGraph)
  -> IRI -> ExtGenSig -> (ExtGenSig, (GlobalEnv, DGraph))
refExtsigAndInsert libenv ln refDG (genv, dg) new extsig =
  let (dg1, extsig1) = refExtsig libenv ln refDG dg (makeName new) extsig
      genv1 = Map.insert new (SpecEntry extsig1) genv
  in (extsig1, (genv1, dg1))

refExtsig :: LibEnv -> LibName -> DGraph -> DGraph -> NodeName -> ExtGenSig
          -> (DGraph, ExtGenSig)
refExtsig libenv ln refDG dg name
  (ExtGenSig (GenSig imps params gsigmaP) body) = let
  pName = extName "Parameters" name
  (dg1, imps1) = case imps of
    EmptyNode _ -> (dg, imps)
    JustNode ns -> let
        (dg0, nns) = refNodesig libenv ln refDG dg (extName "Imports" name, ns)
        in (dg0, JustNode nns)
  (dg2, params1) = refNodesigs libenv ln refDG dg1
      $ snd $ foldr (\ p (n, l) -> let nn = inc n in
              (nn, (nn, p) : l)) (pName, []) params
  (dg3, gsigmaP1) = case gsigmaP of
    EmptyNode _ -> (dg, gsigmaP)
    JustNode ns -> let
        (dg0, nns) = refNodesig libenv ln refDG dg2 (pName, ns)
        in (dg0, JustNode nns)
  (dg4, body1) = refNodesig libenv ln refDG dg3 (name, body)
  in (dg4, ExtGenSig (GenSig imps1 params1 gsigmaP1) body1)

refViewsig :: LibEnv -> LibName -> DGraph -> DGraph -> NodeName -> ExtViewSig
           -> (DGraph, ExtViewSig)
refViewsig libenv ln refDG dg name (ExtViewSig src mor extsig) = let
  (dg1, src1) = refNodesig libenv ln refDG dg (extName "Source" name, src)
  (dg2, extsig1) = refExtsig libenv ln refDG dg1 (extName "Target" name) extsig
  in (dg2, ExtViewSig src1 mor extsig1)

-- BEGIN CURIE expansion

expandCurieItemNameMap :: FilePath -> FilePath -> ItemNameMap
  -> Either (Result ()) ItemNameMap
expandCurieItemNameMap fn newFn (ItemNameMap i1 mi2) =
    case expandCurieByPath fn i1 of
        Just i -> case mi2 of
            Nothing -> Right $ ItemNameMap i mi2
            Just j -> case expandCurieByPath newFn j of
                Nothing -> Left $ prefixErrorIRI j
                mj -> Right $ ItemNameMap i mj
        Nothing -> Left $ prefixErrorIRI i1

itemNameMapsToIRIs :: [ItemNameMap] -> [IRI]
itemNameMapsToIRIs = concatMap (\ (ItemNameMap i mi) -> [i | isNothing mi])

-- END CURIE expansion
