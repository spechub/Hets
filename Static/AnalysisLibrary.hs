{-# LANGUAGE CPP, ScopedTypeVariables #-}
{- |
Module      :  $Header$
Description :  static analysis of CASL specification libraries
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2006
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable(Logic)

Static analysis of CASL specification libraries
   Follows the verification semantics sketched in Chap. IV:6
   of the CASL Reference Manual.
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

import Syntax.AS_Structured
import Syntax.Print_AS_Structured
import Syntax.AS_Library
import Syntax.Parse_AS_Library (useItems)

import Static.GTheory
import Static.DevGraph
import Static.DgUtils
import Static.ComputeTheory
import Static.AnalysisStructured
import Static.AnalysisArchitecture
import Static.ArchDiagram (emptyExtStUnitCtx)

import Common.AS_Annotation hiding (isAxiom, isDef)
import Common.GlobalAnnotations
import Common.ConvertGlobalAnnos
import Common.AnalyseAnnos
import Common.Result
import Common.ResultT
import Common.LibName
import Common.Id
import Common.IRI
import Common.IO
import qualified Common.Unlit as Unlit

import Driver.Options
import Driver.ReadFn
import Driver.WriteLibDefn

#ifndef NOHTTP
import Network.HTTP (simpleHTTP, getRequest, getResponseBody, rspCode, rspReason)
#endif

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List
import Data.Either (lefts, rights)

import Control.Monad
import Control.Monad.Trans
import Control.Exception as Ex (catch)

import Data.Maybe

import System.Directory
import System.FilePath

import LF.Twelf2DG

import Framework.Analysis


-- a set of library names to check for cyclic imports
type LNS = Set.Set LibName

{- | parsing and static analysis for files
Parameters: logic graph, default logic, file name -}
anaSourceFile :: LogicGraph -> HetcatsOpts -> LNS -> LibEnv -> DGraph
  -> FilePath -> ResultT IO (LibName, LibEnv)
anaSourceFile = anaSource Nothing

#ifndef NOHTTP
downloadSource :: HetcatsOpts -> FilePath -> IO (FilePath, String)
downloadSource opts fname = do
  putIfVerbose opts 3 $ "Downloading file " ++ fname
  resp <- simpleHTTP (getRequest fname)
  input <- getResponseBody resp
  case resp of
    Right r -> case rspCode r of
      (2,0,0) -> do
        putIfVerbose opts 3 "Successful"
        return (fname, input)
      (x,y,z) -> do
        let errmsg = "Download of file " ++ fname
                     ++ " yields HTTP error " ++ show x ++ show y ++ show z
                     ++ ": " ++ rspReason r
        putIfVerbose opts 3 errmsg
        fail errmsg
    Left err -> do
      let errmsg = "Download of file " ++ fname ++ " failed: " ++ show err
      putIfVerbose opts 3 errmsg
      fail errmsg

tryDownloadSources :: HetcatsOpts -> [FilePath] -> FilePath
                      -> IO (FilePath, String)
tryDownloadSources opts fnames origname = case fnames of
  [] -> fail $ "Unable to download file " ++ origname ++ "[.*]"
  fname:fnames' -> Ex.catch (downloadSource opts fname)
                   (\(_::IOError) ->
                     tryDownloadSources opts fnames' origname)
#endif

anaSource :: Maybe LibName -- ^ suggested library name
  -> LogicGraph -> HetcatsOpts -> LNS -> LibEnv -> DGraph
  -> FilePath -> ResultT IO (LibName, LibEnv)
anaSource mln lg opts topLns libenv initDG fname =
  let syn = case defSyntax opts of
        "" -> Nothing
        s -> Just $ simpleIdToIRI $ mkSimpleId s
      lgraph = setSyntax syn $ setCurLogic (defLogic opts) lg in ResultT $
#ifndef NOHTTP
  if checkUri fname then do
    (fname', input) <-
      tryDownloadSources opts (getOntoFileNames opts fname) fname
    runResultT $ anaString mln lgraph opts topLns libenv initDG input fname'
  else
#endif
  do
  fname' <- findFileOfLibName opts fname
  case fname' of
    Nothing ->
        return $ fail $ "no file for library '" ++ fname ++ "' found."
    Just file ->
        if any (`isSuffixOf` file) [envSuffix, prfSuffix] then
          return $ fail $ "no matching source file for '" ++ fname ++ "' found."
        else do
        inputLit <- readEncFile (ioEncoding opts) file
        let input = (if unlit opts then Unlit.unlit else id) inputLit
            libStr = if isAbsolute fname
              then convertFileToLibStr fname
              else dropExtensions fname
            nLn = case mln of
              Nothing | useLibPos opts ->
                Just $ emptyLibName libStr
              _ -> mln
        putIfVerbose opts 2 $ "Reading file " ++ file
        if takeExtension file /= ('.' : show TwelfIn)
           then runResultT $
                   anaString nLn lgraph opts topLns libenv initDG input file
           else do
             res <- anaTwelfFile opts file
             case res of
                  Nothing -> fail ""
                  Just (lname, lenv) -> return $ Result [] $
                      Just (lname, Map.union lenv libenv)

{- | parsing and static analysis for string (=contents of file)
Parameters: logic graph, default logic, contents of file, filename -}
anaString :: Maybe LibName -- ^ suggested library name
  -> LogicGraph -> HetcatsOpts -> LNS -> LibEnv -> DGraph -> String
  -> FilePath -> ResultT IO (LibName, LibEnv)
anaString mln lgraph opts topLns libenv initDG input file = do
  curDir <- lift getCurrentDirectory -- get full path for parser positions
  let realFileName = curDir </> file
      posFileName = case mln of
          Just gLn | useLibPos opts -> show $ getLibId gLn
          _ -> if checkUri file then file else realFileName

  Lib_defn pln is ps ans <- readLibDefnAux lgraph opts file posFileName input

  let noSuffixFile = rmSuffix file
      spN = convertFileToLibStr file
      noLibName = null $ show $ getLibId pln
      nIs = case is of
        [Annoted (Spec_defn spn gn as qs) rs [] []]
            | noLibName && null (iriToStringUnsecure spn)
                -> [Annoted (Spec_defn (simpleIdToIRI $ mkSimpleId spN)
                             gn as qs) rs [] []]
        _ -> is
      ln = setFilePath posFileName
            $ if noLibName then fromMaybe (emptyLibName spN) mln else pln
      ast = Lib_defn ln nIs ps ans
  case analysis opts of
      Skip -> do
          lift $ putIfVerbose opts 1 $
                  "Skipping static analysis of library " ++ show ln
          ga <- liftR $ addGlobalAnnos emptyGlobalAnnos ans
          lift $ writeLibDefn lgraph ga file opts ast
          liftR mzero
      _ -> do
          let libstring = show $ getLibId ln
          unless (isSuffixOf libstring noSuffixFile) $ lift
              $ putIfVerbose opts 1
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
    let lnstr = show ln in case Map.lookup ln libenv of
    Just _ -> do
        analyzing opts $ "from " ++ lnstr
        return (ln, libenv)
    Nothing -> do
            putMessageIORes opts 1 $ "Downloading " ++ lnstr ++ " ..."
            res <- anaLibFileOrGetEnv lgraph
              (if recurse opts then opts else opts
                      { outtypes = []
                      , unlit = False })
              (Set.insert ln topLns) libenv initDG ln $ libNameToFile ln
            putMessageIORes opts 1 $ "... loaded " ++ lnstr
            return res

-- | lookup or read a library
anaLibFileOrGetEnv :: LogicGraph -> HetcatsOpts -> LNS -> LibEnv -> DGraph
                   -> LibName -> FilePath -> ResultT IO (LibName, LibEnv)
anaLibFileOrGetEnv lgraph opts topLns libenv initDG ln file = ResultT $ do
     let envFile = rmSuffix file ++ envSuffix
     recent_envFile <- checkRecentEnv opts envFile file
     if recent_envFile
        then do
             mgc <- readVerbose lgraph opts ln envFile
             case mgc of
                 Nothing -> runResultT $ do
                     lift $ putIfVerbose opts 1 $ "Deleting " ++ envFile
                     lift $ removeFile envFile
                     anaSource (Just ln) lgraph opts topLns libenv initDG file
                 Just (ld, gc) -> do
                     writeLibDefn lgraph (globalAnnos gc) file opts ld
                          -- get all DGRefs from DGraph
                     Result ds mEnv <- runResultT $ foldl
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
                     return $ Result ds $ fmap
                                ( \ rEnv -> (ln, rEnv)) mEnv
        else runResultT
          $ anaSource (Just ln) lgraph opts topLns libenv initDG file

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
  let libStr = show (getLibId ln)
      isDOLlib = elem ':' libStr
  gannos <- showDiags1 opts $ liftR $ addGlobalAnnos
    (defPrefixGlobalAnnos $ if isDOLlib then file else libStr) ans
  (libItems', dg', libenv', _, _) <- foldM (anaLibItemAux opts topLns ln)
      ([], dg { globalAnnos = gannos }, libenv
      , lgraph, Map.empty) (map item alibItems)
  let dg1 = computeDGraphTheories libenv' $ markFree libenv' $
            markHiding libenv' dg'
      newLD = Lib_defn ln
        (zipWith replaceAnnoted (reverse libItems') alibItems) pos ans
      dg2 = dg1 { optLibDefn = Just newLD }
  return (ln, newLD, globalAnnos dg2, Map.insert ln dg2 libenv')

defPrefixGlobalAnnos :: FilePath -> GlobalAnnos
defPrefixGlobalAnnos file = emptyGlobalAnnos
  { prefix_map = Map.singleton ""
    $ fromMaybe nullIRI $ parseIRIReference $ file ++ "#" }

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
anaGenericity :: LogicGraph -> LibName -> DGraph -> HetcatsOpts
  -> ExpOverrides -> NodeName -> GENERICITY
  -> Result (GENERICITY, GenSig, DGraph)
anaGenericity lg ln dg opts eo name
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
      (is', _, nsig', dgI) <- anaUnion False lg ln dg baseNode
          (extName "Imports" name) opts eo isps
      return (is', JustNode nsig', dgI)
   (ps', nsigPs, ns, dg'') <- anaUnion False lg ln dg' nsigI
          (extName "Parameters" name) opts eo psps
   return (Genericity (Params ps') (Imported imps') pos,
     GenSig nsigI nsigPs $ JustNode ns, dg'')

-- | analyse a LIB_ITEM
anaLibItem :: LogicGraph -> HetcatsOpts -> LNS -> LibName -> LibEnv -> DGraph
  -> ExpOverrides -> LIB_ITEM
  -> ResultT IO (LIB_ITEM, DGraph, LibEnv, LogicGraph, ExpOverrides)
anaLibItem lg opts topLns currLn libenv dg eo itm =
 case itm of
  Spec_defn spn2 gen asp pos -> let
    spn' = if null (iriToStringUnsecure spn2) then
         simpleIdToIRI $ mkSimpleId "Spec" else spn2
    in case expCurie (globalAnnos dg) eo spn' of
   Nothing -> liftR $ prefixErrorIRI spn'
   Just spn -> do
    let spstr = iriToStringUnsecure spn
        nName = makeName spn
    analyzing opts $ "spec " ++ spstr
    (gen', gsig@(GenSig _ _args allparams), dg') <-
      liftR $ anaGenericity lg currLn dg opts eo nName gen
    (sanno1, impliesA) <- liftR $ getSpecAnnos pos asp
    when impliesA $ liftR $ plain_error ()
      "unexpected initial %implies in spec-defn" pos
    (sp', body, dg'') <-
      liftR (anaSpecTop sanno1 True lg currLn dg'
            allparams nName opts eo (item asp))
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
  View_defn vn' gen vt gsis pos -> case expCurie (globalAnnos dg) eo vn' of
   Nothing -> liftR $ prefixErrorIRI vn'
   Just vn -> do
    (_, dg', libenv', lg', eo') <- downloadMissingSpecs
                                   vt lg opts topLns currLn libenv dg eo itm 
    analyzing opts $ "view " ++ iriToStringUnsecure vn
    liftR $ anaViewDefn lg' currLn libenv' dg' opts eo' vn gen vt gsis pos
  Arch_spec_defn asn' asp pos -> case expCurie (globalAnnos dg) eo asn' of
   Nothing -> liftR $ prefixErrorIRI asn'
   Just asn -> do
    let asstr = iriToStringUnsecure asn
    analyzing opts $ "arch spec " ++ asstr
    (_, _, diag, archSig, dg', asp') <- liftR $ anaArchSpec lg currLn dg
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
  Unit_spec_defn usn' usp pos -> case expCurie (globalAnnos dg) eo usn' of
   Nothing -> liftR $ prefixErrorIRI usn'
   Just usn -> do
    let usstr = iriToStringUnsecure usn
    analyzing opts $ "unit spec " ++ usstr
    l <- lookupCurrentLogic "Unit_spec_defn" lg
    (rSig, dg', usp') <-
      liftR $ anaUnitSpec lg currLn dg opts eo (EmptyNode l) Nothing usp
    unitSig <- liftR $ getUnitSigFromRef rSig
    let usd' = Unit_spec_defn usn usp' pos
        genv = globalEnv dg'
    if Map.member usn genv
      then liftR $ plain_error (itm, dg', libenv, lg, eo)
               (alreadyDefined usstr) pos
      else return (usd', dg'
             { globalEnv = Map.insert usn (UnitEntry unitSig) genv },
             libenv, lg, eo)
  Ref_spec_defn rn' rsp pos -> case expCurie (globalAnnos dg) eo rn' of
   Nothing -> liftR $ prefixErrorIRI rn'
   Just rn -> do
    let rnstr = iriToStringUnsecure rn
    l <- lookupCurrentLogic "Ref_spec_defn" lg
    (_, _, _, rsig, dg', rsp') <- liftR $ anaRefSpec lg currLn dg opts eo
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
  Download_items ln items pos ->
    if Set.member ln topLns then
     liftR $ mkError "illegal cyclic library import"
       $ Set.map getLibId topLns
    else do
        (ln', libenv') <- anaLibFile lg opts topLns libenv
          (cpIndexMaps dg emptyDG) ln
        unless (ln == ln')
          $ liftR $ warning ()
              (shows ln " does not match internal name " ++ shows ln' "")
              pos
        case Map.lookup ln' libenv' of
          Nothing -> error $ "Internal error: did not find library "
            ++ show ln' ++ " available: " ++ show (Map.keys libenv')
          Just dg' -> do
            let dg0 = cpIndexMaps dg' dg
                fn = show $ getLibId ln'
                currFn = show $ getLibId currLn
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
                        then ([], map fail leftExpIms, itemNameMapsToIRIs ims)
                        else (rights expIms, warns, itemNameMapsToIRIs ims)
                  UniqueItem i -> case Map.keys $ globalEnv dg' of
                    [j] -> case expCurie (globalAnnos dg) eo i of
                      Nothing -> ([], [prefixErrorIRI i], [i])
                      Just expI -> case expCurie (globalAnnos dg) eo j of
                        Nothing -> ([], [prefixErrorIRI j], [i, j])
                        Just expJ ->
                            ([ItemNameMap expJ (Just expI)], [], [i, j])
                    _ ->
                     ( []
                     , [ mkError "non-unique name within imported library"
                         ln'], [])
                additionalEo = Map.fromList $ map (\ o -> (o, fn)) origItems
                eo' = Map.unionWith (\ _ p2 -> p2) eo additionalEo
            mapM_ liftR errs
            dg1 <- liftR $ anaItemNamesOrMaps libenv' ln' dg' dg0 realItems
            return (itm, dg1, libenv', lg, eo')
  Newlogic_defn ld _ -> ResultT $ do
    dg' <- anaLogicDef ld dg
    return $ Result [] $ Just (itm, dg', libenv, lg, eo)
  Newcomorphism_defn com _ -> ResultT $ do
    dg' <- anaComorphismDef com dg
    return $ Result [] $ Just (itm, dg', libenv, lg, eo)
  _ -> return (itm, dg, libenv, lg, eo)

downloadMissingSpecs :: VIEW_TYPE -> LogicGraph -> HetcatsOpts -> LNS -> LibName
                        -> LibEnv -> DGraph -> ExpOverrides -> LIB_ITEM
                        -> ResultT IO (LIB_ITEM, DGraph, LibEnv, LogicGraph,
                                       ExpOverrides)
downloadMissingSpecs (View_type sp1 sp2 _)
  lg opts topLns currLn libenv dg eo itm = do
  let iris = filter (\i -> case expCurie (globalAnnos dg) eo i
                                >>= (\i' -> lookupGlobalEnvDG i' dg) of
                        Nothing -> {- trace (show $ Map.keys $ globalEnv dg) -} True
                        _ -> False) $
             concatMap extractSpecnames (map item [sp1, sp2])
  itms <- useItems iris
  chainAnaLibItems lg opts topLns currLn libenv dg eo itms itm

extractSpecnames :: SPEC -> [SPEC_NAME]
extractSpecnames spec =
  case spec of
    Translation asp _ -> (extractSpecnames . item) asp
    Reduction asp _ -> (extractSpecnames . item) asp
    Union asps _ -> concatMap (extractSpecnames . item) asps
    Extension asps _ -> concatMap (extractSpecnames . item) asps
    Free_spec asp _ -> (extractSpecnames . item) asp
    Cofree_spec asp _ -> (extractSpecnames . item) asp
    Local_spec asp1 asp2 _ -> concatMap (extractSpecnames . item) [asp1, asp2]
    Closed_spec asp _ -> (extractSpecnames . item) asp
    Group asp _ -> (extractSpecnames . item) asp
    Spec_inst specname _ _ -> [specname]
    Qualified_spec _ asp _ -> (extractSpecnames . item) asp
    Data _ _ asp1 asp2 _ -> concatMap (extractSpecnames . item) [asp1, asp2]
    _ -> []

chainAnaLibItems :: LogicGraph -> HetcatsOpts -> LNS -> LibName -> LibEnv
                    -> DGraph -> ExpOverrides -> [LIB_ITEM] -> LIB_ITEM
                    -> ResultT IO (LIB_ITEM, DGraph, LibEnv, LogicGraph,
                                   ExpOverrides)
chainAnaLibItems lg opts topLns currLn libenv dg eo itms defItm =
  case itms of
    [] -> return (defItm, dg, libenv, lg, eo)
    [itm] -> anaLibItem lg opts topLns currLn libenv dg eo itm
    itm:itms' -> do
      (_, dg', libenv', lg', eo') <-
        chainAnaLibItems lg opts topLns currLn libenv dg eo itms' defItm
      anaLibItem lg' opts topLns currLn libenv' dg' eo' itm

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

-- | analyse genericity and view type and construct gmorphism
anaViewDefn :: LogicGraph -> LibName -> LibEnv -> DGraph -> HetcatsOpts
  -> ExpOverrides -> IRI -> GENERICITY -> VIEW_TYPE
  -> [G_mapping] -> Range
  -> Result (LIB_ITEM, DGraph, LibEnv, LogicGraph, ExpOverrides)
anaViewDefn lg ln libenv dg opts eo vn gen vt gsis pos = do
  let vName = makeName vn
  (gen', gsig@(GenSig _ _ allparams), dg') <-
       anaGenericity lg ln dg opts eo vName gen
  (vt', (src@(NodeSig nodeS gsigmaS)
        , tar@(NodeSig nodeT gsigmaT@(G_sign lidT _ _))), dg'') <-
       anaViewType lg ln dg' allparams opts eo vName vt
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
The first three arguments give the global context
The AnyLogic is the current logic
The NodeSig is the signature of the parameter of the view
flag, whether just the structure shall be analysed -}
anaViewType :: LogicGraph -> LibName -> DGraph -> MaybeNode -> HetcatsOpts
  -> ExpOverrides
  -> NodeName -> VIEW_TYPE -> Result (VIEW_TYPE, (NodeSig, NodeSig), DGraph)
anaViewType lg ln dg parSig opts eo name (View_type aspSrc aspTar pos) = do
  l <- lookupCurrentLogic "VIEW_TYPE" lg
  (spSrc', srcNsig, dg') <- adjustPos pos $ anaSpec False lg ln dg (EmptyNode l)
    (extName "Source" name) opts eo (item aspSrc)
  (spTar', tarNsig, dg'') <- adjustPos pos $ anaSpec True lg ln dg' parSig
    (extName "Target" name) opts eo (item aspTar)
  return (View_type (replaceAnnoted spSrc' aspSrc)
                    (replaceAnnoted spTar' aspTar)
                    pos,
          (srcNsig, tarNsig), dg'')

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
    ArchOrRefEntry b _rsig -> anaErr $ (if b then "arch" else "ref")
      ++ " spec download"

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

failPrefixIRI :: IRI -> String
failPrefixIRI i =
  let pos = iriPos i
      posStr = if pos == nullRange then "" else "(" ++ show pos ++ ") "
  in failPrefixStr posStr $ iriToStringShortUnsecure i

failPrefixStr :: String -> String -> String
failPrefixStr pos s = "No prefix found for CURIE \"" ++ s ++
    "\" " ++ pos ++ "or expansion does not yield a valid IRI."

expandCurieItemNameMap :: FilePath -> FilePath -> ItemNameMap
  -> Either String ItemNameMap
expandCurieItemNameMap fn newFn (ItemNameMap i1 mi2) =
    case expandCurieByPath fn i1 of
        Just i -> case mi2 of
            Nothing -> Right $ ItemNameMap i mi2
            Just j -> case expandCurieByPath newFn j of
                Nothing -> Left $ failPrefixIRI j
                mj -> Right $ ItemNameMap i mj
        Nothing -> Left $ failPrefixIRI i1

itemNameMapsToIRIs :: [ItemNameMap] -> [IRI]
itemNameMapsToIRIs = concatMap (\ (ItemNameMap i mi) -> [i | isNothing mi])

-- END CURIE expansion
