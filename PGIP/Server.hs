{- |
Module      :  $Header$
Description :  run hets as server
Copyright   :  (c) Christian Maeder, DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (via imports)

-}

module PGIP.Server (hetsServer) where

import PGIP.Query as Query

import Driver.Options
import Driver.ReadFn
import Driver.Version

import Network.Wai.Handler.Warp
import Network.HTTP.Types (Status, status200, status400, status403, status405)
import Control.Monad.Trans (lift, liftIO)
import qualified Data.Text as T

import Network.Wai
import Network.Wai.Parse

import qualified Data.ByteString.Lazy.Char8 as BS
import qualified Data.ByteString.Char8 as B8

import Static.AnalysisLibrary
import Static.ApplyChanges
import Static.ComputeTheory
import Static.DevGraph
import Static.DgUtils
import Static.DotGraph
import Static.FromXml
import Static.GTheory
import Static.History (changeDGH)
import Static.PrintDevGraph
import Static.ToXml as ToXml

import Syntax.ToXml
import Syntax.Print_AS_Structured

import Interfaces.Command
import Interfaces.CmdAction

import Comorphisms.LogicGraph

import Logic.Prover
import Logic.Grothendieck
import Logic.Comorphism
import Logic.Logic

import Proofs.AbstractState
import Proofs.ConsistencyCheck

import Text.XML.Light
import Text.XML.Light.Cursor hiding (findChild)

import Common.AutoProofUtils
import Common.Doc
import Common.DocUtils (pretty, showGlobalDoc, showDoc)
import Common.ExtSign (ExtSign (..))
import Common.GtkGoal
import Common.LibName
import Common.PrintLaTeX
import Common.Result
import Common.ResultT
import Common.ToXml
import Common.Utils
import Common.XUpdate

import Control.Monad

import qualified Data.IntMap as IntMap
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Char
import Data.IORef
import Data.Function
import Data.List
import Data.Maybe
import Data.Ord
import Data.Graph.Inductive.Graph (lab)
import Data.Time.Clock

import System.Random
import System.Directory
import System.Exit
import System.FilePath
import System.IO

data Session = Session
  { sessLibEnv :: LibEnv
  , sessLibName :: LibName
  , sessKey :: Int
  , _sessStart :: UTCTime }

type SessMap = Map.Map (String, [GlobCmd]) Session
type Cache = IORef (IntMap.IntMap Session, SessMap)

randomKey :: IO Int
randomKey = randomRIO (100000000, 999999999)

sessGraph :: DGQuery -> Session -> Maybe (LibName, DGraph)
sessGraph dgQ (Session le ln _ _) = case dgQ of
  DGQuery _ (Just path) ->
      find (\ (n, _) -> libToFileName n == path)
        $ Map.toList le
  _ -> fmap (\ dg -> (ln, dg)) $ Map.lookup ln le

getVal :: [QueryPair] -> String -> Maybe String
getVal qs = fromMaybe Nothing . (`lookup` qs)

hetsServer :: HetcatsOpts -> IO ()
hetsServer opts1 = do
  tempDir <- getTemporaryDirectory
  let tempHetsLib = tempDir </> "MyHetsLib"
      permFile = tempDir </> "empty.txt"
      opts = opts1 { libdirs = tempHetsLib : libdirs opts1 }
  createDirectoryIfMissing False tempHetsLib
  writeFile permFile ""
  sessRef <- newIORef (IntMap.empty, Map.empty)
  run 8000 $ \ re -> do
   let rhost = shows (remoteHost re) "\n"
       bots = ["180.76.", "77.75.77.", "66.249.", "141.8.147."]
       splitQuery = map (\ (bs, ms) -> (B8.unpack bs, fmap B8.unpack ms))
         $ queryString re
       pathBits = map T.unpack $ pathInfo re
       path = intercalate "/" pathBits
       meth = B8.unpack (requestMethod re)
   liftIO $ do
     time <- getCurrentTime
     createDirectoryIfMissing False tempHetsLib
     (m, _) <- readIORef sessRef
     if isPrefixOf "134.102.204.54" rhost -- nagios-plugins 1.4.15
       then appendFile permFile "."
       else do
       appendFile permFile $ shows time " sessions: "
                    ++ shows (IntMap.size m) "\n"
       appendFile permFile rhost
       appendFile permFile $ shows (requestHeaders re) "\n"
   -- better try to read hosts to exclude from a file
   if any (`isInfixOf` rhost) bots then return $ mkResponse status403 ""
    -- if path could be a RESTfull request, try to parse it
    else if isRESTfull pathBits then liftIO $
      parseRESTfull opts sessRef pathBits splitQuery meth
    -- only otherwise stick to the old response methods
    else case meth of
      "GET" -> liftIO $ if isJust $ lookup "menus" splitQuery
         then mkMenuResponse else do
         dirs@(_ : cs) <- getHetsLibContent opts path splitQuery
         if not (null cs) || null path then mkHtmlPage path dirs
           -- AUTOMATIC PROOFS (parsing)
           else if isJust $ getVal splitQuery "autoproof" then
             let qr k = Query (DGQuery k Nothing) $
                   anaAutoProofQuery splitQuery in do
               Result ds ms <- runResultT $ case readMaybe $ head pathBits of
                 Nothing -> fail "cannot read session id for automatic proofs"
                 Just k' -> getHetsResult opts [] sessRef (qr k')
               return $ case ms of
                 Nothing -> mkResponse status400 $ showRelDiags 1 ds
                 Just s -> mkOkResponse s
           -- AUTOMATIC PROOFS E.N.D.
           else getHetsResponse opts [] sessRef pathBits splitQuery
      "POST" -> do
        (params, files) <- parseRequestBody lbsBackEnd re
        mTmpFile <- liftIO $ case lookup "content"
                   $ map (\ (a, b) -> (B8.unpack a, b)) params of
              Nothing -> return Nothing
              Just areatext -> let content = B8.unpack areatext in
                if all isSpace content then return Nothing else do
                   tmpFile <- getTempFile content "temp.het"
                   copyPermissions permFile tmpFile
                   return $ Just tmpFile
        let res tmpFile =
              getHetsResponse opts [] sessRef [tmpFile] splitQuery
            mRes = maybe (return $ mkResponse status400 "nothing submitted")
              res mTmpFile
        liftIO $ case files of
          [] -> if isJust $ getVal splitQuery "prove" then
               getHetsResponse opts [] sessRef pathBits
                 $ splitQuery ++ map (\ (a, b)
                 -> (B8.unpack a, Just $ B8.unpack b)) params
            else mRes
          [(_, f)] | isNothing $ lookup updateS splitQuery -> do
           let fn = takeFileName $ B8.unpack $ fileName f
           if any isAlphaNum fn then do
             let tmpFile = tempHetsLib </> fn
             BS.writeFile tmpFile $ fileContent f
             copyPermissions permFile tmpFile
             maybe (res tmpFile) res mTmpFile
            else mRes
          _ -> getHetsResponse
                 opts (map snd files) sessRef pathBits splitQuery
      _ -> return $ mkResponse status405 ""

-- extract what we need to know from an autoproof request
anaAutoProofQuery :: [QueryPair] -> QueryKind
anaAutoProofQuery splitQuery = let
  lookup2 = getVal splitQuery
  prover = lookup2 "prover"
  trans = lookup2 "translation"
  timeout = lookup2 "timeout" >>= readMaybe
  include = maybe False (== "on") $ lookup2 "includetheorems"
  nodeSel = filter (/= "includetheorems")
      $ map fst $ filter ((== Just "on") . snd) splitQuery
  prOrCons = case lookup2 "autoproof" of
    Just "proof" -> GlProofs
    Just "cons" -> GlConsistency
    err -> error $ "illegal autoproof method: " ++ show err
  in GlAutoProve $ ProveCmd prOrCons include prover trans timeout nodeSel False

-- quick approach to whether or not the query can be a RESTfull request
isRESTfull :: [String] -> Bool
isRESTfull pathBits = case pathBits of
  [] -> False
  h : _ -> elem h listRESTfullIdentifiers

listRESTfullIdentifiers :: [String]
listRESTfullIdentifiers =
  [ "libraries", "sessions", "menus", "hets-lib", "dir"]
  ++ nodeEdgeIdes ++ newRESTIdes

nodeEdgeIdes :: [String]
nodeEdgeIdes = ["nodes", "edges"]

newRESTIdes :: [String]
newRESTIdes =
  [ "dg", "translate", "provers", "consistency-checkers", "prove"
  , "consistency-check" ]

-- query is analysed and processed in accordance with RESTfull interface
parseRESTfull :: HetcatsOpts -> Cache -> [String] -> [QueryPair]
  -> String -> IO Response
parseRESTfull opts sessRef pathBits splitQuery meth = let
  {- some parameters from the paths query part might be needed more than once
  (when using lookup upon querybits, you need to unpack Maybe twice) -}
  lookup2 = getVal splitQuery
  session = lookup2 "session" >>= readMaybe
  library = lookup2 "library"
  format = lookup2 "format"
  nodeM = lookup2 "node"
  transM = lookup2 "translation"
  proverM = lookup2 "prover"
  consM = lookup2 "consistency-checker"
  inclM = lookup2 "include"
  incl = maybe False (\ s ->
              notElem (map toLower s) ["f", "false"]) inclM
  timeout = lookup2 "timeout" >>= readMaybe
  queryFailure = return . mkResponse status400
    $ "this query does not comply with RESTfull interface: "
    ++ intercalate "/" (map encodeForQuery pathBits)
  -- since used more often, generate full query out of nodeIRI and nodeCmd
  nodeQuery s = NodeQuery $ maybe (Right s) Left (readMaybe s :: Maybe Int)
  parseNodeQuery :: Monad m => String -> Int -> m NodeCommand -> m Query
  parseNodeQuery p sId ncmd = ncmd >>= let
      in return . Query (DGQuery sId (Just p)) . nodeQuery (getFragment p)
  -- call getHetsResult with the properly generated query (Final Result)
  getResponse qr = do
    Result ds ms <- runResultT $ getHetsResult opts [] sessRef qr
    return $ case ms of
      Nothing -> mkResponse status400 $ showRelDiags 1 ds
      Just s -> mkOkResponse s
  -- respond depending on request Method
  in case meth of
    rm | elem rm ["GET", "POST"] -> case pathBits of
      -- show all menu options
      "menus" : [] -> mkMenuResponse
      -- list files from directory
      "dir" : r -> let path' = intercalate "/" r in
        getHetsLibContent opts path' splitQuery >>= mkHtmlPage path'
      -- get dgraph from file
      "hets-lib" : r -> let file = intercalate "/" r in
        getResponse $ Query (NewDGQuery file []) $ DisplayQuery format
      -- get library (complies with get/hets-lib for now)
      "libraries" : libIri : "development_graph" : [] ->
        getResponse $ Query (NewDGQuery libIri []) $ DisplayQuery format
      -- get previously created session
      "sessions" : sessId : cmd -> case readMaybe sessId of
          Nothing -> fail $ "failed to read session number from " ++ sessId
          Just sId ->
            (case nodeM of
              Just ndIri -> parseNodeQuery ndIri sId $ case cmd of
                ["provers"] -> return $ NcProvers GlProofs transM
                ["translations"] -> return $ NcTranslations Nothing
                _ -> fail $ "unknown node command for a GET-request: "
                      ++ intercalate "/" cmd
              Nothing -> fmap (Query (DGQuery sId Nothing)) $ case cmd of
                [] -> return $ DisplayQuery format
                ["provers"] -> return $ GlProvers GlProofs transM
                ["translations"] -> return GlTranslations
                _ -> fail $ "unknown global command for a GET-request: "
                  ++ intercalate "/" cmd) >>= getResponse
      -- get node or edge view
      nodeOrEdge : p : c | elem nodeOrEdge nodeEdgeIdes -> let
        iriPath = takeWhile (/= '#') p
        dgQ = maybe (NewDGQuery (fromMaybe iriPath library) [])
                 (`DGQuery` library) session
        f = getFragment p
        in case elemIndex nodeOrEdge nodeEdgeIdes of
          Just 0 -> let
            i = maybe (Right f) Left $ readMaybe f in
            getResponse $ Query dgQ $ NodeQuery i $ case c of
                ["theory"] -> NcCmd Query.Theory
                _ -> NcCmd Query.Info
          Just 1 -> case readMaybe f of
            Just i -> getResponse $ Query dgQ $ EdgeQuery i "edge"
            Nothing -> fail $ "failed to read edgeId from " ++ f
          _ -> error $ "PGIP.Server.elemIndex " ++ nodeOrEdge
      newIde : libIri : rest -> let cmdList = filter (/= "") rest in
        if elem newIde newRESTIdes && all (`elem` globalCommands) cmdList
        then getResponse . Query (NewDGQuery libIri cmdList) $ case newIde of
           "translate" -> case nodeM of
             Nothing -> GlTranslations
             Just n -> nodeQuery n $ NcTranslations Nothing
           _ | elem newIde ["provers", "consistency-checkers"] ->
             let pm = if newIde == "provers" then GlProofs else GlConsistency
             in case nodeM of
             Nothing -> GlProvers pm transM
             Just n -> nodeQuery n $ NcProvers pm transM
           _ | elem newIde ["prove", "consistency-check"] ->
             let isProve = newIde == "prove"
                 pm = if isProve then GlProofs else GlConsistency
                 pc = ProveCmd pm
                   (not (isProve && isJust inclM) || incl)
                   (if isProve then proverM else consM) transM timeout [] True
             in case nodeM of
             Nothing -> GlAutoProve pc
             Just n -> nodeQuery n $ ProveNode pc
           _ -> DisplayQuery (Just $ fromMaybe "xml" format)
        else queryFailure
      _ -> queryFailure
    "PUT" -> case pathBits of
      {- execute global commands
         TODO load other library ??? -}
      "libraries" : libIri : "proofs" : prId : cmd : [] ->
         case readMaybe prId of
           Nothing -> fail $ "failed to read sessionId from " ++ prId
           Just sessId -> let
             dgQ = DGQuery sessId $ Just libIri in
             getResponse $ Query dgQ $ GlobCmdQuery cmd
      -- execute a proof or calculus request
      "sessions" : sessId : cmd : [] -> case readMaybe sessId of
        Nothing -> fail $ "failed to read sessionId from " ++ sessId
        Just sId -> case cmd of
          "prove" ->
            let pc = ProveCmd GlProofs incl proverM transM timeout [] False
            in case nodeM of
                -- prove all nodes if no singleton is selected
                Nothing -> return $ Query (DGQuery sId Nothing)
                  $ GlAutoProve pc
                -- otherwise run prover for single node only
                Just ndIri -> parseNodeQuery ndIri sId $ return
                  $ ProveNode pc
              >>= getResponse
          -- on other cmd look for (optional) specification of node or edge
          _ -> case (nodeM, lookup2 "edge") of
              -- fail if both are specified
              (Just _, Just _) ->
                fail "please specify only either node or edge"
              -- call command upon a single node
              (Just ndIri, Nothing) -> parseNodeQuery ndIri sId
                $ case lookup cmd $ map (\ a -> (showNodeCmd a, a)) nodeCmds of
                  Just nc -> return $ NcCmd nc
                  _ -> fail $ "unknown node command '" ++ cmd ++ "' "
              -- call (the only) command upon a single edge
              (Nothing, Just edIri) -> case readMaybe $ getFragOfCode edIri of
                Just i -> return $ Query (DGQuery sId Nothing)
                  $ EdgeQuery i "edge"
                Nothing ->
                  fail $ "failed to read edgeId from edgeIRI: " ++ edIri
              -- call of global command
              _ -> return $ Query (DGQuery sId Nothing) $ GlobCmdQuery cmd
           >>= getResponse
      -- fail if request doesn't comply
      _ -> queryFailure
    {- create failure response if request method is not known
    (should never happen) -}
    _ -> return $ mkResponse status405 ""


mkMenuResponse :: IO Response
mkMenuResponse = return $ mkOkResponse $ ppTopElement $ unode "menus" mkMenus

mkMenus :: [Element]
mkMenus = menuTriple "" "Get menu triples" "menus"
  : menuTriple "/DGraph" updateS updateS
  : map (\ (c, _) -> menuTriple "/" (menuTextGlobCmd c) $ cmdlGlobCmd c)
    allGlobLibAct
  ++ map (\ nc -> menuTriple "/DGraph/DGNode" ("Show " ++ nc) nc) nodeCommands
  ++ [menuTriple "/DGraph/DGLink" "Show edge info" "edge"]

menuTriple :: String -> String -> String -> Element
menuTriple q d c = unode "triple"
                [ unode "xquery" q
                , unode "displayname" d
                , unode "command" c ]

mkHtmlString :: FilePath -> [Element] -> String
mkHtmlString path dirs = htmlHead ++ mkHtmlElem
  ("Listing of" ++ if null path then " repository" else ": " ++ path)
  (unode "h1" ("Hets " ++ hetcats_version) : unode "p"
     [ bold "Hompage:"
     , aRef "http://www.dfki.de/cps/hets" "dfki.de/cps/hets"
     , bold "Contact:"
     , aRef "mailto:hets-devel@informatik.uni-bremen.de"
       "hets-devel@informatik.uni-bremen.de" ]
   : headElems path ++ [unode "ul" dirs])

mkHtmlElem :: String -> [Element] -> String
mkHtmlElem title body = ppElement $ unode "html"
      [ unode "head" $ unode "title" title, unode "body" body ]

-- include a script within page (manual tags to avoid encoding)
mkHtmlElemScript :: String -> String -> [Element] -> String
mkHtmlElemScript title scr body = "<html>\n<head>\n"
  ++ ppElement (unode "title" title) ++ "\n<script type=text/javascript>"
  ++ scr ++ "</script>\n</head>\n" ++ ppElement (unode "body" body)
  ++ "</html>"

mkHtmlPage :: FilePath -> [Element] -> IO Response
mkHtmlPage path = return . mkOkResponse . mkHtmlString path

mkResponse :: Status -> String -> Response
mkResponse st = responseLBS st [] . BS.pack

mkOkResponse :: String -> Response
mkOkResponse = mkResponse status200

addNewSess :: String -> [GlobCmd] -> Cache -> Session -> IO Int
addNewSess file cl sessRef sess = do
  k <- randomKey
  let s = sess { sessKey = k }
  atomicModifyIORef sessRef $ \ (m, lm) ->
       ((IntMap.insert k s m, Map.insert (file, cl) s lm), k)

nextSess :: Session -> Cache -> LibEnv -> Int -> IO Session
nextSess sess sessRef newLib k = if k <= 0 then return sess else
    atomicModifyIORef sessRef
      (\ (m, lm) -> case IntMap.lookup k m of
      Nothing -> error "nextSess"
      Just s -> let newSess = s { sessLibEnv = newLib }
        in ((IntMap.insert k newSess m, lm), newSess))

ppDGraph :: DGraph -> Maybe PrettyType -> ResultT IO String
ppDGraph dg mt = let ga = globalAnnos dg in case optLibDefn dg of
    Nothing -> fail "parsed LIB-DEFN not avaible"
    Just ld ->
      let d = prettyLG logicGraph ld
          latex = renderLatex Nothing $ toLatex ga d
      in case mt of
      Just pty -> case pty of
        PrettyXml -> return $ ppTopElement $ xmlLibDefn logicGraph ga ld
        PrettyAscii _ -> return $ renderText ga d ++ "\n"
        PrettyHtml -> return $ htmlHead ++ renderHtml ga d
        PrettyLatex _ -> return latex
      Nothing -> lift $ do
         tmpDir <- getTemporaryDirectory
         tmpFile <- writeTempFile (latexHeader ++ latex ++ latexFooter)
           tmpDir "temp.tex"
         copyPermissions (tmpDir </> "empty.txt") tmpFile
         mapM_ (\ s -> do
            let sty = (</> "hetcasl.sty")
                f = sty s
            ex <- doesFileExist f
            when ex $ copyFile f $ sty tmpDir)
              [ "utils", "Hets/utils"
              , "/home/www.informatik.uni-bremen.de/cofi/hets-tmp" ]
         withinDirectory tmpDir $ do
           (ex1, out1, err1) <- executeProcess "pdflatex" [tmpFile] ""
           (ex2, out2, err2) <- executeProcess "pdflatex" [tmpFile] ""
           let pdfFile = replaceExtension tmpFile "pdf"
           pdf <- doesFileExist pdfFile
           if ex1 == ExitSuccess && ex2 == ExitSuccess && pdf then do
             pdfHdl <- openBinaryFile pdfFile ReadMode
             str <- hGetContents pdfHdl
             when (length str < 0) $ putStrLn "pdf file too large"
             hClose pdfHdl
             return str
             else return $ "could not create pdf:\n"
                  ++ unlines [out1, err1, out2, err2]

getDGraph :: HetcatsOpts -> Cache -> DGQuery
  -> ResultT IO (Session, Int)
getDGraph opts sessRef dgQ = do
 (m, lm) <- lift $ readIORef sessRef
 case dgQ of
  NewDGQuery file cmdList ->
   let cl = map (\ s -> fromJust . find ((== s) . cmdlGlobCmd)
                  $ map fst allGlobLibAct) cmdList
   in case Map.lookup (file, cl) lm of
   Just sess -> return (sess, sessKey sess)
   Nothing -> do
    (ln, le1) <- do
        mf <- lift $ getContent opts file
        case mf of
          Right (f, c) | isDgXmlFile opts f c -> readDGXmlR opts f Map.empty
          _ -> anaSourceFile logicGraph opts
            { outputToStdout = False, useLibPos = True }
            Set.empty emptyLibEnv emptyDG file
    le2 <- foldM (\ e c -> liftR
                  $ fromJust (lookup c allGlobLibAct) ln e) le1 cl
    time <- lift getCurrentTime
    let sess = Session le2 ln 0 time
    k <- lift $ addNewSess file cl sessRef sess
    return (sess, k)
  DGQuery k _ -> case IntMap.lookup k m of
      Nothing -> fail "unknown development graph"
      Just sess -> return (sess, k)

getSVG :: String -> String -> DGraph -> ResultT IO String
getSVG title url dg = do
        (exCode, out, err) <- lift $ executeProcess "dot" ["-Tsvg"]
          $ dotGraph title False url dg
        case exCode of
          ExitSuccess -> liftR $ extractSVG dg out
          _ -> fail err

enrichSVG :: DGraph -> Element -> Element
enrichSVG dg e = processSVG dg $ fromElement e

processSVG :: DGraph -> Cursor -> Element
processSVG dg c = case nextDF c of
  Nothing -> case toTree (root c) of
    Elem e -> e
    _ -> error "processSVG"
  Just c2 -> processSVG dg
    $ modifyContent (addSVGAttribs dg) c2

nodeAttrib :: DGNodeLab -> String
nodeAttrib l = let nt = getRealDGNodeType l in
  (if isRefType nt then "Ref" else "")
  ++ (if hasSenKind (const True) l then
          (if isProvenNode nt then "P" else "Unp") ++ "roven"
          ++ if isProvenCons nt then "Cons" else ""
      else "LocallyEmpty")
  ++ (if isInternalSpec nt then "Internal" else "")
  ++ if labelHasHiding l then "HasIngoingHidingLink" else ""

edgeAttrib :: DGLinkLab -> String
edgeAttrib l = show (pretty $ dgl_type l) ++
  if dglPending l then "IncompleteProofChain" else ""

addSVGAttribs :: DGraph -> Content -> Content
addSVGAttribs dg c = case c of
  Elem e -> case getAttrVal "id" e of
    Just istr | isNat istr -> let i = read istr in
      case getAttrVal "class" e of
      Just "node" -> case lab (dgBody dg) i of
        Nothing -> c
        Just l -> Elem $ add_attr (mkAttr "type" $ nodeAttrib l) e
      Just "edge" -> case getDGLinksById (EdgeId i) dg of
        [(_, _, l)] ->
           Elem $ add_attr (mkAttr "type" $ edgeAttrib l) e
        _ -> c
      _ -> c
    _ -> c
  _ -> c

extractSVG :: DGraph -> String -> Result String
extractSVG dg str = case parseXMLDoc str of
  Nothing -> fail "did not recognize svg element"
  Just e -> return $ showTopElement $ enrichSVG dg e

cmpFilePath :: FilePath -> FilePath -> Ordering
cmpFilePath f1 f2 = case comparing hasTrailingPathSeparator f2 f1 of
  EQ -> compare f1 f2
  c -> c

-- | with the 'old' call of getHetsResponse, anaUri is called upon the path
getHetsResponse :: HetcatsOpts -> [FileInfo BS.ByteString]
  -> Cache -> [String] -> [QueryPair] -> IO Response
getHetsResponse opts updates sessRef pathBits query = do
  Result ds ms <- runResultT $ case anaUri pathBits query
    $ updateS : globalCommands of
    Left err -> fail err
    Right q -> getHetsResult opts updates sessRef q
  return $ case ms of
    Just s | not $ hasErrors ds -> mkOkResponse s
    _ -> mkResponse status400 $ showRelDiags 1 ds

getHetsResult :: HetcatsOpts -> [FileInfo BS.ByteString]
  -> Cache -> Query -> ResultT IO String
getHetsResult opts updates sessRef (Query dgQ qk) = do
      sk@(sess, k) <- getDGraph opts sessRef dgQ
      let libEnv = sessLibEnv sess
      (ln, dg) <- maybe (fail "unknown development graph") return
        $ sessGraph dgQ sess
      let title = libToFileName ln
      svg <- getSVG title ('/' : show k) dg
      case qk of
            DisplayQuery ms -> case ms of
              Just "svg" -> return svg
              Just "xml" -> liftR $ return $ ppTopElement
                $ ToXml.dGraph opts libEnv ln dg
              Just "dot" -> liftR $ return $ dotGraph title False title dg
              Just "symbols" -> liftR $ return $ ppTopElement
                $ ToXml.dgSymbols dg
              Just "session" -> liftR $ return $ ppElement
                $ aRef (mkPath sess ln k) (show k)
              Just str | elem str ppList
                -> ppDGraph dg $ lookup str $ zip ppList prettyList
              _ -> liftR $ return $ sessAns ln svg sk
            GlProvers mp mt -> return $ getFullProverList mp mt dg
            GlTranslations -> return $ getFullComorphList dg
            GlShowProverWindow prOrCons -> showAutoProofWindow dg k prOrCons
            GlAutoProve (ProveCmd prOrCons incl mp mt tl nds xForm) -> do
               (newLib, sens) <-
                 proveMultiNodes xForm prOrCons libEnv ln dg incl mp mt tl nds
               if null sens then return "nothing to prove" else do
                  lift $ nextSess sess sessRef newLib k
                  return $ formatResultsMultiple xForm k sens prOrCons
            GlobCmdQuery s ->
              case find ((s ==) . cmdlGlobCmd . fst) allGlobLibAct of
              Nothing -> if s == updateS then
                case filter ((== ".xupdate") . takeExtension . B8.unpack
                            . fileName) updates of
                ch : _ -> do
                  let str = BS.unpack $ fileContent ch
                  (newLn, newLib) <- dgXUpdate opts str libEnv ln dg
                  newSess <- lift $ nextSess sess sessRef newLib k
                  liftR $ return $ sessAns newLn svg (newSess, k)
                [] -> liftR $ return $ sessAns ln svg sk
                else fail "getHetsResult.GlobCmdQuery"
              Just (_, act) -> do
                newLib <- liftR $ act ln libEnv
                newSess <- lift $ nextSess sess sessRef newLib k
                -- calculate updated SVG-view from modified development graph
                newSvg <- getSVG title ('/' : show k) $ lookupDGraph ln newLib
                liftR $ return $ sessAns ln newSvg (newSess, k)
            NodeQuery ein nc -> do
              nl@(i, dgnode) <- case ein of
                Right n -> case lookupNodeByName n dg of
                  p : _ -> return p
                  [] -> fail $ "no node name: " ++ n
                Left i -> case lab (dgBody dg) i of
                  Nothing -> fail $ "no node id: " ++ show i
                  Just dgnode -> return (i, dgnode)
              let fstLine = (if isDGRef dgnode then ("reference " ++) else
                    if isInternalNode dgnode then ("internal " ++) else id)
                    "node " ++ getDGNodeName dgnode ++ " (#" ++ show i ++ ")\n"
                  ins = getImportNames dg i
                  showN d = showGlobalDoc (globalAnnos dg) d "\n"
              case nc of
                NcCmd cmd | elem cmd [Query.Node, Info, Symbols]
                  -> case cmd of
                   Symbols -> return $ ppTopElement
                           $ showSymbols ins (globalAnnos dg) dgnode
                   _ -> return $ fstLine ++ showN dgnode
                _ -> case maybeResult $ getGlobalTheory dgnode of
                  Nothing -> fail $
                    "cannot compute global theory of:\n" ++ fstLine
                  Just gTh -> let subL = sublogicOfTh gTh in case nc of
                    ProveNode (ProveCmd pm incl mp mt tl thms xForm) ->
                      case pm of
                      GlProofs -> do
                        (newLib, sens) <- proveNode libEnv ln dg nl
                          gTh subL incl mp mt tl thms
                        if null sens then return "nothing to prove" else do
                          lift $ nextSess sess sessRef newLib k
                          return . formatResults xForm k i . unode "results"
                            $ map (\ (n, e, d) -> unode "goal"
                              [ unode "name" n
                              , unode "result" e
                              , unode "details" d]) sens
                      GlConsistency -> do
                        (newLib, [(_, res, txt)]) <- consNode libEnv ln dg nl
                          subL incl mp mt tl
                        lift $ nextSess sess sessRef newLib k
                        return . ppTopElement $ formatConsNode res txt
                    _ -> return $ case nc of
                      NcCmd Query.Theory ->
                          showGlobalTh dg i gTh k fstLine
                      NcProvers mp mt -> formatProvers mp $ case mp of
                        GlProofs -> getProversAux mt subL
                        GlConsistency -> getConsCheckersAux mt subL
                      NcTranslations mp -> getComorphs mp subL
                      _ -> error "getHetsResult.NodeQuery."
            EdgeQuery i _ ->
              case getDGLinksById (EdgeId i) dg of
              [e@(_, _, l)] -> return $ showLEdge e ++ "\n" ++ showDoc l ""
              [] -> fail $ "no edge found with id: " ++ show i
              _ -> fail $ "multiple edges found with id: " ++ show i

formatConsNode :: String -> String -> Element
formatConsNode res txt = add_attr (mkAttr "state" res) $ unode "result" txt

formatResultsMultiple :: Bool -> Int -> [Element] -> ProverMode -> String
formatResultsMultiple xForm sessId rs prOrCons =
  if xForm then ppTopElement $ unode "Results" rs else let
  goBack1 = case prOrCons of
    GlConsistency -> aRef ('/' : show sessId ++ "?consistency") "return"
    GlProofs -> aRef ('/' : show sessId ++ "?autoproof") "return"
  goBack2 = aRef ('/' : show sessId) "return to DGraph"
  in ppElement $ unode "html" ( unode "head"
    [ unode "title" "Results", add_attr ( mkAttr "type" "text/css" )
    $ unode "style" resultStyles, goBack1, plain " ", goBack2 ]
    : foldr (\ el r -> unode "h4" (qName $ elName el) : el : r) [] rs )

-- | display results of proving session (single node)
formatResults :: Bool -> Int -> Int -> Element -> String
formatResults xForm sessId i rs =
  if xForm || sessId <= 0 then ppTopElement rs else let
  goBack1 = aRef ('/' : show sessId ++ "?theory=" ++ show i) "return to Theory"
  goBack2 = aRef ('/' : show sessId) "return to DGraph"
  in ppElement $ unode "html" [ unode "head"
    [ unode "title" "Results", add_attr ( mkAttr "type" "text/css" )
    $ unode "style" resultStyles, goBack1, plain " ", goBack2 ], rs ]

resultStyles :: String
resultStyles = unlines
  [ "results { margin: 5px; padding:5px; display:block; }"
  , "goal { display:block; margin-left:15px; }"
  , "name { display:inline; margin:5px; padding:10px; font-weight:bold; }"
  , "result { display:inline; padding:30px; }" ]

showBool :: Bool -> String
showBool = map toLower . show

{- | displays the global theory for a node with the option to prove theorems
and select proving options -}
showGlobalTh :: DGraph -> Int -> G_theory -> Int -> String -> String
showGlobalTh dg i gTh sessId fstLine = case simplifyTh gTh of
  sGTh@(G_theory lid _ (ExtSign sig _) _ thsens _) -> let
    ga = globalAnnos dg
    -- links to translations and provers xml view
    transBt = aRef ('/' : show sessId ++ "?translations=" ++ show i)
      "translations"
    prvsBt = aRef ('/' : show sessId ++ "?provers=" ++ show i) "provers"
    headr = unode "h3" fstLine
    thShow = renderHtml ga $ vcat $ map (print_named lid) $ toNamedList thsens
    sbShow = renderHtml ga $ pretty sig
    in case getThGoals sGTh of
      -- show simple view if no goals are found
      [] -> mkHtmlElem fstLine [ headr, transBt, prvsBt,
        unode "h4" "Theory" ] ++ sbShow ++ "\n<br />" ++ thShow
      -- else create proving functionality
      gs -> let
        -- create list of theorems, selectable for proving
        thmSl = map (\ (nm, bp) -> let gSt = maybe GOpen basicProofToGStatus bp
          in add_attrs
                 [ mkAttr "type" "checkbox", mkAttr "name" $ escStr nm
                 , mkAttr "unproven" $ showBool $ elem gSt [GOpen, GTimeout]]
             $ unode "input" $ nm ++ "   (" ++ showSimple gSt ++ ")" ) gs
        -- select unproven, all or none theorems by button
        (btUnpr, btAll, btNone, jvScr1) = showSelectionButtons True
        -- create prove button and prover/comorphism selection
        (prSl, cmrSl, jvScr2) = showProverSelection GlProofs [sublogicOfTh gTh]
        (prBt, timeout) = showProveButton True
        -- hidden param field
        hidStr = add_attrs [ mkAttr "name" "prove"
          , mkAttr "type" "hidden", mkAttr "style" "display:none;"
          , mkAttr "value" $ show i ]
          inputNode
        -- combine elements within a form
        thmMenu = let br = unode "br " () in add_attrs
          [ mkAttr "name" "thmSel", mkAttr "method" "get"]
          . unode "form"
          $ [hidStr, prSl, cmrSl, br, btUnpr, btAll, btNone, timeout]
          ++ intersperse br (prBt : thmSl)
        -- save dg and return to svg-view
        goBack = aRef ('/' : show sessId) "return to DGraph"
        in mkHtmlElemScript fstLine (jvScr1 ++ jvScr2)
          [ headr, transBt, prvsBt, plain " ", goBack, unode "h4" "Theorems"
          , thmMenu, unode "h4" "Theory" ] ++ sbShow ++ "\n<br />" ++ thShow

-- | show window of the autoproof function
showAutoProofWindow :: DGraph -> Int -> ProverMode -> ResultT IO String
showAutoProofWindow dg sessId prOrCons = let
  dgnodes = labNodesDG dg
  -- some parameters need to be different for consistency and autoproof mode
  (prMethod, isProver, title, nodeSel) = case prOrCons of
    GlProofs -> ("proof", True, "automatic proofs"
      , map (\ fn -> add_attrs [ mkAttr "type" "checkbox"
      , mkAttr "unproven" $ showBool $ not $ allProved fn
      , mkAttr "name" $ escStr $ name fn ]
      $ unode "input" $ showHtml fn) $ initFNodes dgnodes)
    -- TODO sort out nodes with no sentences!
    GlConsistency -> ("cons", False, "consistency checker"
      , map (\ (_, dgn) ->
      let cstat = getConsistencyOf dgn
          nm = getDGNodeName dgn in add_attrs [ mkAttr "type" "checkbox"
      , mkAttr "unproven" $ showBool $ sType cstat == CSUnchecked
      , mkAttr "name" nm]
      $ unode "input" (cStatusToPrefix cstat ++ nm)) dgnodes)
  -- generate param field for the query string, invisible to the user
  hidStr = add_attrs [ mkAttr "name" "autoproof"
         , mkAttr "type" "hidden", mkAttr "style" "display:none;"
         , mkAttr "value" prMethod ] inputNode
  -- select unproven, all or no nodes by button
  (btUnpr, btAll, btNone, jvScr1) = showSelectionButtons isProver
  (prBt, timeout) = showProveButton isProver
  include = add_attrs [ mkAttr "type" "checkbox", mkAttr "checked" "true"
          , mkAttr "name" "includetheorems"] $ unode "input" "include Theorems"
  goBack = aRef ('/' : show sessId) "return to DGraph"
  in do
    (jvScr2, nodeMenu) <- case dgnodes of
      -- return simple feedback if no nodes are present
      [] -> return ("", plain "nothing to prove (graph has no nodes)")
      -- otherwise
      (_, nd) : _ -> case maybeResult $ getGlobalTheory nd of
        Nothing -> fail $ "cannot compute global theory of:\n" ++ show nd
        Just gTh -> let
            br = unode "br " ()
            (prSel, cmSel, jvSc) = showProverSelection prOrCons
              [sublogicOfTh gTh]
          in return (jvSc, add_attrs
          [ mkAttr "name" "nodeSel", mkAttr "method" "get" ]
          . unode "form" $
          [ hidStr, prSel, cmSel, br, btAll, btNone, btUnpr, timeout, include ]
          ++ intersperse br (prBt : nodeSel))
    return $ mkHtmlElemScript title (jvScr1 ++ jvScr2)
               [ goBack, plain " ", nodeMenu ]

showProveButton :: Bool -> (Element, Element)
showProveButton isProver = (prBt, timeout) where
        prBt = [ mkAttr "type" "submit", mkAttr "value"
               $ if isProver then "Prove" else "Check"]
               `add_attrs` inputNode
        -- create timeout field
        timeout = add_attrs [mkAttr "type" "text", mkAttr "name" "timeout"
               , mkAttr "value" "1", mkAttr "size" "3"]
               $ unode "input" "Sec/Goal "

-- | select unproven, all or none theorems by button
showSelectionButtons :: Bool -> (Element, Element, Element, String)
showSelectionButtons isProver = (selUnPr, selAll, selNone, jvScr)
  where prChoice = if isProver then "SPASS" else "darwin"
        selUnPr = add_attrs [mkAttr "type" "button"
          , mkAttr "value" $ if isProver then "Unproven" else "Unchecked"
          , mkAttr "onClick" "chkUnproven()"] inputNode
        selAll = add_attrs [mkAttr "type" "button", mkAttr "value" "All"
          , mkAttr "onClick" "chkAll(true)"] inputNode
        selNone = add_attrs [mkAttr "type" "button", mkAttr "value" "None"
          , mkAttr "onClick" "chkAll(false)"] inputNode
        -- javascript features
        jvScr = unlines
          -- select unproven goals by button
          [ "\nfunction chkUnproven() {"
          , "  var e = document.forms[0].elements;"
          , "  for (i = 0; i < e.length; i++) {"
          , "    if( e[i].type == 'checkbox'"
          , "      && e[i].name != 'includetheorems' )"
          , "      e[i].checked = e[i].getAttribute('unproven') == 'true';"
          , "  }"
          -- select or deselect all theorems by button
          , "}\nfunction chkAll(b) {"
          , "  var e = document.forms[0].elements;"
          , "  for (i = 0; i < e.length; i++) {"
          , "    if( e[i].type == 'checkbox'"
          , "      && e[i].name != 'includetheorems' ) e[i].checked = b;"
          , "  }"
          -- autoselect SPASS if possible
          , "}\nwindow.onload = function() {"
          , "  prSel = document.forms[0].elements.namedItem('prover');"
          , "  prs = prSel.getElementsByTagName('option');"
          , "  for ( i=0; i<prs.length; i++ ) {"
          , "    if( prs[i].value == '" ++ prChoice ++ "' ) {"
          , "      prs[i].selected = 'selected';"
          , "      updCmSel('" ++ prChoice ++ "');"
          , "      return;"
          , "    }"
          , "  }"
          -- if SPASS unable, select first one in list
          , "  prs[0].selected = 'selected';"
          , "  updCmSel( prs[0].value );"
          , "}" ]

-- | create prover and comorphism menu and combine them using javascript
showProverSelection :: ProverMode -> [G_sublogics]
  -> (Element, Element, String)
showProverSelection prOrCons subLs = let
  jvScr = unlines
        -- the chosen prover is passed as param
        [ "\nfunction updCmSel(pr) {"
        , "  var cmrSl = document.forms[0].elements.namedItem('translation');"
        -- then, all selectable comorphisms are gathered and iterated
        , "  var opts = cmrSl.getElementsByTagName('option');"
        -- try to keep current comorph-selection
        , "  var selAccept = false;"
        , "  for( var i = opts.length-1; i >= 0; i-- ) {"
        , "    var cmr = opts.item( i );"
        -- the list of supported provers is extracted
        , "    var prs = cmr.getAttribute('4prover').split(';');"
        , "    var pFit = false;"
        , "    for( var j = 0; ! pFit && j < prs.length; j++ ) {"
        , "      pFit = prs[j] == pr;"
        , "    }"
        -- if prover is supported, remove disabled attribute
        , "    if( pFit ) {"
        , "        cmr.removeAttribute('disabled');"
        , "        selAccept = selAccept || cmr.selected;"
        -- else create and append a disabled attribute
        , "    } else {"
        , "      var ds = document.createAttribute('disabled');"
        , "      ds.value = 'disabled';"
        , "      cmr.setAttributeNode(ds);"
        , "    }"
        , "  }"
        -- check if selected comorphism fits, and select fst. in list otherwise
        , "  if( ! selAccept ) {"
        , "    for( i = 0; i < opts.length; i++ ) {"
        , "      if( ! opts.item(i).disabled ) {"
        , "        opts.item(i).selected = 'selected';"
        , "        return;"
        , "      }"
        , "    }"
        , "  }"
        , "}" ]
  allPrCm = nub $ concatMap ((case prOrCons of
    GlProofs -> getProversAux
    GlConsistency -> getConsCheckersAux) Nothing) subLs
  -- create prover selection (drop-down)
  prs = add_attr (mkAttr "name" "prover") $ unode "select" $ map (\ p ->
    add_attrs [mkAttr "value" p, mkAttr "onClick" $ "updCmSel('" ++ p ++ "')"]
    $ unode "option" p) $ showProversOnly allPrCm
  -- create comorphism selection (drop-down)
  cmrs = add_attr (mkAttr "name" "translation") $ unode "select"
    $ map (\ (cm, ps) -> let c = showComorph cm in
    add_attrs [mkAttr "value" c, mkAttr "4prover" $ intercalate ";" ps]
    $ unode "option" c) allPrCm
  in (prs, cmrs, jvScr)

showHtml :: FNode -> String
showHtml fn = name fn ++ " " ++ goalsToPrefix (toGtkGoals fn)

getAllAutomaticProvers :: G_sublogics -> [(G_prover, AnyComorphism)]
getAllAutomaticProvers subL = getAllProvers ProveCMDLautomatic subL logicGraph

filterByProver :: Maybe String -> [(G_prover, AnyComorphism)]
  -> [(G_prover, AnyComorphism)]
filterByProver mp = case mp of
      Nothing -> id
      Just p -> filter ((== p) . getWebProverName . fst)

filterByComorph :: Maybe String -> [(a, AnyComorphism)]
  -> [(a, AnyComorphism)]
filterByComorph mt = case mt of
      Nothing -> id
      Just c -> filter ((== c) . showComorph . snd)

getProverAndComorph :: Maybe String -> Maybe String -> G_sublogics
   -> [(G_prover, AnyComorphism)]
getProverAndComorph mp mc subL =
   let ps = getFilteredProvers mc subL
       spps = case filterByProver (Just "SPASS") ps of
          [] -> ps
          fps -> fps
   in case mp of
        Nothing -> spps
        _ -> filterByProver mp ps

showComorph :: AnyComorphism -> String
showComorph (Comorphism cid) = removeFunnyChars . drop 1 . dropWhile (/= ':')
  . map (\ c -> if c == ';' then ':' else c)
  $ language_name cid

removeFunnyChars :: String -> String
removeFunnyChars = filter (\ c -> isAlphaNum c || elem c "_.:-")

getWebProverName :: G_prover -> String
getWebProverName = removeFunnyChars . getProverName

getFullProverList :: ProverMode -> Maybe String -> DGraph -> String
getFullProverList mp mt = formatProvers mp . foldr
  (\ (_, nd) ls -> maybe ls ((++ ls) . case mp of
      GlProofs -> getProversAux mt
      GlConsistency -> getConsCheckersAux mt
    . sublogicOfTh)
    $ maybeResult $ getGlobalTheory nd) [] . labNodesDG

showProversOnly :: [(AnyComorphism, [String])] -> [String]
showProversOnly = nubOrd . concatMap snd

groupOnSnd :: Eq b => (a -> c) -> [(a, b)] -> [(b, [c])]
groupOnSnd f =
  map (\ l@((_, b) : _) -> (b, map (f . fst) l)) . groupBy (on (==) snd)

{- | gather provers and comorphisms and resort them to
(comorhism, supported provers) while not changing orig comorphism order -}
getProversAux :: Maybe String -> G_sublogics -> [(AnyComorphism, [String])]
getProversAux mt = groupOnSnd getWebProverName . getFilteredProvers mt

getFilteredProvers :: Maybe String -> G_sublogics
  -> [(G_prover, AnyComorphism)]
getFilteredProvers mt = filterByComorph mt . getAllAutomaticProvers

formatProvers :: ProverMode -> [(AnyComorphism, [String])] -> String
formatProvers pm = let
  tag = case pm of
          GlProofs -> "prover"
          GlConsistency -> "consistency-checker"
  in ppTopElement . unode (tag ++ "s") . map (unode tag)
  . showProversOnly

-- | retrieve a list of consistency checkers
getConsCheckersAux :: Maybe String -> G_sublogics
  -> [(AnyComorphism, [String])]
getConsCheckersAux mt = groupOnSnd getCcName . getFilteredConsCheckers mt

getFilteredConsCheckers :: Maybe String -> G_sublogics
  -> [(G_cons_checker, AnyComorphism)]
getFilteredConsCheckers mt = filterByComorph mt . filter (getCcBatch . fst)
  . getConsCheckers . findComorphismPaths logicGraph

getComorphs :: Maybe String -> G_sublogics -> String
getComorphs mp subL = formatComorphs . filterByProver mp
    $ getAllAutomaticProvers subL

getFullComorphList :: DGraph -> String
getFullComorphList = formatComorphs . foldr
  (\ (_, nd) ls -> maybe ls ((++ ls) . getAllAutomaticProvers . sublogicOfTh)
    $ maybeResult $ getGlobalTheory nd) [] . labNodesDG

formatComorphs :: [(G_prover, AnyComorphism)] -> String
formatComorphs = ppTopElement . unode "translations"
    . map (unode "comorphism") . nubOrd . map (showComorph . snd)

consNode :: LibEnv -> LibName -> DGraph -> (Int, DGNodeLab)
  -> G_sublogics -> Bool -> Maybe String -> Maybe String -> Maybe Int
  -> ResultT IO (LibEnv, [(String, String, String)])
consNode le ln dg nl@(i, lb) subL useTh mp mt tl = let
      consList = getFilteredConsCheckers mt subL
      findCC x = filter ((== x ) . getCcName . fst) consList
      mcc = maybe (findCC "darwin") findCC mp
      in case mcc of
        [] -> fail "no cons checker found"
        ((cc, c) : _) -> lift $ do
          cstat <- consistencyCheck useTh cc c ln le dg nl $ fromMaybe 1 tl
          -- Consistency Results are stored in LibEnv via DGChange object
          let cSt = sType cstat
              le'' = if cSt == CSUnchecked then le else
                     Map.insert ln (changeDGH dg $ SetNodeLab lb
                       (i, case cSt of
                             CSInconsistent -> markNodeInconsistent "" lb
                             CSConsistent -> markNodeConsistent "" lb
                             _ -> lb)) le
          return (le'', [(" ", drop 2 $ show cSt, show cstat)])

proveNode :: LibEnv -> LibName -> DGraph -> (Int, DGNodeLab) -> G_theory
  -> G_sublogics -> Bool -> Maybe String -> Maybe String -> Maybe Int
  -> [String] -> ResultT IO (LibEnv, [(String, String, String)])
proveNode le ln dg nl gTh subL useTh mp mt tl thms = case
    getProverAndComorph mp mt subL of
  [] -> fail "no matching translation or prover found"
  cp : _ -> do
    let ks = map fst $ getThGoals gTh
        diffs = Set.difference (Set.fromList thms)
                $ Set.fromList ks
    unless (Set.null diffs) . fail $ "unknown theorems: " ++ show diffs
    when (null thms && null ks) $ fail "no theorems to prove"
    ((nTh, sens), _) <- autoProofAtNode useTh (maybe 1 (max 1) tl)
      (if null thms then ks else thms) gTh cp
    return (if null sens then le else
        Map.insert ln (updateLabelTheory le dg nl nTh) le, sens)

-- run over multiple dgnodes and prove available goals for each
proveMultiNodes :: Bool -> ProverMode -> LibEnv -> LibName -> DGraph -> Bool
  -> Maybe String -> Maybe String -> Maybe Int -> [String]
  -> ResultT IO (LibEnv, [Element])
proveMultiNodes xF pm le ln dg useTh mp mt tl nodeSel = let
  runProof le' gTh nl = let
    subL = sublogicOfTh gTh
    dg' = lookupDGraph ln le' in case pm of
    GlConsistency -> consNode le' ln dg' nl subL useTh mp mt tl
    GlProofs -> proveNode le' ln dg' nl gTh subL useTh mp mt tl
             $ map fst $ getThGoals gTh
  nodes2check = filter (case nodeSel of
    [] -> case pm of
            GlConsistency -> const True
            GlProofs -> hasOpenGoals . snd
    _ -> (`elem` nodeSel) . getDGNodeName . snd) $ labNodesDG dg
  in foldM
  (\ (le', res) nl@(_, dgn) -> case maybeResult $ getGlobalTheory dgn of
      Nothing -> fail $
                    "cannot compute global theory of:\n" ++ show dgn
      Just gTh -> do
        (le'', sens) <- runProof le' gTh nl
        return (le'', formatResultsAux xF pm (getDGNodeName dgn) sens : res))
          (le, []) nodes2check

formatResultsAux :: Bool -> ProverMode -> String -> [(String, String, String)]
  -> Element
formatResultsAux xF pm nm sens = unode nm $ case (sens, pm) of
    ([(_, e, d)], GlConsistency) | xF -> formatConsNode e d
    _ -> unode "results" $ map (\ (n, e, d) -> unode "goal"
       $ [unode "name" n, unode "result" e]
       ++ [unode "details" d | xF]) sens

mkPath :: Session -> LibName -> Int -> String
mkPath sess l k =
        '/' : concat [ libToFileName l ++ "?session="
                     | l /= sessLibName sess ]
        ++ show k

extPath :: Session -> LibName -> Int -> String
extPath sess l k = mkPath sess l k ++
        if l /= sessLibName sess then "&" else "?"

globalCommands :: [String]
globalCommands = map (cmdlGlobCmd . fst) allGlobLibAct

sessAns :: LibName -> String -> (Session, Int) -> String
sessAns libName svg (sess, k) =
  let libEnv = sessLibEnv sess
      ln = libToFileName libName
      libref l =
        aRef (mkPath sess l k) (libToFileName l) : map (\ d ->
         aRef (extPath sess l k ++ d) d) displayTypes
      libPath = extPath sess libName k
      ref d = aRef (libPath ++ d) d
      autoProofBt = aRef ('/' : show k ++ "?autoproof") "automatic proofs"
      consBt = aRef ('/' : show k ++ "?consistency") "consistency checker"
-- the html quicklinks to nodes and edges have been removed with R.16827
  in htmlHead ++ mkHtmlElem
           ('(' : shows k ")" ++ ln)
           (bold ("library " ++ ln)
            : map ref displayTypes
            ++ menuElement : loadXUpdate (libPath ++ updateS)
            : plain "tools:" : mkUnorderedList [autoProofBt, consBt]
            : plain "commands:"
            : mkUnorderedList (map ref globalCommands)
            : plain "imported libraries:"
            : [mkUnorderedList $ map libref $ Map.keys libEnv]
           ) ++ svg

getHetsLibContent :: HetcatsOpts -> String -> [QueryPair] -> IO [Element]
getHetsLibContent opts dir query = do
  let hlibs = libdirs opts
  ds <- if null dir then return hlibs else
       filterM doesDirectoryExist $ map (</> dir) hlibs
  fs <- fmap (sortBy cmpFilePath . filter (not . isPrefixOf ".") . concat)
    $ mapM getDirContents ds
  return $ map (mkHtmlRef query) $ getParent dir : fs

getParent :: String -> String
getParent = addTrailingPathSeparator . ("/" </>) . takeDirectory
  . dropTrailingPathSeparator

-- | a variant that adds a trailing slash
getDirContents :: FilePath -> IO [FilePath]
getDirContents d = do
    fs <- getDirectoryContents d
    mapM (\ f -> doesDirectoryExist (d </> f) >>= \ b -> return
            $ if b then addTrailingPathSeparator f else f) fs

aRef :: String -> String -> Element
aRef lnk txt = add_attr (mkAttr "href" lnk) $ unode "a" txt

mkHtmlRef :: [QueryPair] -> String -> Element
mkHtmlRef query entry = unode "dir" $ aRef
  (entry ++ if null query then "" else '?' : intercalate "&"
         (map (\ (x, ms) -> x ++ maybe "" ('=' :) ms) query)) entry

mkUnorderedList :: Node t => [t] -> Element
mkUnorderedList = unode "ul" . map (unode "li")

italic :: String -> Element
italic = unode "i"

bold :: String -> Element
bold = unode "b"

plain :: String -> Element
plain = unode "p"

headElems :: String -> [Element]
headElems path = let d = "default" in unode "strong" "Choose a display type:" :
  map (\ q -> aRef (if q == d then "/" </> path else '?' : q) q)
      (d : displayTypes)
  ++ [ unode "p"
       [ unode "small" "internal command overview as XML:"
       , menuElement ]
     , plain $ "Select a local file as library or "
       ++ "enter a HetCASL specification in the text area and press \"submit\""
       ++ ", or browse through our Hets-lib library below."
     , uploadHtml ]

menuElement :: Element
menuElement = aRef "?menus" "menus"

htmlHead :: String
htmlHead =
    let dtd = "PUBLIC \"-//W3C//DTD XHTML 1.0 Transitional//EN\""
        url = "\"http://www.w3.org/TR/xhtml1/DTD/xhtml1-transitional.dtd\""
    in concat ["<!DOCTYPE html ", dtd, " ", url, ">\n"]

inputNode :: Element
inputNode = unode "input" ()

loadNode :: String -> Element
loadNode nm = add_attrs
    [ mkAttr "type" "file"
    , mkAttr "name" nm
    , mkAttr "size" "40"]
    inputNode

submitNode :: Element
submitNode = add_attrs
    [ mkAttr "type" "submit"
    , mkAttr "value" "submit"]
    inputNode

mkForm :: String -> [Element] -> Element
mkForm a = add_attrs
  [ mkAttr "action" a
  , mkAttr "enctype" "multipart/form-data"
  , mkAttr "method" "post" ]
  . unode "form"

uploadHtml :: Element
uploadHtml = mkForm "/"
  [ loadNode "file"
  , unode "p" $ add_attrs
    [ mkAttr "cols" "68"
    , mkAttr "rows" "22"
    , mkAttr "name" "content" ] $ unode "textarea" ""
  , submitNode ]

loadXUpdate :: String -> Element
loadXUpdate a = mkForm a
  [ italic xupdateS
  , loadNode xupdateS
  , italic "impacts"
  , loadNode "impacts"
  , submitNode ]
