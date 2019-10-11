{-# LANGUAGE CPP, DoAndIfThenElse #-}
{- |
Module      :  ./PGIP/Server.hs
Description :  run hets as server
Copyright   :  (c) Christian Maeder, DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (via imports)

-}

module PGIP.Server (hetsServer) where

-- TODO: Delete these two before merge!
import Debug.Trace
import Data.Typeable

import PGIP.Output.Formatting
import PGIP.Output.Mime
import PGIP.Output.Proof
import PGIP.Output.Translations
import qualified PGIP.Output.Provers as OProvers

import PGIP.GraphQL

import PGIP.ReasoningParameters as ReasoningParameters
import PGIP.Query as Query
import PGIP.Server.WebAssets
import PGIP.Shared
import qualified PGIP.Server.Examples as Examples

import Driver.Options
import Driver.ReadFn
import Driver.Version

import Network.Wai.Handler.Warp
import Network.HTTP.Types

import Codec.Binary.UTF8.String
import Control.Monad.Trans (lift, liftIO)
#ifdef WARP1
import Control.Monad.Trans.Resource
import Data.Conduit.Lazy (lazyConsume)
#endif
import qualified Data.Text as T

import Network.Wai
import Network.Wai.Parse as W

import qualified Data.ByteString.Lazy.Char8 as BS
import qualified Data.ByteString.Char8 as B8

import Static.AnalysisLibrary
import Static.ApplyChanges
import Static.ComputeTheory
import Static.DevGraph
import Static.DGTranslation
import Static.DgUtils
import Static.DotGraph
import Static.FromXml
import Static.GTheory
import Static.History (changeDGH)
import Static.PrintDevGraph
import qualified Static.ToJson as ToJson
import Static.ToXml as ToXml

import qualified Persistence.DevGraph
import qualified Persistence.Reasoning

import Logic.LGToXml

import Syntax.ToXml
import Syntax.Print_AS_Structured

import Interfaces.Command
import Interfaces.CmdAction
import Interfaces.GenericATPState

import Comorphisms.LogicGraph

import Logic.Prover
import Logic.Grothendieck
import Logic.Comorphism
import Logic.Logic

import Proofs.AbstractState as AbsState
import Proofs.ConsistencyCheck

import Text.XML.Light
import Text.XML.Light.Cursor hiding (lefts, rights)

import Common.AutoProofUtils
import Common.Doc
import Common.DocUtils (pretty, showGlobalDoc, showDoc)
import Common.ExtSign (ExtSign (..))
import Common.GtkGoal
import Common.Json (Json (..), ppJson)
import Common.JSONOrXML
import Common.LibName
import Common.PrintLaTeX
import Common.Result
import Common.ResultT
import Common.ToXml
import Common.Utils
import Common.XUpdate
import Common.GlobalAnnotations

import Control.Monad
import Control.Exception (catch, throwTo)
import Control.Exception.Base (SomeException)
import Control.Concurrent (myThreadId, ThreadId)

import qualified Data.Aeson as Aeson
import Data.Either
import qualified Data.IntMap as IntMap
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.CaseInsensitive as CI
import Data.Char
import Data.IORef
import Data.Function
import Data.List
import Data.Maybe
import Data.Ord
import Data.Graph.Inductive.Graph (lab)
import Data.Time.Clock
import Data.Time.LocalTime

import System.Random
import System.Directory
import System.Exit
import System.FilePath
import System.IO
import System.Posix.Process (getProcessID)
import System.Posix.Signals

data UsedAPI = OldWebAPI | RESTfulAPI deriving (Show, Eq, Ord)

randomKey :: IO Int
randomKey = randomRIO (100000000, 999999999)

sessGraph :: DGQuery -> Session -> Maybe (LibName, DGraph)
sessGraph dgQ s =
  let le = sessLibEnv s
      ln = sessLibName s
  in case dgQ of
  DGQuery _ (Just path) ->
      find (\ (n, _) -> libToFileName n == path)
        $ Map.toList le
  _ -> fmap (\ dg -> (ln, dg)) $ Map.lookup ln le

getVal :: [QueryPair] -> String -> Maybe String
getVal qs = fromMaybe Nothing . (`lookup` qs)

getIP4 :: String -> [String]
getIP4 = splitOn '.' . takeWhile (\ c -> isDigit c || c == '.')

matchIP4 :: [String] -> [String] -> Bool
matchIP4 ip mask = case mask of
  [] -> True
  ft : rt -> case ip of
    [] -> False -- mask too long or IP too short
    d : s -> (null ft || ft == d) && matchIP4 rt s

matchWhite :: [String] -> [[String]] -> Bool
matchWhite ip l = null l || any (matchIP4 ip) l

#ifdef WARP3
type WebResponse = (Response -> IO ResponseReceived) -> IO ResponseReceived
catchException :: SomeException -> Response
catchException e =
   mkResponse textC
              internalServerError500
              ("*** Error:\n" ++ show e)
#else
type WebResponse = (Response -> RsrcIO Response) -> RsrcIO Response
#endif

deletePidFileAndExit :: HetcatsOpts -> ThreadId -> ExitCode -> IO ()
deletePidFileAndExit opts threadId exitCode = do
  deletePidFile opts
  throwTo threadId exitCode

hetsServer :: HetcatsOpts -> IO ()
hetsServer opts = do
  tid <- myThreadId
  writePidFile opts
  installHandler sigINT (Catch $ deletePidFileAndExit opts tid ExitSuccess) Nothing
  installHandler sigTERM (Catch $ deletePidFileAndExit opts tid ExitSuccess) Nothing
  hetsServer' opts
  deletePidFile opts

writePidFile :: HetcatsOpts -> IO ()
writePidFile opts =
  let pidFilePath = pidFile opts
      v = verbose opts
  in (unless (null pidFilePath) $
     do unless (null pidFilePath)
          (verbMsgIOLn v 2 ("Writing PIDfile " ++ show pidFilePath))
        pid <- getProcessID
        writeFile pidFilePath (show pid))

deletePidFile :: HetcatsOpts -> IO ()
deletePidFile opts =
  let pidFilePath = pidFile opts
  in (unless (null pidFilePath) $ removeFile $ pidFile opts)

hetsServer' :: HetcatsOpts -> IO ()
hetsServer' opts1 = do
  tempDir <- getTemporaryDirectory
  let tempLib = tempDir </> "MyHetsLib"
      logFile = tempDir </>
        ("hets-" ++ show port ++ ".log")
      opts = opts1 { libdirs = tempLib : libdirs opts1 }
      port1 = listen opts1
      port = if port1 < 0 then 8000 else port1
      wl = whitelist opts1
      bl = blacklist opts1
      prList ll = intercalate ", " $ map (intercalate ".") ll
  createDirectoryIfMissing False tempLib
  writeFile logFile ""
  unless (null wl) . appendFile logFile
    $ "white list: " ++ prList wl ++ "\n"
  unless (null bl) . appendFile logFile
    $ "black list: " ++ prList bl ++ "\n"
  sessRef <- newIORef (IntMap.empty, Map.empty)
  putIfVerbose opts 1 $ "hets server is listening on port " ++ show port
  putIfVerbose opts 2 $ "for more information look into file: " ++ logFile
#ifdef WARP3
  runSettings (setOnExceptionResponse catchException $
               setPort port $
               setTimeout 86400 defaultSettings)
    $ \ re respond -> do
#else
  run port $ \ re -> do
   let respond = liftIO . return
#endif
   let rhost = shows (remoteHost re) "\n"
       ip = getIP4 rhost
       white = matchWhite ip wl
       black = any (matchIP4 ip) bl
       splitQuery = map (\ (bs, ms) -> (B8.unpack bs, fmap B8.unpack ms))
         $ queryString re
       pathBits = map T.unpack $ pathInfo re
       meth = B8.unpack (requestMethod re)
       query = showPathQuery pathBits splitQuery
   liftIO $ do
     time <- getCurrentTime
     createDirectoryIfMissing False tempLib
     (m, _) <- readIORef sessRef
     appendFile logFile rhost
     unless black $ if white then do
         appendFile logFile $ shows time " sessions: "
                    ++ shows (IntMap.size m) "\n"
         appendFile logFile $ shows (requestHeaders re) "\n"
         unless (null query) $ appendFile logFile $ query ++ "\n"
       else appendFile logFile "not white listed\n"
   if not white || black then respond $ mkResponse "" status403 ""
    -- if path could be a RESTful request, try to parse it
    else do
     eith <- liftIO $ getArgFlags splitQuery
     case eith of
       Left err -> queryFail err respond
       Right (qr, vs, fs) ->
         let eith2 = getSwitches qr
         in case eith2 of
         Left err -> queryFail err respond
         Right (qr2, fs2) ->
           let newOpts = foldl makeOpts opts $ fs ++ map snd fs2
           in if isGraphQL meth pathBits then do
                   responseString <- processGraphQL newOpts sessRef re
                   respond $ mkOkResponse "application/json" responseString
              else if isRESTful pathBits then do
              requestBodyBS <- strictRequestBody re
              requestBodyParams <- parseRequestParams re requestBodyBS
              let unknown = filter (`notElem` allQueryKeys) $ map fst qr2
              if null unknown
              then do pathBits' <- case requestBodyParams of
                        JObject jsonPairs -> do
                          let uploadFileData = fmap snd $ find ( \(x,_) -> x == "document" ) jsonPairs
                          case uploadFileData of
                            Just (JString fileData) -> do
                              writeFile (tempDir </> ("upload_file")) fileData
                              {-
                                TODO:
                                Prüfen, ob pathBits richtig gesetzt wird.
                              -}
                              return ((head pathBits) : (tempDir ++ "/" ++ "upload_file") : tail (tail pathBits))
                            _ -> return pathBits
                        _ ->
                          return pathBits
                      parseRESTful newOpts sessRef pathBits'
                        (map fst fs2 ++ map (\ (a, b) -> a ++ "=" ++ b) vs)
                        qr2 requestBodyBS requestBodyParams meth respond
              else queryFail ("unknown query key(s): " ++ show unknown) respond
           -- only otherwise stick to the old response methods
           else oldWebApi newOpts tempLib sessRef re pathBits qr2
             meth respond

parseRequestParams :: Request -> BS.ByteString -> RsrcIO Json
parseRequestParams request requestBodyBS =
  let
    noParams :: Json
    noParams = JNull

    lookupHeader :: String -> Maybe String
    lookupHeader s =
      liftM B8.unpack $ lookup (CI.mk $ B8.pack s) $ requestHeaders request

    formParams :: RsrcIO (Maybe Json)
    formParams =
      let toJsonObject :: [(B8.ByteString, B8.ByteString)] -> String
          toJsonObject assocList = "{"
            ++ intercalate ", " (map (\ (k, v) ->
                  show k ++ ": " ++ jsonStringOrArray v) assocList)
            ++ "}"
          jsonStringOrArray str =
            if B8.head str == '[' then B8.unpack str else show str
      in do
        (formDataB8, _) <- parseRequestBody lbsBackEnd request
        return $ parseJson $ toJsonObject formDataB8

#ifdef WARP1
    lazyRequestBody :: Request -> ResourceT IO BS.ByteString
    lazyRequestBody = fmap BS.fromChunks . lazyConsume . requestBody
#endif
  in
    liftM (fromMaybe noParams) $ case lookupHeader "Content-Type" of
      Just "application/json" -> jsonBody requestBodyBS
      Just "multipart/form-data" -> formParams
      _ -> formParams

-- | the old API that supports downloading files and interactive stuff
oldWebApi :: HetcatsOpts -> FilePath -> Cache -> Request -> [String]
  -> [QueryPair] -> String -> WebResponse
oldWebApi opts tempLib sessRef re pathBits splitQuery meth respond =
  case meth of
      "GET" -> if isJust $ lookup "menus" splitQuery
         then mkMenuResponse respond else do
         let path = intercalate "/" pathBits
         dirs@(_ : cs) <- liftIO $ getHetsLibContent opts path splitQuery
         if not (null cs) || null path then htmlResponse path dirs respond
           -- AUTOMATIC PROOFS (parsing)
           else if isJust $ getVal splitQuery "autoproof" then
             let qr k = Query (DGQuery k Nothing) $
                   anaAutoProofQuery splitQuery in do
               Result ds ms <- liftIO $ runResultT
                 $ case readMaybe $ head pathBits of
                 Nothing -> fail "cannot read session id for automatic proofs"
                 Just k' -> getHetsResult opts [] sessRef (qr k')
                              Nothing OldWebAPI proofFormatterOptions
               respond $ case ms of
                 Nothing -> mkResponse textC status422 $ showRelDiags 1 ds
                 Just (t, s) -> mkOkResponse t s
           -- AUTOMATIC PROOFS E.N.D.
           else getHetsResponse opts [] sessRef pathBits splitQuery respond
      "POST" -> do
        (params, files) <- parseRequestBody lbsBackEnd re
        let opts' = case lookup (B8.pack "input-type") params of
                      Nothing -> opts
                      Just inputType -> if null $ B8.unpack inputType
                                        then opts
                                        else opts { intype = read $ B8.unpack inputType }
        mTmpFile <- case lookup "content"
                   $ map (\ (a, b) -> (B8.unpack a, b)) params of
              Nothing -> return Nothing
              Just areatext -> let content = B8.unpack areatext in
                if all isSpace content then return Nothing else liftIO $ do
                   tmpFile <- getTempFile content "temp.het"
                   return $ Just tmpFile
        let res tmpFile =
              getHetsResponse opts' [] sessRef [tmpFile] splitQuery respond
            mRes = maybe (queryFail "nothing submitted" respond)
              res mTmpFile
        case files of
          [] -> if isJust $ getVal splitQuery "prove" then
               getHetsResponse opts' [] sessRef pathBits
                 (splitQuery ++ map (\ (a, b)
                 -> (B8.unpack a, Just $ B8.unpack b)) params) respond
            else mRes
          [(_, f)] | isNothing $ lookup updateS splitQuery -> do
           let fn = takeFileName $ B8.unpack $ fileName f
           if any isAlphaNum fn then do
             let tmpFile = tempLib </> fn
             liftIO $ BS.writeFile tmpFile $ fileContent f
             maybe (res tmpFile) res mTmpFile
            else mRes
          _ -> getHetsResponse
                 opts' (map snd files) sessRef pathBits splitQuery respond
      _ -> respond $ mkResponse "" status400 ""

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
  axioms = mSplitOnComma $ lookup2 "axioms"
  prOrCons = case lookup2 "autoproof" of
    Just "proof" -> GlProofs
    Just "cons" -> GlConsistency
    err -> error $ "illegal autoproof method: " ++ show err
  in GlAutoProve $
        ProveCmd prOrCons include prover trans timeout nodeSel False axioms

-- quick approach to whether or not the query can be a RESTful request
isRESTful :: [String] -> Bool
isRESTful pathBits = case pathBits of
  [] -> False
  [h] | elem h ["numeric-version", "version", "robots.txt"] -> True
  h : _ -> elem h listRESTfulIdentifiers

listRESTfulIdentifiers :: [String]
listRESTfulIdentifiers =
  [ "libraries", "sessions", "menus", "filetype", "hets-lib", "dir"]
  ++ nodeEdgeIdes ++ newRESTIdes
  ++ ["available-provers"]

nodeEdgeIdes :: [String]
nodeEdgeIdes = ["nodes", "edges"]

newRESTIdes :: [String]
newRESTIdes =
  [ "dg", "translations", "provers", "consistency-checkers", "prove"
  , "consistency-check", "theory" ]

queryFail :: String -> WebResponse
queryFail msg respond = respond $ mkResponse textC status400 msg

allQueryKeys :: [String]
allQueryKeys = [updateS, "library", "consistency-checker"]
  ++ globalCommands ++ knownQueryKeys


data RequestBodyParam = Single String | List [String]

-- query is analysed and processed in accordance with RESTful interface
parseRESTful :: HetcatsOpts -> Cache -> [String] -> [String] -> [QueryPair]
  -> BS.ByteString -> Json -> String -> WebResponse
parseRESTful
  opts sessRef pathBits qOpts splitQuery requestBodyBS requestBodyParams meth respond = let
  {- some parameters from the paths query part might be needed more than once
  (when using lookup upon querybits, you need to unpack Maybe twice) -}
  lookupQueryStringParam :: String -> Maybe String
  lookupQueryStringParam = getVal splitQuery

  lookupBodyParam :: String -> Json -> Maybe RequestBodyParam
  lookupBodyParam key json = case json of
    JObject pairs -> case lookup key pairs of
      Just (JArray a) -> Just $ List $ map (read . ppJson) a
      Just v -> Just $ Single $ read $ ppJson v
      _ -> Nothing
    _ -> Nothing

  lookupSingleParam :: String -> Maybe String
  lookupSingleParam key = case meth of
    "GET" -> lookupQueryStringParam key
    _ -> case lookupBodyParam key requestBodyParams of
          Just (Single s) -> Just s
          _ -> Nothing

  isParamTrue :: Bool -> String -> Bool
  isParamTrue def key = case fmap (map toLower) $ lookupSingleParam key of
    Nothing -> def
    Just "true" -> True
    _ -> False

  session = lookupSingleParam "session" >>= readMaybe
  library = lookupSingleParam "library"
  format_ = lookupSingleParam "format"
  nodeM = lookupSingleParam "node"
  includeDetails = isParamTrue True "includeDetails"
  includeProof = isParamTrue True "includeProof"
  transM = lookupSingleParam "translation"
  reasoningParametersE = parseReasoningParametersEither requestBodyBS
  queryFailure = queryFail
    ("this query does not comply with RESTful interface: "
    ++ showPathQuery pathBits splitQuery) respond
  -- since used more often, generate full query out of nodeIRI and nodeCmd
  nodeQuery s = NodeQuery $ maybe (Right s) Left (readMaybe s :: Maybe Int)
  pfOptions = proofFormatterOptions
                { pfoIncludeProof = includeProof
                , pfoIncludeDetails = includeDetails
                }
  parseNodeQuery :: Monad m => String -> Int -> m NodeCommand -> m Query.Query
  parseNodeQuery p sId ncmd = ncmd >>= let
      in return . Query (DGQuery sId (Just p)) . nodeQuery (getFragment p)
  -- call getHetsResult with the properly generated query (Final Result)
  getResponseAux myOpts qr = do
    let format' = Just $ fromMaybe "xml" format_
    Result ds ms <- liftIO $ runResultT $
      getHetsResult myOpts [] sessRef qr format' RESTfulAPI pfOptions
    respond $ case ms of
      Nothing -> mkResponse textC status422 $ showRelDiags 1 ds
      Just (t, s) -> mkOkResponse t s
  getResponse = getResponseAux opts
  -- respond depending on request Method
  in case meth of
    rm | elem rm ["GET", "POST"] -> case pathBits of
      ["robots.txt"] -> respond $ mkOkResponse textC
        $ unlines ["User-agent: *", "Disallow: /"]
      -- show all menu options
      ["menus"] -> mkMenuResponse respond
      -- list files from directory
      "dir" : r -> do
        let path' = intercalate "/" r
        dirs <- liftIO $ getHetsLibContent opts path' splitQuery
        htmlResponse path' dirs respond
      ["version"] -> respond $ mkOkResponse textC hetsVersion
      ["numeric-version"] ->
        respond $ mkOkResponse textC hetsVersionNumeric
      ["available-provers"] ->
         liftIO (usableProvers logicGraph)
         >>= respond . mkOkResponse xmlC . ppTopElement
      -- get dgraph from file
      "filetype" : libIri : _ -> mkFiletypeResponse opts libIri respond
      "hets-lib" : r -> let file = intercalate "/" r in
        getResponse $ Query (NewDGQuery file []) $ DisplayQuery format_
      -- get library (complies with get/hets-lib for now)
      ["libraries", libIri, "development_graph"] ->
        getResponse $ Query (NewDGQuery libIri []) $ DisplayQuery format_
      -- get previously created session
      "sessions" : sessId : cmd -> case readMaybe sessId of
          Nothing -> queryFail ("failed to read session number from " ++ sessId)
            respond
          Just sId ->
            (case nodeM of
              Just ndIri -> parseNodeQuery ndIri sId $ case cmd of
                ["provers"] -> return $ NcProvers GlProofs transM
                ["translations"] -> return $ NcTranslations Nothing
                _ -> fail $ "unknown node command for a GET-request: "
                      ++ intercalate "/" cmd
              Nothing -> fmap (Query (DGQuery sId Nothing)) $ case cmd of
                [] -> return $ DisplayQuery format_
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
            Nothing -> queryFail ("failed to read edgeId from " ++ f) respond
          _ -> error $ "PGIP.Server.elemIndex " ++ nodeOrEdge
      newIde : libIri : rest ->
        let cmdOptList = filter (/= "") rest
            (optFlags, cmdList) = partition (`elem` map fst optionFlags)
              cmdOptList
            newOpts = foldl makeOpts opts $ mapMaybe (`lookup` optionFlags)
              optFlags
            validReasoningParams = isRight reasoningParametersE <=
              elem newIde ["prove", "consistency-check"]
        in 
          -- if libIri == "upload"    -- TODO: hier für die Rückgabe des Ordners ansetzen
          if elem newIde newRESTIdes
                  && all (`elem` globalCommands) cmdList
                  && validReasoningParams
            then let
            qkind = case newIde of
              "translations" -> case nodeM of
                Nothing -> GlTranslations
                Just n -> nodeQuery n $ NcTranslations Nothing
              _ | elem newIde ["provers", "consistency-checkers"] ->
                let pm = if newIde == "provers" then GlProofs else GlConsistency
                in case nodeM of
                Nothing -> GlProvers pm transM
                Just n -> nodeQuery n $ NcProvers pm transM
              _ | elem newIde ["prove", "consistency-check"] ->
                case reasoningParametersE of
                  Left message_ -> error ("Invalid parameters: " ++ message_) -- cannot happen
                  Right reasoningParameters ->
                    let proverMode = if newIde == "prove"
                                      then GlProofs
                                      else GlConsistency
                    in GlAutoProveREST proverMode reasoningParameters
              "dg" -> case transM of
                Nothing -> DisplayQuery (Just $ fromMaybe "xml" format_)
                Just tr -> Query.DGTranslation tr
              "theory" -> case transM of
                Nothing -> case nodeM of
                            Just x -> NodeQuery (maybe (Right x) Left $ readMaybe x)
                                      $ NcCmd Query.Theory
                            Nothing -> error "development graph node missing. Please use <url>?node=<number>"
                Just tr -> case nodeM of
                            Just x -> NodeQuery (maybe (Right x) Left $ readMaybe x)
                                      $ NcCmd $ Query.Translate tr
                            Nothing -> error "development graph node missing. Please specifiy ?node=<number>"
              _ -> error $ "REST: unknown " ++ newIde
            in getResponseAux newOpts . Query (NewDGQuery libIri $ cmdList
                ++ Set.toList (Set.fromList $ optFlags ++ qOpts)) $ qkind
            else if validReasoningParams
                then queryFailure
                else case reasoningParametersE of
                        Left message_ ->
                          queryFail ("Invalid parameters: " ++ message_) respond
                        Right _ ->
                          error "Unexpected error in PGIP.Server.parseRESTful"
      _ -> queryFailure
    "PUT" -> case pathBits of
      {- execute global commands
         TODO load other library ??? -}
      ["libraries", libIri, "proofs", prId, cmd] ->
         case readMaybe prId of
           Nothing -> queryFail ("failed to read sessionId from " ++ prId)
             respond
           Just sessId -> let
             dgQ = DGQuery sessId $ Just libIri in
             getResponse $ Query dgQ $ GlobCmdQuery cmd
      -- execute a proof or calculus request
      ["sessions", sessId, cmd] -> case readMaybe sessId of
        Nothing -> queryFail ("failed to read sessionId from " ++ sessId)
          respond
        Just sId -> case cmd of
          "prove" -> case reasoningParametersE of
              Left message_ -> fail ("Invalid parameters: " ++ message_)
              Right reasoningParameters ->
                return $ Query (DGQuery sId Nothing) $
                  GlAutoProveREST GlProofs reasoningParameters
              >>= getResponse
          -- on other cmd look for (optional) specification of node or edge
          _ -> case (nodeM, lookupSingleParam "edge") of
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
    _ -> respond $ mkResponse "" status400 ""

parseReasoningParametersEither :: BS.ByteString -> Either String ReasoningParameters
parseReasoningParametersEither requestBodyBS = Aeson.eitherDecode requestBodyBS

mSplitOnComma :: Maybe String -> [String]
mSplitOnComma mstr = case mstr of
  Nothing -> []
  Just str -> splitOn ',' str

mkMenuResponse :: WebResponse
mkMenuResponse respond =
  respond $ mkOkResponse xmlC $ ppTopElement $ unode "menus" mkMenus

mkMenus :: [Element]
mkMenus = menuTriple "" "Get menu triples" "menus"
  : menuTriple "/DGraph" updateS updateS
  : map (\ (c, _) -> menuTriple "/" (menuTextGlobCmd c) $ cmdlGlobCmd c)
    allGlobLibAct
  ++ map (\ nc -> menuTriple "/DGraph/DGNode" ("Show " ++ nc) nc) nodeCommands
  ++ [menuTriple "/DGraph/DGLink" "Show edge info" "edge"]

status422 :: Status
status422 = Status 422 $ B8.pack "Unprocessable Entity"

mkFiletypeResponse :: HetcatsOpts -> String -> WebResponse
mkFiletypeResponse opts libIri respond = do
  res <- liftIO $ getContentAndFileType opts libIri
  respond $ case res of
    Left err -> mkResponse textC status422 err
    Right (mr, _, fn, _) -> case mr of
      Nothing -> mkResponse textC status422 $ fn ++ ": unknown file type"
      Just r -> mkOkResponse textC $ fn ++ ": " ++ r

menuTriple :: String -> String -> String -> Element
menuTriple q d c = unode "triple"
                [ unode "xquery" q
                , unode "displayname" d
                , unode "command" c ]

htmlResponse :: FilePath -> [Element] -> WebResponse
htmlResponse path listElements respond = respond . mkOkResponse htmlC
  $ htmlPageWithTopContent path listElements

htmlPageWithTopContent :: FilePath -> [Element] -> String
htmlPageWithTopContent path listElements =
  htmlPage (if null path then "Start Page" else path) []
    (pageHeader ++ pageOptions path listElements)
    ""

htmlPage :: String -> String -> [Element] -> String -> String
htmlPage title javascripts body rawHtmlPageFooter = htmlHead title javascripts
  ++ intercalate "\n" (map ppElement body)
  ++ htmlWrapBottomContent rawHtmlPageFooter
  ++ htmlFoot

htmlHead :: String -> String -> String
htmlHead title javascript =
  "<!DOCTYPE html>\n"
  ++ "<html lang=\"en\">\n"
  ++ "  <head>\n"
  ++ "    <meta charset=\"utf-8\">\n"
  ++ "    <meta content=\"width=device-width,initial-scale=1,shrink-to-fit=no\" name=\"viewport\">\n"
  ++ "    <meta content=\"#000000\" name=\"theme-color\">\n"
  ++ "    <meta name=\"robots\" content=\"noindex,nofollow\">\n"
  ++ "    <title>Hets, the DOLiator - " ++ title ++ "</title>\n"
  ++ "    <!-- Semantic UI stylesheet -->\n"
  ++ "    <style type=\"text/css\">\n"
  ++ semanticUiCss ++ "\n"
  ++ "    </style>\n"
  ++ "    <!-- Hets stylesheet -->\n"
  ++ "    <style type=\"text/css\">\n"
  ++ hetsCss ++ "\n"
  ++ "    </style>\n"
  ++ "  </head>\n"
  ++ "  <body>\n"
  ++ "    <!-- jQuery -->\n"
  ++ "    <script type=\"text/javascript\">\n"
  ++ jQueryJs ++ "\n"
  ++ "    </script>\n"
  ++ "    <!-- Semantic UI Javascript -->\n"
  ++ "    <script type=\"text/javascript\">\n"
  ++ semanticUiJs ++ "\n"
  ++ "    </script>\n"
  ++ "    <!-- Static Hets Javascript -->\n"
  ++ "    <script type=\"text/javascript\">\n"
  ++ hetsJs ++ "\n"
  ++ "    </script>\n"
  ++ "    <!-- Dynamic Hets Javascript -->\n"
  ++ "    <script type=\"text/javascript\">\n"
  ++ javascript ++ "\n"
  ++ "    </script>\n"
  ++ "    <div class=\"ui left aligned doubling stackable centered relaxed grid container\">\n"

htmlWrapBottomContent :: String -> String
htmlWrapBottomContent content =
  if null content then "" else
    "      <div class=\"ui segment pushable left aligned\" style=\"overflow: auto;\">\n"
    ++ content
    ++ "       </div>\n"

htmlFoot :: String
htmlFoot =
  "    </div>\n"
  ++ "  </body>\n"
  ++ "</html>\n"

pageHeader :: [Element]
pageHeader =
  [ add_attr (mkAttr "class" "row") $ unode "div" $ unode "h1" "Hets, the DOLiator"
  , add_attr (mkAttr "class" "row") $ unode "div" $
      add_attr (mkAttr "class" "ui text container raised segment center aligned") $
      unode "div" [ unode "p" "Welcome to DOLiator, the web interface to our implementation of the Distributed Ontology, Modeling and Specification Language (DOL)"
                  , add_attr (mkAttr "class" "ui horizontal list") $ unode "div"
                      [ add_attr (mkAttr "target" "_blank") $ add_attr (mkAttr "class" "item") $ aRef "http://dol-omg.org/" "DOL Homepage"
                      , add_attr (mkAttr "target" "_blank") $ add_attr (mkAttr "class" "item") $ aRef "http://hets.eu/" "Hets Homepage"
                      , add_attr (mkAttr "class" "item") $ aRef "mailto:hets-devel@informatik.uni-bremen.de" "Contact"
                      ]
                  ]
  ]

pageOptions :: String -> [Element] -> [Element]
pageOptions path listElements =
  [ add_attr (mkAttr "class" "row") $ unode "div" $
      add_attr (mkAttr "class" "ui relaxed grid container segment") $ unode "div"
        [ add_attr (mkAttr "class" "row centered") $ unode "div" $
            unode "p" "Select a local DOL file as library or enter a DOL specification in the text area or choose one of the minimal examples from the right hand side and press \"Submit\"."
        , add_attr (mkAttr "class" "three column row") $ unode "div"
            [ pageOptionsFile
            , pageOptionsExamples (not $ null path) listElements
            ]
        ]
  ]

pageOptionsFile :: Element
pageOptionsFile =
  add_attr (mkAttr "class" "ui container ten wide column left aligned") $ unode "div" $
    add_attr (mkAttr "class" "ui row") $ unode "div" pageOptionsFileForm


pageOptionsExamples :: Bool -> [Element] -> Element
pageOptionsExamples moreExamplesAreOpen listElements =
  add_attr (mkAttr "class" "ui container six wide column left aligned") $ unode "div"
    [ unode "h4" "Minimal Examples"
    , add_attr (mkAttr "class" "ui list") $ unode "div" $
        map (\ (elementName, inputType, exampleText) ->
              add_attr (mkAttr "class" "item") $ unode "div" $
                add_attrs [ mkAttr "class" "insert-example-into-user-input-text"
                          , mkAttr "data-text" exampleText
                          , mkAttr "data-input-type" inputType
                          ] $ unode "span" elementName
              ) [ ("DOL", "dol", Examples.dol)
                , ("CASL", "casl", Examples.casl)
                , ("OWL", "owl", Examples.owl)
                , ("CLIF", "clif", Examples.clif)
                , ("Propositional", "dol", Examples.propositional)
                , ("RDF", "rdf", Examples.rdf)
                , ("TPTP", "tptp", Examples.tptp)
                , ("HasCASL", "dol", Examples.hascasl)
                , ("Modal", "dol", Examples.modal)
                ]
    , pageMoreExamples moreExamplesAreOpen listElements
    ]

pageOptionsFileForm :: Element
pageOptionsFileForm = add_attr (mkAttr "id" "user-file-form") $
  mkForm "/" [ pageOptionsFilePickerInput
             , horizontalDivider "OR"
             , pageOptionsFileTextArea
             , add_attrs [mkAttr "class" "ui relaxed grid", mkAttr "style" "margin-top: 1em"] $ unode "div"
                 [ add_attr (mkAttr "class" "six wide column") $ unode "div" inputTypeDropDown
                 , add_attr (mkAttr "class" "ten wide column right aligned") $ unode "div" submitButton
                 ]
             ]

inputTypeDropDown :: Element
inputTypeDropDown = singleSelectionDropDown
  "Input Type of File or Text Field"
  "input-type"
  (Just "user-file-input-type")
  ( ("", "[Try to determine automatically]", [])
    : map (\ inType -> (show inType, show inType, [])) plainInTypes
  )

singleSelectionDropDown :: String -> String -> Maybe String -> [(String, String, [Attr])] -> Element
singleSelectionDropDown label inputName htmlIdM options = unode "div"
   [ add_attr (mkAttr "class" "ui sub header") $ unode "div" label
   , add_attrs ( mkAttr "name" inputName
               : maybe [] (\ htmlId -> [mkAttr "id" htmlId]) htmlIdM
               ) $ unode "select" $
         map (\ (optionValue, optionLabel, attributes) ->
               add_attrs (mkAttr "value" optionValue : attributes) $
                 unode "option" optionLabel
             ) options
   ]

checkboxElement :: String -> [Attr] -> Element
checkboxElement label attributes =
  add_attr (mkAttr "class" "four wide column") $ unode "div" $
    add_attr (mkAttr "class" "ui checkbox") $ unode "div"
      [ add_attrs
          ([ mkAttr "type" "checkbox"
          , mkAttr "tabindex" "0"
          , mkAttr "class" "hidden"
          ] ++ attributes) $ unode "input" ""
      , unode "label" label
      ]

pageOptionsFileTextArea :: Element
pageOptionsFileTextArea = add_attrs
  [ mkAttr "cols" "68"
  , mkAttr "rows" "22"
  , mkAttr "name" "content"
  , mkAttr "id" "user-input-text"
  , mkAttr "style" "font-family: monospace;"
  ] $ unode "textarea" ""

pageOptionsFilePickerInput :: Element
pageOptionsFilePickerInput = filePickerInputElement "file" "file" "Choose File..."

pageOptionsFormat :: String -> String -> Element
pageOptionsFormat delimiter path =
  let defaultFormat = "default"
  in  dropDownElement "Output Format" $
        map (\ f ->
              aRef (if f == defaultFormat then "/" </> path else "/" </> path ++ delimiter ++ f) f
            ) (defaultFormat : displayTypes)

filePickerInputElement :: String -> String -> String -> Element
filePickerInputElement idArgument nameArgument title =
  add_attr (mkAttr "class" "field") $ unode "div" $
    add_attr (mkAttr "class" "ui fluid file input action") $ unode "div"
      [ add_attrs [mkAttr "type" "text", mkAttr "readonly" "true"] $ unode "input" ""
      , add_attrs [ mkAttr "type" "file"
                  , mkAttr "id" idArgument
                  , mkAttr "name" nameArgument
                  , mkAttr "autocomplete" "off"
                  ] $ unode "input" ""
      , add_attr (mkAttr "class" "ui button") $ unode "div" title
      ]

dropDownElement :: String -> [Element] -> Element
dropDownElement title items =
  add_attr (mkAttr "class" "ui dropdown button") $ unode "div"
    [ add_attr (mkAttr "class" "text") $ unode "div" title
    , add_attr (mkAttr "class" "dropdown icon") $ unode "i" ""
    , dropDownSubMenu items
    ]

linkButtonElement :: String -> String -> Element
linkButtonElement address label =
  add_attr (mkAttr "class" "ui button") $ aRef address label

htmlRow :: Element -> Element
htmlRow = add_attr (mkAttr "class" "row") . unode "div"

dropDownToLevelsElement :: String -> [(Element, [Element])] -> Element
dropDownToLevelsElement title twoLeveledItems =
  add_attr (mkAttr "class" "ui dropdown button") $ unode "div"
    [ add_attr (mkAttr "class" "text") $ unode "div" title
    , add_attr (mkAttr "class" "dropdown icon") $ unode "i" ""
    , add_attr (mkAttr "class" "menu") $ unode "div" $
        map (\ (label, items) ->
              add_attr (mkAttr "class" "item") $ unode "div"
                (
                  ( if null items
                    then []
                    else [add_attr (mkAttr "class" "dropdown icon") $ unode "i" ""]
                  )
                  ++ [add_attr (mkAttr "class" "text") $ unode "div" label]
                  ++ if null items then [] else [dropDownSubMenu items]
                )
            ) twoLeveledItems
    ]

dropDownSubMenu :: [Element] -> Element
dropDownSubMenu items =
  add_attr (mkAttr "class" "menu") $ unode "div" $
    map (add_attr (mkAttr "class" "item")) items

pageMoreExamples :: Bool -> [Element] -> Element
pageMoreExamples isOpen listElements =
  let activeClass = if isOpen then "active " else "" in
  add_attr (mkAttr "class" "ui ten wide column container left aligned") $ unode "div" $
    add_attr (mkAttr "class" "ui styled accordion") $ unode "div"
      [ add_attr (mkAttr "class" (activeClass ++ "title")) $ unode "div"
          [ add_attr (mkAttr "class" "dropdown icon") $ unode "i" ""
          , unode "span" "More Examples"
          ]
      , add_attr (mkAttr "class" (activeClass ++ "content")) $ unode "div" $
          add_attr (mkAttr "class" "transistion hidden") $ unode "div" $
            unode "ul" listElements
      ]

horizontalDivider :: String -> Element
horizontalDivider label =
  add_attr (mkAttr "class" "ui horizontal divider") $ unode "div" label

mkResponse :: String -> Status -> String -> Response
mkResponse ty st = responseLBS st
  (if null ty then [] else
#ifdef HTTPTYPES
      [headerContentType $ B8.pack ty]
#else
      [(hContentType, B8.pack ty)]
#endif
  ) . BS.pack . encodeString

mkOkResponse :: String -> String -> Response
mkOkResponse ty = mkResponse ty status200

addSess :: Cache -> Session -> IO Int
addSess sessRef s = do
  let k = sessKey s
  atomicModifyIORef sessRef $ \ (m, lm) ->
       ((IntMap.insert k s m, Map.insert (sessPath s) s lm), k)

cleanUpCache :: Cache -> IO ()
cleanUpCache sessRef = do
  let mSize = 60
  time <- getCurrentTime
  atomicModifyIORef sessRef $ \ (m, lm) ->
    if Map.size lm < mSize then ((m, lm), ()) else
    let ss = cleanUpSessions time mSize m
    in ((IntMap.fromList $ map (\ s -> (sessKey s, s)) ss
       , Map.fromList $ map (\ s -> (sessPath s, s)) ss), ())
  where
    cleanUpSessions :: UTCTime -> Int -> IntMap.IntMap Session -> [Session]
    cleanUpSessions time maxSize =
      unifySessionLists . dropCleanables . sessionCleanableLists
      where
        sessionSort :: [Session] -> [Session]
        sessionSort = sortBy (cmpSess time)

        sessionCleanableLists :: IntMap.IntMap Session -> ([Session], [Session])
        sessionCleanableLists =
          partition sessCleanable . sessionSort . IntMap.elems

        dropCleanables :: ([Session], [Session]) -> ([Session], [Session])
        dropCleanables (cleanables, uncleanables) =
          (drop (maxSize `div` 2) cleanables, uncleanables)

        unifySessionLists :: ([Session], [Session]) -> [Session]
        unifySessionLists = sessionSort . uncurry (++)

cmpSess :: UTCTime -> Session -> Session -> Ordering
cmpSess curTime =
  let f s = let
        l = lastAccess s
        b = sessStart s
        d2 = utctDay curTime
        s2 = utctDayTime curTime
        d1 = utctDay l
        s1 = utctDayTime l
        u = usage s
        in if u <= 1 && d1 == d2 && s2 > secondsToDiffTime 3600 + s1
           then (u + 100, diffUTCTime l curTime)
           else (u, diffUTCTime b l)
  in on compare f

addNewSess :: Cache -> Session -> IO Int
addNewSess sessRef sess = do
  cleanUpCache sessRef
  k <- randomKey
  let s = sess { sessKey = k }
  addSess sessRef s

nextSess :: LibEnv -> Session -> Cache -> Int -> IO Session
nextSess newLib =
  modifySessionAndCache "nextSess" (\ s -> s { sessLibEnv = newLib })

makeSessCleanable :: Session -> Cache -> Int -> IO Session
makeSessCleanable =
  modifySessionAndCache "makeSessCleanable" (\ s -> s { sessCleanable = True })

modifySessionAndCache :: String -> (Session -> Session) -> Session -> Cache
                      -> Int -> IO Session
modifySessionAndCache errorMessage f sess sessRef k =
  if k <= 0 then return sess else
    atomicModifyIORef sessRef
      (\ (m, lm) -> case IntMap.lookup k m of
        Nothing -> error errorMessage
        Just s -> let newSess = f s
                  in ((IntMap.insert k newSess m, lm), newSess))


ppDGraph :: DGraph -> Maybe PrettyType -> ResultT IO (String, String)
ppDGraph dg mt = let ga = globalAnnos dg in case optLibDefn dg of
    Nothing -> fail "parsed LIB-DEFN not avaible"
    Just ld ->
      let d = prettyLG logicGraph ld
          latex = renderLatex Nothing $ toLatex ga d
      in case mt of
      Just pty -> case pty of
        PrettyXml -> return
          (xmlC, ppTopElement $ xmlLibDefn logicGraph ga ld)
        PrettyAscii _ -> return (textC, renderText ga d ++ "\n")
        PrettyHtml -> return (htmlC, renderHtml ga d)
        PrettyLatex _ -> return ("application/latex", latex)
      Nothing -> lift $ do
         tmpDir <- getTemporaryDirectory
         tmpFile <- writeTempFile (latexHeader ++ latex ++ latexFooter)
           tmpDir "temp.tex"
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
             return (pdfC, str)
             else return (textC, "could not create pdf:\n"
                  ++ unlines [out1, err1, out2, err2])

increaseUsage :: Cache -> Session -> ResultT IO (Session, Int)
increaseUsage sessRef sess = do
  time <- lift getCurrentTime
  let s2 = sess { usage = usage sess + 1, lastAccess = time }
  k <- lift $ addSess sessRef s2
  return (s2, k)

getDGraph :: HetcatsOpts -> Cache -> DGQuery
  -> ResultT IO (Session, Int)
getDGraph opts sessRef dgQ = do
  (m, lm) <- lift $ readIORef sessRef
  case dgQ of
    NewDGQuery file cmdList -> do
      let cl = mapMaybe (\ s -> find ((== s) . cmdlGlobCmd)
                  $ map fst allGlobLibAct) cmdList
      mf <- lift $ getContentAndFileType opts file
      case mf of
        Left err -> fail err
        Right (_, mh, f, cont) -> case mh of
          Nothing -> fail $ "could determine checksum for: " ++ file
          Just h -> let q = file : h : cmdList in
            case Map.lookup q lm of
            Just sess -> increaseUsage sessRef sess
            Nothing -> do
              (ln, le1) <- if isDgXmlFile opts f cont
                then readDGXmlR opts f Map.empty
                else anaSourceFile logicGraph opts
                  { outputToStdout = False }
                  Set.empty emptyLibEnv emptyDG file
              le2 <- foldM (\ e c -> liftR
                  $ fromJust (lookup c allGlobLibAct) ln e) le1 cl
              time <- lift getCurrentTime
              let sess = Session
                    { sessLibEnv = le2
                    , sessLibName = ln
                    , sessPath = q
                    , sessKey = 0  -- to be updated by addNewSess
                    , sessStart = time
                    , lastAccess = time
                    , usage = 1
                    , sessCleanable = False }
              k <- lift $ addNewSess sessRef sess
              return (sess, k)
    DGQuery k _ -> case IntMap.lookup k m of
      Nothing -> fail "unknown development graph"
      Just sess -> increaseUsage sessRef sess

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

getHetsResponse :: HetcatsOpts -> [W.FileInfo BS.ByteString]
  -> Cache -> [String] -> [QueryPair] -> WebResponse
getHetsResponse opts updates sessRef pathBits query respond = do
  Result ds ms <- liftIO $ runResultT $ case anaUri pathBits query
    $ updateS : globalCommands of
    Left err -> fail err
    Right q -> getHetsResult opts updates sessRef q Nothing OldWebAPI
                  proofFormatterOptions
  respond $ case ms of
    Just (t, s) | not $ hasErrors ds -> mkOkResponse t s
    _ -> mkResponse textC status422 $ showRelDiags 1 ds

getHetsResult :: HetcatsOpts -> [W.FileInfo BS.ByteString]
  -> Cache -> Query.Query -> Maybe String -> UsedAPI -> ProofFormatterOptions
  -> ResultT IO (String, String)
getHetsResult opts updates sessRef (Query dgQ qk) format_ api pfOptions = do
      let semicolon n = map (\ c -> if c == ':' then ';' else c) n
      let getCom n = case lookupComorphism (semicolon n) logicGraph of
                         Just c -> c
                         Nothing -> error $ "comorphism not found: " ++ n
      sk@(sess', k) <- getDGraph opts sessRef dgQ
      sess <- lift $ makeSessCleanable sess' sessRef k
      let libEnv = sessLibEnv sess
      (ln, dg) <- maybe (fail "unknown development graph") return
        $ sessGraph dgQ sess
      let title = libToFileName ln
      let svg = getSVG title ('/' : show k) dg
      case qk of
            DisplayQuery ms -> case format_ `mplus` ms of
              Just "db" -> do
                result <- liftIO $ Control.Exception.catch
                  (do
                    Persistence.DevGraph.exportLibEnv opts libEnv
                    return (jsonC, "{\"savedToDatabase\": true}")
                  )
                  (\ exception ->
                    return (jsonC, "{\"savedToDatabase\": false, \"error\": " ++ show (exception :: SomeException) ++ "}")
                  )
                liftR $ return result
              Just "svg" -> fmap (\ s -> (svgC, s)) svg
              Just "xml" -> liftR $ return (xmlC, ppTopElement
                $ ToXml.dGraph opts libEnv ln dg)
              Just "json" -> liftR $ return (jsonC, ppJson
                $ ToJson.dGraph opts libEnv ln dg)
              Just "dot" -> liftR $ return
                (dotC, dotGraph title False title dg)
              Just "symbols" -> liftR $ return (xmlC, ppTopElement
                $ ToXml.dgSymbols opts dg)
              Just "session" -> liftR $ return (htmlC, ppElement
                $ aRef (mkPath sess ln k) $ show k)
              Just str | elem str ppList
                -> ppDGraph dg $ lookup str $ zip ppList prettyList
              _ -> sessAns ln svg sk
            Query.DGTranslation path -> do
              -- compose the comorphisms passed in translation
               let coms = map getCom $ splitOn ',' path
               com <- foldM compComorphism (head coms) $ tail coms
               dg' <- liftR $ dg_translation libEnv ln dg com
               liftR $ return (xmlC, ppTopElement
                $ ToXml.dGraph opts libEnv ln dg')
            GlProvers mp mt -> do
              availableProvers <- liftIO $ getFullProverList mp mt dg
              return $ case api of
                OldWebAPI -> (xmlC, formatProvers mp $
                  proversToStringAux availableProvers)
                RESTfulAPI -> OProvers.formatProvers format_ mp availableProvers
            GlTranslations -> do
              availableComorphisms <- liftIO $ getFullComorphList dg
              return $ case api of
                OldWebAPI ->
                  (xmlC, formatComorphs availableComorphisms)
                RESTfulAPI ->
                  formatTranslations format_ availableComorphisms
            GlShowProverWindow prOrCons -> showAutoProofWindow dg k prOrCons
            GlAutoProveREST proverMode reasoningParameters -> case api of
              RESTfulAPI -> do
                (newLib, nodesAndProofResults) <-
                  reasonREST opts libEnv ln dg proverMode (queryLib dgQ) reasoningParameters
                if all (null . snd) nodesAndProofResults
                then return (textC, "nothing to prove")
                else do
                  lift $ nextSess newLib sess sessRef k
                  processProofResult format_ pfOptions nodesAndProofResults (opts, libEnv, ln, dg)
              _ -> fail ("The GlAutoProveREST path is only "
                         ++ "available in the REST interface.")
            GlAutoProve (ProveCmd prOrCons incl mp mt tl nds xForm axioms) -> do
              (newLib, nodesAndProofResults) <-
                proveMultiNodes prOrCons libEnv ln dg incl mp mt tl nds axioms
              if all (null . snd) nodesAndProofResults
              then return (textC, "nothing to prove")
              else do
                lift $ nextSess newLib sess sessRef k
                case api of
                  OldWebAPI -> let
                    sens = foldr (\ (dgNodeName, proofResults) res ->
                        formatResultsAux xForm prOrCons dgNodeName proofResults
                        : res
                      ) [] nodesAndProofResults
                    in return (htmlC, formatResultsMultiple xForm k sens prOrCons)
                  RESTfulAPI ->
                    processProofResult format_ pfOptions nodesAndProofResults (opts, libEnv, ln, dg)
            GlobCmdQuery s ->
              case find ((s ==) . cmdlGlobCmd . fst) allGlobLibAct of
              Nothing -> if s == updateS then
                case filter ((== ".xupdate") . takeExtension . B8.unpack
                            . fileName) updates of
                ch : _ -> do
                  let str = BS.unpack $ fileContent ch
                  (newLn, newLib) <- dgXUpdate opts str libEnv ln dg
                  newSess <- lift $ nextSess newLib sess sessRef k
                  sessAns newLn svg (newSess, k)
                [] -> sessAns ln svg sk
                else fail "getHetsResult.GlobCmdQuery"
              Just (_, act) -> do
                newLib <- liftR $ act ln libEnv
                newSess <- lift $ nextSess newLib sess sessRef k
                -- calculate updated SVG-view from modified development graph
                let newSvg = getSVG title ('/' : show k)
                      $ lookupDGraph ln newLib
                sessAns ln newSvg (newSess, k)
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
                    "Node " ++ getDGNodeName dgnode ++ " (#" ++ show i ++ ")\n"
                  ins = getImportNames dg i
                  showN d = showGlobalDoc (globalAnnos dg) d "\n"
              case nc of
                NcCmd cmd | elem cmd [Query.Node, Info, Symbols]
                  -> case cmd of
                   Symbols -> return (xmlC, ppTopElement
                           $ showSymbols opts ins (globalAnnos dg) dgnode)
                   _ -> return (textC, fstLine ++ showN dgnode)
                _ -> case maybeResult $ getGlobalTheory dgnode of
                  Nothing -> fail $
                    "cannot compute global theory of:\n" ++ fstLine
                  Just gTh -> let subL = sublogicOfTh gTh in case nc of
                    ProveNode (ProveCmd pm incl mp mt tl thms xForm axioms) ->
                      case pm of
                      GlProofs -> do
                        (newLib, proofResults) <- proveNode libEnv ln dg nl
                          gTh subL incl mp mt tl thms axioms
                        if null proofResults
                        then return (textC, "nothing to prove")
                        else do
                          lift $ nextSess newLib sess sessRef k
                          case api of
                            OldWebAPI -> return (htmlC,
                              formatResults xForm k i .
                                add_attr (mkAttr "class" "results") $
                                unode "div" $ formatGoals True proofResults)
                            RESTfulAPI -> processProofResult format_ pfOptions
                              [(getDGNodeName dgnode, proofResults)] (opts, libEnv, ln, dg)
                      GlConsistency -> do
                        (newLib, [(_, res, txt, _, _, _, _)]) <-
                          consNode libEnv ln dg nl subL incl mp mt tl
                        lift $ nextSess newLib sess sessRef k
                        return (xmlC, ppTopElement $ formatConsNode res txt)
                    _ -> case nc of
                      NcCmd Query.Theory -> case api of
                          OldWebAPI -> lift $ fmap (\ t -> (htmlC, t))
                                       $ showGlobalTh dg i gTh k fstLine False
                          RESTfulAPI -> return $ 
                                          showNode opts (globalAnnos dg) libEnv dg i format_
                      NcCmd (Query.Translate x) -> do
                          -- compose the comorphisms passed in translation
                          let coms = map getCom $ splitOn ',' x
                          com <- foldM compComorphism (head coms) $ tail coms
                          -- translate the theory of i along com
                          gTh1 <- liftR $ mapG_theory False com gTh
                          -- insert the translation of i in dg
                          let n1 = getNewNodeDG dg
                              labN1 = newInfoNodeLab
                                       emptyNodeName
                                       (newNodeInfo DGBasic) -- to be corrected
                                       gTh1
                              dg1 = insLNodeDG (n1, labN1) dg
                          gmor <- liftR $ gEmbedComorphism com $ signOf $ dgn_theory dgnode
                          -- add a link from i to n1 labeled with (com, id)
                          let (_, dg2) = insLEdgeDG
                                          (i, n1, globDefLink gmor SeeSource) -- origin to be corrected
                                          dg1
                          case api of
                            OldWebAPI -> 
                                 lift $ fmap (\ t -> (htmlC, t))
                                          $ showGlobalTh dg n1 gTh1 k fstLine True
                            RESTfulAPI ->
                            -- show the theory of n1 in xml format
                              return $ showNode opts (globalAnnos dg2) libEnv dg2 n1 format_
                      NcProvers mp mt -> do
                        availableProvers <- liftIO $ getProverList mp mt subL
                        return $ case api of
                          OldWebAPI -> (xmlC, formatProvers mp $
                            proversToStringAux availableProvers)
                          RESTfulAPI ->
                            OProvers.formatProvers format_ mp availableProvers
                      NcTranslations mp -> do
                        availableComorphisms <- liftIO $ getComorphs mp subL
                        return $ case api of
                          OldWebAPI ->
                            (xmlC, formatComorphs availableComorphisms)
                          RESTfulAPI ->
                            formatTranslations format_ availableComorphisms
                      q -> error ("getHetsResult.NodeQuery: unnkown query"++show q)
            EdgeQuery i _ ->
              case getDGLinksById (EdgeId i) dg of
              [e@(_, _, l)] ->
                return (textC, showLEdge e ++ "\n" ++ showDoc l "")
              [] -> fail $ "no edge found with id: " ++ show i
              _ -> fail $ "multiple edges found with id: " ++ show i

processProofResult :: Maybe String
                   -> ProofFormatterOptions
                   -> [(String, [ProofResult])]
                   -> (HetcatsOpts, LibEnv, LibName, DGraph)
                   -> ResultT IO (String, String)
processProofResult (Just "db") _ _ _ =
  return (jsonC, "{\"savedToDatabase\": true}")
processProofResult format_ options nodesAndProofResults (opts, libEnv, ln, dg) =
  do
    joinedResult <- liftR $ getJSONOrXMLResult format_ options nodesAndProofResults opts libEnv ln dg
    let result = prettyWithTag joinedResult
    return result

-- returns the joined data consisting of the development graph and prover results
getJSONOrXMLResult :: Maybe String -> ProofFormatterOptions
                   -> [(String, [ProofResult])] -> HetcatsOpts -> LibEnv
                   -> LibName -> DGraph -> Result JSONOrXML
getJSONOrXMLResult format_ options nodesAndProofResults opts libEnv ln dg =
  let
    proverResults = ("prover_output", formatProofs format_ options nodesAndProofResults)
  in
    case format_ of
      Just "xml" -> joinData ("dgraph", (XML (ToXml.dGraph opts libEnv ln dg)))
                             proverResults
      _ -> joinData ("dgraph", (JSON (ToJson.dGraph opts libEnv ln dg)))
                    proverResults

formatGoals :: Bool -> [ProofResult] -> [Element]
formatGoals includeDetails =
  map (\ (n, e, d, _, _, mps, _) -> add_attr (mkAttr "class" "results-goal") $ unode "div"
    ([ unode "h3" ("Results for " ++ n ++ " (" ++ e ++ ")") ]
    ++ [add_attr (mkAttr "class" "results-details") $ unode "div" d | includeDetails]
    ++ case mps of
        Nothing -> []
        Just ps -> formatProofStatus ps))

formatProofStatus :: ProofStatus G_proof_tree -> [Element]
formatProofStatus ps =
  [ unode "h5" "Used Prover"
  , add_attr (mkAttr "class" "usedProver") $ unode "p" $ usedProver ps
  -- `read` makes this type-unsafe
  , unode "h5" "Tactic Script"
  , add_attr (mkAttr "class" "tacticScript") $ unode "p" $ formatTacticScript $ read $
      (\ (TacticScript ts) -> ts) $ tacticScript ps
  , unode "h5" "Proof Tree"
  , add_attr (mkAttr "class" "proofTree") $ unode "div" $ show $ proofTree ps
  , unode "h5" "Used Time"
  , add_attr (mkAttr "class" "usedTime") $ unode "div" $ formatUsedTime $ usedTime ps
  , unode "h5" "Used Axioms"
  , add_attr (mkAttr "class" "usedAxioms") $ unode "div" $ formatUsedAxioms $ usedAxioms ps
  , unode "h5" "Prover Output"
  , add_attr (mkAttr "class" "proverOutput") $ unode "div" $ formatProverOutput $ proofLines ps
  ]

formatProverOutput :: [String] -> Element
formatProverOutput = unode "pre" . unlines

formatTacticScript :: ATPTacticScript -> [Element]
formatTacticScript ts =
  [ unode "timeLimit" $ show $ tsTimeLimit ts
  , unode "extraOpts" $ map (unode "option") $ tsExtraOpts ts
  ]

formatUsedTime :: TimeOfDay -> [Element]
formatUsedTime tod =
  [ unode "seconds" $ init $ show $ timeOfDayToTime tod
  , unode "components"
    [ unode "hours" $ show $ todHour tod
    , unode "minutes" $ show $ todMin tod
    , unode "seconds" $ show $ todSec tod
    ]
  ]

formatUsedAxioms :: [String] -> [Element]
formatUsedAxioms = map (unode "axiom")

formatConsNode :: String -> String -> Element
formatConsNode res txt = add_attr (mkAttr "state" res) $ unode "result" txt

formatResultsMultiple :: Bool -> Int -> [Element] -> ProverMode -> String
formatResultsMultiple xForm sessId rs prOrCons =
  if xForm then ppTopElement $ unode "Results" rs else let
  goBack1 = case prOrCons of
    GlConsistency -> aRef ('/' : show sessId ++ "?consistency") "return"
    GlProofs -> aRef ('/' : show sessId ++ "?autoproof") "return"
  goBack2 = aRef ('/' : show sessId) "return to DGraph"
  in htmlPage "Results" []
       [ htmlRow $ unode "h1" "Results"
       , htmlRow $ unode "div" [goBack1, goBack2]
       , htmlRow $ unode "div" $
           foldr (\ el r -> unode "h4" (qName $ elName el) : el : r) [] rs
       ] ""

-- | display results of proving session (single node)
formatResults :: Bool -> Int -> Int -> Element -> String
formatResults xForm sessId i rs =
  if xForm || sessId <= 0 then ppTopElement rs else let
  goBack1 = linkButtonElement ('/' : show sessId ++ "?theory=" ++ show i) "return to Theory"
  goBack2 = linkButtonElement ('/' : show sessId) "return to DGraph"
  in htmlPage "Results" []
       [ htmlRow $ unode "h1" "Results"
       , htmlRow $ unode "div" [goBack1, goBack2]
       , htmlRow $ add_attr (mkAttr "class" "ui relaxed grid raised segment container left aligned") $ unode "div" rs
       ] ""

showBool :: Bool -> String
showBool = map toLower . show

showNode :: HetcatsOpts -> GlobalAnnos -> LibEnv -> DGraph -> Int -> Maybe String -> (String,String)
showNode opts ga lenv dg n format_ = 
 let lNodeN = case lab (dgBody dg) n of
       Just lNode -> lNode
       Nothing -> error $ "no node for " ++ show n
 in case format_ of 
           Just "xml" -> (xmlC,ppTopElement $ ToXml.lnode opts ga lenv (n,lNodeN)) 
           Just "json" -> (jsonC,ppJson $ ToJson.lnode opts ga lenv (n,lNodeN))
           Just str | elem str ["dol","het","text"]
                      -> (textC,showGlobalDoc (globalAnnos dg) (dgn_theory lNodeN) "\n")
           _ -> error ("unknown format: "++show format_)

{- | displays the global theory for a node with the option to prove theorems
and select proving options -}
showGlobalTh :: DGraph -> Int -> G_theory -> Int -> String -> Bool -> IO String
showGlobalTh dg i gTh sessId fstLine isTrans = case simplifyTh gTh of
  sGTh@(G_theory lid _ (ExtSign sig _) _ thsens _) -> do
   let
    paths = findComorphismPaths logicGraph (sublogicOfTh gTh) 
    comorSelection = map (\ cm -> let c = showComorph cm in
                              (c, c, [])
                         ) paths
    ga = globalAnnos dg
    -- links to translations and provers xml view
    headr = htmlRow $ unode "h3" fstLine
    thShow = renderHtml ga $ vcat $ map (print_named lid) $ toNamedList thsens
    sbShow = renderHtml ga $ pretty sig
    theoryHeader = htmlRow $ unode "h4" (if isTrans then "Translated theory" else "Theory")
    transForm = if isTrans then []
                else [ htmlRow $ unode "h4" "Translate Theory"
                     , translationForm comorSelection]
    gs = getThGoals sGTh
    in if null gs || isTrans
      -- show simple view if no goals are found
       then return $ htmlPage fstLine ""
                       ([ headr ] ++ transForm ++
                        [ theoryHeader
                        ]) $ "<pre>\n" ++ sbShow ++ "\n<br />" ++ thShow ++ "\n</pre>\n"
      -- else create proving functionality
       else do
        -- create list of theorems, selectable for proving
        let thmSl =
              map (\ (nm, bp) ->
                    let gSt = maybe GOpen basicProofToGStatus bp
                    in checkboxElement (nm ++ "   (" ++ showSimple gSt ++ ")")
                       [ mkAttr "name" $ escStr nm
                       , mkAttr "unproven" $ showBool $ elem gSt [GOpen, GTimeout]
                       ]
                ) gs
        -- select unproven, all or none theorems by button
            (btUnpr, btAll, btNone, jvScr1) = showSelectionButtons True
        -- create prove button and prover/comorphism selection
        (prSl, cmrSl, jvScr2) <- showProverSelection GlProofs [sublogicOfTh gTh]
        let (prBt, timeout) = showProveButton True
        -- hidden param field with "prove=nodeid"
            hidStr = add_attrs [ mkAttr "name" "prove"
              , mkAttr "type" "hidden", mkAttr "style" "display:none;"
              , mkAttr "value" $ show i ] inputNode
        -- combine elements within a form
            thmMenu =
              add_attrs [ mkAttr "name" "thmSel", mkAttr "method" "get"]
                . add_attr (mkAttr "class" "ui form") $ unode "form"
                $ add_attr (mkAttr "class" "ui relaxed grid container left aligned") $ unode "div"
                $ [ add_attr (mkAttr "class" "row") $ unode "div" [hidStr, prSl, cmrSl]
                  , add_attr (mkAttr "class" "row") $ unode "div" [btUnpr, btAll, btNone, timeout]
                  , add_attr (mkAttr "class" "row") $ unode "div" thmSl
                  , add_attr (mkAttr "class" "row") $ unode "div" prBt
                  ]
        -- save dg and return to svg-view
            goBack = linkButtonElement ('/' : show sessId) "Return to DGraph"
        return $ htmlPage fstLine (jvScr1 ++ jvScr2)
         ([ headr
          , goBack ] ++ transForm ++
          [ htmlRow $ unode "h4" "Theorems"
          , thmMenu
          , theoryHeader
          ]) $ "<pre>\n" ++ sbShow ++ "\n<br />" ++ thShow ++ "\n</pre>\n"
  where
    translationForm comorSelection =
      let selectElement =
            add_attr (mkAttr "class" "eight wide column") $ unode "div" $
              singleSelectionDropDown "Translation" "translation" Nothing comorSelection
        -- hidden param field with "theory=nodeid"
          hideStr = add_attrs [ mkAttr "name" "theory"
              , mkAttr "type" "hidden", mkAttr "style" "display:none;"
              , mkAttr "value" $ show i ] inputNode
          translateButton =
            add_attr (mkAttr "class" "eight wide column") $ unode "div" $
              add_attrs [mkAttr "value" "Translate"] submitButton
      in  add_attrs [ mkAttr "name" "translation-form", mkAttr "method" "get"]
            $ add_attr (mkAttr "class" "ui form")
            $ unode "form"
            $ add_attr (mkAttr "class" "ui relaxed grid container left aligned")
            $ unode "div"
            $ add_attr (mkAttr "class" "row")
            $ unode "div" [hideStr, selectElement, translateButton]


-- | show window of the autoproof function
showAutoProofWindow :: DGraph -> Int -> ProverMode
  -> ResultT IO (String, String)
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
        Just gTh -> do
          let br = unode "br " ()
          (prSel, cmSel, jvSc) <- lift $ showProverSelection prOrCons
              [sublogicOfTh gTh]
          return (jvSc, add_attrs
            [ mkAttr "name" "nodeSel", mkAttr "method" "get" ]
            . unode "form" $
            [ hidStr, prSel, cmSel, br, btAll, btNone, btUnpr, timeout
            , include ] ++ intersperse br (prBt : nodeSel))
    return (htmlC, htmlPage title (jvScr1 ++ jvScr2)
               [ goBack, plain " ", nodeMenu ] "")

showProveButton :: Bool -> (Element, Element)
showProveButton isProver = (prBt, timeout) where
        prBt = add_attrs
          [ mkAttr "type" "submit"
          , mkAttr "class" "ui button"
          , mkAttr "value" $ if isProver then "Prove" else "Check"
          ] inputNode
        -- create timeout field
        timeout = add_attr (mkAttr "class" "three wide field") $ unode "div"
          [ unode "label" "Timeout (Sec/Goal)"
          , add_attrs
              [ mkAttr "type" "text"
              , mkAttr "name" "timeout"
              , mkAttr "placeholder" "Timeout (Sec/Goal)"
              , mkAttr "value" "1"
              ] $ unode "input" ""
          ]

-- | select unproven, all or none theorems by button
showSelectionButtons :: Bool -> (Element, Element, Element, String)
showSelectionButtons isProver = (selUnPr, selAll, selNone, jvScr)
  where prChoice = if isProver then "SPASS" else "darwin"
        selUnPr = add_attrs
          [ mkAttr "type" "button"
          , mkAttr "class" "ui button"
          , mkAttr "value" $ if isProver then "Unproven" else "Unchecked"
          , mkAttr "onClick" "chkUnproven()"
          ] inputNode
        selAll = add_attrs
          [ mkAttr "type" "button", mkAttr "value" "All"
          , mkAttr "class" "ui button"
          , mkAttr "onClick" "chkAll(true)"
          ] inputNode
        selNone = add_attrs
          [ mkAttr "type" "button", mkAttr "value" "None"
          , mkAttr "class" "ui button"
          , mkAttr "onClick" "chkAll(false)"
          ] inputNode
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
  -> IO (Element, Element, String)
showProverSelection prOrCons subLs = do
  let jvScr = unlines
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
  pcs <- mapM (liftM proversToStringAux . (case prOrCons of
    GlProofs -> getProversAux
    GlConsistency -> getConsCheckersAux) Nothing) subLs
  let allPrCm = nub $ concat pcs
  -- create prover selection (drop-down)
      prs = add_attr (mkAttr "class" "eight wide column") $ unode "div" $
        singleSelectionDropDown "Prover" "prover" Nothing $
          map (\ p ->
                (p, p, [mkAttr "onClick" $ "updCmSel('" ++ p ++ "')"])
              ) $ showProversOnly allPrCm
  -- create comorphism selection (drop-down)
      cmrs = add_attr (mkAttr "class" "eight wide column") $ unode "div" $
        singleSelectionDropDown "Translation" "translation" Nothing $
          map (\ (cm, ps) -> let c = showComorph cm in
                (c, c, [mkAttr "4prover" $ intercalate ";" ps])
              ) allPrCm
  return (prs, cmrs, jvScr)

showHtml :: FNode -> String
showHtml fn = name fn ++ " " ++ goalsToPrefix (toGtkGoals fn)

getAllAutomaticProvers :: G_sublogics -> IO [(G_prover, AnyComorphism)]
getAllAutomaticProvers subL =
  getUsableProvers ProveCMDLautomatic subL logicGraph

filterByProver :: Maybe String -> [(G_prover, AnyComorphism)]
  -> [(G_prover, AnyComorphism)]
filterByProver mp = case mp of
      Nothing -> id
      Just p -> filter ((== p) . mkNiceProverName . getProverName . fst)

filterByComorph :: Maybe String -> [(a, AnyComorphism)]
  -> [(a, AnyComorphism)]
filterByComorph mt = case mt of
      Nothing -> id
      Just c -> filter ((== c) . showComorph . snd)

getProverAndComorph :: Maybe String -> Maybe String -> G_sublogics
   -> IO [(G_prover, AnyComorphism)]
getProverAndComorph mp mc subL = do
   ps <- getFilteredProvers mc subL
   let spps = case filterByProver (Just "SPASS") ps of
          [] -> ps
          fps -> fps
   return $ case mp of
        Nothing -> spps
        _ -> filterByProver mp ps

getProverList :: ProverMode -> Maybe String -> G_sublogics
              -> IO [(AnyComorphism, [ProverOrConsChecker])]
getProverList mp mt subL = case mp of
  GlProofs -> getProversAux mt subL
  GlConsistency -> getConsCheckersAux mt subL

getFullProverList :: ProverMode -> Maybe String -> DGraph
                  -> IO [(AnyComorphism, [ProverOrConsChecker])]
getFullProverList mp mt = foldM
  (\ ls (_, nd) -> maybe (return ls) (fmap (++ ls) . case mp of
      GlProofs -> getProversAux mt
      GlConsistency -> getConsCheckersAux mt
    . sublogicOfTh)
    $ maybeResult $ getGlobalTheory nd) [] . labNodesDG

groupOnSnd :: Eq b => (a -> c) -> [(a, b)] -> [(b, [c])]
groupOnSnd f =
  map (\ l@((_, b) : _) -> (b, map (f . fst) l)) . groupBy (on (==) snd)

proversToStringAux :: [(AnyComorphism, [ProverOrConsChecker])]
                   -> [(AnyComorphism, [String])]
proversToStringAux = map (\ (x, ps) ->
                           (x, map (mkNiceProverName . internalProverName) ps))

{- | gather provers and comorphisms and resort them to
(comorhism, supported provers) while not changing orig comorphism order -}
getProversAux :: Maybe String -> G_sublogics
              -> IO [(AnyComorphism, [ProverOrConsChecker])]
getProversAux mt x =
  fmap (groupOnSnd AbsState.Prover) $ getFilteredProvers mt x

getFilteredProvers :: Maybe String -> G_sublogics
  -> IO [(G_prover, AnyComorphism)]
getFilteredProvers mt = fmap (filterByComorph mt) . getAllAutomaticProvers

formatProvers :: ProverMode -> [(AnyComorphism, [String])] -> String
formatProvers pm = let
  tag = case pm of
          GlProofs -> "prover"
          GlConsistency -> "consistency-checker"
  in ppTopElement . unode (tag ++ "s") . map (unode tag)
  . showProversOnly

-- | retrieve a list of consistency checkers
getConsCheckersAux :: Maybe String -> G_sublogics
  -> IO [(AnyComorphism, [ProverOrConsChecker])]
getConsCheckersAux mt =
  fmap (groupOnSnd AbsState.ConsChecker) . getFilteredConsCheckers mt

getFilteredConsCheckers :: Maybe String -> G_sublogics
  -> IO [(G_cons_checker, AnyComorphism)]
getFilteredConsCheckers mt = fmap
  (filterByComorph mt . filter (getCcBatch . fst))
  . getConsCheckers . findComorphismPaths logicGraph

getComorphs :: Maybe String -> G_sublogics -> IO [(G_prover, AnyComorphism)]
getComorphs mp = fmap (filterByProver mp)
    . getAllAutomaticProvers

getFullComorphList :: DGraph -> IO [(G_prover, AnyComorphism)]
getFullComorphList = foldM
   (\ ls (_, nd) -> maybe (return ls)
    (fmap (++ ls) . getAllAutomaticProvers . sublogicOfTh)
    $ maybeResult $ getGlobalTheory nd) [] . labNodesDG

formatComorphs :: [(G_prover, AnyComorphism)] -> String
formatComorphs = ppTopElement . unode "translations"
    . map (unode "comorphism") . nubOrd . map (showComorph . snd)

consNode :: LibEnv -> LibName -> DGraph -> (Int, DGNodeLab)
  -> G_sublogics -> Bool -> Maybe String -> Maybe String -> Maybe Int
  -> ResultT IO (LibEnv, [ProofResult])
consNode le ln dg nl@(i, lb) subL useTh mp mt tl = do
  (cc, c) <- liftIO $ findConsChecker mt subL mp
  lift $ do
    cstat <- consistencyCheck useTh cc c ln le dg nl $ fromMaybe 1 tl
    -- Consistency Results are stored in LibEnv via DGChange object
    let cSt = sType cstat
        le'' = if cSt == CSUnchecked then le else
               Map.insert ln (changeDGH dg $ SetNodeLab lb
                 (i, case cSt of
                       CSInconsistent -> markNodeInconsistent "" lb
                       CSConsistent -> markNodeConsistent "" lb
                       _ -> lb)) le
    return (le'', [(" ", drop 2 $ show cSt, show cstat,
                    AbsState.ConsChecker cc, c, Nothing, Just $ sMessage cstat)])

findConsChecker :: Maybe String -> G_sublogics -> Maybe String
                -> IO (G_cons_checker, AnyComorphism)
findConsChecker translationM gSublogic consCheckerNameM = do
  consList <- getFilteredConsCheckers translationM gSublogic
  let findCC x = filter ((== x ) . getCcName . fst) consList
      consCheckersL = maybe (findCC "darwin") findCC consCheckerNameM
  case consCheckersL of
        [] -> fail "no cons checker found"
        (gConsChecker, comorphism) : _ -> return (gConsChecker, comorphism)

reasonREST :: HetcatsOpts -> LibEnv -> LibName -> DGraph -> ProverMode
           -> String -> ReasoningParameters
           -> ResultT IO (LibEnv, [(String, [ProofResult])])
reasonREST opts libEnv libName dGraph_ proverMode location reasoningParameters = do
  reasoningCacheE <- liftIO buildReasoningCache
  failOnLefts reasoningCacheE
  let reasoningCache1 = rights reasoningCacheE
  reasoningCache2 <- liftIO $ PGIP.Server.setupReasoning opts reasoningCache1
  (libEnv', cacheGoalsAndProofResults) <-
    PGIP.Server.performReasoning opts libEnv libName
      dGraph_ location reasoningCache2
  let nodesAndProofResults = map
        (\ (nodeLabel, proofResults) ->
          (show (getName $ dgn_name nodeLabel), proofResults)
        )
        cacheGoalsAndProofResults
  return (libEnv', nodesAndProofResults)
  where
    useDatabase :: Bool
    useDatabase = format reasoningParameters == Just "db"

    failOnLefts :: ReasoningCacheE -> ResultT IO ()
    failOnLefts reasoningCache =
      let lefts_ = lefts reasoningCache
      in  unless (null lefts_) $ fail $ unlines lefts_

    buildReasoningCache :: IO ReasoningCacheE
    buildReasoningCache =
      let reasoningParametersGroupedByNodeName =
            groupBy (\ a b ->
                      ReasoningParameters.node a == ReasoningParameters.node b
                    ) $ ReasoningParameters.goals reasoningParameters
      in  foldM buildReasoningCacheForNode [] reasoningParametersGroupedByNodeName

    buildReasoningCacheForNode :: ReasoningCacheE
                               -> [ReasoningParameters.GoalConfig]
                               -> IO ReasoningCacheE
    buildReasoningCacheForNode reasoningCacheE goalConfigsOfSameNode =
      let nodeName = ReasoningParameters.node $ head goalConfigsOfSameNode
          nodeM = find (\ (_, nodeLabel) ->
                         showName (dgn_name nodeLabel) == nodeName
                       ) $ labNodesDG dGraph_
      in  case nodeM of
            Nothing ->
              return (Left ("Node \"" ++ nodeName ++ "\" not found")
                       : reasoningCacheE)
            Just node_@(_, nodeLabel) -> do
              let gTheoryM = maybeResult $ getGlobalTheory nodeLabel
              gTheory <- case gTheoryM of
                Nothing ->
                  fail ("Cannot compute global theory of: "
                        ++ showName (dgn_name nodeLabel) ++ "\n")
                Just gTheory -> return gTheory
              let gSublogic = sublogicOfTh gTheory
              foldM (buildReasoningCacheForGoal nodeName node_ gTheory gSublogic)
                reasoningCacheE goalConfigsOfSameNode

    buildReasoningCacheForGoal :: String
                               -> (Int, DGNodeLab)
                               -> G_theory
                               -> G_sublogics
                               -> ReasoningCacheE
                               -> ReasoningParameters.GoalConfig
                               -> IO ReasoningCacheE
    buildReasoningCacheForGoal nodeName node_ gTheory gSublogic reasoningCacheE goalConfig =
      let reasonerM = reasoner $ reasonerConfiguration goalConfig
          translationM = translation goalConfig
          timeLimit_ = ReasoningParameters.timeLimit $
            reasonerConfiguration goalConfig
          caseReasoningCacheEntry = ReasoningCacheGoal
            { rceProverMode = proverMode
            , rceNode = node_
            , rceGoalNameM = Nothing
            , rceGoalConfig = goalConfig
            , rceGTheory = gTheory
            , rceGSublogic = gSublogic
            , rceReasoner = undefined -- will be overwritten a few lines below
            , rceComorphism = undefined -- will be overwritten a few lines below
            , rceTimeLimit = timeLimit_
            , rceUseDatabase = useDatabase
            , rceReasonerConfigurationKeyM = Nothing
            , rceReasoningAttemptKeyM = Nothing
            }
      in  case proverMode of
            GlConsistency -> do
              (gConsChecker, comorphism) <-
                findConsChecker translationM gSublogic reasonerM
              return ((Right $ caseReasoningCacheEntry
                       { rceReasoner = AbsState.ConsChecker gConsChecker
                       , rceComorphism = comorphism
                       }
                     ) : reasoningCacheE)
            GlProofs -> do
              proversAndComorphisms <-
                getProverAndComorph reasonerM translationM gSublogic
              (gProver, comorphism) <- case proversAndComorphisms of
                [] -> fail ("No matching translation or prover found for "
                            ++ nodeName ++ "\n")
                (gProver, comorphism) : _ ->
                  return (gProver, comorphism)
              let possibleGoalNames = map fst $ getThGoals gTheory :: [String]
              let goalNames = (case conjecture goalConfig of
                    Nothing -> possibleGoalNames
                    Just goalName_ ->
                      filter (== goalName_) possibleGoalNames) :: [String]
              return
                (map (\ goalName_ -> Right $ caseReasoningCacheEntry
                       { rceGoalNameM = Just goalName_
                       , rceReasoner = AbsState.Prover gProver
                       , rceComorphism = comorphism
                       }
                     ) goalNames ++ reasoningCacheE)

setupReasoning :: HetcatsOpts -> ReasoningCache -> IO ReasoningCache
setupReasoning opts reasoningCache =
  mapM (\ reasoningCacheGoal -> do
         reasoningConfigurationKey <-
           Persistence.Reasoning.setupReasoning opts reasoningCacheGoal
         return reasoningCacheGoal
           { rceReasonerConfigurationKeyM = reasoningConfigurationKey }
       ) reasoningCache


performReasoning :: HetcatsOpts -> LibEnv -> LibName -> DGraph
                 -> String -> ReasoningCache
                 -> ResultT IO (LibEnv, [(DGNodeLab, [ProofResult])])
performReasoning opts libEnv libName dGraph_ location reasoningCache = do
  (libEnv', nodesAndProofResults') <- liftIO $ foldM
    (\ (libEnvAcc1, nodesAndProofResults1) reasoningCacheGoalsByNode -> do
      let nodeLabel = snd $ rceNode $ head reasoningCacheGoalsByNode
      (libEnvAcc2, proofResults2) <-
        foldM
          (\ (libEnvAcc3, proofResults3) reasoningCacheGoal -> do
            -- update state
            let gTheoryM = maybeResult $ getGlobalTheory nodeLabel
            gTheory_ <- case gTheoryM of
              Nothing ->
                fail ("Cannot compute global theory of: "
                      ++ showName (dgn_name nodeLabel) ++ "\n")
              Just gTheory_ -> return gTheory_
            let reasoningCacheGoal' = reasoningCacheGoal { rceGTheory = gTheory_ }

            -- preprocess (with database)
            (premisesM, reasoningCacheGoal3) <-
              Persistence.Reasoning.preprocessReasoning opts location
                reasoningCacheGoal'

            -- run the reasoner
            Result _ (Just (libEnvAcc4, proofResult : _)) <- runResultT $
              runReasoning libEnvAcc3 libName dGraph_ reasoningCacheGoal3 premisesM

            -- postprocess (with database)
            Persistence.Reasoning.postprocessReasoning opts reasoningCacheGoal3
              premisesM proofResult

            -- update state
            let proofResults4 = proofResult : proofResults3
            return (libEnvAcc4, proofResults4)
          )
          (libEnvAcc1, [])
          reasoningCacheGoalsByNode
      return (libEnvAcc2, (nodeLabel, proofResults2) : nodesAndProofResults1)
    )
    (libEnv, []) $
    groupBy sameNode reasoningCache
  return (libEnv', nodesAndProofResults')
  where
    sameNode :: ReasoningCacheGoal -> ReasoningCacheGoal -> Bool
    sameNode a b = fst (rceNode a) == fst (rceNode b)

runReasoning :: LibEnv -> LibName -> DGraph
             -> ReasoningCacheGoal -> Maybe [String]
             -> ResultT IO (LibEnv, [ProofResult])
runReasoning libEnv libName dGraph_ reasoningCacheGoal premisesM =
  let node_ = rceNode reasoningCacheGoal
      gTheory_ = rceGTheory reasoningCacheGoal
      gSublogic = rceGSublogic reasoningCacheGoal
      useTheorems_ = fromMaybe True $ useTheorems $ rceGoalConfig reasoningCacheGoal
      reasonerM = reasoner $ reasonerConfiguration $ rceGoalConfig reasoningCacheGoal
      translationM = translation $ rceGoalConfig reasoningCacheGoal
      timeLimitM = Just $ ReasoningParameters.timeLimit $ reasonerConfiguration $
                     rceGoalConfig reasoningCacheGoal
      goalName_ = fromJust $ rceGoalNameM reasoningCacheGoal
      premises = fromMaybe [] premisesM
  in  case rceProverMode reasoningCacheGoal of
        GlConsistency -> consNode libEnv libName dGraph_ node_ gSublogic
          useTheorems_ reasonerM translationM timeLimitM
        GlProofs -> proveNode libEnv libName dGraph_ node_ gTheory_ gSublogic
          useTheorems_ reasonerM translationM timeLimitM [goalName_] premises

proveNode :: LibEnv -> LibName -> DGraph -> (Int, DGNodeLab)
  -> G_theory -> G_sublogics -> Bool
  -> Maybe String -> Maybe String -> Maybe Int
  -> [String] -> [String]
  -> ResultT IO (LibEnv, [ProofResult])
proveNode le ln dg nl gTh subL useTh mp mt tl thms axioms = do
 ps <- lift $ getProverAndComorph mp mt subL
 case ps of
  [] -> fail "no matching translation or prover found"
  cp : _ -> do
    let ks = map fst $ getThGoals gTh
        diffs = Set.difference (Set.fromList thms)
                $ Set.fromList ks
    unless (Set.null diffs) . fail $ "unknown theorems: " ++ show diffs
    when (null thms && null ks) $ fail "no theorems to prove"
    let selectedGoals_ = if null thms then ks else thms
    let timeLimit_ = maybe 1 (max 1) tl
    (nTh, sens, proofStatuses) <- do
      let premises = axioms
      ((nTh, sens), (_, proofStatuses)) <-
        autoProofAtNode useTh timeLimit_ selectedGoals_ premises gTh cp
      return (nTh, sens, proofStatuses)
    return ( if null sens
             then le
             else Map.insert ln ( updateLabelTheory le ln dg nl nTh) le
           , combineToProofResult sens cp proofStatuses
           )

combineToProofResult :: [(String, String, String)] -> (G_prover, AnyComorphism)
  -> [ProofStatus G_proof_tree] -> [ProofResult]
combineToProofResult sens (prover, comorphism) proofStatuses = let
  findProofStatusByName :: String -> Maybe (ProofStatus G_proof_tree)
  findProofStatusByName n =
    case filter ((n ==) . goalName) proofStatuses of
      [] -> Nothing
      (ps : _) -> Just ps
  combineSens :: (String, String, String) -> ProofResult
  combineSens (n, e, d) = (n, e, d, AbsState.Prover prover, comorphism,
                           findProofStatusByName n, Nothing)
  in map combineSens sens

-- run over multiple dgnodes and prove available goals for each
proveMultiNodes :: ProverMode -> LibEnv -> LibName -> DGraph
  -> Bool -> Maybe String -> Maybe String -> Maybe Int -> [String] -> [String]
  -> ResultT IO (LibEnv, [(String, [ProofResult])])
proveMultiNodes pm le ln dg useTh mp mt tl nodeSel axioms = let
  runProof :: LibEnv -> G_theory -> (Int, DGNodeLab)
    -> ResultT IO (LibEnv, [ProofResult])
  runProof le' gTh nl = let
    subL = sublogicOfTh gTh
    dg' = lookupDGraph ln le' in case pm of
    GlConsistency -> consNode le' ln dg' nl subL useTh mp mt tl
    GlProofs ->
      proveNode le' ln dg' nl gTh subL useTh mp mt tl
        (map fst $ getThGoals gTh) axioms
  nodes2check = filter (case nodeSel of
    [] -> case pm of
            GlConsistency -> const True
            GlProofs -> hasOpenGoals . snd
    _ -> (`elem` nodeSel) . getDGNodeName . snd) $ labNodesDG dg
  in foldM
  (\ (le', res) nl@(_, dgn) ->
    case maybeResult $ getGlobalTheory dgn of
      Nothing -> fail $
                    "cannot compute global theory of:\n" ++ show dgn
      Just gTh -> do
        (le'', proofResults) <- runProof le' gTh nl
        return (le'', (getDGNodeName dgn, proofResults) : res)
  )
  (le, [])
  nodes2check

formatResultsAux :: Bool -> ProverMode -> String -> [ProofResult] -> Element
formatResultsAux xF pm nm sens = unode nm $ case (sens, pm) of
    ([(_, e, d, _, _, _, _)], GlConsistency) | xF -> formatConsNode e d
    _ -> add_attr (mkAttr "class" "results") $ unode "div" $ formatGoals xF sens

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

sessAns :: LibName -> ResultT IO String -> (Session, Int)
  -> ResultT IO (String, String)
sessAns libName svgComp (sess, k) =
  svgComp >>= \ svg -> return $ sessAnsAux libName svg (sess, k)

sessAnsAux :: LibName -> String -> (Session, Int) -> (String, String)
sessAnsAux libName svg (sess, k) =
  let libEnv = sessLibEnv sess
      ln = libToFileName libName
      libref l =
        ( aRef (mkPath sess l k) (libToFileName l)
        , aRef (mkPath sess l k) "default"
            : map (\ d -> aRef (extPath sess l k ++ d) d) displayTypes
        )
      libPath = extPath sess libName k
      ref d = aRef (libPath ++ d) d
      autoProofBt = aRef ('/' : show k ++ "?autoproof") "automatic proofs"
      consBt = aRef ('/' : show k ++ "?consistency") "consistency checker"
-- the html quicklinks to nodes and edges have been removed with R.16827
  in  ( htmlC
      , htmlPage
          ("Hets, the DOLiator - (" ++ shows k ")" ++ ln)
          []
          [ add_attr (mkAttr "class" "row") (unode "div" $ unode "h1" ("Library " ++ ln))
          , add_attr (mkAttr "class" "row") $ unode "div"
              [ pageOptionsFormat "" libPath
              , dropDownElement "Tools" [autoProofBt, consBt]
              , dropDownElement "Commands" (map ref globalCommands)
              , dropDownToLevelsElement "Imported Libraries" $ map libref $ Map.keys libEnv
              ]
          , add_attr (mkAttr "class" "row") $ unode "div" $ unode "h3" "Development Graph (click on node or edge)"
          ]
          svg
      )

getHetsLibContent :: HetcatsOpts -> String -> [QueryPair] -> IO [Element]
getHetsLibContent opts dir query = do
  let hlibs = libdirs opts
  ds <- if null dir || isAbsolute dir then return hlibs else
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

plain :: String -> Element
plain = unode "p"

inputNode :: Element
inputNode = unode "input" ()

submitButton :: Element
submitButton = add_attrs
    [ mkAttr "type" "submit"
    , mkAttr "value" "submit"
    , mkAttr "class" "ui button"
    ] inputNode

mkForm :: String -> [Element] -> Element
mkForm a =
  add_attrs [ mkAttr "action" a
            , mkAttr "enctype" "multipart/form-data"
            , mkAttr "method" "post"
            , mkAttr "class" "ui basic form"
            ] . unode "form"
