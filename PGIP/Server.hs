{- |
Module      :  $Header$
Description :  run hets as server
Copyright   :  (c) Christian Maeder, DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (via imports)

-}

module PGIP.Server (hetsServer, sourceToBs) where

import PGIP.Query

import Driver.Options
import Driver.ReadFn

import Network.Wai.Handler.SimpleServer
import Network.Wai
import Network.Wai.Parse

import qualified Data.ByteString.Lazy.Char8 as BS
import qualified Data.ByteString.Char8 as B8

import Static.ComputeTheory
import Static.GTheory
import Static.DevGraph
import Static.PrintDevGraph
import Static.DotGraph
import Static.AnalysisLibrary
import Static.ToXml as ToXml
import Static.ApplyChanges

import Interfaces.Command
import Interfaces.CmdAction

import Comorphisms.LogicGraph

import Logic.Prover
import Logic.Grothendieck
import Logic.Comorphism
import Logic.Logic

import Proofs.AbstractState

import Text.XML.Light

import Common.DocUtils
import Common.LibName
import Common.Result
import Common.ResultT
import Common.ToXml
import Common.Utils

import Control.Monad.Trans (lift)
import Control.Monad

import qualified Data.Map as Map
import qualified Data.IntMap as IntMap
import qualified Data.Set as Set
import Data.Char
import Data.IORef
import Data.Maybe
import Data.List
import Data.Ord
import Data.Graph.Inductive.Graph (lab)
import Data.Time.Clock

import System.Random
import System.Process
import System.Directory
import System.Exit
import System.FilePath

data Session = Session
  { sessLibEnv :: LibEnv
  , sessLibName :: LibName
  , _previousKeys :: [Int]
  , _sessStart :: UTCTime }

randomKey :: IO Int
randomKey = randomRIO (100000000, 999999999)

sessGraph :: DGQuery -> Session -> Maybe (LibName, DGraph)
sessGraph dgQ (Session le ln _ _) = case dgQ of
  DGQuery _ (Just path) ->
      find (\ (n, _) -> show (getLibId n) == path)
        $ Map.toList le
  _ -> fmap (\ dg -> (ln, dg)) $ Map.lookup ln le

hetsServer :: HetcatsOpts -> IO ()
hetsServer opts1 = do
  tempDir <- getTemporaryDirectory
  let tempHetsLib = tempDir </> "MyHetsLib"
      opts = opts1 { libdirs = tempHetsLib : libdirs opts1 }
  createDirectoryIfMissing False tempHetsLib
  sessRef <- newIORef IntMap.empty
  run 8000 $ \ re ->
    let query = B8.unpack $ queryString re
        path = dropWhile (== '/') $ B8.unpack (pathInfo re)
    in case B8.unpack (requestMethod re) of
    "GET" -> if query == "?menus" then mkMenuResponse else do
         dirs@(_ : cs) <- getHetsLibContent opts path query
         if null cs then getHetsResponse opts [] sessRef path query
           else mkHtmlPage path dirs
    "POST" -> do
      (_, files) <- parseRequestBody tempFileSink re
      case files of
        [] -> return $ mkResponse status400 "no file uploaded"
        [(_, f)] | query /= "?update" -> do
           let fn = takeFileName $ B8.unpack $ fileName f
           if any isAlphaNum fn then do
             copyFile (fileContent f) (tempHetsLib </> fn)
             dirs <- getHetsLibContent opts "" query
             mkHtmlPage "" dirs
            else return $ mkResponse status400 $ "illegal file name: " ++ fn
        _ -> getHetsResponse opts (map snd files) sessRef path query
    _ -> return $ mkResponse status405 ""

-- for debugging purposes copied from Network.Wai.Parse
sourceToBs :: Source -> IO B8.ByteString
sourceToBs = fmap B8.concat . go id
  where
    go front (Source src) = do
        res <- src
        case res of
            Nothing -> return $ front []
            Just (bs, src') -> go (front . (:) bs) src'

mkMenuResponse :: IO Response
mkMenuResponse = return $ mkOkResponse $ ppTopElement $ unode "menus" mkMenus

mkMenus :: [Element]
mkMenus = menuTriple "" "Get menu triples" "menus"
  : menuTriple "/DGraph" "update" "update"
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
  (headElems path ++ [unode "ul" dirs])

mkHtmlElem :: String -> [Element] -> String
mkHtmlElem title body = ppElement $ unode "html"
                [ unode "head" $ unode "title" title
                , unode "body" body ]

mkHtmlPage :: FilePath -> [Element] -> IO Response
mkHtmlPage path = return . mkOkResponse . mkHtmlString path

mkResponse :: Status -> String -> Response
mkResponse st = Response st [] . ResponseLBS . BS.pack

mkOkResponse :: String -> Response
mkOkResponse = mkResponse status200

addNewSess :: IORef (IntMap.IntMap Session) -> Session -> IO Int
addNewSess sessRef sess = do
  k <- randomKey
  atomicModifyIORef sessRef
      (\ m -> (IntMap.insert k sess m, k))

nextSess :: IORef (IntMap.IntMap Session) -> LibEnv -> Int -> IO Session
nextSess sessRef newLib k =
    atomicModifyIORef sessRef
      (\ m -> case IntMap.lookup k m of
      Nothing -> error "nextSess"
      Just s -> let newSess = s { sessLibEnv = newLib }
        in (IntMap.insert k newSess m, newSess))

getDGraph :: HetcatsOpts -> IORef (IntMap.IntMap Session) -> DGQuery
  -> ResultT IO (Session, Int)
getDGraph opts sessRef dgQ = case dgQ of
  NewDGQuery file -> do
    (ln, le) <- anaLibFileOrGetEnv logicGraph opts { outputToStdout = False }
      Set.empty emptyLibEnv emptyDG (fileToLibName opts file) file
    time <- lift getCurrentTime
    let sess = Session le ln [] time
    k <- lift $ addNewSess sessRef sess
    return (sess, k)
  DGQuery k _ -> do
    m <- lift $ readIORef sessRef
    case IntMap.lookup k m of
      Nothing -> liftR $ fail "unknown development graph"
      Just sess -> return (sess, k)

getSVG :: FilePath -> DGraph -> ResultT IO String
getSVG file dg = do
    (exCode, out, err) <- lift $ readProcessWithExitCode "dot" ["-Tsvg"]
          $ dotGraph file False dg
    case exCode of
      ExitSuccess -> liftR $ extractSVG out
      _ -> fail err

extractSVG :: String -> Result String
extractSVG str = case parseXMLDoc str of
  Nothing -> fail "did not recognize svg element"
  Just e -> return $ showTopElement e

cmpFilePath :: FilePath -> FilePath -> Ordering
cmpFilePath f1 f2 = case comparing hasTrailingPathSeparator f2 f1 of
  EQ -> compare f1 f2
  c -> c

getHetsResponse :: HetcatsOpts -> [FileInfo FilePath]
  -> IORef (IntMap.IntMap Session) -> FilePath
  -> String -> IO Response
getHetsResponse opts updates sessRef path query = do
  Result ds ms <- getHetsResult opts updates sessRef path query
  return $ case ms of
    Nothing -> mkResponse status400 $ showRelDiags 1 ds
    Just s -> mkOkResponse s

getHetsResult :: HetcatsOpts -> [FileInfo FilePath]
  -> IORef (IntMap.IntMap Session) -> FilePath
  -> String -> IO (Result String)
getHetsResult opts updates sessRef file query =
  runResultT $ case anaUri file $ dropWhile (== '?')
                 $ filter (not . isSpace) query of
    Left err -> fail err
    Right (Query dgQ qk) -> do
      sk@(sess, k) <- getDGraph opts sessRef dgQ
      let libEnv = sessLibEnv sess
      case sessGraph dgQ sess of
        Nothing -> fail $ "unknown library given by: " ++ file
        Just (ln, dg) ->
          case qk of
            DisplayQuery ms -> case ms of
              Just "svg" -> getSVG file dg
              Just "xml" -> liftR $ return $ ppTopElement
                $ ToXml.dGraph libEnv (getFilePath ln) dg
              Just "dot" -> liftR $ return $ dotGraph file False dg
              Just "session" -> liftR $ return $ ppElement
                $ aRef (mkPath sess ln k) (show k)
              _ -> liftR $ return $ sessAns ln sk
            GlobCmdQuery s ->
              case find ((s ==) . cmdlGlobCmd . fst) allGlobLibAct of
              Nothing -> if s == "update" then
                case filter ((== ".xupdate") . takeExtension . B8.unpack
                            . fileName) updates of
                ch : _ -> do
                  str <- lift $ readFile $ fileContent ch
                  newDg <- liftR $ applyXUpdates str dg
                  let newLib = Map.insert ln newDg libEnv
                  newSess <- lift $ nextSess sessRef newLib k
                  liftR $ return $ sessAns ln (newSess, k)
                [] -> liftR $ return $ sessAns ln sk
                else fail "getHetsResult.GlobCmdQuery"
              Just (_, act) -> do
                newLib <- liftR $ act ln libEnv
                newSess <- lift $ nextSess sessRef newLib k
                liftR $ return $ sessAns ln (newSess, k)
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
                    "node " ++ getDGNodeName dgnode ++ " " ++ show i ++ "\n"
                  showN d = showGlobalDoc (globalAnnos dg) d "\n"
              case nc of
                NcInfo -> return $ fstLine ++ showN dgnode
                _ -> case maybeResult $ getGlobalTheory dgnode of
                  Nothing -> fail $
                    "cannot compute global theory of:\n" ++ fstLine
                  Just gTh -> let subL = sublogicOfTh gTh in case nc of
                    ProveNode incl mp mt tl thms -> do
                      (newLib, sens) <- proveNode libEnv ln dg nl
                                  gTh subL incl mp mt tl thms
                      if null sens then return "nothing to prove" else do
                        lift $ nextSess sessRef newLib k
                        return $ ppTopElement $ unode "results" $
                           map (\ (n, e) -> unode "goal"
                             [unode "name" n, unode "result" e]) sens
                    _ -> return $ case nc of
                      NcTheory -> fstLine ++ showN gTh
                      NcProvers mt -> getProvers mt subL
                      NcTranslations mp -> getComorphs mp subL
                      _ -> error "getHetsResult.NodeQuery."
            EdgeQuery i _ ->
              case getDGLinksById i dg of
              [e@(_, _, l)] -> return $ showLEdge e ++ "\n" ++ showDoc l ""
              [] -> fail $ "no edge found with id: " ++ showEdgeId i
              _ -> fail $ "multiple edges found with id: " ++ showEdgeId i

getAllAutomaticProvers :: G_sublogics -> [(G_prover, AnyComorphism)]
getAllAutomaticProvers subL = getAllProvers ProveCMDLautomatic subL logicGraph

filterByProver :: Maybe String -> [(G_prover, AnyComorphism)]
  -> [(G_prover, AnyComorphism)]
filterByProver mp = case mp of
      Nothing -> id
      Just p -> filter ((== p) . getWebProverName . fst)

filterByComorph :: Maybe String -> [(G_prover, AnyComorphism)]
  -> [(G_prover, AnyComorphism)]
filterByComorph mt = case mt of
      Nothing -> id
      Just c -> filter ((== c) . showComorph . snd)

getProverAndComorph :: Maybe String -> Maybe String -> G_sublogics
   -> [(G_prover, AnyComorphism)]
getProverAndComorph mp mc subL =
   let ps = filterByComorph mc $ getAllAutomaticProvers subL
       spps = case filterByProver (Just "SPASS") ps of
          [] -> ps
          fps -> fps
   in case mp of
        Nothing -> spps
        _ -> case filterByProver mp ps of
               [] -> spps
               mps -> mps

showComorph :: AnyComorphism -> String
showComorph (Comorphism cid) = removeFunnyChars . drop 1 . dropWhile (/= ':')
  . map (\ c -> if c == ';' then ':' else c)
  $ language_name cid

removeFunnyChars :: String -> String
removeFunnyChars = filter (\ c -> isAlphaNum c || elem c "_.-")

getWebProverName :: G_prover -> String
getWebProverName = removeFunnyChars . getProverName

getProvers :: Maybe String -> G_sublogics -> String
getProvers mt subL = ppTopElement . unode "provers" . map (unode "prover")
    . nubOrd . map (getWebProverName . fst)
    . filterByComorph mt
    $ getAllAutomaticProvers subL

getComorphs :: Maybe String -> G_sublogics -> String
getComorphs mp subL = ppTopElement . unode "translations"
    . map (unode "comorphism")
    . nubOrd . map (showComorph . snd)
    . filterByProver mp
    $ getAllAutomaticProvers subL

proveNode :: LibEnv -> LibName -> DGraph -> (Int, DGNodeLab) -> G_theory
  -> G_sublogics -> Bool -> Maybe String -> Maybe String -> Maybe Int
  -> [String] -> ResultT IO (LibEnv, [(String, String)])
proveNode le ln dg nl gTh subL useTh mp mt tl thms = case
    getProverAndComorph mp mt subL of
  [] -> fail "no prover found"
  cp : _ -> do
      let ks = map fst $ getThGoals gTh
          diffs = Set.difference (Set.fromList thms)
                  $ Set.fromList ks
      unless (Set.null diffs) $ fail $ "unknown theorems: " ++ show diffs
      (res, prfs) <- lift $ autoProofAtNode useTh (fromMaybe 5 tl) thms gTh cp
      case prfs of
        Nothing -> fail "proving failed"
        Just sens -> if null sens then return (le, sens) else
          case res of
            Nothing -> error "proveNode"
            Just nTh -> return
              (Map.insert ln (updateLabelTheory le dg nl nTh) le, sens)

mkPath :: Session -> LibName -> Int -> String
mkPath sess l k =
        '/' : concat [ show (getLibId l) ++ "?session="
                     | l /= sessLibName sess ]
        ++ show k

extPath :: Session -> LibName -> Int -> String
extPath sess l k = mkPath sess l k ++
        if l /= sessLibName sess then "&" else "?"

sessAns :: LibName -> (Session, Int) -> String
sessAns libName (sess, k) =
  let libEnv = sessLibEnv sess
      ln = show $ getLibId libName
      libref l =
        aRef (mkPath sess l k) (show $ getLibId l) : map (\ d ->
         aRef (extPath sess l k ++ d) d) displayTypes
      libPath = extPath sess libName k
      ref d = aRef (libPath ++ d) d
      noderef (n, lbl) =
        let s = show n
            gs = getThGoals $ dgn_theory lbl
            (ps, os) = partition (maybe False isProvedBasically . snd) gs
        in
        unode "i" (s ++ " " ++ getDGNodeName lbl) : map (\ c ->
        let isProve = c == "prove" in
        if isProve && null gs then unode "i" "no goals" else
        aRef (libPath ++ c ++ "=" ++ s
              ++ if isProve then "&theorems="
                 ++ encodeForQuery
                   (unwords $ map fst $ if null os then gs else os)
                 else "")
              $ if isProve then
                  c ++ "[" ++ show (length ps) ++ "/"
                        ++ show (length gs) ++ "]"
                else c) nodeCommands
      edgeref e@(_, _, lbl) =
        aRef (libPath ++ "edge=" ++ showEdgeId (dgl_id lbl))
                 $ showLEdge e
      dg = lookupDGraph libName libEnv
      nlabs = labNodesDG dg
      elabs = labEdgesDG dg
  in htmlHead ++ mkHtmlElem
           ('(' : shows k ")" ++ ln)
           (unode "b" ("library " ++ ln)
            : map ref displayTypes
            ++ menuElement : loadXUpdate (libPath ++ "update")
            : [unode "p" "commands:"]
            ++ [unode "ul" $
                map (unode "li" . ref) globalCommands]
            ++ [unode "p" "imported libraries:"]
            ++ [unode "ul" $
                map (unode "li" . libref) $ Map.keys libEnv]
            ++ [unode "p" (show (length nlabs)
                           ++ " nodes with local and global theories:")]
            ++ [unode "ul" $
                map (unode "li" . noderef) nlabs]
            ++ [unode "p" (show (length elabs) ++ " edges:")]
            ++ [unode "ul" $
                map (unode "li" . edgeref)
                $ sortBy (comparing (\ (_, _, l) -> dgl_id l)) elabs]
           )

getHetsLibContent :: HetcatsOpts -> String -> String -> IO [Element]
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

mkHtmlRef :: String -> String -> Element
mkHtmlRef query entry = unode "dir" $ aRef (entry ++ query) entry

headElems :: String -> [Element]
headElems path = let d = "default" in unode "strong" "Choose query type:" :
  map (\ q -> aRef (if q == d then "/" </> path else '?' : q) q)
      (d : displayTypes) ++ [menuElement, uploadHtml]

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
loadNode name = add_attrs
    [ mkAttr "type" "file"
    , mkAttr "name" name
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
  , submitNode ]

loadXUpdate :: String -> Element
loadXUpdate a = mkForm a
  [ unode "i" "xupdate"
  , loadNode "xupdate"
  , unode "i" "impacts"
  , loadNode "impacts"
  , submitNode ]
