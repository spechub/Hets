{- |
Module      :  $Header$
Description :  Conversion of Twelf files to Development Graphs
Copyright   :  (c) Kristina Sojakova, DFKI Bremen 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  k.sojakova@jacobs-university.de
Stability   :  experimental
Portability :  portable
-}
module LF.Twelf2DG where

import System.Exit
import System.IO
import System.Process
import System.Directory
import System.FilePath

import Network.URI

import Static.DevGraph
import Static.ComputeTheory
import Static.GTheory

import Logic.Grothendieck
import Logic.ExtSign
import Logic.Coerce

import LF.Sign
import LF.Morphism
import LF.Logic_LF

import Data.Maybe
import Data.List
import Data.Graph.Inductive.Graph (Node)
import qualified Data.Map as Map
import qualified Data.Set as Set

import Common.LibName
import Common.Utils
import Common.Id
import Common.ExtSign
import qualified Common.Consistency as Cons

import Control.Monad

import Text.XML.Light.Input
import Text.XML.Light.Types
import Text.XML.Light.Proc

import Driver.Options

import Debug.Trace

data LINK_TYPE = Definitional | Postulated

type RAW_NODE_NAME = (BASE,MODULE)
type RAW_LINK_NAME = (BASE,MODULE,NAME)
type RAW_NODES = Map.Map RAW_NODE_NAME Sign
type RAW_LINKS = Map.Map (RAW_LINK_NAME,RAW_NODE_NAME,RAW_NODE_NAME)
                         (LINK_TYPE,Morphism)
type RAW_GRAPH = (RAW_NODES,RAW_LINKS)

type MAP_NODES = Map.Map RAW_NODE_NAME Node
type LibEnvNodes = (LibEnv,MAP_NODES)

emptyRawGraph :: RAW_GRAPH
emptyRawGraph = (Map.empty,Map.empty)

omdocNS :: Maybe String
omdocNS = Just "http://omdoc.org/ns"

openMathNS :: Maybe String
openMathNS = Just "http://www.openmath.org/OpenMath"

omdocQN :: QName
omdocQN = QName "omdoc" omdocNS Nothing

theoryQN :: QName
theoryQN = QName "theory" omdocNS Nothing

viewQN :: QName
viewQN = QName "view" omdocNS Nothing

includeQN :: QName
includeQN = QName "include" omdocNS Nothing

structureQN :: QName
structureQN = QName "structure" omdocNS Nothing

constantQN :: QName
constantQN = QName "constant" omdocNS Nothing

aliasQN :: QName
aliasQN = QName "alias" omdocNS Nothing

notationQN :: QName
notationQN = QName "notation" omdocNS Nothing

typeQN :: QName
typeQN = QName "type" omdocNS Nothing

definitionQN :: QName
definitionQN = QName "definition" omdocNS Nothing

omobjQN :: QName 
omobjQN = QName "OMOBJ" openMathNS Nothing

omsQN :: QName 
omsQN = QName "OMS" openMathNS Nothing

omaQN :: QName 
omaQN = QName "OMA" openMathNS Nothing

ombindQN :: QName 
ombindQN = QName "OMBIND" openMathNS Nothing

ombvarQN :: QName 
ombvarQN = QName "OMBVAR" openMathNS Nothing

omattrQN :: QName 
omattrQN = QName "OMATTR" openMathNS Nothing

omatpQN :: QName 
omatpQN = QName "OMATP" openMathNS Nothing

omvQN :: QName 
omvQN = QName "OMV" openMathNS Nothing

typeOMS :: Element
typeOMS = 
  Element omsQN [Attr baseQN "http://cds.omdoc.org/foundations/lf/lf.omdoc",
                 Attr moduleQN "lf",
                 Attr nameQN "type"] [] Nothing

arrowOMS :: Element
arrowOMS = 
  Element omsQN [Attr baseQN "http://cds.omdoc.org/foundations/lf/lf.omdoc",
                 Attr moduleQN "lf",
                 Attr nameQN "arrow"] [] Nothing

lambdaOMS :: Element
lambdaOMS = 
  Element omsQN [Attr baseQN "http://cds.omdoc.org/foundations/lf/lf.omdoc",
                 Attr moduleQN "lf",
                 Attr nameQN "lambda"] [] Nothing

piOMS :: Element
piOMS = 
  Element omsQN [Attr baseQN "http://cds.omdoc.org/foundations/lf/lf.omdoc",
                 Attr moduleQN "lf",
                 Attr nameQN "Pi"] [] Nothing  


impLambdaOMS :: Element
impLambdaOMS = 
  Element omsQN [Attr baseQN "http://cds.omdoc.org/foundations/lf/lf.omdoc",
                 Attr moduleQN "lf",
                 Attr nameQN "implicit_lambda"] [] Nothing

impPiOMS :: Element
impPiOMS = 
  Element omsQN [Attr baseQN "http://cds.omdoc.org/foundations/lf/lf.omdoc",
                 Attr moduleQN "lf",
                 Attr nameQN "implicit_Pi"] [] Nothing     


oftypeOMS :: Element
oftypeOMS = 
  Element omsQN [Attr baseQN "http://cds.omdoc.org/foundations/lf/lf.omdoc",
                 Attr moduleQN "lf",
                 Attr nameQN "oftype"] [] Nothing

nameQN :: QName
nameQN = (QName "name" Nothing Nothing)

moduleQN :: QName
moduleQN = (QName "module" Nothing Nothing)

baseQN :: QName
baseQN = (QName "base" Nothing Nothing)

fromQN :: QName
fromQN = (QName "from" Nothing Nothing)

toQN :: QName
toQN = (QName "to" Nothing Nothing)

getNameAttr :: Element -> Maybe String
getNameAttr e = findAttr nameQN e

getModuleAttr :: Element -> Maybe String
getModuleAttr e = findAttr moduleQN e

getBaseAttr :: Element -> Maybe String
getBaseAttr e = findAttr baseQN e

getFromAttr :: Element -> Maybe String
getFromAttr e = findAttr fromQN e

getToAttr :: Element -> Maybe String
getToAttr e = findAttr toQN e

-- path to the Twelf folder must be set in the environment variable TWELF_LIB
twelf :: String
twelf = "check-some"
options :: [String]
options = ["-omdoc"]

------------------------------------------------------------------------------
------------------------------------------------------------------------------

-- constructs base and module out of a reference
splitRef :: String -> RAW_NODE_NAME
splitRef ref = 
  case elemIndices '?' ref of
       [i] -> let (b,(_:m)) = splitAt i ref
                   in (b,m)    
       _ -> error "Invalid reference."

-- compares two OMS elements
eqOMS :: Element -> Element -> Bool
eqOMS e1 e2 =
  let b = getBaseAttr e1 == getBaseAttr e2
      m = getModuleAttr e1 == getModuleAttr e2
      n = getNameAttr e1 == getNameAttr e2   
      in and [b,m,n]

-- resolves the first file path wrt to the second
resolve :: FilePath -> FilePath -> FilePath
resolve fp1 fp2 = 
  case parseURIReference fp1 of
    Nothing -> error "Invalid file name."
    Just uri1 -> do
      case parseURIReference fp2 of
        Nothing -> error "Invalid file name."
        Just uri2 -> do
          case relativeTo uri1 uri2 of
               Nothing -> error "Invalid file name."
               Just f -> show f

-- looks up the node number for the given signature reference
lookupNode :: RAW_NODE_NAME -> MAP_NODES -> Node
lookupNode ref nmap = 
  case Map.lookup ref nmap of
       Nothing -> error "Invalid signature reference."
       Just node -> node 

-- finds the signature by base and module
lookupSig :: RAW_NODE_NAME -> LibEnvNodes -> RAW_NODES -> IO Sign
lookupSig ref@(b,_) (libs,nmap) sigs =
  case Map.lookup ref sigs of
       Just sig -> return sig
       Nothing -> do
         let node = lookupNode ref nmap
         let dg = lookupDGraph (emptyLibName b) libs
         let gth = dgn_theory $ labDG dg node
         case gth of
              (G_theory lid extsig _ _ _) -> 
                coercePlainSign lid LF "" $ plainSign extsig

------------------------------------------------------------------------------
------------------------------------------------------------------------------

-- analyzes the given Twelf file
anaTwelfFile :: HetcatsOpts -> FilePath -> IO (Maybe (LibName, LibEnv))
anaTwelfFile _ fp = do
  dir <- getCurrentDirectory
  let file = resolve fp (dir ++ "/")
  let name = emptyLibName file
  (libs,_) <- twelf2DG file (emptyLibEnv,Map.empty)
  return $ Just (name,libs)  

-- updates the library environment by adding specs from the Twelf file
twelf2DG :: FilePath -> LibEnvNodes -> IO LibEnvNodes
twelf2DG file ln = do
  runTwelf $ trace ("Running Twelf on file: " ++ show file) file
  (ln1,g) <- buildGraph (trace ("Analyzing file: " ++ show file) file) ln
  makeLibEnv (trace ("Building graph for file: " ++ show file) file) ln1 g  
     
-- runs twelf to create an omdoc file
runTwelf :: FilePath -> IO ()
runTwelf file = do
  let dir = dropFileName file
  twelfdir <- getEnvDef "TWELF_LIB" ""
  if null twelfdir 
     then error "environment variable TWELF_LIB is not set"
     else do
       (_, _, _, pr) <- 
         runInteractiveProcess (concat [twelfdir, "/" ,twelf])
                               (options ++ [dir,file])
                               Nothing
                               Nothing
       exitCode <- waitForProcess pr
       case exitCode of
            ExitFailure i -> 
               error $ "Calling Twelf failed with exitCode: " ++ show i ++
                       " on file " ++ file                    
            ExitSuccess -> return ()

-- generates a library environment from raw libraries
makeLibEnv :: FilePath -> LibEnvNodes -> RAW_GRAPH -> IO LibEnvNodes
makeLibEnv file ln g = do
  (ln1,dg) <- addNodes emptyDG g ln
  (ln2,dg1) <- addLinks dg g ln1
  let (libs,nmap) = ln2
  let dg2 = computeDGraphTheories libs $ trace ("Computing theories for file: " ++ show file) dg1
  let libs1 = Map.insert (emptyLibName file) dg2 libs
  return (libs1,nmap)

-- adds nodes to the library environment
addNodes :: DGraph -> RAW_GRAPH -> LibEnvNodes -> IO (LibEnvNodes,DGraph)
addNodes dg (sigs,_) (libs,nmap) = do
  let (nmap3,dg3) =
        foldl (\ (nmap1,dg1) ((b,m),sig) -> 
                 let (node,dg2) = insSigToDG sig dg1
                     nmap2 = Map.insert (b,m) node nmap1
                     in (nmap2,dg2)
              ) 
              (nmap,dg)
              $ Map.toList sigs
  return ((libs,nmap3),dg3)

-- inserts a signature as a node to the development graph
insSigToDG :: Sign -> DGraph -> (Node,DGraph)
insSigToDG sig dg = 
  let node = getNewNodeDG dg
      m = sigModule sig
      nodeName = emptyNodeName { getName = Token m nullRange }
      info = newNodeInfo DGBasic
      extSign = makeExtSign LF sig
      gth = noSensGTheory LF extSign startSigId
      nodeLabel = newInfoNodeLab nodeName info gth
      dg1 = insNodeDG (node,nodeLabel) dg   
      in (node,dg1)

-- adds links to the library environment
addLinks :: DGraph -> RAW_GRAPH -> LibEnvNodes -> IO (LibEnvNodes,DGraph)
addLinks dg (sigs,morphs) ln = do
  dg2 <- foldM (\ dg1 ((_,s,t),(k,morph)) -> do 
                  sig1 <- lookupSig s ln sigs
                  sig2 <- lookupSig t ln sigs
                  let morph1 = morph { source = sig1, target = sig2 }
                  return $ insMorphToDG morph1 k ln dg1                                              
               ) 
               dg
               $ Map.toList morphs 
  return (ln,dg2)

-- inserts a morphism as a link to the development graph
insMorphToDG :: Morphism -> LINK_TYPE -> LibEnvNodes -> DGraph -> DGraph
insMorphToDG morph k ln dg =
  let gmorph = gEmbed $ G_morphism LF morph startMorId
      thmStatus = Proven (DGRule "Type-checked") emptyProofBasis
      linkKind = case k of
                      Definitional -> DefLink
                      Postulated -> ThmLink thmStatus 
      consStatus = ConsStatus Cons.None Cons.None LeftOpen
      linkType = ScopedLink Global linkKind consStatus
      linkLabel = defDGLink gmorph linkType SeeTarget
      b = morphBase morph
      (node1,dg1) = addRefNode b dg (source morph) ln
      (node2,dg2) = addRefNode b dg1 (target morph) ln
      in snd $ insLEdgeDG (node1,node2,linkLabel) dg2  
      
-- constructs a reference node to the specified signature, if needed
addRefNode :: BASE -> DGraph -> Sign -> LibEnvNodes -> (Node,DGraph)
addRefNode base dg sig (libs,nmap) =
  let b = sigBase sig
      m = sigModule sig
      node = lookupNode (b,m) nmap 
      in if (b == base)
         then (node,dg)
         else let info = newRefInfo (emptyLibName b) node
                  refNodeM = lookupInAllRefNodesDG info dg
                  in case refNodeM of
                          Just refNode -> (refNode,dg)
                          Nothing -> insRefSigToDG sig info dg libs

-- inserts a signature as a reference node to the development graph
insRefSigToDG :: Sign -> DGNodeInfo -> DGraph -> LibEnv -> (Node,DGraph)
insRefSigToDG sig info dg libs = 
  let node = getNewNodeDG dg
      m = sigModule sig
      nodeName = emptyNodeName { getName = Token m nullRange }
      extSign = makeExtSign LF sig
      gth = noSensGTheory LF extSign startSigId
      nodeLabel1 = newInfoNodeLab nodeName info gth
      refDG = lookupDGraph (ref_libname info) libs
      refGlobTh = globalTheory $ labDG refDG $ ref_node info 
      nodeLabel2 = nodeLabel1 { globalTheory = refGlobTh}
      dg1 = insNodeDG (node,nodeLabel2) dg
      dg2 = addToRefNodesDG node info dg1    
      in (node,dg2)                                   

------------------------------------------------------------------------------
------------------------------------------------------------------------------

-- builds raw development graph libraries
buildGraph :: FilePath -> LibEnvNodes -> IO (LibEnvNodes,RAW_GRAPH)
buildGraph file (libs,nmap) = do
  let omdoc_file = replaceExtension file "omdoc"
  xml <- readFile $ trace "Parsing omdoc file." omdoc_file
  let elems = onlyElems $ parseXML xml
  let elems1 = filter (\ e -> elName e == omdocQN) elems
  case elems1 of
       [root] -> do
         foldM (\ lng e -> 
                  let n = elName e
                      in if (n == theoryQN) then addSign file e lng else
                         if (n == viewQN) then addMorph file e lng else
                         return lng
               ) 
               ((libs,nmap),emptyRawGraph)
               $ elChildren root        
       _ -> fail "Not an OMDoc file."

-- transforms a theory element into a signature and adds it to the libraries
addSign :: FilePath -> Element -> (LibEnvNodes,RAW_GRAPH) -> 
           IO (LibEnvNodes,RAW_GRAPH)
addSign file e lng =
  case getNameAttr e of
       Nothing -> error "Theory element must have a name."
       Just name -> do
          let sig = Sign file name []
          (lng1,sig1) <-
            foldM (\ lngs el -> 
                     let n = elName el
                         in if (n == includeQN) then addIncl el lngs else
                            if (n == structureQN) then addStruct el lngs else
                            if (n == constantQN) then addConst el lngs else
                            if (n == aliasQN) then addAlias el lngs else
                            if (n == notationQN) then addNotat el lngs else 
                            return lngs
                  ) 
                  (lng,sig)
                  $ elChildren e
          let (ln,(sigs,morphs)) = lng1
          let sigs1 = Map.insert (file,name) sig1 sigs
          return (ln,(sigs1,morphs)) 
              
-- adds a constant declaration to the signature
addConst :: Element -> ((LibEnvNodes,RAW_GRAPH),Sign) -> 
            IO ((LibEnvNodes,RAW_GRAPH),Sign)
addConst e (lng,sig) = do
  let sym = case getNameAttr e of
                 Nothing -> error "Constant element must have a name."
                 Just n -> Symbol (sigBase sig) (sigModule sig) n
  let typ = case findChildren typeQN e of
                 [t] -> type2exp sig t
                 _ -> error "Constant element must have a unique type child."
  let val = case findChildren definitionQN e of
                 [] -> Nothing
                 [v] -> Just $ definition2exp sig v         
                 _ ->  error $ concat ["Constant element must have at most ",
                                       "one definition child."]
  let sig1 = addDef (Def sym typ val) sig
  return (lng,sig1)               

-- converts a type element to an expression
type2exp :: Sign -> Element -> EXP
type2exp sig e = 
  case findChildren omobjQN e of
       [omobj] -> omobj2exp sig omobj
       _ -> error "Type element must have a unique OMOBJ child."

-- converts a definition element to an expression
definition2exp :: Sign -> Element -> EXP
definition2exp sig e = 
  case findChildren omobjQN e of
       [omobj] -> omobj2exp sig omobj
       _ -> error "Definition element must have a unique OMOBJ child."

-- converts an OMOBJ element to an expression
omobj2exp :: Sign -> Element -> EXP
omobj2exp sig e = 
  case elChildren e of
       [el] -> omel2exp sig el
       _ -> error "OMOBJ element must have a unique child."

-- converts an Open Math element to an expression
omel2exp :: Sign -> Element -> EXP
omel2exp sig e =
  let name = elName e
      in if (name == omsQN) then oms2exp sig e else
         if (name == omaQN) then oma2exp sig e else
         if (name == ombindQN) then ombind2exp sig e else
         if (name == omvQN) then oms2exp sig e else
            error $ concat ["Only OMA, OMS, and OMBIND elements correspond "
                           ,"to an expression."]

-- converts an OMS element to an expression
oms2exp :: Sign -> Element -> EXP                                      
oms2exp sig e =
  let curBase = sigBase sig
      curModule = sigModule sig
  in if (eqOMS e typeOMS)
        then Type
        else case getNameAttr e of
                  Nothing -> error "OMS element must have a name."
                  Just n -> 
                    case getModuleAttr e of
                         Nothing -> Const $ Symbol curBase curModule n
                         Just m -> 
                           case getBaseAttr e of
                                Nothing -> Const $ Symbol curBase m n
                                Just b -> Const $ Symbol (resolve b curBase) m n

-- converts an OMA element to an expression
oma2exp :: Sign -> Element -> EXP                                      
oma2exp sig e = 
  case elChildren e of
       [] -> error "OMA element must have at least one child."
       (f:as) -> 
         let as1 = map (omel2exp sig) as
             in if (elName f == omsQN && eqOMS f arrowOMS)
                   then case as1 of
                             [] -> error $ 
                                    concat ["The -> constructor must be applied"
                                           ," to at least one argument."]  
                             _ -> Func (init as1) (last as1)
                else let f1 = omel2exp sig f
                         in Appl f1 as1      

-- converts an OMBIND element to an expression
ombind2exp :: Sign -> Element -> EXP                                      
ombind2exp sig e = 
  case elChildren e of
       [f,d,b] -> 
         if (elName d /= ombvarQN)
            then error "The second child of OMBIND must be OMBVAR."
            else let d1 = ombvar2decls sig d
                     b1 = omel2exp sig b
                     in if (elName f/= omsQN) 
                           then error "The first child of OMBIND must be OMS."
                           else if (eqOMS f lambdaOMS) then Lamb d1 b1 else
                                if (eqOMS f piOMS) then Pi d1 b1 else
                                {- so far implicit binders are treated
                                   as explicit -}
                                if (eqOMS f impLambdaOMS) then Lamb d1 b1 else
                                if (eqOMS f impPiOMS) then Pi d1 b1 else
                                error $ concat ["The first child of OMBIND "
                                               ,"must be be Pi or Lambda."]                                         
       _ -> error "OMBIND element must have exactly 3 children."                   

-- converts an OMBVAR element to a list of declaration
ombvar2decls :: Sign -> Element -> [DECL]
ombvar2decls sig e = 
  let attrs = findChildren omattrQN e
      in map (omattr2decl sig) attrs

-- converts an OMATTR element to a declaration
omattr2decl :: Sign -> Element -> DECL
omattr2decl sig e =
  case findChildren omatpQN e of
       [omatp] -> 
         case findChildren omvQN e of
              [omv] -> (omv2var omv, omatp2exp sig omatp)
              _ -> error "OMATTR element must have a unique OMV child."
       _ -> error "OMATTR element must have a unique OMATP child."

-- converts an OMV element to a variable
omv2var :: Element -> Var
omv2var e = 
  case getNameAttr e of
       Nothing -> error "OMV element must have a name."
       Just v -> v

-- converts an OMATP element to an expression
omatp2exp :: Sign -> Element -> EXP
omatp2exp sig e = 
  case elChildren e of
       [c1,c2] -> 
          if (and [elName c1 == omsQN, eqOMS c1 oftypeOMS])
             then omel2exp sig c2
             else error $ concat ["The first child of OMATP",
                                  "must be the \"oftype\" symbol."]
       _ -> error "OMATP element must have exactly two children."
      
{- adds declarations arising from an inclusion to the signature
   adds the inclusion to the morphism map -}
addIncl :: Element -> ((LibEnvNodes,RAW_GRAPH),Sign) -> 
           IO ((LibEnvNodes,RAW_GRAPH),Sign)
addIncl e ((ln,(sigs,morphs)),sig) = do
  case getFromAttr e of
       Nothing -> error "Include element must have a \"from\" attribute."
       Just ref -> do
         let curBase = sigBase sig
         let curModule = sigModule sig
         let (br,m) = splitRef ref
         let b = replaceExtension (resolve br curBase) "elf"
         ln1 <- addFromFile b curBase ln
         let s = (b,m)
         let t = (curBase,curModule)
         sourceSig <- lookupSig s ln1 sigs
         let sig1 = addInclSyms sourceSig sig
         let morphs1 = addInclToMorphs s t morphs
         return ((ln1,(sigs,morphs1)),sig1)

{- parses the referenced file and imports all signatures
   and morphisms from it -}
addFromFile :: String -> FilePath -> LibEnvNodes -> IO LibEnvNodes
addFromFile file base ln@(libs,_) = do
  if (file == base || Map.member (emptyLibName file) libs)
     then return ln
     else twelf2DG file ln

-- adds included definitions to the signature
addInclSyms :: Sign -> Sign -> Sign
addInclSyms (Sign _ _ ds) sig = 
  let syms = getAllSyms sig
      in foldl (\ sig1 d -> 
                  if (Set.member (getSym d) syms)
                     then sig1
                     else addDef d sig1
               )
               sig
               ds
  
-- adds the inclusion to the collection of morphisms
addInclToMorphs :: RAW_NODE_NAME -> RAW_NODE_NAME -> RAW_LINKS -> RAW_LINKS
addInclToMorphs s t morphs = 
  let (b,m) = t
      l = (b,m,"")
      morph = Morphism b m "" emptySig emptySig Map.empty
      in Map.insert (l,s,t) (Definitional,morph) morphs

{- adds declarations arising from a structure to the signature
   adds the structure to the morphism map -}
addStruct :: Element -> ((LibEnvNodes,RAW_GRAPH),Sign) -> 
           IO ((LibEnvNodes,RAW_GRAPH),Sign)
addStruct _ lngs = return lngs 

-- so far aliases are ignored
addAlias :: Element -> ((LibEnvNodes,RAW_GRAPH),Sign) -> 
           IO ((LibEnvNodes,RAW_GRAPH),Sign)
addAlias _ lngs = return lngs

-- so far notations are ignored
addNotat :: Element -> ((LibEnvNodes,RAW_GRAPH),Sign) -> 
           IO ((LibEnvNodes,RAW_GRAPH),Sign)
addNotat _ lngs = return lngs

-- so far views are ignored
addMorph :: FilePath -> Element -> (LibEnvNodes,RAW_GRAPH) -> 
           IO (LibEnvNodes,RAW_GRAPH)
addMorph _ _ lng = return lng
