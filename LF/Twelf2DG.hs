{- |
Module      :  $Header$
Description :  Conversion of Twelf files to Development Graphs
Copyright   :  (c) Kristina Sojakova, DFKI Bremen 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  k.sojakova@jacobs-university.de
Stability   :  experimental
Portability :  portable
-}
module LF.Twelf2DG ( anaTwelfFile ) where

import System.Exit
import System.Process
import System.Directory
import System.FilePath
import System.IO (hGetContents)

import Network.URI

import Static.DevGraph
import Static.ComputeTheory
import Static.GTheory

import Logic.Grothendieck

import LF.Sign
import LF.Morphism
import LF.Logic_LF
import Logic.ExtSign

import Data.List
import Data.Graph.Inductive.Graph (Node)
import qualified Data.Map as Map
import qualified Data.Set as Set

import Common.LibName
import Common.Result
import Common.Utils
import Common.Id
import qualified Common.Consistency as Cons

import Control.Monad

import Text.XML.Light.Input
import Text.XML.Light.Types
import Text.XML.Light.Proc

import Driver.Options

type NODE = (BASE,MODULE)
type LINK = (BASE,MODULE,NAME)

type SIGS = Map.Map NODE Sign
type MORPHS = Map.Map (LINK,NODE,NODE) Morphism

type GRAPH = (SIGS,MORPHS)

type NODE_MAP = Map.Map NODE (Sign,Node)
type LINK_MAP = Map.Map LINK Morphism
type GR_MAP = (NODE_MAP,LINK_MAP)

type LibEnvExt = (LibEnv,GR_MAP)
type LibEnvFull = (LibEnvExt,BASE,GRAPH)

emptyGraph :: GRAPH
emptyGraph = (Map.empty,Map.empty)

emptyGrMap :: GR_MAP
emptyGrMap = (Map.empty,Map.empty)

omdocNS :: Maybe String
omdocNS = Just "http://omdoc.org/ns"

openMathNS :: Maybe String
openMathNS = Just "http://www.openmath.org/OpenMath"

lfBase :: String
lfBase = "http://cds.omdoc.org/foundations/lf/lf.omdoc"

mmtBase :: String
mmtBase = "http://cds.omdoc.org/omdoc/mmt.omdoc"

lfMod :: String
lfMod = "lf"

mmtMod :: String
mmtMod = "mmt"

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

ommorQN :: QName
ommorQN = QName "OMMOR" omdocNS Nothing

conassQN :: QName
conassQN = QName "conass" omdocNS Nothing

strassQN :: QName
strassQN = QName "strass" omdocNS Nothing

typeOMS :: Element
typeOMS =
  Element omsQN [Attr baseQN lfBase,
                 Attr moduleQN lfMod,
                 Attr nameQN "type"] [] Nothing

arrowOMS :: Element
arrowOMS =
  Element omsQN [Attr baseQN lfBase,
                 Attr moduleQN lfMod,
                 Attr nameQN "arrow"] [] Nothing

lambdaOMS :: Element
lambdaOMS =
  Element omsQN [Attr baseQN lfBase,
                 Attr moduleQN lfMod,
                 Attr nameQN "lambda"] [] Nothing

piOMS :: Element
piOMS =
  Element omsQN [Attr baseQN lfBase,
                 Attr moduleQN lfMod,
                 Attr nameQN "Pi"] [] Nothing


impLambdaOMS :: Element
impLambdaOMS =
  Element omsQN [Attr baseQN lfBase,
                 Attr moduleQN lfMod,
                 Attr nameQN "implicit_lambda"] [] Nothing

impPiOMS :: Element
impPiOMS =
  Element omsQN [Attr baseQN lfBase,
                 Attr moduleQN lfMod,
                 Attr nameQN "implicit_Pi"] [] Nothing


oftypeOMS :: Element
oftypeOMS =
  Element omsQN [Attr baseQN lfBase,
                 Attr moduleQN lfMod,
                 Attr nameQN "oftype"] [] Nothing

compOMS :: Element
compOMS =
  Element omsQN [Attr baseQN mmtBase,
                 Attr moduleQN mmtMod,
                 Attr nameQN "composition"] [] Nothing

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

omdocE :: String
omdocE = "omdoc"

twelfE :: String
twelfE = "elf"

-- path to the Twelf folder must be set in the environment variable TWELF_LIB
twelf :: String
twelf = "check-some"

options :: [String]
options = ["-omdoc"]

------------------------------------------------------------------------------
------------------------------------------------------------------------------
-- HELPER FUNCTIONS

getNameAttr :: Element -> String
getNameAttr e =
  case findAttr nameQN e of
       Nothing -> error $ "Element is missing a name." ++ (show e)
       Just n -> n

getModuleAttr :: Element -> Maybe String
getModuleAttr e = findAttr moduleQN e

getBaseAttr :: Element -> Maybe String
getBaseAttr e = findAttr baseQN e

getFromAttr :: Element -> String
getFromAttr e =
  case findAttr fromQN e of
       Nothing -> error "Element is missing a \"from\" attribute."
       Just a -> a

getToAttr :: Element -> String
getToAttr e =
  case findAttr toQN e of
       Nothing -> error "Element is missing a \"to\" attribute."
       Just a -> a

makeLName :: FilePath -> IO FilePath
makeLName fp = do
  fp1 <- makeRelativeToCurrentDirectory fp 
  return $ dropExtension fp1

-- retrieves the base, module, and name attributes
getBMN :: Element -> NODE -> (BASE,MODULE,NAME)
getBMN e (base,modul) =
  let n = case findAttr nameQN e of
               Nothing -> ""
               Just n' -> n'
      m = case getModuleAttr e of
               Nothing -> modul
               Just m' -> m'
      b = case getBaseAttr e of
               Nothing -> base
               Just b' -> replaceExtension (resolve b' base) twelfE
      in (b,m,n)

-- compares two OMS elements
eqOMS :: Element -> Element -> Bool
eqOMS e1 e2 =
  if (elName e1 /= omsQN || elName e2 /= omsQN)
     then False
     else and [getNameAttr e1 == getNameAttr e2
              ,getModuleAttr e1 == getModuleAttr e2
              ,getBaseAttr e1 == getBaseAttr e2]

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

-- returns the referenced base and module
parseRef :: String -> String -> NODE
parseRef ref base =
  case elemIndices '?' ref of
       [i] -> let (br,(_:m)) = splitAt i ref
                  b = replaceExtension (resolve br base) twelfE
                  in (b,m)
       _ -> error "Invalid reference."

{- parses the referenced file if needed and imports all signatures
   and morphisms from it -}
addFromFile :: FilePath -> LibEnvFull -> IO LibEnvFull
addFromFile fp libs@(le@(lenv,_),base,gr) = do
  file <- makeLName fp
  if (file == base || Map.member (emptyLibName file) lenv)
     then return libs
     else do le1 <- twelf2DG fp le
             return (le1,base,gr)

-- looks up the node number for the given signature reference
lookupNode :: NODE -> LibEnvFull -> Node
lookupNode ref ((_,(sigmap,_)),_,_) =
  case Map.lookup ref sigmap of
       Just (_,n) -> n
       Nothing -> error $ "Node number cannot be found." ++ (show ref)

-- finds the signature by base and module
lookupSig :: NODE -> LibEnvFull -> Sign
lookupSig ref ((_,(sigmap,_)),_,(sigs,_)) =
  case Map.lookup ref sigmap of
       Just (sig,_) -> sig
       Nothing -> case Map.lookup ref sigs of
                       Just sig -> sig
                       Nothing -> error "Signature cannot be found."

-- finds the morphism by base, module, and name
lookupMorph :: LINK -> LibEnvFull -> Morphism
lookupMorph ref ((_,(_,mormap)),_,(_,morphs)) =
  case Map.lookup ref mormap of
       Just morph -> morph
       Nothing ->
         let morphs1 = Map.filterWithKey (\ (l,_,_) _ -> l == ref) morphs
             in case Map.toList morphs1 of
                     [(_,morph)] -> morph
                     _ -> error "Morphism cannot be found."

-- adds the signature to the signature collection
addSigToGraph :: Sign -> LibEnvFull -> LibEnvFull
addSigToGraph sig (le,file,(sigs,morphs)) =
  let b = sigBase sig
      m = sigModule sig
      sigs1 = Map.insert (b,m) sig sigs
      in (le,file,(sigs1,morphs))

-- adds the morphism to the morphism collection
addMorphToGraph :: Morphism -> LibEnvFull -> LibEnvFull
addMorphToGraph m (le,file,(sigs,morphs)) =
  let sig1 = source m
      sig2 = target m
      l = (morphBase m, morphModule m, morphName m)
      s = (sigBase sig1, sigModule sig1)
      t = (sigBase sig2, sigModule sig2)
      morphs1 = Map.insert (l,s,t) m morphs
      in (le,file,(sigs,morphs1))

-- adds the signature to the node map
addSigToGrMap :: Sign -> Node -> LibEnvFull -> LibEnvFull
addSigToGrMap sig nod ((l,(sigmap,mormap)),file,gr) =
  let b = sigBase sig
      m = sigModule sig
      sigmap1 = Map.insert (b,m) (sig,nod) sigmap
      in ((l,(sigmap1,mormap)),file,gr)

-- adds the morphism to the link map
addMorphToGrMap :: Morphism -> LibEnvFull -> LibEnvFull
addMorphToGrMap morph ((l,(sigmap,mormap)),file,gr) =
  let b = morphBase morph
      m = morphModule morph
      n = morphName morph
      mormap1 = Map.insert (b,m,n) morph mormap
      in ((l,(sigmap,mormap1)),file,gr)

------------------------------------------------------------------------------
------------------------------------------------------------------------------
-- CONSTRUCTING THE DGRAPH

-- analyzes the given Twelf file
anaTwelfFile :: HetcatsOpts -> FilePath -> IO (Maybe (LibName, LibEnv))
anaTwelfFile _ fp = do
  name <- makeLName fp
  (libs,_) <- twelf2DG fp (emptyLibEnv,emptyGrMap)
  return $ Just (emptyLibName name, libs)

-- updates the library environment by adding specs from the Twelf file
twelf2DG :: FilePath -> LibEnvExt -> IO LibEnvExt
twelf2DG fp le = do
  dir <- getCurrentDirectory
  let file = resolve fp (dir ++ "/")
  runTwelf file
  libs <- buildGraph file le
  return $ makeLibEnv libs

-- runs twelf to create an omdoc file
runTwelf :: FilePath -> IO ()
runTwelf file = do
  let dir = dropFileName file
  twelfdir <- getEnvDef "TWELF_LIB" ""
  if null twelfdir
     then error "environment variable TWELF_LIB is not set"
     else do
       (_, out, err, pr) <-
         runInteractiveProcess (concat [twelfdir, "/" ,twelf])
                               (options ++ [dir,file])
                               Nothing
                               Nothing
       exitCode <- waitForProcess pr
       outH <- hGetContents out
       errH <- hGetContents err
       case exitCode of
            ExitFailure i -> do
               putStrLn (outH ++ errH)
               error $ "Calling Twelf failed with exitCode: " ++ show i ++
                       " on file " ++ file
            ExitSuccess -> return ()

-- generates a library environment from raw libraries
makeLibEnv :: LibEnvFull -> LibEnvExt
makeLibEnv libs = do
  let libs1 = addNodes libs
      libs2 = addLinks libs1
      ((l,grmap),file,_) = libs2
      lname = emptyLibName file
      dg = computeDGraphTheories l $ lookupDGraph lname l
      l1 = Map.insert lname dg l
      in (l1,grmap)

-- adds nodes to the library environment
addNodes :: LibEnvFull -> LibEnvFull
addNodes libs@(_,_,(sigs,_)) =
  let (dg2,libs3) =
         Map.fold (\ sig (dg,libs1) ->
                     let (nod,dg1) = addSigToDG sig dg
                         libs2 = addSigToGrMap sig nod libs1
                         in (dg1,libs2)
                  ) (emptyDG,libs) sigs
      ((l,grmap),base,gr) = libs3
      l1 = Map.insert (emptyLibName base) dg2 l
      in ((l1,grmap),base,gr)

-- inserts a signature as a node to the development graph
addSigToDG :: Sign -> DGraph -> (Node,DGraph)
addSigToDG sig dg =
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
addLinks :: LibEnvFull -> LibEnvFull
addLinks libs@((l,_),file,(_,morphs)) =
  let lname = emptyLibName file
      dg = lookupDGraph lname l
      (dg3,libs3) =
         Map.foldWithKey (\ (_,_,t) morph (dg1,libs1) ->
                            let sig = lookupSig t libs1
                                morph1 = morph { target = sig }
                                dg2 = addMorphToDG morph1 dg1 libs1
                                libs2 = addMorphToGrMap morph1 libs1
                                in (dg2,libs2)
                         ) (dg,libs) morphs
      ((l1,grmap),_,gr) = libs3
      l2 = Map.insert lname dg3 l1
      in ((l2,grmap),file,gr)

-- inserts a morphism as a link to the development graph
addMorphToDG :: Morphism -> DGraph -> LibEnvFull -> DGraph
addMorphToDG morph dg libs =
  let gmorph = gEmbed $ G_morphism LF morph startMorId
      thmStatus = Proven (DGRule "Type-checked") emptyProofBasis
      linkKind = case morphType morph of
                      Definitional -> DefLink
                      Postulated -> ThmLink thmStatus
                      Unknown -> error "Unknown morphism type."
      consStatus = ConsStatus Cons.None Cons.None LeftOpen
      linkType = ScopedLink Global linkKind consStatus
      linkLabel = defDGLink gmorph linkType SeeTarget
      (node1,dg1) = addRefNode dg (source morph) libs
      (node2,dg2) = addRefNode dg1 (target morph) libs
      in snd $ insLEdgeDG (node1,node2,linkLabel) dg2

-- constructs a reference node to the specified signature, if needed
addRefNode :: DGraph -> Sign -> LibEnvFull -> (Node,DGraph)
addRefNode dg sig libs@(_,file,_) =
  let b = sigBase sig
      m = sigModule sig
      node = lookupNode (b,m) libs
      in if (b == file)
         then (node,dg)
         else let info = newRefInfo (emptyLibName b) node
                  refNodeM = lookupInAllRefNodesDG info dg
                  in case refNodeM of
                          Just refNode -> (refNode,dg)
                          Nothing -> insRefSigToDG sig info dg libs

-- inserts a signature as a reference node to the development graph
insRefSigToDG :: Sign -> DGNodeInfo -> DGraph -> LibEnvFull -> (Node,DGraph)
insRefSigToDG sig info dg ((l,_),_,_) =
  let node = getNewNodeDG dg
      m = sigModule sig
      nodeName = emptyNodeName { getName = Token m nullRange }
      extSign = makeExtSign LF sig
      gth = noSensGTheory LF extSign startSigId
      nodeLabel1 = newInfoNodeLab nodeName info gth
      refDG = lookupDGraph (ref_libname info) l
      refGlobTh = globalTheory $ labDG refDG $ ref_node info
      nodeLabel2 = nodeLabel1 { globalTheory = refGlobTh}
      dg1 = insNodeDG (node,nodeLabel2) dg
      dg2 = addToRefNodesDG node info dg1
      in (node,dg2)

------------------------------------------------------------------------------
------------------------------------------------------------------------------
-- CONSTRUCTING SIGNATURES AND MORPHISMS

-- builds raw development graph libraries
buildGraph :: FilePath -> LibEnvExt -> IO LibEnvFull
buildGraph fp le = do
  let omdoc_file = replaceExtension fp omdocE
  xml <- readFile omdoc_file
  file <- makeLName fp
  let elems = onlyElems $ parseXML xml
  let elems1 = filter (\ e -> elName e == omdocQN) elems
  case elems1 of
       [root] -> do
         foldM (\ libs e ->
                  let n = elName e
                      in if (n == theoryQN) then addSign e libs else
                         if (n == viewQN) then addView e libs else
                         return libs
               )
               (le,file,emptyGraph)
               $ elChildren root
       _ -> fail "Not an OMDoc file."

-- transforms a theory element into a signature and adds it to the libraries
addSign :: Element -> LibEnvFull -> IO LibEnvFull
addSign e libs@(_,base,_) = do
  let name = getNameAttr e
  let sig = Sign base name []
  (libs1,sig1) <-
     foldM (\ ls el ->
              let n = elName el
                  in if (n == includeQN) then addIncl el ls else
                     if (n == structureQN) then addStruct el ls else
                     if (n == constantQN) then addConst el ls else
                     if (n == aliasQN) then addAlias el ls else
                     if (n == notationQN) then addNotat el ls else
                     return ls
           )
           (libs,sig)
           $ elChildren e
  return $ addSigToGraph sig1 libs1

-- so far views are ignored
addView :: Element -> LibEnvFull -> IO LibEnvFull
addView e libs@(_,file,_) = do
  let name = getNameAttr e
  let from = getFromAttr e
  let to = getToAttr e
  let (b1,m1) = parseRef from file
  let (b2,m2) = parseRef to file
  libs1 <- addFromFile b1 libs
  libs2 <- addFromFile b2 libs1
  let srcSig = lookupSig (dropExtension b1, m1) libs2
  let tarSig = lookupSig (dropExtension b2, m2) libs2
  (morph,libs3) <- getViewMorph name srcSig tarSig (elChildren e) libs2
  let libs4 = addMorphToGraph morph libs3
  return libs4

{- constructs the view morphism -}
getViewMorph :: String -> Sign -> Sign -> [Element] -> LibEnvFull ->
               IO (Morphism,LibEnvFull)
getViewMorph name srcSig tarSig els libs@(_,file,_) = do
  let b1 = sigBase srcSig
  let m1 = sigModule srcSig
  let b2 = sigBase tarSig
  let m2 = sigModule tarSig
  (symmap,libs1) <- constructMap els (b1,m1) (b2,m2) libs
  let morph = Morphism file name "" srcSig tarSig Postulated symmap
  return (morph,libs1)

------------------------------------------------------------------------------
------------------------------------------------------------------------------
-- CONSTRUCTING CONSTANTS

-- adds a constant declaration to the signature
addConst :: Element -> (LibEnvFull,Sign) -> IO (LibEnvFull,Sign)
addConst e (lib,sig) = do
  let ref@(base,modul) = (sigBase sig, sigModule sig)
  let sym = Symbol base modul $ getNameAttr e
  let typ = case findChildren typeQN e of
                 [t] -> type2exp t ref
                 _ -> error "Constant element must have a unique type child."
  let val = case findChildren definitionQN e of
                 [] -> Nothing
                 [v] -> Just $ definition2exp v ref
                 _ ->  error $ concat ["Constant element must have at most ",
                                       "one definition child."]
  let sig1 = addDef (Def sym typ val) sig
  return (lib,sig1)

-- converts a type element to an expression
type2exp :: Element -> NODE -> EXP
type2exp e ref =
  case findChildren omobjQN e of
       [omobj] -> omobj2exp omobj ref
       _ -> error "Type element must have a unique OMOBJ child."

-- converts a definition element to an expression
definition2exp :: Element -> NODE -> EXP
definition2exp e ref =
  case findChildren omobjQN e of
       [omobj] -> omobj2exp omobj ref
       _ -> error "Definition element must have a unique OMOBJ child."

-- converts an OMOBJ element to an expression
omobj2exp :: Element -> NODE -> EXP
omobj2exp e ref =
  case elChildren e of
       [el] -> omel2exp el ref
       _ -> error "OMOBJ element must have a unique child."

-- converts an Open Math element to an expression
omel2exp :: Element -> NODE -> EXP
omel2exp e ref =
  let name = elName e
      in if (name == omsQN) then oms2exp e ref else
         if (name == omaQN) then oma2exp e ref else
         if (name == ombindQN) then ombind2exp e ref else
         if (name == omvQN) then omv2exp e ref else
            error $ concat ["Only OMA, OMS, and OMBIND elements correspond "
                           ,"to an expression."]

-- converts an OMS element to an expression
oms2exp :: Element -> NODE -> EXP
oms2exp e ref =
  if (eqOMS e typeOMS)
     then Type
     else let (b,m,n) = getBMN e ref
              in Const $ Symbol (dropExtension b) m n

-- converts an OMA element to an expression
oma2exp :: Element -> NODE -> EXP
oma2exp e ref =
  case elChildren e of
       [] -> error "OMA element must have at least one child."
       (f:as) ->
         let as1 = map (\ a -> omel2exp a ref) as
             in if (eqOMS f arrowOMS)
                   then case as1 of
                             [] -> error $
                                    concat ["The -> constructor must be applied"
                                           ," to at least one argument."]
                             _ -> Func (init as1) (last as1)
                   else let f1 = omel2exp f ref
                            in Appl f1 as1

-- converts an OMBIND element to an expression
ombind2exp :: Element -> NODE -> EXP
ombind2exp e ref =
  case elChildren e of
       [f,d,b] ->
         if (elName d /= ombvarQN)
            then error "The second child of OMBIND must be OMBVAR."
            else let d1 = ombvar2decls d ref
                     b1 = omel2exp b ref
                     in if (eqOMS f lambdaOMS) then Lamb d1 b1 else
                        if (eqOMS f piOMS) then Pi d1 b1 else
                        {- so far implicit binders are treated
                           as explicit -}
                        if (eqOMS f impLambdaOMS) then Lamb d1 b1 else
                        if (eqOMS f impPiOMS) then Pi d1 b1 else
                        error $ concat ["The first child of OMBIND "
                                       ,"must be be Pi or Lambda."]
       _ -> error "OMBIND element must have exactly 3 children."

-- converts an OMBVAR element to a list of declaration
ombvar2decls :: Element -> NODE -> [DECL]
ombvar2decls e ref =
  let attrs = findChildren omattrQN e
      in map (\ a -> omattr2decl a ref) attrs

-- converts an OMATTR element to a declaration
omattr2decl :: Element -> NODE -> DECL
omattr2decl e ref =
  case findChildren omatpQN e of
       [omatp] ->
         case findChildren omvQN e of
              [omv] -> (getNameAttr omv, omatp2exp omatp ref)
              _ -> error "OMATTR element must have a unique OMV child."
       _ -> error "OMATTR element must have a unique OMATP child."

-- converts an OMATP element to an expression
omatp2exp :: Element -> NODE -> EXP
omatp2exp e ref =
  case elChildren e of
       [c1,c2] ->
          if (eqOMS c1 oftypeOMS)
             then omel2exp c2 ref
             else error $ concat ["The first child of OMATP",
                                  "must be the \"oftype\" symbol."]
       _ -> error "OMATP element must have exactly two children."

-- converts an OMV element to an expression
omv2exp :: Element -> NODE -> EXP
omv2exp e _ = Var $ getNameAttr e

------------------------------------------------------------------------------
------------------------------------------------------------------------------
-- CONSTRUCTING INCLUSIONS

{- adds declarations arising from an inclusion to the signature
   adds the inclusion to the morphism map -}
addIncl :: Element -> (LibEnvFull,Sign) -> IO (LibEnvFull,Sign)
addIncl e (libs@(_,file,_),sig) = do
  let from = getFromAttr e
  let (b,m) = parseRef from file
  libs1 <- addFromFile b libs
  let srcSig = lookupSig (dropExtension b, m) libs1
  let tarSig = addInclSyms srcSig sig
  let morph = getInclMorph srcSig tarSig
  let libs2 = addMorphToGraph morph libs1
  return (libs2,tarSig)

-- adds included definitions to the signature
addInclSyms :: Sign -> Sign -> Sign
addInclSyms (Sign _ _ ds) sig =
  let syms = getAllSyms sig
      in foldl (\ sig1 d ->
                  if (Set.member (getSym d) syms)
                     then sig1
                     else addDef d sig1
               ) sig ds

-- constructs the inclusion morphism
getInclMorph :: Sign -> Sign -> Morphism
getInclMorph sig1 sig2 =
  Morphism (sigBase sig2) (sigModule sig2) "" sig1 sig2 Definitional Map.empty

------------------------------------------------------------------------------
------------------------------------------------------------------------------
-- CONSTRUCTING STRUCTURES

{- adds declarations arising from a structure to the signature
   adds the structure to the morphism map -}
addStruct :: Element -> (LibEnvFull,Sign) -> IO (LibEnvFull,Sign)
addStruct e (libs@(_,file,_),sig) = do
  let name = getNameAttr e
  let from = getFromAttr e
  let (b,m) = parseRef from file
  libs1 <- addFromFile b libs
  let srcSig = lookupSig (dropExtension b, m) libs1
  (tarSig,morph,libs2) <- processStruct name srcSig sig (elChildren e) libs1
  let libs3 = addMorphToGraph morph libs2
  return (libs3,tarSig)

{- adds the definitions imported by a structure to the signature and
   constructs the structure morphism -}
processStruct :: String -> Sign -> Sign -> [Element] -> LibEnvFull ->
                 IO (Sign,Morphism,LibEnvFull)
processStruct name srcSig tarSig els libs = do
  let b1 = sigBase srcSig
  let m1 = sigModule srcSig
  let b2 = sigBase tarSig
  let m2 = sigModule tarSig
  let prefix = name ++ "/"
  let rel sym = Symbol b2 m2 $ prefix ++ (symName sym)
  (symmap,libs1) <- constructMap els (b1,m1) (b2,m2) libs
  let Sign _ _ ds = srcSig
  let morph_init =
        Morphism b2 m2 name (Sign b1 m1 []) tarSig Definitional Map.empty
  let (sig2,morph2) =
        foldl (\ (sig,morph) (Def s t v) ->
                 let local = isLocalSym s srcSig
                     defined = isDefinedSym s srcSig
                     sig1 = if (not local) then sig else
                       let s1 = rel s
                           t1 = case translate morph t of
                                     Just t1'-> t1'
                                     Nothing -> error $
                                       "Structure could not be formed. " ++ name
                           v1 = case v of
                                     Just v1' -> translate morph v1'
                                     Nothing -> Map.lookup s symmap
                           in addDef (Def s1 t1 v1) sig
                     morph1 = let source1 = addDef (Def s t v) $ source morph
                                  e = if local
                                         then Const $ rel s
                                         else Map.findWithDefault (Const s)
                                              s symmap
                                  map1 = if defined
                                            then symMap morph
                                            else Map.insert s e $ symMap morph
                                  in morph { source = source1
                                           , target = sig1
                                           , symMap = map1 }
                     in (sig1, canForm morph1)
              ) (tarSig,morph_init) ds
  return (sig2,morph2,libs1)

  -- constructs the translation part of the structure
constructMap :: [Element] -> NODE -> NODE -> LibEnvFull ->
                IO (Map.Map Symbol EXP, LibEnvFull)
constructMap els src tar libs = do
  foldM (\ ml el ->
           let n = elName el
               in if (n == conassQN) then conass2map el ml src tar else
                  if (n == includeQN) then incl2map el ml src tar else
                  if (n == strassQN) then strass2map el ml src tar else
                  return ml
        ) (Map.empty,libs) els

-- converts the constant assignment into a map
conass2map :: Element -> (Map.Map Symbol EXP, LibEnvFull) -> NODE ->
              NODE -> IO (Map.Map Symbol EXP, LibEnvFull)
conass2map e (mapp,libs) src tar = do
  let (b,m,n) = getBMN e src
  case findChildren omobjQN e of
       [omobj] -> do let expr = omobj2exp omobj tar
                     let map1 = Map.insert (Symbol b m n) expr mapp
                     return (map1,libs)
       _ -> error "Constant assignment element must have a unique OMMOR child."

-- converts the included morphism into a map
incl2map :: Element -> (Map.Map Symbol EXP, LibEnvFull) -> NODE ->
            NODE -> IO (Map.Map Symbol EXP, LibEnvFull)
incl2map e (m,l) _ tar =
  case findChildren ommorQN e of
       [ommor] -> do (mor,l1) <- ommor2mor ommor tar l
                     let m1 = Map.union m $ symMap mor
                     return (m1,l1)
       _ -> error "Include element must have a unique OMMOR child."

-- converts the structure assignment into a map
strass2map :: Element -> (Map.Map Symbol EXP, LibEnvFull) -> NODE ->
              NODE -> IO (Map.Map Symbol EXP, LibEnvFull)
strass2map e (m,l) src tar =
  case findChildren ommorQN e of
       [ommor] -> do (mor1,l1) <- retrieveMorph (getBMN e src) l
                     (mor2,l2) <- ommor2mor ommor tar l1
                     let m1 = Map.union m $ combineMorphs mor1 mor2
                     return (m1,l2)
       _ -> error "Structure assignment element must have a unique OMMOR child."

-- converts an OMMOR element to a morphism
ommor2mor :: Element -> NODE -> LibEnvFull -> IO (Morphism,LibEnvFull)
ommor2mor e ref libs =
  case elChildren e of
       [el] -> omel2mor el ref libs
       _ -> error "OMMOR element must have a unique child."

-- converts an Open Math element to a morphism
omel2mor :: Element -> NODE -> LibEnvFull -> IO (Morphism,LibEnvFull)
omel2mor e ref libs =
  let name = elName e
      in if (name == omsQN) then oms2mor e ref libs else
         if (name == omaQN) then oma2mor e ref libs else
         error "Only OMA and OMS elements correspond to a morphism."

-- converts an OMS element to a morphism
oms2mor :: Element -> NODE -> LibEnvFull -> IO (Morphism,LibEnvFull)
oms2mor e ref libs = retrieveMorph (getBMN e ref) libs

-- converts an OMA element to a morphism
oma2mor :: Element -> NODE -> LibEnvFull -> IO (Morphism,LibEnvFull)
oma2mor e ref l = do
  case elChildren e of
       [c,m1,m2] -> do
         if (eqOMS c compOMS)
            then do (mor1,l1) <- omel2mor m1 ref l
                    (mor2,l2) <- omel2mor m2 ref l1
                    let morR = compMorph (mor1 { target = source mor2 }) mor2
                    let mor = case morR of
                                   Result _ (Just mor') -> mor'
                                   _ -> error "Morphism cannot be retrieved."
                    return (mor,l2)
            else error "The first child of OMA in OMMOR must be composition."
       _ -> error "OMA in OMMOR must have exactly three children."

-- retrieves a morphism by the link name
retrieveMorph :: LINK -> LibEnvFull -> IO (Morphism,LibEnvFull)
retrieveMorph (b,m,n) l = do
  l1 <- addFromFile (replaceExtension b twelfE) l
  let b' = dropExtension b
  case elemIndex '/' n of
       Nothing -> do
         let mor = lookupMorph (b',m,n) l1
         return (mor,l1)
       Just i -> do
         let (n1,(_:n2)) = splitAt i n
         let mor1 = lookupMorph (b',m,n1) l1
         let sig = source mor1
         let b1 = sigBase sig
         let m1 = sigModule sig
         (mor2,l2) <- retrieveMorph (b1,m1,n2) l1
         let morR = compMorph (mor2 { target = sig }) mor1
         let mor = case morR of
                        Result _ (Just mor') -> mor'
                        _ -> error "Morphism cannot be retrieved."
         return (mor,l2)

-- combines two morphisms according to the structure assignment
combineMorphs :: Morphism -> Morphism -> Map.Map Symbol EXP
combineMorphs mor1 mor2 =
  let local = getLocalSyms $ source mor1
      declared = getDeclaredSyms $ source mor1
      in Set.fold ( \ s ->
                      let s1 = case mapSymbol s mor1 of
                                    Just (Const s1') -> s1'
                                    _ -> error $ "Morphisms cannot be combined."
                          e1 = case mapSymbol s mor2 of
                                    Just e1' -> e1'
                                    _ -> error $ "Morphisms cannot be combined."
                          in Map.insert s1 e1
                  ) Map.empty $ Set.intersection local declared

------------------------------------------------------------------------------
------------------------------------------------------------------------------
-- CONSTRUCTING ALIASES AND NOTATIONS

 -- so far aliases are ignored
addAlias :: Element -> (LibEnvFull,Sign) -> IO (LibEnvFull,Sign)
addAlias _ ls = return ls

-- so far notations are ignored
addNotat :: Element -> (LibEnvFull,Sign) -> IO (LibEnvFull,Sign)
addNotat _ ls = return ls
