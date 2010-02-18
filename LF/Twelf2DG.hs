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
import Debug.Trace
import Network.URI

import Static.AnalysisStructured
import Static.DevGraph

import Logic.Grothendieck
import Logic.ExtSign

import LF.Sign
--import LF.Morphism
import LF.Logic_LF

import Data.Maybe
import Data.List
import qualified Data.Map as Map
import qualified Data.Set as Set

import Common.LibName
import Common.Utils
import Common.Id

import Control.Monad

import Text.XML.Light.Input
import Text.XML.Light.Types
import Text.XML.Light.Proc

import Driver.Options

type RAW_LIBS = (RAW_GRAPH,Set.Set FilePath)

type RAW_GRAPH = (RAW_NODES,RAW_LINKS)
type RAW_NODES = Map.Map RAW_NODE_NAME Sign
type RAW_LINKS = Map.Map (RAW_LINK_NAME,RAW_NODE_NAME,RAW_NODE_NAME)
                         (Map.Map Symbol EXP)

type RAW_NODE_NAME = (BASE,MODULE)
type RAW_LINK_NAME = (BASE,MODULE,NAME)

emptyLibs :: RAW_LIBS
emptyLibs = ((Map.empty,Map.empty),Set.empty)

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

------------------------------------------------------------------------------
------------------------------------------------------------------------------

-- generates a library environment from the path of a Twelf file
anaTwelfFile :: HetcatsOpts -> FilePath -> IO (Maybe (LibName, LibEnv))
anaTwelfFile _ fp = do
    dir <- getCurrentDirectory
    let file = resolve fp (dir ++ "/")
    (rg,_) <- twelf2libs file emptyLibs
    let envir = makeLibEnv rg
    let name = LibName (IndirectLink "" nullRange file noTime) Nothing
    return $ Just (name,envir)                 

-- generates a library environment from raw libraries
makeLibEnv :: RAW_GRAPH -> LibEnv
makeLibEnv rg = addLinks rg $ addNodes rg emptyLibEnv

-- adds nodes to the library environment
addNodes :: RAW_GRAPH -> LibEnv -> LibEnv
addNodes (sigs,_) envir =
  foldl (\ e ((b,m),sig) -> 
           let libname = LibName (IndirectLink "" nullRange b noTime) Nothing
               dg = Map.findWithDefault emptyDG libname e
               nodeName = emptyNodeName { getName = Token m nullRange }
               gsig = G_sign LF (makeExtSign LF sig) startSigId
               (_,dg1) = insGSig dg nodeName DGBasic gsig
               in Map.insert libname dg1 e
        ) 
        envir
        $ Map.toList sigs   

-- adds links to the library environment
addLinks :: RAW_GRAPH -> LibEnv -> LibEnv
addLinks _ envir = 
  {-foldl (\ e ((l,d,c),symmap) -> 
           let (b,m,n) = l
               libname = LibName (IndirectLink "" nullRange b noTime) Nothing
               dg = Map.findWithDefault emptyDG libname env
               dom = case Map.lookup d sigs of
                          Nothing -> error "Invalid link source."
                          Just s -> s
               cod = case Map.lookup c sigs of
                          Nothing -> error "Invalid link target."
                          Just s -> s
               morph = Morphism b m n dom cod symmap
               gmorph = GMorphism LF (makeExtSign LF dom) morph startMorId ----- TODO
               (_,dg1) = insLink dg gmorph ----- TODO
               in Map.insert libname dg1 e
        ) 
        env
        $ Map.toList morphs -} envir

------------------------------------------------------------------------------
------------------------------------------------------------------------------       

-- path to the Twelf folder must be set in the environment variable TWELF_LIB
twelf :: String
twelf = "check-some"
options :: [String]
options = ["-omdoc"]

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

-- generates signatures and morphisms from the absolute path of a Twelf file
twelf2libs :: FilePath -> RAW_LIBS -> IO RAW_LIBS
twelf2libs file libs = do
  runTwelf (trace ("Analyzing file: " ++ file) file)
  getSigsAndMorphs file libs 

-- converts the specifications and views into signatures and morphisms
getSigsAndMorphs :: FilePath -> RAW_LIBS -> IO RAW_LIBS 
getSigsAndMorphs file libs = do
  let omdoc_file = replaceExtension file "omdoc"
  xml <- readFile omdoc_file
  let elems = onlyElems $ parseXML xml
  let elems1 = filter (\ e -> elName e == omdocQN) elems
  case elems1 of
       [root] -> 
          foldM (\ sm e -> 
                     let n = elName e
                         in if (n == theoryQN) then addSign file e sm else
                            if (n == viewQN) then addMorph file e sm else
                            return sm
                ) 
                libs
                $ elChildren root
       _ -> fail "Not an OMDoc file."

-- transforms a theory element into a signature and adds it to the map
addSign :: FilePath -> Element -> RAW_LIBS -> IO RAW_LIBS
addSign file e sm =
  case getNameAttr e of
       Nothing -> error "Theory element must have a name."
       Just name -> do
          let sig = Sign file name []
          (sm1,sig1) <-
                foldM (\ sms el -> 
                  let n = elName el
                      in if (n == includeQN) then addIncl el sms else
                         if (n == structureQN) then addStruct el sms else
                         if (n == constantQN) then addConst el sms else
                         if (n == aliasQN) then addAlias el sms else
                         if (n == notationQN) then addNotat el sms else 
                         return sms
                      ) 
                      (sm,sig)
                      $ elChildren e
          let ((sigs,morphs),incl) = sm1
          let sigs1 = Map.insert (file,name) sig1 sigs
          return ((sigs1,morphs),incl) 
              
-- adds a constant declaration to the signature
addConst :: Element -> (RAW_LIBS,Sign) -> IO (RAW_LIBS,Sign)
addConst e (sm,sig) = do
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
  return (sm,sig1)               

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
addIncl :: Element -> (RAW_LIBS,Sign) -> IO (RAW_LIBS,Sign)
addIncl e (libs,sig) = do
  case getFromAttr e of
       Nothing -> error "Include element must have a \"from\" attribute."
       Just ref -> do
         let curBase = sigBase sig
         let curModule = sigModule sig
         let (br,m) = splitRef ref
         let b = replaceExtension (resolve br curBase) "elf"
         ((sigs,morphs),incls) <- addFromFile b curBase libs  
         let s = (b,m)
         let t = (curBase,curModule)
         let sig1 = addToSig s sig sigs  
         let morphs1 = addToMorphs s t morphs
         return (((sigs,morphs1),incls),sig1)

{- parses the referenced file and imports all signatures
   and morphisms from it -}
addFromFile :: String -> FilePath -> RAW_LIBS -> IO RAW_LIBS
addFromFile file base libs = do
  let ((sigs,morphs),incls) = libs
  if (file == base || Set.member file incls)
     then return libs
     else do ((sigs1,morphs1),incls1) <- twelf2libs file libs
             let sigs2 = Map.union sigs sigs1
             let morphs2 = Map.union morphs morphs1
             let incls2 = Set.insert file $ Set.union incls incls1
             return ((sigs2,morphs2),incls2) 

-- adds included definitions to the signature
addToSig :: RAW_NODE_NAME -> Sign -> RAW_NODES -> Sign
addToSig s sig sigs = 
  case Map.lookup s sigs of
       Nothing -> error "Invalid inclusion source."
       Just (Sign _ _ ds) -> addDefs ds sig

-- adds the inclusion to the collection of morphisms
addToMorphs :: RAW_NODE_NAME -> RAW_NODE_NAME -> RAW_LINKS -> RAW_LINKS
addToMorphs s t morphs = 
  let (b,m) = t
      name = (b,m,"") 
      in Map.insert (name,s,t) Map.empty morphs   

{- adds declarations arising from a structure to the signature
   adds the structure to the morphism map -}
addStruct :: Element -> (RAW_LIBS,Sign) -> IO (RAW_LIBS,Sign)
addStruct _ sm = return sm 

-- so far aliases are ignored
addAlias :: Element -> (RAW_LIBS,Sign) -> IO (RAW_LIBS,Sign)
addAlias _ sm = return sm

-- so far notations are ignored
addNotat :: Element -> (RAW_LIBS,Sign) -> IO (RAW_LIBS,Sign)
addNotat _ sm = return sm

-- so far views are ignored
addMorph :: FilePath -> Element -> RAW_LIBS -> IO RAW_LIBS
addMorph _ _ sm = return sm
