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

--import Static.GTheory
import Static.ComputeTheory
--import Static.AnalysisStructured
import Static.DevGraph

--import Logic.Grothendieck

import LF.Sign
--import LF.Morphism

import Data.Maybe
import Data.List
import qualified Data.Map as Map

import Common.LibName
import Common.Utils

import Control.Monad

import Text.XML.Light.Input
import Text.XML.Light.Types
import Text.XML.Light.Proc

import Driver.Options

-- path to the Twelf folder must be set in the environment variable TWELF_LIB
twelf :: String
twelf = "check-some"
options :: [String]
options = ["-omdoc", "."]

type SIG_VIEW_NAME = (BASE_NAME,MODULE_NAME)
type SIGS_AND_MORPHS = (Map.Map SIG_VIEW_NAME Sign, 
                        Map.Map (SIG_VIEW_NAME,SIG_VIEW_NAME,SIG_VIEW_NAME)
                                (Map.Map Symbol EXP))

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

-- generates a library from the path of a Twelf file
anaTwelfFile :: HetcatsOpts -> FilePath -> IO (Maybe (LibName, LibEnv))
anaTwelfFile _ file = do
    dg <- twelf2DG file
    let name = emptyLibName ""
    return $ Just (name, 
                   Map.singleton name $ computeDGraphTheories Map.empty dg)

-- generates a development graph from the path of a Twelf file
twelf2DG :: FilePath -> IO DGraph
twelf2DG file = do
  twelf2SigsAndMorphs file
  return emptyDG

{- runs twelf to create an omdoc file
   generates the corresponding signatures and morphisms -}
twelf2SigsAndMorphs :: FilePath -> IO SIGS_AND_MORPHS
twelf2SigsAndMorphs file = do
  dir <- getEnvDef "TWELF_LIB" ""
  if null dir 
     then error "environment variable TWELF_LIB is not set"
     else do
       (_, _, _, pr) <- runInteractiveProcess (concat [dir, "/" ,twelf])
                                              (options ++ [file])
                                              Nothing
                                              Nothing 
       exitCode <- getProcessExitCode pr
       case exitCode of
            Nothing -> getSigsAndMorphs file
            Just ExitSuccess -> error "Twelf terminated immediately."
            Just (ExitFailure i) -> 
              error $ "Calling Twelf failed with exitCode: " ++ show i

-- converts the specifications and views into signatures and morphisms
getSigsAndMorphs :: FilePath -> IO SIGS_AND_MORPHS 
getSigsAndMorphs fp = do
  dir <- getCurrentDirectory
  let file = resolve fp (dir ++ "/")
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
                (Map.empty, Map.empty)
                $ elChildren root
       _ -> fail "Not an OMDoc file."

-- transforms a theory element into a signature and adds it to the map
addSign :: FilePath -> Element -> SIGS_AND_MORPHS -> IO SIGS_AND_MORPHS
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
          let (sigs,morphs) = sm1
          let sigs1 = Map.insert (file,name) sig1 sigs
          return (sigs1,morphs) 
              
-- adds a constant declaration to the signature
addConst :: Element -> (SIGS_AND_MORPHS,Sign) -> IO (SIGS_AND_MORPHS,Sign)
addConst e (sm,sig) = do
  let sym = case getNameAttr e of
                 Nothing -> error "Constant element must have a name."
                 Just n -> Symbol (sigBase sig) (sigName sig) n
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
      curModule = sigName sig
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
omv2var :: Element -> VAR
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
addIncl :: Element -> (SIGS_AND_MORPHS,Sign) -> IO (SIGS_AND_MORPHS,Sign)
addIncl e ((sigs1,morphs1),sig1) = do
  let curBase = sigBase sig1
  let curModule = sigName sig1
  case getFromAttr e of
       Nothing -> error "Include element must have a \"from\" attribute."
       Just ref -> 
         case elemIndices '?' ref of
              [i] -> do let (br,m) = splitAt i ref
                        let b = replaceExtension (resolve br curBase) "elf"
                        let source = (b,m)
                        let target = (curBase,curModule)
                        (sigs2,morphs2) <- twelf2SigsAndMorphs b
                        let sigs = Map.union sigs1 sigs2
                        let morphs3 = Map.union morphs1 morphs2
                        let sig = case Map.lookup source sigs of
                                       Nothing -> 
                                          error "Invalid inclusion source."
                                       Just (Sign _ _ ds) -> addDefs ds sig1
                        let morphs = Map.insert ((curBase,""),source,target)
                                                Map.empty
                                                morphs3
                        return ((sigs,morphs),sig)
              _ -> error "Invalid inclusion source."      

{- adds declarations arising from a structure to the signature
   adds the structure to the morphism map -}
addStruct :: Element -> (SIGS_AND_MORPHS,Sign) -> IO (SIGS_AND_MORPHS,Sign)
addStruct _ sm = return sm 

-- so far aliases are ignored
addAlias :: Element -> (SIGS_AND_MORPHS,Sign) -> IO (SIGS_AND_MORPHS,Sign)
addAlias _ sm = return sm

-- so far notations are ignored
addNotat :: Element -> (SIGS_AND_MORPHS,Sign) -> IO (SIGS_AND_MORPHS,Sign)
addNotat _ sm = return sm

-- so far views are ignored
addMorph :: FilePath -> Element -> SIGS_AND_MORPHS -> IO SIGS_AND_MORPHS
addMorph _ _ sm = return sm
