{- |
Module      :  ./LF/Twelf2GR.hs
Description :  Conversion of Twelf files to LF signatures and morphisms
Copyright   :  (c) Kristina Sojakova, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  k.sojakova@jacobs-university.de
Stability   :  experimental
Portability :  portable
-}

module LF.Twelf2GR where

import System.Exit
import System.Process
import System.Directory
import System.FilePath
import System.IO (hGetContents)


import LF.Sign
import LF.Morphism

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe (fromMaybe)

import Common.IRI
import Common.Result
import Common.Utils
import Common.Keywords

import Control.Monad
import qualified Control.Monad.Fail as Fail

import Text.XML.Light.Input
import Text.XML.Light.Types
import Text.XML.Light.Proc

type NODE = (BASE, MODULE)
type LINK = (BASE, MODULE, NAME)

type SIGS = Map.Map MODULE Sign
type MORPHS = Map.Map ((MODULE, NAME), NODE, NODE) Morphism

type GRAPH = (SIGS, MORPHS)
type LIBS = Map.Map BASE GRAPH
type LIBS_EXT = ((LIBS, [BASE]), (BASE, GRAPH))

data Namespace = LATIN | HETS

latinEnv :: String
latinEnv = "LATIN_LIB"

twelfEnv :: String
twelfEnv = "TWELF_LIB"

hetsEnv :: String
hetsEnv = "HETS_HOME"

emptyGraph :: GRAPH
emptyGraph = (Map.empty, Map.empty)

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
nameQN = QName "name" Nothing Nothing

moduleQN :: QName
moduleQN = QName "module" Nothing Nothing

baseQN :: QName
baseQN = QName "base" Nothing Nothing

fromQN :: QName
fromQN = QName "from" Nothing Nothing

toQN :: QName
toQN = QName "to" Nothing Nothing

omdocE :: String
omdocE = "omdoc"

twelfE :: String
twelfE = "elf"

-- path to the Twelf folder must be set in the environment variable TWELF_LIB
twelf :: String
twelf = "check-some"

options :: [String]
options = ["-omdoc"]

{- ----------------------------------------------------------------------------
----------------------------------------------------------------------------
HELPER FUNCTIONS -}

getFromAttr :: Element -> String
getFromAttr e = fromMaybe (error "Element is missing a \"from\" attribute.") $
   findAttr fromQN e

getToAttr :: Element -> String
getToAttr e = fromMaybe (error "Element is missing a \"to\" attribute.") $
  findAttr toQN e

getNameAttr :: Element -> String
getNameAttr e = fromMaybe (error $ "Element is missing a name." ++ show e) $
  findAttr nameQN e

getModuleAttr :: Element -> Maybe String
getModuleAttr = findAttr moduleQN

getBaseAttr :: Element -> Maybe String
getBaseAttr = findAttr baseQN

-- compares two OMS elements
eqOMS :: Element -> Element -> Bool
eqOMS e1 e2 = not $ elName e1 /= omsQN || elName e2 /= omsQN
{- and [ getNameAttr e1 == getNameAttr e2
, getModuleAttr e1 == getModuleAttr e2
, getBaseAttr e1 == getBaseAttr e2] -}

toOMDoc :: FilePath -> FilePath
toOMDoc fp = replaceExtension fp omdocE

toTwelf :: FilePath -> FilePath
toTwelf fp = replaceExtension fp twelfE

getEnv :: Namespace -> String
getEnv ns =
  case ns of
    LATIN -> latinEnv
    HETS -> hetsEnv

getEnvVar :: String -> IO String
getEnvVar var = do
  val <- getEnvDef var ""
  if null val
     then error $ "environment variable " ++ var ++ " is not set."
     else return val

-- resolves the first file path wrt to the second
resolve :: FilePath -> FilePath -> FilePath
resolve fp1 fp2 =
  case parseIRIReference fp1 of
    Nothing -> er
    Just uri1 ->
      case parseIRIReference fp2 of
        Nothing -> er
        Just uri2 ->
          case relativeTo uri1 uri2 of
               Nothing -> er
               Just f -> show f
  where er = error "Invalid file name."

-- relativizes the first file path wrt to the second
relativize :: FilePath -> FilePath -> FilePath
relativize fp1 fp2 =
  case parseIRIReference fp1 of
    Nothing -> er
    Just uri1 ->
      case parseIRIReference fp2 of
        Nothing -> er
        Just uri2 -> show $ relativeFrom uri1 uri2
  where er = error "Invalid file name."

-- resolves the file path wrt to the current directory
toAbsoluteURI :: FilePath -> IO FilePath
toAbsoluteURI fp = do
  dir <- getCurrentDirectory
  return $ resolve fp $ dir ++ "/"

-- relativizes an absolute file path wrt to the current directory
toRelativeURI :: FilePath -> IO FilePath
toRelativeURI fp = do
  dir <- getCurrentDirectory
  return $ relativize fp $ dir ++ "/"

{- converts a filepath to a library name, i.e.
   relativizes w.r.t. the LATIN_HOME env variable -}
toLibName :: Namespace -> FilePath -> IO BASE
toLibName ns fp = do
  file <- toAbsoluteURI fp
  dir <- getEnvVar $ getEnv ns
  return $ relativize file $ dir ++ "/"

{- converts a library name to a filepath, i.e.
   resolves w.r.t. the LATIN_HOME env variable -}
fromLibName :: Namespace -> BASE -> IO FilePath
fromLibName ns lname = do
  dir <- getEnvVar $ getEnv ns
  return $ resolve lname $ dir ++ "/"

{- returns the referenced base and module resolved w.r.t.
   the second argument -}
parseRef :: Namespace -> String -> String -> IO NODE
parseRef ns ref base = do
  file <- fromLibName ns base
  case splitBy '?' ref of
       [br, m] -> do let b = toTwelf $ resolve br file
                     lname <- toLibName ns b
                     return (lname, m)
       _ -> Fail.fail "Invalid reference."

{- retrieves the base, module, and name attributes resolved w.r.t.
   the second argument -}
getBMN :: Namespace -> Element -> NODE -> IO (BASE, MODULE, NAME)
getBMN ns e (base, modul) = do
  file <- fromLibName ns base
  let n = fromMaybe "" $ findAttr nameQN e
  let m = fromMaybe modul $ getModuleAttr e
  let b = fromMaybe file $ getBaseAttr e
  lname <- toLibName ns b
  return (lname, m, n)

{- parses the referenced file if needed and imports all signatures
   and morphisms from it -}
addFromFile :: Namespace -> FilePath -> LIBS_EXT -> IO LIBS_EXT
addFromFile ns lname libs@(lb@(l, _), (b, gr)) =
  if lname == b || Map.member lname l
     then return libs
     else do file <- fromLibName ns lname
             lb' <- twelf2GR ns file lb
             return (lb', (b, gr))

-- finds the signature by base and module
lookupSig :: NODE -> LIBS_EXT -> Sign
lookupSig (b, m) ((libs, _), (base, (sigs, _))) =
  let sigs1 = if b == base then sigs else
                 fst $ Map.findWithDefault er b libs
      in Map.findWithDefault er m sigs1
  where er = error "Signature cannot be found."

-- finds the morphism by base, module, and name
lookupMorph :: LINK -> LIBS_EXT -> Morphism
lookupMorph (b, m, n) ((libs, _), (base, (_, morphs))) =
  let morphs1 = if b == base then morphs else
                   snd $ Map.findWithDefault er b libs
      morphs2 = Map.filterWithKey (\ (l, _, _) _ -> l == (m, n)) morphs1
      in case Map.toList morphs2 of
              [(_, morph)] -> morph
              _ -> er
  where er = error "Morphism cannot be found."

-- adds the signature to the signature collection
addSigToGraph :: Sign -> LIBS_EXT -> LIBS_EXT
addSigToGraph sig (lb, (b, (sigs, morphs))) =
  let sigs1 = Map.insert (sigModule sig) sig sigs
      in (lb, (b, (sigs1, morphs)))

-- adds the morphism to the morphism collection
addMorphToGraph :: Morphism -> LIBS_EXT -> LIBS_EXT
addMorphToGraph m (lb, (b, (sigs, morphs))) =
  let sig1 = source m
      sig2 = target m
      l = (morphModule m, morphName m)
      s = (sigBase sig1, sigModule sig1)
      t = (sigBase sig2, sigModule sig2)
      morphs1 = Map.insert (l, s, t) m morphs
      in (lb, (b, (sigs, morphs1)))

-- computes the correct targets of morphisms
computeTargets :: GRAPH -> LIBS_EXT -> GRAPH
computeTargets (sigs, morphs) libs =
   let morphs2 = Map.foldrWithKey
          (\ k@((_, _), _, t) morph morphs1 ->
             let morph1 = morph { target = lookupSig t libs }
                 in Map.insert k morph1 morphs1
          ) Map.empty morphs
       in (sigs, morphs2)

{- ----------------------------------------------------------------------------
----------------------------------------------------------------------------
CONSTRUCTING THE LIBRARY OF LF SIGNATURES AND MORPHISMS -}

-- analyzes the given Twelf file and returns LF signatures and morphisms
twelf2SigMor :: Namespace -> FilePath -> IO LIBS
twelf2SigMor ns fp = do
  (libs, _) <- twelf2GR ns fp (Map.empty, [])
  return libs

{- updates the graph libraries by adding specs from the Twelf file;
   the list of library names stores the order in which they were added,
   which is needed later for the construction of DGraphs -}
twelf2GR :: Namespace -> FilePath -> (LIBS, [BASE]) -> IO (LIBS, [BASE])
twelf2GR ns fp lb = do
  file <- toAbsoluteURI fp
  runTwelf file
  le@((libs, bs), (b, gr)) <- buildGraph ns file lb
  let gr' = computeTargets gr le
  let libs' = Map.insert b gr' libs
  let bs' = bs ++ [b]
  return (libs', bs')

-- runs twelf to create an omdoc file
runTwelf :: FilePath -> IO ()
runTwelf file = do
  let dir = dropFileName file
  twelfdir <- getEnvVar twelfEnv
  (_, out, err, pr) <-
    runInteractiveProcess (concat [twelfdir, "/" , twelf])
                          (options ++ [dir, file])
                          Nothing
                          Nothing
  exitCode <- waitForProcess pr
  outH <- hGetContents out
  errH <- hGetContents err
  case exitCode of
       ExitFailure i -> do
          putStrLn (outH ++ errH)
          error $ "Calling Twelf failed with exitCode: " ++ show i ++
                  " on file " ++ file ++ "dir: " ++ dir ++ "twelfdir: " ++ twelfdir
       ExitSuccess -> return ()

{- ----------------------------------------------------------------------------
----------------------------------------------------------------------------
CONSTRUCTING SIGNATURES AND MORPHISMS -}

-- builds the LF signature and morphism graph
buildGraph :: Namespace -> FilePath -> (LIBS, [BASE]) -> IO LIBS_EXT
buildGraph ns file lb = do
  xml <- readFile $ toOMDoc file
  lname <- toLibName ns file
  let elems = onlyElems $ parseXML xml
  let elems1 = filter (\ e -> elName e == omdocQN) elems
  case elems1 of
       [root] ->
         foldM (\ libs e ->
                  let n = elName e
                      in if n == theoryQN then addSign ns e libs else
                         if n == viewQN then addView ns e libs else
                         return libs
               )
               (lb, (lname, emptyGraph))
               $ elChildren root
       _ -> Fail.fail "Not an OMDoc file."

-- transforms a theory element into a signature and adds it to the graph
addSign :: Namespace -> Element -> LIBS_EXT -> IO LIBS_EXT
addSign ns e libs@(_, (lname, _)) = do
  let sig = Sign lname (getNameAttr e) []
  (libs1, sig1) <-
     foldM (\ ls el ->
              let n = elName el
                  in if n == includeQN then addIncl ns el ls else
                     if n == structureQN then addStruct ns el ls else
                     if n == constantQN then addConst ns el ls else
                     return ls
           )
           (libs, sig)
           $ elChildren e
  return $ addSigToGraph sig1 libs1

-- transforms a view element into a view and adds it to the graph
addView :: Namespace -> Element -> LIBS_EXT -> IO LIBS_EXT
addView ns e libs@(_, (lname, _)) = do
  let name = getNameAttr e
  let from = getFromAttr e
  let to = getToAttr e
  (b1, m1) <- parseRef ns from lname
  (b2, m2) <- parseRef ns to lname
  libs1 <- addFromFile ns b1 libs
  libs2 <- addFromFile ns b2 libs1
  let srcSig = lookupSig (b1, m1) libs2
  let tarSig = lookupSig (b2, m2) libs2
  (morph, libs3) <- getViewMorph ns name srcSig tarSig (elChildren e) libs2
  let libs4 = addMorphToGraph morph libs3
  return libs4

-- constructs the view morphism
getViewMorph :: Namespace -> String -> Sign -> Sign -> [Element] -> LIBS_EXT ->
                IO (Morphism, LIBS_EXT)
getViewMorph ns name srcSig tarSig els libs@(_, (lname, _)) = do
  let b1 = sigBase srcSig
  let m1 = sigModule srcSig
  let b2 = sigBase tarSig
  let m2 = sigModule tarSig
  (symmap, libs1) <- constructMap ns els (b1, m1) (b2, m2) libs
  let morph = Morphism lname name "" srcSig tarSig Postulated symmap
  return (morph, libs1)

{- ----------------------------------------------------------------------------
----------------------------------------------------------------------------
CONSTRUCTING CONSTANTS -}

-- adds a constant declaration to the signature
addConst :: Namespace -> Element -> (LIBS_EXT, Sign) -> IO (LIBS_EXT, Sign)
addConst ns e (libs, sig) = do
  let ref@(b, m) = (sigBase sig, sigModule sig)
  let sym = Symbol b m $ getNameAttr e
  typ <- case findChildren typeQN e of
              [t] -> type2exp ns t ref
              _ -> Fail.fail "Constant element must have a unique type child."
  val <- case findChildren definitionQN e of
              [] -> return Nothing
              [v] -> fmap Just $ definition2exp ns v ref
              _ -> Fail.fail $ "Constant element must have at most " ++
                          "one definition child."
  let sig1 = addDef (Def sym typ val) sig
  return (libs, sig1)

{- converts a type element to an expression
   second argument is used for resolving symbol references -}
type2exp :: Namespace -> Element -> NODE -> IO EXP
type2exp ns e ref =
  case findChildren omobjQN e of
       [omobj] -> omobj2exp ns omobj ref
       _ -> Fail.fail "Type element must have a unique OMOBJ child."

{- converts a definition element to an expression
   second argument is used for resolving symbol references -}
definition2exp :: Namespace -> Element -> NODE -> IO EXP
definition2exp ns e ref =
  case findChildren omobjQN e of
       [omobj] -> omobj2exp ns omobj ref
       _ -> Fail.fail "Definition element must have a unique OMOBJ child."

-- converts an OMOBJ element to an expression
omobj2exp :: Namespace -> Element -> NODE -> IO EXP
omobj2exp ns e ref =
  case elChildren e of
       [el] -> omel2exp ns el ref
       _ -> Fail.fail "OMOBJ element must have a unique child."

-- converts an Open Math element to an expression
omel2exp :: Namespace -> Element -> NODE -> IO EXP
omel2exp ns e ref =
  let name = elName e
      in if name == omsQN then oms2exp ns e ref else
         if name == omaQN then oma2exp ns e ref else
         if name == ombindQN then ombind2exp ns e ref else
         if name == omvQN then omv2exp ns e ref else
         Fail.fail $ "Only OMA, OMS, and OMBIND elements correspond " ++
                "to an expression."

-- converts an OMS element to an expression
oms2exp :: Namespace -> Element -> NODE -> IO EXP
oms2exp ns e ref =
  if eqOMS e typeOMS then return Type else do
  (b, m, n) <- getBMN ns e ref
  return $ Const $ Symbol b m n

-- converts an OMA element to an expression
oma2exp :: Namespace -> Element -> NODE -> IO EXP
oma2exp ns e ref =
  case elChildren e of
    [] -> Fail.fail "OMA element must have at least one child."
    (f : as) -> do
      as1 <- mapM (\ a -> omel2exp ns a ref) as
      if eqOMS f arrowOMS
         then case as1 of
                   [] -> Fail.fail $ "The -> constructor must be applied" ++
                                " to at least one argument."
                   _ -> return $ Func (init as1) (last as1)
         else do f1 <- omel2exp ns f ref
                 return $ Appl f1 as1

-- converts an OMBIND element to an expression
ombind2exp :: Namespace -> Element -> NODE -> IO EXP
ombind2exp ns e ref =
  case elChildren e of
    [f, d, b] ->
      if elName d /= ombvarQN
         then Fail.fail "The second child of OMBIND must be OMBVAR."
         else do d1 <- ombvar2decls ns d ref
                 b1 <- omel2exp ns b ref
                 if eqOMS f lambdaOMS then return $ Lamb d1 b1 else
                  if eqOMS f piOMS then return $ Pi d1 b1 else
                 {- so far implicit binders are treated
                    as explicit -}
                   if eqOMS f impLambdaOMS then return $ Lamb d1 b1 else
                    if eqOMS f impPiOMS then return $ Pi d1 b1 else
                     Fail.fail "The first child of OMBIND must be be Pi or Lambda."
    _ -> Fail.fail "OMBIND element must have exactly 3 children."

-- converts an OMBVAR element to a list of declaration
ombvar2decls :: Namespace -> Element -> NODE -> IO CONTEXT
ombvar2decls ns e ref =
  mapM (\ a -> omattr2vardecl ns a ref) $ findChildren omattrQN e

-- converts an OMATTR element to a variable declaration
omattr2vardecl :: Namespace -> Element -> NODE -> IO (VAR, EXP)
omattr2vardecl ns e ref =
  case findChildren omatpQN e of
       [omatp] -> do
         val <- omatp2exp ns omatp ref
         case findChildren omvQN e of
              [omv] -> return (getNameAttr omv, val)
              _ -> Fail.fail "OMATTR element must have a unique OMV child."
       _ -> Fail.fail "OMATTR element must have a unique OMATP child."

-- converts an OMATP element to an expression
omatp2exp :: Namespace -> Element -> NODE -> IO EXP
omatp2exp ns e ref =
  case elChildren e of
       [c1, c2] ->
          if eqOMS c1 oftypeOMS
             then omel2exp ns c2 ref
             else Fail.fail $ "The first child of OMATP " ++
                         "must be the \"oftype\" symbol."
       _ -> Fail.fail "OMATP element must have exactly two children."

-- converts an OMV element to an expression
omv2exp :: Namespace -> Element -> NODE -> IO EXP
omv2exp _ e _ = return $ Var $ getNameAttr e

{- ----------------------------------------------------------------------------
----------------------------------------------------------------------------
CONSTRUCTING INCLUSIONS -}

{- adds declarations arising from an inclusion to the signature
   adds the inclusion to the morphism map -}
addIncl :: Namespace -> Element -> (LIBS_EXT, Sign) -> IO (LIBS_EXT, Sign)
addIncl ns e (libs@(_, (lname, _)), sig) = do
  let from = getFromAttr e
  (b, m) <- parseRef ns from lname
  libs1 <- addFromFile ns b libs
  let srcSig = lookupSig (b, m) libs1
  let tarSig = addInclSyms srcSig sig
  let morph = getInclMorph srcSig tarSig
  let libs2 = addMorphToGraph morph libs1
  return (libs2, tarSig)

-- adds included definitions to the signature
addInclSyms :: Sign -> Sign -> Sign
addInclSyms (Sign _ _ ds) sig =
  let syms = getSymbols sig
      in foldl (\ sig1 d ->
                  if Set.member (getSym d) syms
                     then sig1
                     else addDef d sig1
               ) sig ds

-- constructs the inclusion morphism
getInclMorph :: Sign -> Sign -> Morphism
getInclMorph sig1 sig2 =
  Morphism (sigBase sig2) (sigModule sig2) "" sig1 sig2 Definitional Map.empty

{- ----------------------------------------------------------------------------
----------------------------------------------------------------------------
CONSTRUCTING STRUCTURES -}

{- adds declarations arising from a structure to the signature
   adds the structure to the morphism map -}
addStruct :: Namespace -> Element -> (LIBS_EXT, Sign) -> IO (LIBS_EXT, Sign)
addStruct ns e (libs@(_, (lname, _)), sig) = do
  let name = getNameAttr e
  let from = getFromAttr e
  (b, m) <- parseRef ns from lname
  libs1 <- addFromFile ns b libs
  let srcSig = lookupSig (b, m) libs1
  (tarSig, morph, libs2) <- processStruct ns name srcSig sig (elChildren e) libs1
  let libs3 = addMorphToGraph morph libs2
  return (libs3, tarSig)

{- adds the definitions imported by a structure to the signature and
   constructs the structure morphism -}
processStruct :: Namespace -> String -> Sign -> Sign -> [Element] -> LIBS_EXT ->
                 IO (Sign, Morphism, LIBS_EXT)
processStruct ns name srcSig tarSig els libs = do
  let b1 = sigBase srcSig
  let m1 = sigModule srcSig
  let b2 = sigBase tarSig
  let m2 = sigModule tarSig
  let prefix = name ++ structDelimS
  let rel sym = Symbol b2 m2 $ prefix ++ symName sym
  (symmap, libs1) <- constructMap ns els (b1, m1) (b2, m2) libs
  let Sign _ _ ds = srcSig
  let morph_init =
        Morphism b2 m2 name (Sign b1 m1 []) tarSig Definitional Map.empty
  let (sig2, morph2) =
        foldl (\ (sig, morph) (Def s t v) ->
                 let local = isLocalSym s srcSig
                     defined = isDefinedSym s srcSig
                     sig1 = if not local then sig else
                       let s1 = rel s
                           t1 = fromMaybe (error $
                                 "Structure could not be formed. " ++ name) $
                                 translate morph t
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
              ) (tarSig, morph_init) ds
  return (sig2, morph2, libs1)

  -- constructs the translation part of the structure
constructMap :: Namespace -> [Element] -> NODE -> NODE -> LIBS_EXT ->
                IO (Map.Map Symbol EXP, LIBS_EXT)
constructMap ns els src tar libs =
  foldM (\ ml el ->
           let n = elName el
               in if n == conassQN then conass2map ns el ml src tar else
                  if n == includeQN then incl2map ns el ml src tar else
                  if n == strassQN then strass2map ns el ml src tar else
                  return ml
        ) (Map.empty, libs) els

-- converts the constant assignment into a map
conass2map :: Namespace -> Element -> (Map.Map Symbol EXP, LIBS_EXT) ->
              NODE -> NODE -> IO (Map.Map Symbol EXP, LIBS_EXT)
conass2map ns e (mapp, libs) src tar = do
  (b, m, n) <- getBMN ns e src
  case findChildren omobjQN e of
       [omobj] -> do expr <- omobj2exp ns omobj tar
                     let map1 = Map.insert (Symbol b m n) expr mapp
                     return (map1, libs)
       _ -> Fail.fail "Constant assignment element must have a unique OMOBJ child."

-- converts the included morphism into a map
incl2map :: Namespace -> Element -> (Map.Map Symbol EXP, LIBS_EXT) ->
            NODE -> NODE -> IO (Map.Map Symbol EXP, LIBS_EXT)
incl2map ns e (mapp, libs) _ tar =
  case findChildren ommorQN e of
       [ommor] -> do (mor, libs1) <- ommor2mor ns ommor tar libs
                     let map1 = Map.union mapp $ symMap mor
                     return (map1, libs1)
       _ -> Fail.fail "Include element must have a unique OMMOR child."

-- converts the structure assignment into a map
strass2map :: Namespace -> Element -> (Map.Map Symbol EXP, LIBS_EXT) ->
              NODE -> NODE -> IO (Map.Map Symbol EXP, LIBS_EXT)
strass2map ns e (mapp, libs) src tar = do
  (b, m, n) <- getBMN ns e src
  case findChildren ommorQN e of
       [ommor] -> do (mor1, libs1) <- retrieveMorph ns (b, m, n) libs
                     (mor2, libs2) <- ommor2mor ns ommor tar libs1
                     let map1 = Map.union mapp $ combineMorphs mor1 mor2
                     return (map1, libs2)
       _ -> Fail.fail "Structure assignment element must have a unique OMMOR child."

-- converts an OMMOR element to a morphism
ommor2mor :: Namespace -> Element -> NODE -> LIBS_EXT -> IO (Morphism, LIBS_EXT)
ommor2mor ns e ref libs =
  case elChildren e of
       [el] -> omel2mor ns el ref libs
       _ -> Fail.fail "OMMOR element must have a unique child."

-- converts an Open Math element to a morphism
omel2mor :: Namespace -> Element -> NODE -> LIBS_EXT -> IO (Morphism, LIBS_EXT)
omel2mor ns e ref libs =
  let name = elName e
      in if name == omsQN then oms2mor ns e ref libs else
         if name == omaQN then oma2mor ns e ref libs else
         Fail.fail "Only OMA and OMS elements correspond to a morphism."

-- converts an OMS element to a morphism
oms2mor :: Namespace -> Element -> NODE -> LIBS_EXT -> IO (Morphism, LIBS_EXT)
oms2mor ns e ref libs = do
  (b, m, n) <- getBMN ns e ref
  retrieveMorph ns (b, m, n) libs

-- converts an OMA element to a morphism
oma2mor :: Namespace -> Element -> NODE -> LIBS_EXT -> IO (Morphism, LIBS_EXT)
oma2mor ns e ref libs =
  case elChildren e of
       [c, m1, m2] ->
         if eqOMS c compOMS
            then do (mor1, libs1) <- omel2mor ns m1 ref libs
                    (mor2, libs2) <- omel2mor ns m2 ref libs1
                    let morR = compMorph (mor1 { target = source mor2 }) mor2
                    let mor = case morR of
                                   Result _ (Just mor') -> mor'
                                   _ -> error "Morphism cannot be retrieved."
                    return (mor, libs2)
            else Fail.fail "The first child of OMA in OMMOR must be composition."
       _ -> Fail.fail "OMA in OMMOR must have exactly three children."

-- retrieves a morphism by the link name
retrieveMorph :: Namespace -> LINK -> LIBS_EXT -> IO (Morphism, LIBS_EXT)
retrieveMorph ns (b, m, n) = retrieveMorphH ns b m (splitBy '/' n)

retrieveMorphH :: Namespace -> BASE -> MODULE -> [NAME] -> LIBS_EXT ->
                  IO (Morphism, LIBS_EXT)
retrieveMorphH ns b m names libs = do
  libs1 <- addFromFile ns b libs
  case names of
    [] -> Fail.fail "Empty morphism name."
    [n] -> do
        let mor = lookupMorph (b, m, n) libs1
        return (mor, libs1)
    (n1 : n2) -> do
        let mor1 = lookupMorph (b, m, n1) libs1
        let sig = source mor1
        let b1 = sigBase sig
        let m1 = sigModule sig
        (mor2, libs2) <- retrieveMorphH ns b1 m1 n2 libs1
        let morR = compMorph (mor2 { target = sig }) mor1
        let mor = case morR of
                       Result _ (Just mor') -> mor'
                       _ -> error "Morphism cannot be retrieved."
        return (mor, libs2)

-- combines two morphisms according to the structure assignment
combineMorphs :: Morphism -> Morphism -> Map.Map Symbol EXP
combineMorphs mor1 mor2 =
  let local = getLocalSyms $ source mor1
      declared = getDeclaredSyms $ source mor1
      er = error "Morphisms cannot be combined."
      in Set.fold ( \ s ->
                      let s1 = case mapSymbol s mor1 of
                                    Just (Const s1') -> s1'
                                    _ -> er
                          e1 = case mapSymbol s mor2 of
                                    Just e1' -> e1'
                                    _ -> er
                          in Map.insert s1 e1
                  ) Map.empty $ Set.intersection local declared
