{- |
Module      :  $Header$
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

import Network.URI

import LF.Sign
import LF.Morphism

import qualified Data.Map as Map
import qualified Data.Set as Set

import Common.Result
import Common.Utils
import Common.Keywords

import Control.Monad

import Text.XML.Light.Input
import Text.XML.Light.Types
import Text.XML.Light.Proc

type NODE = (BASE,MODULE)
type LINK = (BASE,MODULE,NAME)

type SIGS = Map.Map MODULE Sign
type MORPHS = Map.Map ((MODULE,NAME),NODE,NODE) Morphism

type GRAPH = (SIGS,MORPHS)
type LIBS = Map.Map BASE GRAPH
type LIBS_EXT = ((LIBS,[BASE]),(BASE,GRAPH))

emptyGraph :: GRAPH
emptyGraph = (Map.empty,Map.empty)

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

getNameAttr :: Element -> String
getNameAttr e =
  case findAttr nameQN e of
       Nothing -> error $ "Element is missing a name." ++ (show e)
       Just n -> n

getModuleAttr :: Element -> Maybe String
getModuleAttr e = findAttr moduleQN e

getBaseAttr :: Element -> Maybe String
getBaseAttr e = findAttr baseQN e

-- compares two OMS elements
eqOMS :: Element -> Element -> Bool
eqOMS e1 e2 =
  if (elName e1 /= omsQN || elName e2 /= omsQN) then False else
     and [ getNameAttr e1 == getNameAttr e2
         , getModuleAttr e1 == getModuleAttr e2
         , getBaseAttr e1 == getBaseAttr e2]

toOMDoc :: FilePath -> FilePath
toOMDoc fp = replaceExtension fp omdocE

fromOMDoc :: FilePath -> FilePath
fromOMDoc fp = replaceExtension fp twelfE

-- resolves the first file path wrt to the second
resolve :: FilePath -> FilePath -> FilePath
resolve fp1 fp2 =
  case parseURIReference fp1 of
    Nothing -> er
    Just uri1 -> do
      case parseURIReference fp2 of
        Nothing -> er
        Just uri2 -> do
          case relativeTo uri1 uri2 of
               Nothing -> er
               Just f -> show f
  where er = error "Invalid file name."

-- relativizes the first file path wrt to the second
relativize :: FilePath -> FilePath -> FilePath
relativize fp1 fp2 =
  case parseURIReference fp1 of
    Nothing -> er
    Just uri1 -> do
      case parseURIReference fp2 of
        Nothing -> er
        Just uri2 -> show $ relativeFrom uri1 uri2
  where er = error "Invalid file name."

-- resolves the file path wrt to the current directory
resolveToCur :: FilePath -> IO FilePath
resolveToCur fp = do
  dir <- getCurrentDirectory
  return $ resolve fp $ dir ++ "/"

-- relativizes the file path wrt to the current directory
relativizeToCur :: FilePath -> IO FilePath
relativizeToCur fp = do
  dir <- getCurrentDirectory
  let dir' = dir ++ "/"
  return $ relativize (resolve fp dir') dir'

{- returns the referenced base and module resolved w.r.t.
   the second argument and relativized to the current directory -}
parseRef :: String -> String -> IO NODE
parseRef ref base = do
  baseA <- resolveToCur base  
  case splitBy '?' ref of
       [br1,m] -> do let b = fromOMDoc $ resolve br1 baseA
                     br2 <- relativizeToCur b
                     return (br2,m)
       _ -> fail "Invalid reference."

{- retrieves the base, module, and name attributes resolved w.r.t.
   the second argument and relativized to the current directory -}
getBMN :: Element -> NODE -> IO (BASE,MODULE,NAME)
getBMN e (base,modul) = do
  baseA <- resolveToCur base
  let n = case findAttr nameQN e of
               Nothing -> ""
               Just n' -> n'
  let m = case getModuleAttr e of
               Nothing -> modul
               Just m' -> m'
  let b = case getBaseAttr e of
               Nothing -> base
               Just b' -> fromOMDoc $ resolve b' baseA
  br <- relativizeToCur b
  return (br,m,n)

{- parses the referenced file if needed and imports all signatures
   and morphisms from it -}
addFromFile :: FilePath -> LIBS_EXT -> IO LIBS_EXT
addFromFile fp libs@(lb@(l,_),(b,gr)) = do
  if (fp == b || Map.member fp l)
     then return libs
     else do lb' <- twelf2GR fp lb
             return (lb',(b,gr))

-- finds the signature by base and module
lookupSig :: NODE -> LIBS_EXT -> Sign
lookupSig (b,m) ((libs,_),(base,(sigs,_))) =
  let sigs1 = if b == base then sigs else
                 fst $ Map.findWithDefault er b libs
      in Map.findWithDefault er m sigs1
  where er = error "Signature cannot be found."

-- finds the morphism by base, module, and name
lookupMorph :: LINK -> LIBS_EXT -> Morphism
lookupMorph (b,m,n) ((libs,_),(base,(_,morphs))) =
  let morphs1 = if b == base then morphs else
                   snd $ Map.findWithDefault er b libs
      morphs2 = Map.filterWithKey (\ (l,_,_) _ -> l == (m,n)) morphs1
      in case Map.toList morphs2 of
              [(_,morph)] -> morph
              _ -> er
  where er = error "Morphism cannot be found."

-- adds the signature to the signature collection
addSigToGraph :: Sign -> LIBS_EXT -> LIBS_EXT
addSigToGraph sig (lb,(b,(sigs,morphs))) =
  let sigs1 = Map.insert (sigModule sig) sig sigs
      in (lb,(b,(sigs1,morphs)))

-- adds the morphism to the morphism collection
addMorphToGraph :: Morphism -> LIBS_EXT -> LIBS_EXT
addMorphToGraph m (lb,(b,(sigs,morphs))) =
  let sig1 = source m
      sig2 = target m
      l = (morphModule m, morphName m)
      s = (sigBase sig1, sigModule sig1)
      t = (sigBase sig2, sigModule sig2)
      morphs1 = Map.insert (l,s,t) m morphs
      in (lb,(b,(sigs,morphs1)))

-- computes the correct targets of morphisms
computeTargets :: GRAPH -> LIBS_EXT -> GRAPH
computeTargets (sigs,morphs) libs =
   let morphs2 = Map.foldWithKey
          (\ k@((_,_),_,t) morph morphs1 ->
             let morph1 = morph { target = lookupSig t libs }
                 in Map.insert k morph1 morphs1
          ) Map.empty morphs
       in (sigs,morphs2)

------------------------------------------------------------------------------
------------------------------------------------------------------------------
-- CONSTRUCTING THE LIBRARY OF LF SIGNATURES AND MORPHISMS

-- analyzes the given Twelf file and returns LF signatures and morphisms
twelf2SigMor :: FilePath -> IO LIBS
twelf2SigMor fp = do
  (libs,_) <- twelf2GR fp (Map.empty,[])
  return libs

{- updates the graph libraries by adding specs from the Twelf file;
   the list of library names stores the order in which they were added,
   which is needed later for the construction of DGraphs -}
twelf2GR :: FilePath -> (LIBS,[BASE]) -> IO (LIBS,[BASE])
twelf2GR fp lb = do
  runTwelf fp
  file <- relativizeToCur fp
  le@((libs,bs),(b,gr)) <- buildGraph file lb
  let gr' = computeTargets gr le
  let libs' = Map.insert b gr' libs
  let bs' = bs ++ [b]
  return (libs',bs')

-- runs twelf to create an omdoc file
runTwelf :: FilePath -> IO ()
runTwelf fp = do
  file <- resolveToCur fp
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

------------------------------------------------------------------------------
------------------------------------------------------------------------------
-- CONSTRUCTING SIGNATURES AND MORPHISMS

-- builds the LF signature and morphism graph
buildGraph :: FilePath -> (LIBS,[BASE]) -> IO LIBS_EXT
buildGraph file lb = do
  xml <- readFile $ toOMDoc file
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
               (lb,(file,emptyGraph))
               $ elChildren root
       _ -> fail "Not an OMDoc file."

-- transforms a theory element into a signature and adds it to the graph
addSign :: Element -> LIBS_EXT -> IO LIBS_EXT
addSign e libs@(_,(file,_)) = do
  let sig = Sign file (getNameAttr e) []
  (libs1,sig1) <-
     foldM (\ ls el ->
              let n = elName el
                  in if (n == includeQN) then addIncl el ls else
                     if (n == structureQN) then addStruct el ls else
                     if (n == constantQN) then addConst el ls else
                     return ls
           )
           (libs,sig)
           $ elChildren e
  return $ addSigToGraph sig1 libs1

-- transforms a view element into a view and adds it to the graph
addView :: Element -> LIBS_EXT -> IO LIBS_EXT
addView e libs@(_,(file,_)) = do
  let name = getNameAttr e
  let from = getFromAttr e
  let to = getToAttr e
  (b1,m1) <- parseRef from file
  (b2,m2) <- parseRef to file
  libs1 <- addFromFile b1 libs
  libs2 <- addFromFile b2 libs1  
  let srcSig = lookupSig (b1,m1) libs2
  let tarSig = lookupSig (b2,m2) libs2
  (morph,libs3) <- getViewMorph name srcSig tarSig (elChildren e) libs2
  let libs4 = addMorphToGraph morph libs3
  return libs4

{- constructs the view morphism -}
getViewMorph :: String -> Sign -> Sign -> [Element] -> LIBS_EXT ->
                IO (Morphism,LIBS_EXT)
getViewMorph name srcSig tarSig els libs@(_,(file,_)) = do
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
addConst :: Element -> (LIBS_EXT,Sign) -> IO (LIBS_EXT,Sign)
addConst e (libs,sig) = do
  let ref@(b,m) = (sigBase sig, sigModule sig)
  let sym = Symbol b m $ getNameAttr e
  typ <- case findChildren typeQN e of
              [t] -> type2exp t ref
              _ -> fail "Constant element must have a unique type child."
  val <- case findChildren definitionQN e of
              [] -> return Nothing
              [v] -> fmap Just $ definition2exp v ref                   
              _ -> fail $ "Constant element must have at most " ++
                          "one definition child."
  let sig1 = addDef (Def sym typ val) sig
  return (libs,sig1)

{- converts a type element to an expression
   second argument is used for resolving symbol references -}
type2exp :: Element -> NODE -> IO EXP
type2exp e ref =
  case findChildren omobjQN e of
       [omobj] -> omobj2exp omobj ref
       _ -> fail "Type element must have a unique OMOBJ child."

{- converts a definition element to an expression
   second argument is used for resolving symbol references -}
definition2exp :: Element -> NODE -> IO EXP
definition2exp e ref =
  case findChildren omobjQN e of
       [omobj] -> omobj2exp omobj ref
       _ -> fail "Definition element must have a unique OMOBJ child."

-- converts an OMOBJ element to an expression
omobj2exp :: Element -> NODE -> IO EXP
omobj2exp e ref =
  case elChildren e of
       [el] -> omel2exp el ref
       _ -> fail "OMOBJ element must have a unique child."

-- converts an Open Math element to an expression
omel2exp :: Element -> NODE -> IO EXP
omel2exp e ref =
  let name = elName e
      in if (name == omsQN) then oms2exp e ref else
         if (name == omaQN) then oma2exp e ref else
         if (name == ombindQN) then ombind2exp e ref else
         if (name == omvQN) then omv2exp e ref else
         fail $ "Only OMA, OMS, and OMBIND elements correspond " ++
                "to an expression."

-- converts an OMS element to an expression
oms2exp :: Element -> NODE -> IO EXP
oms2exp e ref =
  if (eqOMS e typeOMS) then return Type else do
  (b,m,n) <- getBMN e ref
  return $ Const $ Symbol b m n

-- converts an OMA element to an expression
oma2exp :: Element -> NODE -> IO EXP
oma2exp e ref =
  case elChildren e of
    [] -> fail "OMA element must have at least one child."
    (f:as) -> do
      as1 <- mapM (\ a -> omel2exp a ref) as
      if (eqOMS f arrowOMS)
         then case as1 of
                   [] -> fail $ "The -> constructor must be applied" ++
                                " to at least one argument."
                   _ -> return $ Func (init as1) (last as1)
         else do f1 <- omel2exp f ref
                 return $ Appl f1 as1             

-- converts an OMBIND element to an expression
ombind2exp :: Element -> NODE -> IO EXP
ombind2exp e ref =
  case elChildren e of
    [f,d,b] ->
      if (elName d /= ombvarQN)
         then fail "The second child of OMBIND must be OMBVAR."
         else do d1 <- ombvar2decls d ref
                 b1 <- omel2exp b ref
                 if (eqOMS f lambdaOMS) then return $ Lamb d1 b1 else do
                 if (eqOMS f piOMS) then return $ Pi d1 b1 else do
                 {- so far implicit binders are treated
                    as explicit -}
                 if (eqOMS f impLambdaOMS) then return $ Lamb d1 b1 else do
                 if (eqOMS f impPiOMS) then return $ Pi d1 b1 else do
                 fail $ "The first child of OMBIND must be be Pi or Lambda."
    _ -> fail "OMBIND element must have exactly 3 children."

-- converts an OMBVAR element to a list of declaration
ombvar2decls :: Element -> NODE -> IO CONTEXT
ombvar2decls e ref =
  mapM (\ a -> omattr2vardecl a ref) $ findChildren omattrQN e

-- converts an OMATTR element to a variable declaration
omattr2vardecl :: Element -> NODE -> IO (VAR,EXP)
omattr2vardecl e ref =
  case findChildren omatpQN e of
       [omatp] -> do
         val <- omatp2exp omatp ref
         case findChildren omvQN e of
              [omv] -> return (getNameAttr omv, val)
              _ -> fail "OMATTR element must have a unique OMV child."
       _ -> fail "OMATTR element must have a unique OMATP child."

-- converts an OMATP element to an expression
omatp2exp :: Element -> NODE -> IO EXP
omatp2exp e ref =
  case elChildren e of
       [c1,c2] ->
          if (eqOMS c1 oftypeOMS)
             then omel2exp c2 ref
             else fail $ "The first child of OMATP " ++
                         "must be the \"oftype\" symbol."
       _ -> fail "OMATP element must have exactly two children."

-- converts an OMV element to an expression
omv2exp :: Element -> NODE -> IO EXP
omv2exp e _ = return $ Var $ getNameAttr e

------------------------------------------------------------------------------
------------------------------------------------------------------------------
-- CONSTRUCTING INCLUSIONS

{- adds declarations arising from an inclusion to the signature
   adds the inclusion to the morphism map -}
addIncl :: Element -> (LIBS_EXT,Sign) -> IO (LIBS_EXT,Sign)
addIncl e (libs@(_,(file,_)),sig) = do
  let from = getFromAttr e
  (b,m) <- parseRef from file
  libs1 <- addFromFile b libs  
  let srcSig = lookupSig (b,m) libs1
  let tarSig = addInclSyms srcSig sig
  let morph = getInclMorph srcSig tarSig
  let libs2 = addMorphToGraph morph libs1
  return (libs2,tarSig)

-- adds included definitions to the signature
addInclSyms :: Sign -> Sign -> Sign
addInclSyms (Sign _ _ ds) sig =
  let syms = getSymbols sig
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
addStruct :: Element -> (LIBS_EXT,Sign) -> IO (LIBS_EXT,Sign)
addStruct e (libs@(_,(file,_)),sig) = do
  let name = getNameAttr e
  let from = getFromAttr e
  (b,m) <- parseRef from file
  libs1 <- addFromFile b libs  
  let srcSig = lookupSig (b,m) libs1
  (tarSig,morph,libs2) <- processStruct name srcSig sig (elChildren e) libs1
  let libs3 = addMorphToGraph morph libs2
  return (libs3,tarSig)

{- adds the definitions imported by a structure to the signature and
   constructs the structure morphism -}
processStruct :: String -> Sign -> Sign -> [Element] -> LIBS_EXT ->
                 IO (Sign,Morphism,LIBS_EXT)
processStruct name srcSig tarSig els libs = do
  let b1 = sigBase srcSig
  let m1 = sigModule srcSig
  let b2 = sigBase tarSig
  let m2 = sigModule tarSig
  let prefix = name ++ structDelimS
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
constructMap :: [Element] -> NODE -> NODE -> LIBS_EXT ->
                IO (Map.Map Symbol EXP, LIBS_EXT)
constructMap els src tar libs = do
  foldM (\ ml el ->
           let n = elName el
               in if (n == conassQN) then conass2map el ml src tar else
                  if (n == includeQN) then incl2map el ml src tar else
                  if (n == strassQN) then strass2map el ml src tar else
                  return ml
        ) (Map.empty,libs) els

-- converts the constant assignment into a map
conass2map :: Element -> (Map.Map Symbol EXP, LIBS_EXT) -> NODE -> NODE ->
              IO (Map.Map Symbol EXP, LIBS_EXT)
conass2map e (mapp,libs) src tar = do
  (b,m,n) <- getBMN e src
  case findChildren omobjQN e of
       [omobj] -> do expr <- omobj2exp omobj tar
                     let map1 = Map.insert (Symbol b m n) expr mapp
                     return (map1,libs)
       _ -> fail "Constant assignment element must have a unique OMOBJ child."

-- converts the included morphism into a map
incl2map :: Element -> (Map.Map Symbol EXP, LIBS_EXT) -> NODE -> NODE ->
            IO (Map.Map Symbol EXP, LIBS_EXT)
incl2map e (mapp,libs) _ tar =
  case findChildren ommorQN e of
       [ommor] -> do (mor,libs1) <- ommor2mor ommor tar libs
                     let map1 = Map.union mapp $ symMap mor
                     return (map1,libs1)
       _ -> fail "Include element must have a unique OMMOR child."

-- converts the structure assignment into a map
strass2map :: Element -> (Map.Map Symbol EXP, LIBS_EXT) -> NODE -> NODE ->
              IO (Map.Map Symbol EXP, LIBS_EXT)
strass2map e (mapp,libs) src tar = do
  (b,m,n) <- getBMN e src
  case findChildren ommorQN e of
       [ommor] -> do (mor1,libs1) <- retrieveMorph (b,m,n) libs
                     (mor2,libs2) <- ommor2mor ommor tar libs1
                     let map1 = Map.union mapp $ combineMorphs mor1 mor2
                     return (map1,libs2)
       _ -> fail "Structure assignment element must have a unique OMMOR child."

-- converts an OMMOR element to a morphism
ommor2mor :: Element -> NODE -> LIBS_EXT -> IO (Morphism,LIBS_EXT)
ommor2mor e ref libs =
  case elChildren e of
       [el] -> omel2mor el ref libs
       _ -> fail "OMMOR element must have a unique child."

-- converts an Open Math element to a morphism
omel2mor :: Element -> NODE -> LIBS_EXT -> IO (Morphism,LIBS_EXT)
omel2mor e ref libs =
  let name = elName e
      in if (name == omsQN) then oms2mor e ref libs else
         if (name == omaQN) then oma2mor e ref libs else
         fail "Only OMA and OMS elements correspond to a morphism."

-- converts an OMS element to a morphism
oms2mor :: Element -> NODE -> LIBS_EXT -> IO (Morphism,LIBS_EXT)
oms2mor e ref libs = do
  (b,m,n) <- getBMN e ref
  retrieveMorph (b,m,n) libs

-- converts an OMA element to a morphism
oma2mor :: Element -> NODE -> LIBS_EXT -> IO (Morphism,LIBS_EXT)
oma2mor e ref libs = do
  case elChildren e of
       [c,m1,m2] -> do
         if (eqOMS c compOMS)
            then do (mor1,libs1) <- omel2mor m1 ref libs
                    (mor2,libs2) <- omel2mor m2 ref libs1
                    let morR = compMorph (mor1 { target = source mor2 }) mor2
                    let mor = case morR of
                                   Result _ (Just mor') -> mor'
                                   _ -> error "Morphism cannot be retrieved."
                    return (mor,libs2)
            else fail "The first child of OMA in OMMOR must be composition."
       _ -> fail "OMA in OMMOR must have exactly three children."

-- retrieves a morphism by the link name
retrieveMorph :: LINK -> LIBS_EXT -> IO (Morphism,LIBS_EXT)
retrieveMorph (b,m,n) libs = retrieveMorphH b m (splitBy '/' n) libs

retrieveMorphH :: BASE -> MODULE -> [NAME] -> LIBS_EXT ->
                  IO (Morphism,LIBS_EXT)
retrieveMorphH b m ns libs = do
  libs1 <- addFromFile b libs
  case ns of
    [] -> fail "Empty morphism name."
    [n] -> do
        let mor = lookupMorph (b,m,n) libs1
        return (mor,libs1)
    (n1:n2) -> do
        let mor1 = lookupMorph (b,m,n1) libs1
        let sig = source mor1
        let b1 = sigBase sig
        let m1 = sigModule sig
        (mor2,libs2) <- retrieveMorphH b1 m1 n2 libs1
        let morR = compMorph (mor2 { target = sig }) mor1
        let mor = case morR of
                       Result _ (Just mor') -> mor'
                       _ -> error "Morphism cannot be retrieved."
        return (mor,libs2)

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
