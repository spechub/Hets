{-# OPTIONS -cpp #-}
{- |
Module      :  $Header$
Description :  Writing various formats, according to Hets options
Copyright   :  (c) Klaus Lüttich, C.Maeder, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(DevGraph)

Writing various formats, according to Hets options
-}

module Driver.WriteFn where

import Text.ParserCombinators.Parsec
import Text.PrettyPrint.HughesPJ (render)
import Data.List (partition, (\\))

import Common.AS_Annotation
import Common.Utils
import Common.Id
import Common.Doc
import Common.DocUtils
import Common.ExtSign
import Common.PrintLaTeX
import Common.Result
import Common.GlobalAnnotations (GlobalAnnos)
import Common.ConvertGlobalAnnos ()
import qualified Data.Map as Map
import Common.SimpPretty (writeFileSDoc)

import Common.ATerm.Lib
import Common.ATerm.ReadWrite

import Logic.Coerce
import Logic.Grothendieck
import Comorphisms.LogicGraph

import Syntax.AS_Library (getLIB_ID, LIB_DEFN(), LIB_NAME())
import Syntax.Print_AS_Library ()

import CASL.Logic_CASL

#if HAXML_PACKAGE
import CASL.CompositionTable.ToXml
#endif
import CASL.CompositionTable.ComputeTable
import CASL.CompositionTable.ModelChecker
import CASL.CompositionTable.ParseSparQ

#ifdef PROGRAMATICA
import Haskell.CreateModules
#endif
import Isabelle.CreateTheories
import Isabelle.IsaParse
import Isabelle.IsaPrint (printIsaTheory)
import SoftFOL.CreateDFGDoc
import SoftFOL.DFGParser

import Logic.Prover
import Static.GTheory
import Static.DevGraph
import Static.CheckGlobalContext
import Static.DotGraph
import Static.DGToSpec
import qualified Static.PrintDevGraph as DG
import Proofs.StatusUtils

import ATC.DevGraph()
import ATC.GlobalAnnotations()

import Driver.Options

import OMDoc.OMDocOutput

-- | compute the prefix for files to be written out
getFilePrefix :: HetcatsOpts -> FilePath -> (FilePath, FilePath)
getFilePrefix opt file =
    let odir' = outdir opt
        (base, path, _) = fileparse (envSuffix : downloadExtensions) file
        odir = if null odir' then path else odir'
    in (odir, pathAndBase odir base)

{- |
  Write the given LIB_DEFN in every format that HetcatsOpts includes.
  Filenames are determined by the output formats.
-}
write_LIB_DEFN :: GlobalAnnos -> FilePath -> HetcatsOpts -> LIB_DEFN -> IO ()
write_LIB_DEFN ga file opt ld = do
    let (odir, filePrefix) = getFilePrefix opt file
        filename ty = filePrefix ++ "." ++ show ty
        verbMesg ty = putIfVerbose opt 2 $ "Writing file: " ++ filename ty
        printAscii ty = do
          verbMesg ty
          write_casl_asc opt ga (filename ty) ld
        showAst ty = do
          verbMesg ty
          writeFile (filename ty) $ show ld
        write_type :: OutType -> IO ()
        write_type t = case t of
            HetCASLOut OutASTree OutAscii -> showAst t
            PrettyOut PrettyAscii -> printAscii t
            PrettyOut PrettyLatex -> do
                verbMesg t
                write_casl_latex opt ga (filename t) ld
            _ -> return () -- implemented elsewhere
    putIfVerbose opt 3 ("Current OutDir: " ++ odir)
    mapM_ write_type $ outtypes opt

write_casl_asc :: HetcatsOpts -> GlobalAnnos -> FilePath -> LIB_DEFN -> IO ()
write_casl_asc _ ga oup ld = writeFile oup $
          shows (useGlobalAnnos ga $ pretty ld) "\n"

debug_latex_filename :: FilePath -> FilePath
debug_latex_filename =
    ( \ (b, p, _) -> p ++ b ++ ".debug.tex") . fileparse [".pp.tex"]

write_casl_latex :: HetcatsOpts -> GlobalAnnos -> FilePath -> LIB_DEFN -> IO ()
write_casl_latex opt ga oup ld =
    do let ldoc = toLatex ga $ pretty ld
       writeFile oup $ renderLatex Nothing ldoc
       doIfVerbose opt 5 $
           writeFile (debug_latex_filename oup) $
               debugRenderLatex Nothing ldoc

toShATermString :: (ShATermConvertible a) => a -> IO String
toShATermString atcon = fmap writeSharedATerm $ versionedATermTable atcon

writeShATermFile :: (ShATermConvertible a) => FilePath -> a -> IO ()
writeShATermFile fp atcon = toShATermString atcon >>= writeFile fp

versionedATermTable :: (ShATermConvertible a) => a -> IO ATermTable
versionedATermTable atcon = do
    att0 <- newATermTable
    (att1, versionnr) <- toShATermAux att0 hetsVersion
    (att2, aterm) <- toShATermAux att1 atcon
    return $ fst $ addATerm (ShAAppl "hets" [versionnr,aterm] []) att2

writeShATermFileSDoc :: (ShATermConvertible a) => FilePath -> a -> IO ()
writeShATermFileSDoc fp atcon = do
   att <- versionedATermTable atcon
   writeFileSDoc fp $ writeSharedATermSDoc att

writeFileInfo :: HetcatsOpts -> LIB_NAME -> FilePath -> LIB_DEFN
              -> DGraph -> IO ()
writeFileInfo opts ln file ld gctx =
  let envFile = snd (getFilePrefix opts file) ++ envSuffix in
  case analysis opts of
  Basic -> do
      putIfVerbose opts 2 ("Writing file: " ++ envFile)
      catch (writeShATermFileSDoc envFile (ln, (ld, gctx))) $ \ err -> do
              putIfVerbose opts 2 (envFile ++ " not written")
              putIfVerbose opts 3 ("see following error description:\n"
                                   ++ shows err "\n")
  _ -> putIfVerbose opts 2 ("Not writing " ++ envFile)

writeVerbFile :: HetcatsOpts -> FilePath -> String -> IO ()
writeVerbFile opt f str = do
    putIfVerbose opt 2 $ "Writing file: " ++ f
    writeFile f str

writeLibEnv :: HetcatsOpts -> FilePath -> LibEnv -> LIB_NAME -> OutType
            -> IO ()
writeLibEnv opt filePrefix lenv ln ot =
    let f = filePrefix ++ "." ++ show ot in case ot of
      Prf -> toShATermString (ln, lookupHistory ln lenv)
             >>= writeVerbFile opt f
      OmdocOut -> hetsToOMDoc opt (ln, lenv) f
      GraphOut (Dot showInternalNodeLabels) -> writeVerbFile opt f
        . dotGraph showInternalNodeLabels $ lookupDGraph ln lenv
      _ -> putIfVerbose opt 5 $ printStatistics $ lookupDGraph ln lenv
        -- only works if outtypes are not empty

writeSoftFOL :: HetcatsOpts -> FilePath -> G_theory -> LIB_NAME -> SIMPLE_ID
             -> SPFType -> Int -> String -> IO ()
writeSoftFOL opt f gTh ln i c n msg = do
      mDoc <- printTheoryAsSoftFOL ln i n (case c of
          ConsistencyCheck -> True
          OnlyAxioms  -> False) $ theoremsToAxioms gTh
      maybe (putIfVerbose opt 0 $
             "could not translate to " ++ msg ++ " file: " ++ f)
          ( \ d -> do
              let str = shows d "\n"
              if n == 0 then case parse parseSPASS f str of
                Left err -> putIfVerbose opt 0 $ show err
                _ -> putIfVerbose opt 3 $ "reparsed: " ++ f
                else return ()
              writeVerbFile opt f str) mDoc

writeIsaFile :: HetcatsOpts -> FilePath -> G_theory -> LIB_NAME -> SIMPLE_ID
             -> IO ()
writeIsaFile opt fp raw_gTh ln i = case createIsaTheory raw_gTh of
    Result ds Nothing -> do
      putIfVerbose opt 0 $ "could not translate to Isabelle theory: " ++ fp
      putIfVerbose opt 2 $ unlines $ map show ds
    Result _ (Just (sign, sens)) -> do
      let tn = reverse (takeWhile (/= '/') $ reverse $ show $ getLIB_ID ln)
                   ++ "_" ++ show i
          sf = shows (printIsaTheory tn sign sens) "\n"
          f = fp ++ ".thy"
      case parse parseTheory f sf of
            Left err -> putIfVerbose opt 0 $ show err
            _ -> putIfVerbose opt 3 $ "reparsed: " ++ f
      writeVerbFile opt f sf
      if hasPrfOut opt && verbose opt >= 3 then let
              (axs, rest) = partition ( \ s -> isAxiom s || isDef s) sens
              in mapM_ ( \ s -> let
                tnf = tn ++ "_" ++ senAttr s
                tf = fp ++ "_" ++ senAttr s ++ ".thy"
                in writeVerbFile opt tf $ shows
                   (printIsaTheory tnf sign $ s : axs) "\n") rest
            else return ()

writeTheory :: HetcatsOpts -> FilePath -> GlobalAnnos -> G_theory -> LIB_NAME
            -> SIMPLE_ID -> OutType -> IO ()
writeTheory opt filePrefix ga
  raw_gTh@(G_theory lid (ExtSign sign0 _) _ sens0 _) ln i ot =
    let fp = filePrefix ++ "_" ++ show i
        f = fp ++  "." ++ show ot
    in case ot of
    ThyFile -> writeIsaFile opt fp raw_gTh ln i
    DfgFile c -> writeSoftFOL opt f raw_gTh ln i c 0 "DFG"
    TPTPFile c -> writeSoftFOL opt f raw_gTh ln i c 1 "TPTP"
    TheoryFile d -> if null $ show d then
        writeVerbFile opt f $ shows (DG.printTh ga i raw_gTh) "\n"
        else putIfVerbose opt 0 "printing theory delta is not implemented"
    SigFile d -> if null $ show d then
        writeVerbFile opt f $ shows (pretty $ signOf raw_gTh) "\n"
        else putIfVerbose opt 0 "printing signature delta is not implemented"
#ifdef PROGRAMATICA
    HaskellOut -> case printModule raw_gTh of
        Nothing ->
            putIfVerbose opt 0 $ "could not translate to Haskell file: " ++ f
        Just d -> writeVerbFile opt f $ shows d "\n"
#endif
#if HAXML_PACKAGE
    ComptableXml -> let
        th = (sign0, toNamedList sens0)
        r1 = coerceBasicTheory lid CASL "" th in case r1 of
        Nothing ->
            putIfVerbose opt 0 $ "could not translate CASL to file: " ++ f
        Just th2 -> do
          let Result d res = computeCompTable i th2
          showDiags opt d
          case res of
            Just td -> writeVerbFile opt f $ render $ table_document td
            Nothing -> return ()
#endif
    _ -> return () -- ignore other file types

modelSparQCheck :: HetcatsOpts -> G_theory -> SIMPLE_ID -> IO ()
modelSparQCheck opt gTh@(G_theory lid (ExtSign sign0 _) _ sens0 _) i =
    case coerceBasicTheory lid CASL "" (sign0, toNamedList sens0) of
    Just th2 -> do
      table <- parseSparQTableFromFile $ modelSparQ opt
      case table of
        Left _ -> putIfVerbose opt 0 $ "could not parse SparQTable from file: "
            ++ modelSparQ opt
        Right y -> let Result d _ = modelCheck i th2 y in
            if length d > 0 then  showDiags opt {verbose = 2 } $ take 10 d
            else putIfVerbose opt 0 "Modelcheck suceeded, no errors found"
    _ ->
      putIfVerbose opt 0 $ "could not translate Theory to CASL:\n "
         ++ showDoc gTh ""

writeTheoryFiles :: HetcatsOpts -> [OutType] -> FilePath -> LibEnv -> GlobalAnnos
                 -> LIB_NAME -> SIMPLE_ID -> Int -> IO ()
writeTheoryFiles opt specOutTypes filePrefix lenv ga ln i n =
    if isDGRef $ labDG (lookupDGraph ln lenv) n then return () else
    case computeTheory lenv ln n of
          Result ds Nothing -> do
                 putIfVerbose opt 0 $ "could not compute theory of spec "
                                  ++ show i
                 putIfVerbose opt 2 $ unlines $ map show ds
          Result _ (Just raw_gTh0) -> do
            let tr = transNames opt
                resTh = if null tr then return (raw_gTh0, "") else do
                   comor <- lookupCompComorphism (map tokStr tr) logicGraph
                   tTh <- mapG_theory comor raw_gTh0
                   return (tTh, show comor)
            case resTh of
             Result es Nothing -> do
               putIfVerbose opt 0 "could not translate theory"
               putIfVerbose opt 0 $ unlines $ map show es
             Result _ (Just (raw_gTh, tStr)) -> do
               if null tStr then return () else
                   putIfVerbose opt 2 $ "Translated using comorphism " ++ tStr
               putIfVerbose opt 4 $ "Sublogic of " ++ show i ++ ": " ++
                   show (sublogicOfTh raw_gTh)
               if modelSparQ opt == "" then return () else
                   modelSparQCheck opt (theoremsToAxioms raw_gTh) i
               mapM_ (writeTheory opt filePrefix ga raw_gTh ln i) specOutTypes

writeSpecFiles :: HetcatsOpts -> FilePath -> LibEnv -> GlobalAnnos
               -> LIB_NAME -> DGraph -> IO ()
writeSpecFiles opt file lenv ga ln dg = do
    let gctx = globalEnv dg
        ns = specNames opt
        filePrefix = snd $ getFilePrefix opt file
        outTypes = outtypes opt
        specOutTypes = filter ( \ ot -> case ot of
            ThyFile -> True
            DfgFile _  -> True
            TPTPFile _ -> True
            TheoryFile _ -> True
            SigFile _ -> True
            HaskellOut -> True
            ComptableXml -> True
            _ -> False) outTypes
        allSpecs = null ns
        ignore = null specOutTypes && modelSparQ opt == ""
    mapM_ (writeLibEnv opt filePrefix lenv ln) outTypes
    mapM_ ( \ i -> case Map.lookup i gctx of
        Just (SpecEntry (ExtGenSig _ _ _ (NodeSig n _))) ->
            writeTheoryFiles opt specOutTypes filePrefix lenv ga ln i n
        _ -> if allSpecs then return () else
                 putIfVerbose opt 0 $ "Unknown spec name: " ++ show i
      ) $ if ignore then [] else
        if allSpecs then Map.keys gctx else ns
    mapM_ ( \ n ->
      writeTheoryFiles opt specOutTypes filePrefix lenv ga ln
         (genToken $ 'n' : show n) n)
      $ if ignore || not allSpecs then [] else
      nodesDG dg
      \\ Map.fold ( \ e l -> case e of
            SpecEntry (ExtGenSig _ _ _ (NodeSig n _)) -> n : l
            _ -> l) [] gctx
