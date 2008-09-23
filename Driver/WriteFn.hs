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

import Control.Monad
import Text.ParserCombinators.Parsec
import Text.PrettyPrint.HughesPJ (render)
import Data.List (partition, (\\))

import Common.AS_Annotation
import Common.Id
import Common.DocUtils
import Common.ExtSign
import Common.LibName
import Common.Result
import Common.GlobalAnnotations (GlobalAnnos)
import qualified Data.Map as Map
import Common.SExpr

import Logic.Coerce
import Logic.Logic (language_name)
import Logic.Grothendieck
import Comorphisms.LogicGraph

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
import SoftFOL.ParseTPTP

import VSE.Logic_VSE
import VSE.ToSExpr

import Logic.Prover
import Static.GTheory
import Static.DevGraph
import Static.CheckGlobalContext
import Static.DotGraph
import qualified Static.PrintDevGraph as DG
import Proofs.StatusUtils
import Proofs.TheoremHideShift(theoremsToAxioms, computeTheory)

import Driver.Options
import Driver.WriteLibDefn

import OMDoc.OMDocOutput

writeVerbFile :: HetcatsOpts -> FilePath -> String -> IO ()
writeVerbFile opts f str = do
    putIfVerbose opts 2 $ "Writing file: " ++ f
    writeFile f str

writeLibEnv :: HetcatsOpts -> FilePath -> LibEnv -> LIB_NAME -> OutType
            -> IO ()
writeLibEnv opts filePrefix lenv ln ot =
    let f = filePrefix ++ "." ++ show ot
        dg = lookupDGraph ln lenv in case ot of
      Prf -> toShATermString (ln, lookupHistory ln lenv)
             >>= writeVerbFile opts f
      OmdocOut -> hetsToOMDoc opts (ln, lenv) f
      GraphOut (Dot showInternalNodeLabels) -> writeVerbFile opts f
        $ dotGraph showInternalNodeLabels dg
      _ -> do
        doDump opts "PrintStat" $ putStrLn $ printStatistics dg
        doDump opts "DGraph" $ putStrLn $ showDoc dg ""
        doDump opts "LogicGraph" $ putStrLn $ showDoc logicGraph ""
        doDump opts "LibEnv" $
               writeVerbFile opts (filePrefix ++ ".lenv") $
                    shows (DG.prettyLibEnv lenv) "\n"

writeSoftFOL :: HetcatsOpts -> FilePath -> G_theory -> LIB_NAME -> SIMPLE_ID
             -> SPFType -> Int -> String -> IO ()
writeSoftFOL opts f gTh ln i c n msg = do
      mDoc <- printTheoryAsSoftFOL ln i n (case c of
          ConsistencyCheck -> True
          OnlyAxioms  -> False) $ theoremsToAxioms gTh
      maybe (putIfVerbose opts 0 $
             "could not translate to " ++ msg ++ " file: " ++ f)
          ( \ d -> do
              let str = shows d "\n"
                  forget p = fmap (const ()) p
              case parse (if n == 0 then forget parseSPASS else forget tptp)
                   f str of
                Left err -> putIfVerbose opts 0 $ show err
                _ -> putIfVerbose opts 3 $ "reparsed: " ++ f
              writeVerbFile opts f str) mDoc

writeIsaFile :: HetcatsOpts -> FilePath -> G_theory -> LIB_NAME -> SIMPLE_ID
             -> IO ()
writeIsaFile opts fp raw_gTh ln i = case createIsaTheory raw_gTh of
    Result ds Nothing -> do
      putIfVerbose opts 0 $ "could not translate to Isabelle theory: " ++ fp
      putIfVerbose opts 2 $ unlines $ map show ds
    Result _ (Just (sign, sens)) -> do
      let tn = reverse (takeWhile (/= '/') $ reverse $ show $ getLIB_ID ln)
                   ++ "_" ++ show i
          sf = shows (printIsaTheory tn sign sens) "\n"
          f = fp ++ ".thy"
      case parse parseTheory f sf of
        Left err -> putIfVerbose opts 0 $ show err
        _ -> putIfVerbose opts 3 $ "reparsed: " ++ f
      writeVerbFile opts f sf
      when (hasPrfOut opts && verbose opts >= 3) $ let
        (axs, rest) = partition ( \ s -> isAxiom s || isDef s) sens
         in mapM_ ( \ s -> let
           tnf = tn ++ "_" ++ senAttr s
           tf = fp ++ "_" ++ senAttr s ++ ".thy"
           in writeVerbFile opts tf $ shows
                   (printIsaTheory tnf sign $ s : axs) "\n") rest

writeTheory :: HetcatsOpts -> FilePath -> GlobalAnnos -> G_theory -> LIB_NAME
            -> SIMPLE_ID -> OutType -> IO ()
writeTheory opts filePrefix ga
  raw_gTh@(G_theory lid (ExtSign sign0 _) _ sens0 _) ln i ot =
    let fp = filePrefix ++ "_" ++ show i
        f = fp ++ "." ++ show ot
        th = (sign0, toNamedList sens0)
    in case ot of
    ThyFile -> writeIsaFile opts fp raw_gTh ln i
    DfgFile c -> writeSoftFOL opts f raw_gTh ln i c 0 "DFG"
    TPTPFile c -> writeSoftFOL opts f raw_gTh ln i c 1 "TPTP"
    TheoryFile d -> do
      if null $ show d then
        writeVerbFile opts f $ shows (DG.printTh ga i raw_gTh) "\n"
        else putIfVerbose opts 0 "printing theory delta is not implemented"
      when (language_name lid == language_name VSE) $ do
        (sign, sens) <- coerceBasicTheory lid VSE "" th
        let (sign', sens') = addUniformRestr sign sens
            lse = map (namedSenToSExpr sign') sens'
        unless (null lse) $ writeVerbFile opts (fp ++ ".sexpr")
            $ shows (prettySExpr $ SList lse) "\n"
    SigFile d -> do
      if null $ show d then
        writeVerbFile opts f $ shows (pretty $ signOf raw_gTh) "\n"
        else putIfVerbose opts 0 "printing signature delta is not implemented"
      when (language_name lid == language_name VSE) $ do
        (sign, sens) <- coerceBasicTheory lid VSE "" th
        let (sign', _sens') = addUniformRestr sign sens
        writeVerbFile opts (f ++ ".sexpr")
          $ shows (prettySExpr $ vseSignToSExpr sign') "\n"
#ifdef PROGRAMATICA
    HaskellOut -> case printModule raw_gTh of
        Nothing ->
            putIfVerbose opts 0 $ "could not translate to Haskell file: " ++ f
        Just d -> writeVerbFile opts f $ shows d "\n"
#endif
#if HAXML_PACKAGE
    ComptableXml -> if language_name lid == language_name CASL then do
          th2 <- coerceBasicTheory lid CASL "" th
          let Result ds res = computeCompTable i th2
          showDiags opts ds
          case res of
            Just td -> writeVerbFile opts f $ render $ table_document td
            Nothing -> return ()
        else putIfVerbose opts 0 $ "expected CASL theory for: " ++ f
#endif
    _ -> return () -- ignore other file types

modelSparQCheck :: HetcatsOpts -> G_theory -> SIMPLE_ID -> IO ()
modelSparQCheck opts gTh@(G_theory lid (ExtSign sign0 _) _ sens0 _) i =
    case coerceBasicTheory lid CASL "" (sign0, toNamedList sens0) of
    Just th2 -> do
      table <- parseSparQTableFromFile $ modelSparQ opts
      case table of
        Left _ -> putIfVerbose opts 0
          $ "could not parse SparQTable from file: " ++ modelSparQ opts
        Right y -> let Result d _ = modelCheck i th2 y in
            if length d > 0 then  showDiags opts {verbose = 2 } $ take 10 d
            else putIfVerbose opts 0 "Modelcheck suceeded, no errors found"
    _ ->
      putIfVerbose opts 0 $ "could not translate Theory to CASL:\n "
         ++ showDoc gTh ""

writeTheoryFiles :: HetcatsOpts -> [OutType] -> FilePath -> LibEnv
                 -> GlobalAnnos -> LIB_NAME -> SIMPLE_ID -> Int -> IO ()
writeTheoryFiles opts specOutTypes filePrefix lenv ga ln i n =
    unless (isDGRef $ labDG (lookupDGraph ln lenv) n) $
    case computeTheory False lenv ln n of
          Result ds Nothing -> do
                 putIfVerbose opts 0 $ "could not compute theory of spec "
                                  ++ show i
                 putIfVerbose opts 2 $ unlines $ map show ds
          Result _ (Just (_lenv', raw_gTh0)) -> do
                    -- what do I do with lenv' here?
            let tr = transNames opts
                resTh = if null tr then return (raw_gTh0, "") else do
                   comor <- lookupCompComorphism (map tokStr tr) logicGraph
                   tTh <- mapG_theory comor raw_gTh0
                   return (tTh, show comor)
            case resTh of
             Result es Nothing -> do
               putIfVerbose opts 0 "could not translate theory"
               putIfVerbose opts 0 $ unlines $ map show es
             Result _ (Just (raw_gTh, tStr)) -> do
               unless (null tStr) $
                   putIfVerbose opts 2 $ "Translated using comorphism " ++ tStr
               putIfVerbose opts 4 $ "Sublogic of " ++ show i ++ ": " ++
                   show (sublogicOfTh raw_gTh)
               unless (modelSparQ opts == "") $
                   modelSparQCheck opts (theoremsToAxioms raw_gTh) i
               mapM_ (writeTheory opts filePrefix ga raw_gTh ln i) specOutTypes

writeSpecFiles :: HetcatsOpts -> FilePath -> LibEnv -> LIB_NAME -> DGraph
               -> IO ()
writeSpecFiles opts file lenv ln dg = do
    let gctx = globalEnv dg
        ga = globalAnnos dg
        ns = specNames opts
        filePrefix = snd $ getFilePrefix opts file
        outTypes = outtypes opts
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
        ignore = null specOutTypes && modelSparQ opts == ""
    mapM_ (writeLibEnv opts filePrefix lenv ln) $
          if null $ dumpOpts opts then outTypes else EnvOut : outTypes
    mapM_ ( \ i -> case Map.lookup i gctx of
        Just (SpecEntry (ExtGenSig _ _ _ (NodeSig n _))) ->
            writeTheoryFiles opts specOutTypes filePrefix lenv ga ln i n
        _ -> if allSpecs then return () else
                 putIfVerbose opts 0 $ "Unknown spec name: " ++ show i
      ) $ if ignore then [] else
        if allSpecs then Map.keys gctx else ns
    mapM_ ( \ n ->
      writeTheoryFiles opts specOutTypes filePrefix lenv ga ln
         (genToken $ 'n' : show n) n)
      $ if ignore || not allSpecs then [] else
      nodesDG dg
      \\ Map.fold ( \ e l -> case e of
            SpecEntry (ExtGenSig _ _ _ (NodeSig n _)) -> n : l
            _ -> l) [] gctx
    doDump opts "GlobalAnnos" $ putStrLn $ showGlobalDoc ga ga ""
