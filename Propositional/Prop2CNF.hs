{- |
Module      :  $Header$
Description :  Helper functions for CNF translation
Copyright   :  (c) Dominik Luecke, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

Helper functions for the translation of propositional formulae to CNF. We are
using SPASS -Flotter=1 here
-}

{-
  Ref.

  http://en.wikipedia.org/wiki/Propositional_logic

  Till Mossakowski, Joseph Goguen, Razvan Diaconescu, Andrzej Tarlecki.
  What is a Logic?.
  In Jean-Yves Beziau (Ed.), Logica Universalis, pp. 113-@133. Birkhaeuser.
  2005.
-}

{-
  ToDo: clause formula relation to SPASS Parser + AS
        add analysis for clause formula
        put the stuff together
-}

module Propositional.Prop2CNF
    (
     translateToCNF            -- CNF conversion via SPASS
    )
    where

import qualified SoftFOL.ProverState as PState
import qualified Propositional.Prop2CASLHelpers as P2C
import qualified Comorphisms.SuleCFOL2SoftFOL as C2S
import qualified Logic.Comorphism as Com
import qualified SoftFOL.Sign as Sig
import qualified Propositional.Sign as PSign
import qualified Common.Result as Result
import qualified Propositional.AS_BASIC_Propositional as PBasic
import qualified Common.AS_Annotation as AS_Anno
import qualified SoftFOL.Conversions as Conv
import qualified SoftFOL.DFGParser as SParse
import qualified Common.Id as Id
import qualified Data.Set as Set
import qualified SoftFOL.Translate as Translate
import qualified CASL.Logic_CASL as CLogic
import qualified Logic.Coerce as LC
import Propositional.ChildMessage

import ChildProcess as CP
import ProcessClasses

import Data.List
import Data.Maybe
import HTk
import qualified Control.Exception as Exception
import Common.DocUtils
import Text.ParserCombinators.Parsec

safeDFGFiles ::Bool
safeDFGFiles = False

prover_name :: String
prover_name = "SPASS"

-- This hack is needed to break up a cicle in imports :(
map_theory :: (PSign.Sign, [AS_Anno.Named PBasic.FORMULA])
           -> Result.Result (Sig.Sign, [AS_Anno.Named Sig.SPTerm])
map_theory  =
    \ti1 ->
        do ti2 <- P2C.mapTheory ti1
           ti2' <- LC.coerceBasicTheory (CLogic.CASL) (Com.sourceLogic C2S.SuleCFOL2SoftFOL)
                   "Mapping theory along comorphism" ti2
           Com.wrapMapTheory C2S.SuleCFOL2SoftFOL ti2'

-- | Shortcut for the translation of the theory
getTheory :: (PSign.Sign, [AS_Anno.Named PBasic.FORMULA])
             -> Result.Result (Sig.Sign, [AS_Anno.Named Sig.SPTerm])
getTheory = map_theory

-- | forget the internal settings for a while
-- this is no loss, since we have to restore them
-- anyways
dementia :: [AS_Anno.Named PBasic.FORMULA]
            -> [AS_Anno.Named PBasic.FORMULA]
dementia frm = map (\xv ->
                        xv
                        {
                          AS_Anno.isAxiom = True
                        , AS_Anno.isDef   = False
                        , AS_Anno.wasTheorem = False
                        }
                   ) frm

-- | Initial ProverState for Spass
createInitProverState :: PSign.Sign
                      -> [AS_Anno.Named PBasic.FORMULA]
                      -> PState.SoftFOLProverState
createInitProverState sign nForms =
    let (osig, oth) =
            case Result.maybeResult $ getTheory  (sign, dementia nForms) of
              Just (xs,ys) -> (xs,ys)
              Nothing    -> error "Should not happen... Error in Prop2CNF"
    in
      PState.spassProverState osig oth

{- |
  Runs SPASS. SPASS is assumed to reside in PATH.
-}
runSpass :: PState.SoftFOLProverState -- Spass Prover state... Theory + Sig
         -> Bool -- ^ True means save DFG file
         -> IO String -- Placeholder
runSpass sps saveDFG =
    do
      spass <- newChildProcess prover_name [CP.arguments allOptions]
      Exception.catch (runSpassReal spass)
                   (\ excep -> do
                      -- kill spass process
                      destroy spass
                      _ <- waitForChildProcess spass
                      return ("SPASS not found... Bailing out!!! Cause was: "
                              ++ show excep
                             )
                   )
    where
      runSpassReal spass = do
        -- check if SPASS is running
        e <- getToolStatus spass
        if isJust e
           then error "Something is wrong"
           else do
             prob <- showDFGProblem "Translation" sps (filteredOptions)
             when saveDFG
                      (writeFile ("FlotterIn.dfg") prob)
             sendMsg spass prob
             flotterOut <- parseIt spass isEnd
             when saveDFG
                      (writeFile ("FlotterOut.dfg") flotterOut)
             return flotterOut

      filteredOptions = ["-Auto=0","-Flotter=1","-Stdin=1"]
      allOptions = filteredOptions

{- |
  Pretty printing SPASS goal in DFG format.
-}
showDFGProblem :: String -- ^ theory name
                  -> PState.SoftFOLProverState -- ^ prover state containing
                                      -- initial logical part
                  -> [String] -- ^ extra options
                  -> IO String -- ^ formatted output of the goal
showDFGProblem thName pst opts = do
  prob <- Conv.genSoftFOLProblem thName (PState.initialLogicalPart pst) $ Nothing
  -- add SPASS command line settings and extra options
  let prob' = prob { Sig.settings = (Sig.settings prob) ++
                     (PState.parseSPASSCommands opts) }
  return $ showDoc prob' ""

-- | We are searching for Flotter needed to determine the end of input
isEnd :: String -> Bool
isEnd inS = isPrefixOf "FLOTTER needed" inS

-- | Main function for run SPASS and Parse
runSPASSandParseDFG :: PState.SoftFOLProverState -- Spass Prover state... Theory + Sig
         -> Bool                                 -- True means save DFG file
         -> IO Sig.SPProblem                     -- Output AS
runSPASSandParseDFG pstate save =
    fmap parseDFG $ runSpass pstate save

-- | run the DFG Parser
parseDFG :: String -> Sig.SPProblem
parseDFG input
    = case (parse SParse.parseSPASS "" input) of
        Left err -> error $ "parse error at " ++ show err
        Right xv -> xv

-- | Restore the values of the named fields in Formulae
restoreContext :: [AS_Anno.Named PBasic.FORMULA]  -- Input Formulae
               -> [AS_Anno.Named PBasic.FORMULA]  -- Translated Formula
               -> [AS_Anno.Named PBasic.FORMULA]  -- Output
restoreContext [] [] = []
restoreContext [] _  = []
restoreContext xs (yv:ys) =
    let
        trName = AS_Anno.senAttr yv
        trNm   = Translate.transSenName
        frm    = head $ filter (\xv -> (trNm $ AS_Anno.senAttr xv) == trName) xs
        inName = AS_Anno.senAttr    frm
        isAx   = AS_Anno.isAxiom    frm
        isDef  = AS_Anno.isDef      frm
        wasTh  = AS_Anno.wasTheorem frm
        sent   = AS_Anno.sentence   yv
    in
      [(AS_Anno.makeNamed inName sent)
       {
         AS_Anno.isAxiom    = isAx
       , AS_Anno.isDef      = isDef
       , AS_Anno.wasTheorem = wasTh
       }
      ] ++ restoreContext xs ys
restoreContext _ _ = []

-- | Join different clauses to a single CNF-Formula
joinClause :: Sig.SPClauseType
           -> Sig.SPSettingBody
           -> [AS_Anno.Named PBasic.FORMULA]
           -> [AS_Anno.Named PBasic.FORMULA]
joinClause inCt inSetting inFrm =
    case inFrm of
      []-> []
      _ -> joinClauseHelper inCt (determineClauseNames inSetting) inSetting inFrm

-- | Join Clauses according to the Clause-Formula-Relation
joinClauseHelper :: Sig.SPClauseType
                 -> Set.Set String
                 -> Sig.SPSettingBody
                 -> [AS_Anno.Named PBasic.FORMULA]
                 -> [AS_Anno.Named PBasic.FORMULA]
joinClauseHelper inCt inSet inSetting inFrm =
    case (Set.null inSet) of
      True -> []
      _    ->
          let
              smallestElem = Set.findMin   inSet
              newSet       = Set.deleteMin inSet
              clauses      = filterClauseNames smallestElem inSetting inFrm
              nakedForms   = map (AS_Anno.sentence) clauses
              firstForm    = head clauses
              inName       = smallestElem
              isAx         = AS_Anno.isAxiom    firstForm
              isDef        = AS_Anno.isDef      firstForm
              wasTh        = AS_Anno.wasTheorem firstForm
          in
            case inCt of
              Sig.SPCNF -> [(AS_Anno.makeNamed inName (PBasic.Conjunction nakedForms Id.nullRange))
                            {
                              AS_Anno.isAxiom    = isAx
                            , AS_Anno.isDef      = isDef
                            , AS_Anno.wasTheorem = wasTh
                            }
                           ]
                           ++ (joinClauseHelper inCt newSet inSetting inFrm)
              Sig.SPDNF -> [(AS_Anno.makeNamed inName (PBasic.Disjunction nakedForms Id.nullRange))
                            {
                              AS_Anno.isAxiom    = isAx
                            , AS_Anno.isDef      = isDef
                            , AS_Anno.wasTheorem = wasTh
                            }
                           ]
                           ++ (joinClauseHelper inCt newSet inSetting inFrm)

-- | get Clauses with a particular name
filterClauseNames :: String -> Sig.SPSettingBody -> [AS_Anno.Named PBasic.FORMULA] -> [AS_Anno.Named PBasic.FORMULA]
filterClauseNames name setting frms =
    let clrel =
            (\xy -> case xy of
                      -- sign of list_of_settings is changed, see
                      -- SoftFOL/Sign.hs
                      Sig.SPClauseRelation cls -> cls
                      _                        -> error "Wrong type"
            ) setting
        thisNames = map (Sig.clauseSPR) $ filter (\xv -> Sig.formulaSPR xv == name) clrel
        namesSet  = foldl (\yv xv -> Set.insert xv yv) Set.empty thisNames
    in
      filter (\xv -> Set.member (AS_Anno.senAttr xv) namesSet) frms

-- | determine all names for clauses that occur
determineClauseNames :: Sig.SPSettingBody -> Set.Set String
determineClauseNames xs =
    foldl (\yv xv -> Set.insert (Sig.formulaSPR xv) yv) Set.empty
          (
           (\xy -> case xy of
                     Sig.SPClauseRelation cls -> cls
                     _                        -> error "Wrong type"
           )
           xs
          )

-- | Translation of named clauses
translateSPClause :: Sig.SPClauseType -- Clause Type is needed
                  -> Sig.SPClause
                  -> Result.Result (AS_Anno.Named PBasic.FORMULA)
translateSPClause ct nspc = do
    cla' <- case AS_Anno.sentence nspc of
        Sig.SimpleClause sc -> return sc
        Sig.QuanClause _ sc -> return sc
        Sig.BriefClause _ (Sig.TWL l1 _) (Sig.TWL l2 _) -> do
          s1 <- mapM Sig.toLiteral l1
          s2 <- mapM Sig.toLiteral l2
          let s3 = map (\ (Sig.SPLiteral b s) -> Sig.SPLiteral (not b) s) s2
          return $ Sig.NSPClauseBody Sig.SPCNF $ s1 ++ s3
    transL <- translateNSPClause ct cla'
    return nspc { AS_Anno.sentence = transL }

-- | the simple translation of Literals
translateLiteral :: Sig.SPLiteral -> PBasic.FORMULA
translateLiteral (Sig.SPLiteral b l) =
    (if b then id else flip PBasic.Negation Id.nullRange)
    $ case l of
         Sig.SPTrue -> PBasic.True_atom Id.nullRange
         Sig.SPFalse -> PBasic.False_atom Id.nullRange
         Sig.SPCustomSymbol idF -> PBasic.Predication idF
         _ -> PBasic.Predication $ Id.mkSimpleId $ Sig.showSPSymbol l

-- | translation of clauses
translateNSPClause :: Sig.SPClauseType -> Sig.NSPClauseBody
                   -> Result.Result PBasic.FORMULA
translateNSPClause ct frm =
    case frm of
      Sig.NSPClauseBody ct2 lits | ct == ct2 ->
          Result.maybeToResult Id.nullRange "All fine" $ Just $ case lits of
              [hd] -> translateLiteral hd
              _ -> (case ct of
                  Sig.SPCNF -> PBasic.Disjunction
                  Sig.SPDNF -> PBasic.Conjunction)
                (map translateLiteral lits) Id.nullRange
      _ -> Result.fatal_error "Translation impossible" Id.nullRange

translateClauseList :: Sig.SPClauseList -> Sig.SPSettingBody -> Result.Result [AS_Anno.Named PBasic.FORMULA]
translateClauseList clist inSetting =
    let
        clauseType = Sig.clauseType clist
        clauses    = Sig.clauses    clist
        tclauses   = map (translateSPClause clauseType) clauses
        nclauses   = map (Result.maybeResult) tclauses
        hasErrors  = foldl (\xh yh -> xh && (Result.hasErrors $ Result.diags yh)) True tclauses
    in
      case hasErrors of
        True  ->
            if clauses == []
            then
                do
                  Result.maybeToResult Id.nullRange "All fine" $ Just $
                        joinClause clauseType inSetting []
            else
                Result.fatal_error ("Cannot translate clause list" ++ show clist) Id.nullRange
        False -> let theClauses =
                         map (\xv -> case xv of
                                      Just yv -> yv
                                      _       -> error "Bailing out in translateClauseList..."
                             ) nclauses
                 in
                   do
                     Result.maybeToResult Id.nullRange "All fine" $ Just $
                           joinClause clauseType inSetting theClauses


-- | Translation of the logical part of SPASS to Propositional
translateLogicalPart :: Sig.SPLogicalPart -> Sig.SPSettingBody -> IO [AS_Anno.Named PBasic.FORMULA]
translateLogicalPart spLog inSetting =
    let
        clauseLists    = filterSPCL $ Sig.clauseLists  spLog
        outLists       = map (\xv -> translateClauseList xv inSetting) clauseLists
        outForm        = map (Result.maybeResult) outLists
        hasErrors      = foldl (\xh yh -> xh && (Result.hasErrors $ Result.diags yh)) True outLists
    in
      if clauseLists == []
      then
          return []
      else
          case hasErrors of
            True  -> fail ("Cannot translate logical part" ++ show spLog)
            False ->
                let theFormulae = concat $
                         map (\xv -> case xv of
                                       Just yv -> yv
                                       _       -> error "Bailing out in translateLogicalPart..."
                             ) outForm
                in
                  do
                    return theFormulae

-- | Determines the output signature
getOutputSign :: Sig.SPSymbolList -> PSign.Sign
getOutputSign inList =
    let
        preds = Sig.predicates inList
    in
      PSign.emptySig
           {
             PSign.items =
                 foldl (\ xv yv -> Set.insert yv xv) Set.empty $
                       map translateSymbol preds
           }

translateSymbol :: Sig.SPSignSym -> Id.Id
translateSymbol inSym = case inSym of
      Sig.SPSignSym name _ -> Id.simpleIdToId name
      Sig.SPSimpleSignSym name -> Id.simpleIdToId name

-- | Translation of a SPASS Problem to propositional
translateProblem :: Sig.SPProblem -> IO [AS_Anno.Named PBasic.FORMULA]
translateProblem spProb =
    let
        logicalPart = Sig.logicalPart spProb
        setting     = head $ Sig.settings spProb
    in
      -- data of setting of list_of_setting is changed, see
      -- SoftFOL/Sign.hs
      case setting of
        Sig.SPSettings _  sb ->
            translateLogicalPart logicalPart (head sb)
        _   -> error "clause formula relation is not set."

-- | Translation of Propositional theories to CNF
translateToCNF :: (PSign.Sign, [AS_Anno.Named PBasic.FORMULA])
               -> IO (PSign.Sign, [AS_Anno.Named PBasic.FORMULA])
translateToCNF (sig, forms) =
    case forms of
      [] -> return (sig, [])
      _  ->
          let pState      = createInitProverState sig forms
          in
            do
              outProb <- runSPASSandParseDFG pState safeDFGFiles
              let
                  mSymList    = Sig.symbolList $ Sig.logicalPart outProb
                  outSymList  =
                      case mSymList of
                        Just xsym -> getOutputSign xsym
                        _         -> sig
              re <- translateProblem outProb
              return $ (outSymList, restoreContext forms re)

-- | Filtering of empty ClauseLists
emptySPCL :: Sig.SPClauseList -> Bool
emptySPCL clist =
    let
        clauses = Sig.clauses clist
    in
      clauses == []

filterSPCL :: [Sig.SPClauseList] -> [Sig.SPClauseList]
filterSPCL clist = filter (\xv -> not $ emptySPCL xv) clist
