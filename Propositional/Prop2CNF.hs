{- |
Module      :  $Header$
Description :  Instance of class Logic for propositional logic
Copyright   :  (c) Dominik Luecke, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@tzi.de
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
  In Jean-Yves Beziau (Ed.), Logica Universalis, pp. 113-@133. Birkhäuser.
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

import qualified SPASS.ProverState as PState
import qualified Comorphisms.Prop2CASL as P2C
import qualified Comorphisms.CASL2SPASS as C2S
import qualified Logic.Comorphism as Com
import qualified SPASS.Sign as Sig
import qualified Propositional.Sign as PSign
import qualified Common.Result as Result
import qualified Propositional.AS_BASIC_Propositional as PBasic
import qualified Common.AS_Annotation as AS_Anno
import qualified SPASS.Conversions as Conv
import qualified SPASS.DFGParser as SParse
import qualified Common.Id as Id
import qualified Data.Set as Set
import qualified SPASS.Translate as Translate

import ChildProcess
import ProcessClasses

import System

import Data.List
import Data.Maybe
import HTk
import qualified Control.Exception as Exception
import Common.DocUtils
import Text.Regex
import System.IO.Unsafe
import Text.ParserCombinators.Parsec
import Common.Lib.State as St

prover_name :: String
prover_name = "SPASS"

-- | the used comorphism is an embedding
comp :: Com.CompComorphism P2C.Prop2CASL C2S.SuleCFOL2SoftFOL
comp = (Com.CompComorphism P2C.Prop2CASL C2S.SuleCFOL2SoftFOL)

-- | Shortcut for the translation of the theory
getTheory :: (PSign.Sign, [AS_Anno.Named PBasic.FORMULA]) 
             -> Result.Result (Sig.Sign, [AS_Anno.Named Sig.SPTerm])
getTheory = Com.map_theory comp

-- | Initial ProverState for Spass
createInitProverState :: PSign.Sign 
                      -> [AS_Anno.Named PBasic.FORMULA] 
                      -> PState.SPASSProverState
createInitProverState sign nForms =
    let (osig, oth) = 
            case Result.maybeResult $ getTheory  (sign, nForms) of
              Just (xs,ys) -> (xs,ys)
              Nothing    -> error "Should not happen... Error in Prop2CNF"
    in
      PState.spassProverState osig oth

{- |
  Runs SPASS. SPASS is assumed to reside in PATH.
-}
runSpass :: PState.SPASSProverState -- Spass Prover state... Theory + Sig
         -> Bool -- ^ True means save DFG file
         -> IO String -- Placeholder
runSpass sps saveDFG = 
    do
      spass <- newChildProcess "SPASS" [ChildProcess.arguments allOptions]
      Exception.catch (runSpassReal spass)
                   (\ excep -> do
                      -- kill spass process
                      destroy spass
                      _ <- waitForChildProcess spass
                      return "SPASS not found... Bailing out!!!"
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
             flotterOut <- parseProtected spass
             when saveDFG
                      (writeFile ("FlotterOut.dfg") flotterOut)
             return flotterOut

      filteredOptions = ["-Stdin", "-Flotter"]
      allOptions = ["-Stdin", "-Flotter", "-CNFRenaming=0"]
      
{- |
  Pretty printing SPASS goal in DFG format.
-}
showDFGProblem :: String -- ^ theory name
                  -> PState.SPASSProverState -- ^ prover state containing
                                      -- initial logical part
                  -> [String] -- ^ extra options
                  -> IO String -- ^ formatted output of the goal
showDFGProblem thName pst opts = do
  prob <- Conv.genSPASSProblem thName (PState.initialLogicalPart pst) $ Nothing
  -- add SPASS command line settings and extra options
  let prob' = prob { Sig.settings = (Sig.settings prob) ++ 
                     (PState.parseSPASSCommands opts) }
  return $ showDoc prob' ""

-- | Helper for reading SPASS output
parseProtected :: ChildProcess -> IO String
parseProtected spass = do
  e <- getToolStatus spass
  case e of 
    Nothing                   -> 
        do  
          dfg <- parseIt spass
          return dfg
    Just (ExitFailure retval) -> 
        do
          _ <- waitForChildProcess spass
          return "error"
    Just ExitSuccess          -> return "done"

parseIt :: ChildProcess -> IO String
parseIt spass = do
  line <- readMsg spass
  msg  <- parseItHelp spass $ return line
  return msg

parseItHelp :: ChildProcess -> IO String -> IO String
parseItHelp spass inp = do
  e <- getToolStatus spass
  inT <- inp
  case e of 
    Nothing
         -> 
           do
             line <- readMsg spass
             case isEnd line of
               True -> 
                   return inT
               _    ->
                   parseItHelp spass $ return (inT ++ "\n" ++ line)
    Just (ExitFailure retval)
        -- returned error
        -> do
           _ <- waitForChildProcess spass
           return $ "SPASS returned error: "++(show retval)
    Just ExitSuccess
         -- completed successfully. read remaining output.
         -> 
           do
             line <- readMsg spass
             case isEnd line of
               True -> 
                   return inT
               _    ->
                   parseItHelp spass $ return (inT ++ "\n" ++ line)

-- | We are searching for Flotter needed to determine the end of input
isEnd :: String -> Bool
isEnd inS = isPrefixOf "FLOTTER needed" inS

-- | Main function for run SPASS and Parse
runSPASSandParseDFG :: PState.SPASSProverState -- Spass Prover state... Theory + Sig
         -> Bool                               -- True means save DFG file
         -> Sig.SPProblem                      -- Output AS
runSPASSandParseDFG pstate save = let inputTerms = PState.initialLogicalPart pstate in
                                  parseDFG $ unsafePerformIO $ runSpass pstate save
-- | run the DFG Parser
parseDFG :: String -> Sig.SPProblem
parseDFG input
    = case (parse SParse.parseSPASS "" input) of
        Left err -> error $ "parse error at " ++ show err
        Right x  -> x

-- | Restore the values of the named fields in Formulae 
restoreContext :: [AS_Anno.Named PBasic.FORMULA]  -- Input Formulae
               -> [AS_Anno.Named PBasic.FORMULA]  -- Translated Formula
               -> [AS_Anno.Named PBasic.FORMULA]  -- Output
restoreContext [] [] = []
restoreContext [] _  = []
restoreContext xs (y:ys) = 
    let
        trName = AS_Anno.senAttr y
        trNm   = Translate.transSenName
        frm    = head $ filter (\x -> (trNm $ AS_Anno.senAttr x) == trName) xs
        isAx   = AS_Anno.isAxiom    frm
        isDef  = AS_Anno.isDef      frm
        wasTh  = AS_Anno.wasTheorem frm  
        sent   = AS_Anno.sentence   y
    in
      [(AS_Anno.makeNamed trName sent)
       {
         AS_Anno.isAxiom    = isAx
       , AS_Anno.isDef      = isDef
       , AS_Anno.wasTheorem = wasTh       
       }
      ] ++ restoreContext xs ys
restoreContext _ _ = []

-- | Join different clauses to a single CNF-Formula
joinClause :: Sig.SPClauseType
           -> Sig.SPSetting
           -> [AS_Anno.Named PBasic.FORMULA] 
           -> [AS_Anno.Named PBasic.FORMULA]          
joinClause inCt inSetting inFrm = joinClauseHelper inCt (determineClauseNames inSetting) inSetting inFrm
                 
-- | Join Clauses according to the Clause-Formula-Relation
joinClauseHelper :: Sig.SPClauseType 
                 -> Set.Set String 
                 -> Sig.SPSetting
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
filterClauseNames :: String -> Sig.SPSetting -> [AS_Anno.Named PBasic.FORMULA] -> [AS_Anno.Named PBasic.FORMULA]
filterClauseNames name setting frms = let clrel =   
                                              (\xy -> case xy of 
                                                        Sig.SPClauseRelation cls -> cls
                                                        _                        -> error "Wrong type"
                                              ) 
                                              setting
                                          thisNames = map (Sig.clauseSPR) $ filter (\x -> Sig.formulaSPR x == name) clrel
                                          namesSet  = foldl (\y x -> Set.insert x y) Set.empty thisNames
                                      in
                                        filter (\x -> Set.member (AS_Anno.senAttr x) namesSet) frms

-- | determine all names for clauses that occur
determineClauseNames :: Sig.SPSetting -> Set.Set String
determineClauseNames xs = foldl (\y x -> Set.insert (Sig.formulaSPR x) y) Set.empty 
                          (
                           (\xy -> case xy of 
                                     Sig.SPClauseRelation cls -> cls
                                     _                        -> error "Wrong type"
                           ) 
                           xs
                          )

-- | Translation of named clauses
translateSPClause :: Sig.SPClauseType                            -- Clause Type is needed
                -> Sig.SPClause                                  -- the named clause
                -> Result.Result (AS_Anno.Named PBasic.FORMULA)  -- output Formula can fail
translateSPClause ct nspc = 
    let 
        inName = AS_Anno.senAttr    nspc
        isAx   = AS_Anno.isAxiom    nspc
        isDef  = AS_Anno.isDef      nspc
        wasTh  = AS_Anno.wasTheorem nspc
        cla    = AS_Anno.sentence   nspc
        transL = translateNSPClause ct cla
        diags  = Result.diags       transL
        mres   = Result.maybeResult transL
    in
      case (Result.hasErrors diags) of
        True -> Result.fatal_error  "Translation impossible" Id.nullRange
        _    -> Result.maybeToResult Id.nullRange
                "All fine" $
                 Just $ (AS_Anno.makeNamed inName (unwrapMaybe mres))
                          {
                            AS_Anno.isAxiom    = isAx
                          , AS_Anno.isDef      = isDef
                          , AS_Anno.wasTheorem = wasTh
                          }
-- | Helper to get out of the Maybe Monad

unwrapMaybe :: Maybe a -> a
unwrapMaybe (Just y)  = y
unwrapMaybe Nothing   = error "Cannot unwrap Nothing"

-- | translation of clauses
translateNSPClause :: Sig.SPClauseType                                  -- Clause Type is needed
                -> Sig.NSPClause                                        -- the clause
                -> Result.Result PBasic.FORMULA                         -- output Formula can fail
translateNSPClause ct inClause = 
    case ct of
      Sig.SPCNF -> translateCNF inClause
      Sig.SPDNF -> translateDNF inClause

-- | the simple translation of Literals    

translateLiteral :: Sig.SPLiteral -> PBasic.FORMULA
translateLiteral lt =
    case lt of
      Sig.NSPFalse     -> PBasic.False_atom Id.nullRange
      Sig.NSPTrue      -> PBasic.True_atom Id.nullRange
      Sig.NSPId idF    -> PBasic.Predication $ Id.mkSimpleId idF
      Sig.NSPNotId idF -> PBasic.Negation 
                          (
                           PBasic.Predication $ Id.mkSimpleId idF
                          )
                          Id.nullRange
-- | Enforced translation of CNF clauses
translateCNF :: Sig.NSPClause -> Result.Result PBasic.FORMULA
translateCNF frm =
    case frm of
      Sig.NSPCNF lits -> Result.maybeToResult Id.nullRange
                         "All fine" $ 
                         Just $
                              PBasic.Disjunction 
                                        (map translateLiteral lits) 
                                        Id.nullRange
      _               -> Result.fatal_error "Translation impossible" Id.nullRange


-- | Enforced translation of DNF clauses
translateDNF :: Sig.NSPClause -> Result.Result PBasic.FORMULA
translateDNF frm =
    case frm of
      Sig.NSPDNF lits -> Result.maybeToResult Id.nullRange
                         "All fine" $
                         Just $
                              PBasic.Conjunction 
                                        (map translateLiteral lits) 
                                        Id.nullRange
      _               -> Result.fatal_error "Translation impossible" Id.nullRange

translateClauseList :: Sig.SPClauseList -> Sig.SPSetting -> Result.Result [AS_Anno.Named PBasic.FORMULA]
translateClauseList clist inSetting =
    let
        clauseType = Sig.clauseType clist
        clauses    = Sig.clauses    clist
        tclauses   = map (translateSPClause clauseType) clauses
        nclauses   = map (Result.maybeResult) tclauses
        hasErrors  = foldl (\xh yh -> xh && (Result.hasErrors $ Result.diags yh)) True tclauses
    in
      case hasErrors of
        True  -> Result.fatal_error ("Cannot translate clause list" ++ show clist) Id.nullRange
        False -> let theClauses =
                         map (\x -> case x of 
                                      Just y -> y
                                      _      -> error "Bailing out in translateClauseList..."
                             ) nclauses
                 in
                   Result.maybeToResult Id.nullRange "All fine" $ Just $
                     joinClause clauseType inSetting theClauses


-- | Translation of the logical part of SPASS to Propositional
translateLogicalPart :: Sig.SPLogicalPart -> Sig.SPSetting -> Result.Result [AS_Anno.Named PBasic.FORMULA]
translateLogicalPart spLog inSetting = 
    let
        clauseLists    = init $ Sig.clauseLists  spLog
        outLists       = map (\x -> translateClauseList x inSetting) clauseLists
        outForm        = map (Result.maybeResult) outLists
        hasErrors      = foldl (\xh yh -> xh && (Result.hasErrors $ Result.diags yh)) True outLists
    in
      case hasErrors of
        True  -> Result.fatal_error ("Cannot translate logical part" ++ show spLog) Id.nullRange
        False -> let theFormulae = concat $
                         map (\x -> case x of 
                                      Just y -> y
                                      _      -> error "Bailing out in translateLogicalPart..."
                             ) outForm
                 in 
                   Result.maybeToResult Id.nullRange "All fine" $ Just $
                         theFormulae

-- | Translation of a SPASS Problem to propositional
translateProblem :: Sig.SPProblem -> Result.Result [AS_Anno.Named PBasic.FORMULA]
translateProblem spProb = 
    let
        identifier  = Sig.identifier  spProb
        descr       = Sig.description spProb
        logicalPart = Sig.logicalPart spProb
        setting     = head $ Sig.settings spProb
   in
     translateLogicalPart logicalPart setting
     
-- | Translation of Propositional theories to CNF
translateToCNF :: (PSign.Sign, [AS_Anno.Named PBasic.FORMULA]) -> Result.Result (PSign.Sign, [AS_Anno.Named PBasic.FORMULA])
translateToCNF (sig, forms) = 
    let pState      = createInitProverState sig forms
        translation = translateProblem $ runSPASSandParseDFG pState False
        pDiags      = Result.diags translation
        pMaybe      = Result.maybeResult translation
        hasErrs     = Result.hasErrors pDiags
    in
      case hasErrs of
        True  -> Result.fatal_error ("Translation to CNF encountered errors... Bailing out...") Id.nullRange
        False -> let re = (\x -> case x of 
                                   Just y -> y
                                   _      -> error "Bailing out in translateToCNF..."
                          ) pMaybe
                 in
                   Result.maybeToResult Id.nullRange "All fine" $ Just $
                         (sig, restoreContext forms re) 
                   