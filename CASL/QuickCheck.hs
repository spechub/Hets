{-# OPTIONS -fallow-undecidable-instances #-}
{- |
Module      :  $Header$
Description :  QuickCheck model checker for CASL.CFOL
Copyright   :  (c) Till Mossakowski, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

QuickCheck model checker for CASL.CFOL.
Initially, only finite enumeration domains are supported
-}

module CASL.QuickCheck(quickCheckProver,
                       Q_ProofTree (..),
                       QModel (..),
                       VARIABLE_ASSIGNMENT (..)) where

import Debug.Trace

import qualified Common.AS_Annotation as AS_Anno
import qualified Common.Result as Result

import CASL.AS_Basic_CASL
import CASL.Sublogic as SL
import CASL.Sign
import CASL.Amalgamability -- for CASLSign
import CASL.Quantification
import CASL.ToDoc
import CASL.SimplifySen


import Logic.Prover
import SoftFOL.ProverState (parseTactic_script)

import Common.Result
import Common.Id
import Common.DocUtils

import qualified Data.Map as Map
import Data.Maybe
import Data.List
--import Data.Time (timeToTimeOfDay)
--import Data.Time.Clock (UTCTime(..), secondsToDiffTime, getCurrentTime)

import Control.Monad
import qualified Control.Concurrent as Concurrent

import System.IO
import GUI.GenericATP
import GUI.GenericATPState
import Proofs.BatchProcessing


type CASLFORMULA = FORMULA ()
type CASLTERM = TERM ()

data Q_ProofTree = Q_ProofTree String
       deriving (Eq, Ord)

instance Show Q_ProofTree where
  show (Q_ProofTree st) = st

qSublogic :: CASL_SL ()
qSublogic = SL.top { sub_features = NoSub, -- no subsorting
                        has_part = False -- no partiality
                   }

-- a qmodel is a certain term model used by QuickCheck
data QModel = QModel
        { sign :: CASLSign,
          -- sentences determining the set of terms for a sort
          carrierSens :: Map.Map SORT [CASLFORMULA],
          -- definitions of predicates and operations
          predDefs :: Map.Map PRED_SYMB [([CASLTERM],CASLFORMULA)],
          opDefs :: Map.Map OP_SYMB [([CASLTERM],CASLTERM)],
          -- currently evaluated items,
          -- for avoiding infinite recursion
          evaluatedPreds :: [(PRED_SYMB,[CASLTERM])],
          evaluatedOps :: [(OP_SYMB,[CASLTERM])]
        }
        deriving (Eq, Show)

{- |
  Run the QuickCheck service.
-}
runQuickCheck :: QModel
           -- ^ logical part containing the input Sign and axioms and possibly
           --   goals that have been proved earlier as additional axioms
           -> GenericConfig Q_ProofTree -- ^ configuration to use
           -> Bool -- ^ True means save theory file
           -> String -- ^ name of the theory in the DevGraph
           -> AS_Anno.Named CASLFORMULA -- ^ goal to prove
           -> IO (ATPRetval, GenericConfig Q_ProofTree)
           -- ^ (retval, configuration with proof status and complete output)
runQuickCheck qm cfg _saveFile _thName nGoal = do
   let Result d res = quickCheck qm nGoal
       fstr = show(printTheoryFormula(AS_Anno.mapNamed
                        (simplifySen dummyMin dummy (sign qm)) nGoal))
              ++ "\n"
       showDiagStrings = concat . intersperse "\n" . map diagString
       diagstr = case (res,d) of
          (Just True,_) -> showDiagStrings(take 10 d)
          (_,[]) -> ""
          _ -> "Formula failed: \n" ++ fstr ++
               " some Counterexamples: \n"
               ++ showDiagStrings(take 10 d)
       gstat = case res of
          Just True -> Proved Nothing
          Just False -> Disproved
          Nothing -> Open
       setStatus pstat = pstat { goalStatus = gstat,
                                 proverName = "QuickCheck",
                                 proofTree = Q_ProofTree diagstr }
       cfg' = cfg { proof_status = setStatus (proof_status cfg),
                    resultOutput = [diagstr] }
   return (ATPSuccess, cfg')
     -- return ATPError is time is up???

-- duplicated from Logic_CASL

dummy :: Sign f s -> a -> ()
dummy _ _ = ()

-- dummy of "Min f e"
dummyMin :: b -> c -> Result ()
dummyMin _ _ = Result {diags = [], maybeResult = Just ()}

-----------------------------------------------------------------------------
-- * QModels

-- | initial QModel
makeQm :: CASLSign -> QModel
makeQm sig = QModel { sign = sig,
                      carrierSens = Map.empty,
                      predDefs = Map.empty,
                      opDefs = Map.empty,
                      evaluatedPreds = [],
                      evaluatedOps = []
                    }

-- | insert sentences into a QModel
insertSen :: QModel -> AS_Anno.Named CASLFORMULA -> QModel
insertSens :: QModel -> [AS_Anno.Named CASLFORMULA] -> QModel
insertSens = foldl insertSen
insertSen qm sen =
-- trace ("\nsen: "++show sen) $
 if (not $ AS_Anno.isAxiom sen) then qm else
  let f = AS_Anno.sentence sen
      qm1 = case f of
               Sort_gen_ax cs _ ->
                 let s = zip (map newSort cs) (map (const [f]) [1..length cs])
                     ins = foldr $ uncurry $ Map.insertWith (++)
                  in qm { carrierSens =  ins (carrierSens qm) s }
               _ -> qm
      insertPred p args body =
        qm1 { predDefs = Map.insertWith (++) p [(args,body)] (predDefs qm1)}
      insertOp op args body =
        qm1 { opDefs = Map.insertWith (++) op [(args,body)] (opDefs qm1) }
  in case stripAllQuant f of
  -- insert a predicate or operation definition into a QModel
   Predication predsymb args _ ->
     insertPred predsymb args $ True_atom nullRange
   Negation (Predication predsymb args _) _ ->
     insertPred predsymb args $ False_atom nullRange
   Equivalence (Predication predsymb args _) body _ ->
     insertPred predsymb args body
   Strong_equation (Application opsymb args _) body _ ->
     insertOp opsymb args body
   Existl_equation (Application opsymb args _) body _ ->
     insertOp opsymb args body
   _ -> qm1


----------------------------------------------------------------------------
-- * Variable assignments

data VARIABLE_ASSIGNMENT =
     Variable_Assignment QModel [(VAR, CASLTERM)] deriving Eq

instance Show VARIABLE_ASSIGNMENT where
    show (Variable_Assignment qm assignList) = showAssignments qm assignList

showAssignments :: QModel -> [(VAR, CASLTERM)] -> String
showAssignments qm xs =
    "["++ concat (intersperse ", " $ map (showSingleAssignment qm) xs)  ++"]"

showSingleAssignment :: QModel -> (VAR, CASLTERM) -> String
showSingleAssignment qm (v, t) =
  let st = rmTypesT dummyMin dummy (sign qm) t
   in show v ++ "->" ++ showDoc st ""

emptyAssignment :: QModel -> VARIABLE_ASSIGNMENT
emptyAssignment qm = Variable_Assignment qm []

insertAssignment :: VARIABLE_ASSIGNMENT -> (VAR, CASLTERM) -> VARIABLE_ASSIGNMENT
insertAssignment (Variable_Assignment qm ass) (v,t) =
  Variable_Assignment qm ((v,t):ass)

concatAssignment :: VARIABLE_ASSIGNMENT -> VARIABLE_ASSIGNMENT
                 -> VARIABLE_ASSIGNMENT
concatAssignment (Variable_Assignment qm l1) (Variable_Assignment _ l2) =
  Variable_Assignment qm $ l1 ++ l2


--------------------------------------------------------------------------
-- * The quickcheck model checker

quickCheck :: QModel -> AS_Anno.Named CASLFORMULA -> Result Bool
quickCheck qm nSen =
  let f = {- trace (show qm) $ -} AS_Anno.sentence nSen
   in case f of
        Quantification _ _ _ _ ->
          calculateQuantification True qm (emptyAssignment qm) f
        _ -> calculateFormula1 qm (emptyAssignment qm) f

calculateQuantification :: Bool -> QModel -> VARIABLE_ASSIGNMENT -> CASLFORMULA
                              -> Result Bool
calculateQuantification isOuter qm ass qf = case qf of
  Quantification quant vardecls f range -> do
    assments <- generateVariableAssignments qm vardecls
    let assments' = map (\ x -> concatAssignment x ass) assments
    tuples <- mapM ( \ a -> do
                            res <- calculateFormula1 qm a f
                            return (res,a))
                     assments'
    case {- trace ("\ntuples: "++show tuples) -} quant of
      Universal -> do
        let failedtuples = take 10 $ filter (not.fst) tuples
        if null failedtuples then return True else do
          when isOuter
            (mapM_ (\ (_, a)-> warning () (" "++show a) range) failedtuples)
          return False
      Existential -> do
        let suceededTuples = filter fst tuples
        if not (null suceededTuples) then return True else do
          when isOuter
            (warning () "Existential quantification not fulfilled" range)
          return False
      Unique_existential -> do
        let suceededTuples = take 2 $ filter fst tuples
        case suceededTuples of
          [_] -> return True
          t -> do when isOuter
                    (warning () ("Unique Existential quantification"
                      ++" not fulfilled: "
                      ++ (if null t then "no" else "more than one")
                      ++" assignments") range)
                  return False
  _ -> fail "calculateQuantification wrongly applied"

calculateTerm :: QModel -> VARIABLE_ASSIGNMENT -> CASLTERM -> Result CASLTERM
calculateTerm qm ass trm = case trm of
    Simple_id var -> lookupVar var ass
    Qual_var var _ _ -> lookupVar var ass
    Application opSymb terms _ ->
              applyOperation qm ass opSymb terms
    Sorted_term term _ _ -> calculateTerm qm ass term
    Cast _ _ _ -> error "Cast not implemented"
    Conditional t1 fo t2 _ -> do
              res <- calculateFormula1 qm ass fo
              if res then calculateTerm qm ass t1
                     else calculateTerm qm ass t2
    _ -> fail "unsopprted term"

lookupVar :: VAR -> VARIABLE_ASSIGNMENT -> Result CASLTERM
lookupVar v (Variable_Assignment _ ass) = case lookup v ass of
  Nothing -> fail ("no value for variable "++show v++" found")
  Just val -> return val

applyOperation :: QModel -> VARIABLE_ASSIGNMENT -> OP_SYMB -> [CASLTERM] ->
                       Result CASLTERM
applyOperation qm ass opsymb terms = do
  -- block infinite recursion
  when ((opsymb,terms) `elem` evaluatedOps qm)
       (fail ("infinite recursion when calculating"++
              show (Application opsymb terms nullRange)))
  let qm' = qm { evaluatedOps = (opsymb,terms):evaluatedOps qm }
  -- evaluate argument terms
  args <- mapM (calculateTerm qm' ass) terms
  -- find appropriate operation definition
  case Map.lookup opsymb (opDefs qm) of
    Nothing ->
      -- no operation definition? Then return unevaluated term
      return (Application opsymb terms nullRange)
    Just bodies -> do
      -- bind formal to actual arguments
      (body,m) <- match bodies args (showDoc opsymb "")
      let ass' = {- trace ("\nargs: "++show args++"\nbodies: "++show bodies++"\nbody: "++show body ++ "\nm: "++show m) -} foldl insertAssignment ass m
      -- evaluate body of operation definition
      calculateTerm qm' ass' body

match :: [([CASLTERM],a)] -> [CASLTERM] -> String
          -> Result (a,[(VAR,CASLTERM)])
match bodies args msg =
  case mapMaybe (match1 args) bodies of
    [] -> fail ("no matching found for "++msg)
    (subst:_) -> return subst

match1 :: [CASLTERM] -> ([CASLTERM],a)
           -> Maybe (a,[(VAR,CASLTERM)])
match1 args (vars,body) = do
  substs <- mapM (uncurry match2) (zip vars args)
  let subst = concat substs
  if consistent subst then return (body,subst) else Nothing


match2 :: CASLTERM -> CASLTERM -> Maybe [(VAR,CASLTERM)]
match2 (Qual_var v _ _) t = Just [(v,t)]
match2 (Simple_id v) t = Just [(v,t)]
match2 (Application opsymb1 terms1 _) (Application opsymb2 terms2 _) = do
   when (opsymb1 /= opsymb2) Nothing
   substs <- mapM (uncurry match2) (zip terms1 terms2)
   return (concat substs)
match2 (Sorted_term t1 _ _) t2 = match2 t1 t2
match2 t1 (Sorted_term t2 _ _) = match2 t1 t2
match2 _ _ = Nothing

consistent :: [(VAR,CASLTERM)] -> Bool
consistent ass =
  isJust $ foldM insertAss Map.empty ass
  where
  insertAss m (v,t) =
    case Map.lookup v m of
      Just t1 -> if t==t1 then return m else Nothing
      Nothing -> Just $ Map.insert v t m

calculateFormula1 qm varass f =
  let Result d res = calculateFormula qm varass f
  in {- (trace ("\nf: "++showDoc f ""++"\nass:"++show varass++"\nres: "++show res)) $ -} Result d res

calculateFormula :: QModel -> VARIABLE_ASSIGNMENT -> CASLFORMULA
                     -> Result Bool
calculateFormula qm varass f = case f of
    Quantification _ _ _ _ ->
       calculateQuantification False qm varass f
    Conjunction formulas _ -> do
        res <- mapM (calculateFormula1 qm varass) formulas
        return (and res)
    Disjunction formulas _ -> do
        res <- mapM (calculateFormula1 qm varass) formulas
        return (or res)
    Implication f1 f2 _ _ -> do
        res1 <- calculateFormula1 qm varass f1
        res2 <- calculateFormula1 qm varass f2
        return (not res1 || res2)
    Equivalence f1 f2 _ -> do
        res1 <- calculateFormula1 qm varass f1
        res2 <- calculateFormula1 qm varass f2
        return (res1 == res2)
    Negation f1 _ -> do
        res <- calculateFormula1 qm varass f1
        return (not res)
    True_atom _ -> return True
    False_atom _ -> return False
    Strong_equation term1 term2 _ -> do
        t1 <- calculateTerm qm varass term1
        t2 <- calculateTerm qm varass term2
        return (equalElements t1 t2)
    Existl_equation term1 term2 _ -> do
        t1 <- calculateTerm qm varass term1
        t2 <- calculateTerm qm varass term2
        return (equalElements t1 t2)
    Predication predsymb terms _ ->
        applyPredicate qm varass predsymb terms
    _ -> fail $ "formula evaluation not implemented for: " ++ showDoc f ""

applyPredicate :: QModel -> VARIABLE_ASSIGNMENT -> PRED_SYMB -> [CASLTERM] ->
                       Result Bool
applyPredicate qm ass predsymb terms = do
  -- block infinite recursion
  when ((predsymb,terms) `elem` evaluatedPreds qm)
       (fail ("infinite recursion when calculating"++
              show (Predication predsymb terms nullRange)))
  let qm' = qm { evaluatedPreds = (predsymb,terms):evaluatedPreds qm }
  -- evaluate argument terms
  args <- mapM (calculateTerm qm' ass) terms
  -- find appropriate predicate definition
  case Map.lookup predsymb (predDefs qm) of
    Nothing -> fail ("no predicate definition for "++show predsymb)
    Just bodies -> do
      -- bind formal to actual arguments
      (body,m) <- match bodies args (showDoc predsymb "")
      let ass' = {- trace ("\nargs: "++show args++"\nbodies: "++show bodies++"\nbody: "++show body ++ "\nm: "++show m) -} foldl insertAssignment ass m
--      let ass' = foldl insertAssignment ass m
      -- evaluate body of predicate definition
      calculateFormula1 qm' ass' body

equalElements :: CASLTERM -> CASLTERM -> Bool
equalElements = (==)

getVars:: [VAR_DECL] -> [(VAR,SORT)]
getVars = concatMap getVarsAtomic

getVarsAtomic:: VAR_DECL -> [(VAR,SORT)]
getVarsAtomic (Var_decl vars s _) = zip vars (map (const s) [1..length vars])


generateVariableAssignments :: QModel -> [VAR_DECL]
                                -> Result [VARIABLE_ASSIGNMENT]
generateVariableAssignments qm vardecls = do
   let vars = getVars vardecls
   carriers <- mapM (getCarrier qm) (map snd vars)
   let varsCarriers = zip (map fst vars) carriers
   return $ map (Variable_Assignment qm) (gVAs varsCarriers)

gVAs :: [(VAR,[CASLTERM])] -> [[(VAR, CASLTERM)]]
gVAs [] = [[]]
gVAs ((v,carrier) : vs) = let
    rs = gVAs vs
    fs = map (\ b -> [(v, b)]) carrier
    in [f ++ r | f <- fs, r <- rs]


-- | check whether some formula leads to term generation of a sort
termSort :: CASLFORMULA -> Maybe (SORT,[CASLTERM])
termSort (Sort_gen_ax constr _)
  = case sorts of
     -- at the moment, we only treat one-sort constraints with constants
     [s] -> if all constant ops
             then Just (s,map mkTerm ops)
             else Nothing
     _ -> Nothing
    where (sorts,ops,_) = recover_Sort_gen_ax constr
          constant (Qual_op_name _ (Op_type _ [] _ _) _) = True
          constant _ = False
          mkTerm op = Application op [] nullRange
termSort _ = Nothing

-- | get the carrier set for a specific sort
getCarrier:: QModel -> SORT -> Result [CASLTERM]
getCarrier qm s =
  case Map.lookup s (carrierSens qm) of
    Nothing -> fail ("sort "++show s++" is not generated")
    Just sens -> case mapMaybe termSort sens of
      [] -> fail ("sort "++show s++" is not generated by constants")
      (_,terms):_ -> return terms
  -- todo: generalise this



----------------------------------------------------------------------------
-- * Interfacing to Hets prover interface

{- |
  The Prover implementation. First runs the batch prover (with graphical feedback), then starts the GUI prover.
-}
quickCheckProver :: Prover CASLSign CASLFORMULA CASL_Sublogics Q_ProofTree
quickCheckProver = (mkProverTemplate "QuickCheck" qSublogic quickCheckGUI)
    { proveCMDLautomatic = Just quickCheckCMDLautomatic
    , proveCMDLautomaticBatch = Just quickCheckCMDLautomaticBatch }

{- |
  Record for prover specific functions. This is used by both GUI and command
  line interface.
-}

atpFun :: String -- ^ theory name
       -> ATPFunctions CASLSign CASLFORMULA Q_ProofTree QModel
atpFun _thName = ATPFunctions
    { initialProverState = \ sig sens -> insertSens (makeQm sig) sens,
      atpTransSenName = id,
      atpInsertSentence = insertSen,
      goalOutput = \_ _ _ -> do
            putStrLn "No display of output yet"
            return "",
      proverHelpText = "QuickCheck tries to evaluate sentences in term generated models. This only works if your theory contains enough generated or freely generated datatypes.",
      batchTimeEnv = "HETS_SPASS_BATCH_TIME_LIMIT",
      fileExtensions = FileExtensions{problemOutput = ".none1",
                                      proverOutput = ".none2",
                                      theoryConfiguration = ".none3"},
      runProver = runQuickCheck,
      createProverOptions = \_ -> []}

-- ** GUI

{- |
  Invokes the generic prover GUI. SPASS specific functions are omitted by
  data type ATPFunctions.
-}
quickCheckGUI :: String -- ^ theory name
           -> Theory CASLSign CASLFORMULA Q_ProofTree
           -- ^ theory consisting of a signature
           --   and a list of named sentences
           -> IO([Proof_status Q_ProofTree]) -- ^ proof status for each goal
quickCheckGUI thName th =
    genericATPgui (atpFun thName) True (prover_name quickCheckProver) thName th $
                  Q_ProofTree ""

-- ** command line functions

{- |
  Implementation of 'Logic.Prover.proveCMDLautomatic' which provides an
  automatic command line interface for a single goal.
  QuickCheck specific functions are omitted by data type ATPFunctions.
-}
quickCheckCMDLautomatic ::
           String -- ^ theory name
        -> Tactic_script -- ^ default tactic script
        -> Theory CASLSign CASLFORMULA Q_ProofTree
           -- ^ theory consisting of a signature and a list of Named sentence
        -> IO (Result.Result ([Proof_status Q_ProofTree]))
           -- ^ Proof status for goals and lemmas
quickCheckCMDLautomatic thName defTS th =
    genericCMDLautomatic (atpFun thName) (prover_name quickCheckProver) thName
        (parseTactic_script batchTimeLimit [] defTS) th (Q_ProofTree "")

{- |
  Implementation of 'Logic.Prover.proveCMDLautomaticBatch' which provides an
  automatic command line interface to the QuickCheck prover via MathServe.
  QuickCheck specific functions are omitted by data type ATPFunctions.
-}
quickCheckCMDLautomaticBatch ::
           Bool -- ^ True means include proved theorems
        -> Bool -- ^ True means save problem file
        -> Concurrent.MVar (Result.Result [Proof_status Q_ProofTree])
           -- ^ used to store the result of the batch run
        -> String -- ^ theory name
        -> Tactic_script -- ^ default tactic script
        -> Theory CASLSign CASLFORMULA Q_ProofTree -- ^ theory consisting of a
           --   signature and a list of named sentences
        -> IO (Concurrent.ThreadId,Concurrent.MVar ())
           -- ^ fst: identifier of the batch thread for killing it
           --   snd: MVar to wait for the end of the thread
quickCheckCMDLautomaticBatch inclProvedThs saveProblem_batch resultMVar
                        thName defTS th =
    genericCMDLautomaticBatch (atpFun thName) inclProvedThs saveProblem_batch
        resultMVar (prover_name quickCheckProver) thName
        (parseTactic_script batchTimeLimit [] defTS) th (Q_ProofTree "")
