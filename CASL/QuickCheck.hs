{-# LANGUAGE FlexibleInstances #-}
{- |
Module      :  $Header$
Description :  QuickCheck model checker for CASL.CFOL
Copyright   :  (c) Till Mossakowski, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (via GUI imports, FlexibleInstances)

QuickCheck model checker for CASL.CFOL.
Initially, only finite enumeration domains are supported
-}

module CASL.QuickCheck(quickCheckProver) where

import qualified Common.AS_Annotation as AS_Anno
import qualified Common.Result as Result

import CASL.AS_Basic_CASL
import CASL.Sublogic as SL
import CASL.Sign
import CASL.Morphism
import CASL.Quantification
import CASL.ToDoc
import CASL.SimplifySen

import Logic.Prover

import Common.DocUtils
import Common.Id
import Common.ProofTree
import Common.Result

import qualified Data.Map as Map
import Data.Maybe
import Data.List

import Control.Monad.Error
import Control.Concurrent

import System.Timeout

import GUI.GenericATP

import Interfaces.GenericATPState

import Proofs.BatchProcessing

-- a qmodel is a certain term model used by QuickCheck
data QModel = QModel
        { sign :: CASLSign
        -- sentences determining the set of terms for a sort
        , carrierSens :: Map.Map SORT [CASLFORMULA]
        -- definitions of predicates and operations
        , predDefs :: Map.Map PRED_SYMB [([CASLTERM], CASLFORMULA)]
        , opDefs :: Map.Map OP_SYMB [([CASLTERM], CASLTERM)]
        -- currently evaluated items, for avoiding infinite recursion
        , evaluatedPreds :: [(PRED_SYMB, [CASLTERM])]
        , evaluatedOps :: [(OP_SYMB, [CASLTERM])]
        } deriving (Eq, Show)

{- |
  Run the QuickCheck service.
-}
runQuickCheck :: QModel
           -- ^ logical part containing the input Sign and axioms and possibly
           --   goals that have been proved earlier as additional axioms
           -> GenericConfig ProofTree -- ^ configuration to use
           -> Bool -- ^ True means save theory file
           -> String -- ^ name of the theory in the DevGraph
           -> AS_Anno.Named CASLFORMULA -- ^ goal to prove
           -> IO (ATPRetval, GenericConfig ProofTree)
           -- ^ (retval, configuration with proof status and complete output)
runQuickCheck qm cfg _saveFile _thName nGoal = do
  (stat,Result d res) <- case timeLimit cfg of
    Nothing -> return (ATPSuccess, quickCheck qm nGoal)
    Just t -> do
      mRes <- timeout (t * 1000000) $ return $ quickCheck qm nGoal
      return $ maybe (ATPTLimitExceeded,fail "time limit exceeded")
                     (\ x -> (ATPSuccess,x)) mRes
  let fstr = show(printTheoryFormula $ AS_Anno.mapNamed
                       (simplifySen dummyMin dummy (sign qm)) nGoal)
      showDiagStrings = intercalate "\n" . map diagString -- no final newline
      diagstr = case (res,d) of
        (Just True, _) -> showDiagStrings(take 10 d)
        (_, []) -> ""
        _ -> unlines ["Formula failed: ", fstr, " some Counterexamples: "]
             ++ showDiagStrings(take 10 d)
      gstat = case res of
        Just True -> Proved True
        Just False -> Disproved
        Nothing -> openGoalStatus
      setStatus pstat = pstat { goalStatus = gstat
                              , usedProver = "QuickCheck"
                              , proofTree = ProofTree diagstr }
      cfg' = cfg { proofStatus = setStatus (proofStatus cfg)
                 , resultOutput = [diagstr] }
  return (stat, cfg')
  -- return ATPError if time is up???

-- * QModels

-- | initial QModel
makeQm :: CASLSign -> QModel
makeQm sig = QModel { sign = sig
                    , carrierSens = Map.empty
                    , predDefs = Map.empty
                    , opDefs = Map.empty
                    , evaluatedPreds = []
                    , evaluatedOps = []
                    }

insertSens :: QModel -> [AS_Anno.Named CASLFORMULA] -> QModel
insertSens = foldl insertSen

-- | insert sentences into a QModel
insertSen :: QModel -> AS_Anno.Named CASLFORMULA -> QModel
insertSen qm sen = if not $ AS_Anno.isAxiom sen then qm else
  let f = AS_Anno.sentence sen
      qm1 = case f of
               -- sort generation constraint?
               Sort_gen_ax cs _ ->
                 let s = map (\ c -> (newSort c, [f])) cs
                     ins = foldr $ uncurry $ Map.insertWith (++)
                  in qm { carrierSens = ins (carrierSens qm) s }
               -- axiom forcing empty carrier?
               Quantification Universal [Var_decl [_] s _] (False_atom _) _ ->
                 qm { carrierSens = Map.insertWith (++) s [f] (carrierSens qm) }
               _ -> qm
      insertPred p args body q =
        q { predDefs = Map.insertWith (++) p [(args,body)] (predDefs q)}
      insertOp op args body q =
        q { opDefs = Map.insertWith (++) op [(args,body)] (opDefs q) }
  in case stripAllQuant f of
  -- insert a predicate or operation definition into a QModel
   Predication predsymb args _ ->
     insertPred predsymb args (True_atom nullRange) qm1
   Negation (Predication predsymb args _) _ ->
     insertPred predsymb args (False_atom nullRange) qm1
   Equivalence (Predication predsymb args _) body _ ->
     insertPred predsymb args body qm1
   Strong_equation (Application opsymb args _) body _ ->
     insertOp opsymb args body qm1
   Existl_equation (Application opsymb args _) body _ ->
     insertOp opsymb args body qm1
   -- treat equality as special predicate symbol, for detecting inequalities
   -- also exploit that inequality is symmetric
   Negation (Strong_equation t1 t2 _) _ ->
     insertPred eqSymb [t1,t2] (False_atom nullRange) $
       insertPred eqSymb [t2,t1] (False_atom nullRange) qm1
   Negation (Existl_equation t1 t2 _) _ ->
     insertPred eqSymb [t1,t2] (False_atom nullRange) $
       insertPred eqSymb [t2,t1] (False_atom nullRange) qm1
   _ -> qm1

-- | predicate symbol for equality (with dummy type)
eqSymb :: PRED_SYMB
eqSymb = Qual_pred_name eqId (Pred_type [] nullRange) nullRange

----------------------------------------------------------------------------
-- * Variable assignments

data VariableAssignment = VariableAssignment QModel [(VAR, CASLTERM)]
                          deriving Eq

instance Show VariableAssignment where
  show (VariableAssignment qm assignList) = showAssignments qm assignList

showAssignments :: QModel -> [(VAR, CASLTERM)] -> String
showAssignments qm xs =
  '[' : intercalate ", " (map (showSingleAssignment qm) xs) ++ "]"

showSingleAssignment :: QModel -> (VAR, CASLTERM) -> String
showSingleAssignment qm (v, t) =
  show v ++ "->" ++ showDoc (rmTypesT dummyMin dummy (sign qm) t) ""

emptyAssignment :: QModel -> VariableAssignment
emptyAssignment qm = VariableAssignment qm []

insertAssignment :: VariableAssignment -> (VAR, CASLTERM) -> VariableAssignment
insertAssignment (VariableAssignment qm ass) (v, t) =
  VariableAssignment qm ((v, t) : ass)

concatAssignment :: VariableAssignment -> VariableAssignment
                 -> VariableAssignment
concatAssignment (VariableAssignment qm l1) (VariableAssignment _ l2) =
  VariableAssignment qm $ l1 ++ l2

--------------------------------------------------------------------------
-- * The quickcheck model checker

quickCheck :: QModel -> AS_Anno.Named CASLFORMULA -> Result Bool
quickCheck qm =
  calculateFormula True qm (emptyAssignment qm) . AS_Anno.sentence

-- needed for instance Monad (Either ([Diagnosis], Maybe a))
-- in calculateQuantification
instance Error ([Diagnosis], Maybe a) where
  noMsg = ([], Nothing)
  strMsg x = ([Diag Error x nullRange], Nothing)

calculateTerm :: QModel -> VariableAssignment -> CASLTERM -> Result CASLTERM
calculateTerm qm ass trm = case trm of
    Qual_var var _ _ -> lookupVar var ass
    Application opSymb terms _ ->
              applyOperation qm ass opSymb terms
    Sorted_term term _ _ -> calculateTerm qm ass term
    Cast _ _ _ -> error "Cast not implemented"
    Conditional t1 fo t2 _ -> do
              res <- calculateFormula False qm ass fo
              if res then calculateTerm qm ass t1
                     else calculateTerm qm ass t2
    _ -> fail "unsopprted term"

lookupVar :: VAR -> VariableAssignment -> Result CASLTERM
lookupVar v (VariableAssignment _ ass) = case lookup v ass of
  Nothing -> fail ("no value for variable " ++ show v ++ " found")
  Just val -> return val

applyOperation :: QModel -> VariableAssignment -> OP_SYMB -> [CASLTERM]
               -> Result CASLTERM
applyOperation qm ass opsymb terms = do
  -- block infinite recursion
  when ((opsymb,terms) `elem` evaluatedOps qm)
       (fail ("infinite recursion when calculating"
              ++ show (Application opsymb terms nullRange)))
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
      (body,m) <- match bodies args $
                   showDoc (Application opsymb args nullRange) ""
      let ass' = foldl insertAssignment ass m
      -- evaluate body of operation definition
      calculateTerm qm' ass' body

-- | match a list of arguments (second parameter) against a
--   a a list of bodies (first argument), each coming with a
--   list of formal parameters and a body term or formula
match :: [([CASLTERM],a)] -> [CASLTERM] -> String
      -> Result (a, [(VAR, CASLTERM)])
match bodies args msg =
  case mapMaybe (match1 args) bodies of
    [] -> fail ("no matching found for " ++ msg)
    (subst:_) -> return subst

-- match against a single body
match1 :: [CASLTERM] -> ([CASLTERM], a) -> Maybe (a, [(VAR, CASLTERM)])
match1 args (vars, body) = do
  substs <- mapM (uncurry match2) (zip vars args)
  let subst = concat substs
  if consistent subst then return (body,subst) else Nothing

match2 :: CASLTERM -> CASLTERM -> Maybe [(VAR, CASLTERM)]
match2 (Qual_var v _ _) t = Just [(v, t)]
match2 (Application opsymb1 terms1 _) (Application opsymb2 terms2 _) =
   -- direct match of operation symbols?
   if opsymb1 == opsymb2 then do
     substs <- mapM (uncurry match2) (zip terms1 terms2)
     return (concat substs)
   --  if not, try to exploit overloading relation
    else do
      let (opsymb1', terms1', w1) = stripInj opsymb1 terms1
          (opsymb2', terms2', w2) = stripInj opsymb2 terms2
      when (opSymbName opsymb1' /= opSymbName opsymb2' || w1 /= w2) Nothing
      substs <- mapM (uncurry match2) (zip terms1' terms2')
      return (concat substs)
match2 (Sorted_term t1 _ _) t2 = match2 t1 t2
match2 t1 (Sorted_term t2 _ _) = match2 t1 t2
match2 _ _ = Nothing

-- | strip off the injections of an application
stripInj :: OP_SYMB -> [CASLTERM] -> (OP_SYMB, [CASLTERM], [SORT])
stripInj opsymb terms =
  let (opsymb', terms') =
        case (isInjName $ opSymbName opsymb, terms) of
          (True, [Application o ts _]) -> (o,ts)
          _ -> (opsymb,terms)
      strip1 t1@(Application o [t2] _) =
        if isInjName $ opSymbName o then t2 else t1
      strip1 t1 = t1
      terms'' = map strip1 terms'
  in (opsymb', terms'', map sortOfTerm terms'')

-- | is a substitution consistent with itself?
consistent :: [(VAR, CASLTERM)] -> Bool
consistent ass =
  isJust $ foldM insertAss Map.empty ass
  where
  insertAss m (v,t) =
    case Map.lookup v m of
      Just t1 -> if t == t1 then return m else Nothing
      Nothing -> Just $ Map.insert v t m

ternaryAnd :: (Result Bool, a) -> (Result Bool, a) -> (Result Bool, a)
ternaryAnd b1@(Result _ (Just False), _) _ = b1
ternaryAnd (Result d1 (Just True), _) (b2, x2) =
  (Result d1 (Just ()) >> b2, x2)
ternaryAnd (Result d1 Nothing, _) (b2@(Result _ (Just False)), x2) =
  (Result d1 (Just ()) >> b2, x2)
ternaryAnd (Result d1 Nothing, _) (b2, x2) =
  (Result d1 (Just ()) >> b2 >> Result [] Nothing, x2)

ternaryOr :: Result Bool -> Result Bool -> Result Bool
ternaryOr b1@(Result _ (Just True)) _ = b1
ternaryOr (Result d1 (Just False)) b2 = Result d1 (Just ()) >> b2
ternaryOr (Result d1 Nothing) b2@(Result _ (Just True)) =
  Result d1 (Just ()) >> b2
ternaryOr (Result d1 Nothing) b2 =
  Result d1 (Just ()) >> b2 >> Result [] Nothing

calculateFormula :: Bool -> QModel -> VariableAssignment -> CASLFORMULA
    -> Result Bool
calculateFormula isOuter qm varass f = case f of
    Quantification _ _ _ _ ->
       calculateQuantification isOuter qm varass f
    Conjunction formulas _ -> do
       let (res,f1) =
             foldl ternaryAnd (return True,f)
               (zip (map (calculateFormula False qm varass) formulas) formulas)
       when isOuter
          (case res of Result _ (Just False) ->
                        (warning () ("Conjunction not fulfilled\n"
                           ++"Formula that failed: "++showDoc f1 "") nullRange)
                       _ -> return ()
          )
       res
    Disjunction formulas _ ->
        foldl ternaryOr (return False)
               (map (calculateFormula False qm varass) formulas)
    Implication f1 f2 _ _ ->
        ternaryOr (fmap not (calculateFormula False qm varass f1))
                  (calculateFormula False qm varass f2)
    Equivalence f1 f2 _ -> do
        res1 <- calculateFormula False qm varass f1
        res2 <- calculateFormula False qm varass f2
        return (res1 == res2)
    Negation f1 _ ->
        fmap not $ calculateFormula False qm varass f1
    True_atom _ -> return True
    False_atom _ -> return False
    Strong_equation term1 term2 _ -> do
        t1 <- calculateTerm qm varass term1
        t2 <- calculateTerm qm varass term2
        equalElements qm t1 t2
    Existl_equation term1 term2 _ -> do
        t1 <- calculateTerm qm varass term1
        t2 <- calculateTerm qm varass term2
        equalElements qm t1 t2
    Predication predsymb terms _ ->
        applyPredicate qm varass predsymb terms
    _ -> fail $ "formula evaluation not implemented for: " ++ showDoc f ""

calculateQuantification :: Bool -> QModel -> VariableAssignment -> CASLFORMULA
                        -> Result Bool
calculateQuantification isOuter qm varass qf = case qf of
  Quantification quant vardecls f _ -> do
    assments <- generateVariableAssignments qm vardecls
    let assments' = map (flip concatAssignment varass) assments
    case quant of
      Universal -> do
        let resList = map (flip (calculateFormula False qm) f) assments'
            (res,fass) = foldl ternaryAnd (return True,emptyAssignment qm)
                                          (zip resList assments')
        when isOuter
          (case res of Result _ (Just False) ->
                        (warning () ("Universal quantification not fulfilled\n"
                           ++ "Counterexample: " ++ show fass) nullRange)
                       _ -> return ()
          )
        res
      Existential ->
        foldl ternaryOr (return False)
                        (map (flip (calculateFormula False qm) f) assments')
      Unique_existential -> do
        -- scan the assingments, stop scanning once the result is clear,
        -- using the Left constructor of the Either monad
        let combineEx1 (msgsSoFar,ass1) ass2 = do
              let Result msgs res = calculateFormula False qm ass2 f
              case (res, ass1) of
                -- the first fulfilment
                (Just True, Nothing) -> return (msgsSoFar ++ msgs, Just ass2)
                -- the second fulfilment
                (Just True, Just ass1') ->
                    Left (msgsSoFar ++ msgs, Just (ass1', ass2))
                -- not fulfilled? Then nothing changes
                (Just False, _) -> return (msgsSoFar ++ msgs, ass1)
                -- don't know? Then we don't know either
                (Nothing, _) -> Left (msgsSoFar ++ msgs, Nothing)
        case foldM combineEx1 ([], Nothing) assments' of
          Right (msgs, Just _) -> Result msgs (Just True)
          Right (msgs, Nothing) -> do
            Result msgs (Just ())
            when isOuter
              (warning () ("Unique Existential quantification"
                           ++ " not fulfilled: no assignment found") nullRange)
            return False
          Left (msgs, Just (ass1, ass2)) -> do
            Result msgs (Just ())
            when isOuter
              (warning () ("Unique Existential quantification"
                ++ " not fulfilled: at least two assignments found:\n"
                ++ show ass1 ++ "\n" ++ show ass2 ++"\n") nullRange)
            return False
          Left (msgs, Nothing) ->
            Result msgs Nothing
  _ -> fail "calculateQuantification wrongly applied"

applyPredicate :: QModel -> VariableAssignment -> PRED_SYMB -> [CASLTERM]
               -> Result Bool
applyPredicate qm ass predsymb terms = do
  -- block infinite recursion
  when (elem (predsymb, terms) $ evaluatedPreds qm)
       (fail ("infinite recursion when calculating"
              ++ show (Predication predsymb terms nullRange)))
  let qm' = qm { evaluatedPreds = (predsymb,terms):evaluatedPreds qm }
  -- evaluate argument terms
  args <- mapM (calculateTerm qm' ass) terms
  -- find appropriate predicate definition
  case Map.lookup predsymb (predDefs qm) of
    Nothing -> fail ("no predicate definition for " ++ showDoc predsymb "")
    Just bodies -> do
      -- bind formal to actual arguments
      (body,m) <- match bodies args $
                   showDoc (Predication predsymb args nullRange) ""
      let ass' = foldl insertAssignment ass m
      -- evaluate body of predicate definition
      calculateFormula False qm' ass' body

equalElements :: QModel -> CASLTERM -> CASLTERM -> Result Bool
equalElements qm t1 t2 =
  if t1 == t2 then return True
   else applyPredicate qm (emptyAssignment qm) eqSymb [t1, t2]

generateVariableAssignments :: QModel -> [VAR_DECL]
                            -> Result [VariableAssignment]
generateVariableAssignments qm vardecls = do
   let vars = flatVAR_DECLs vardecls
   carriers <- mapM (getCarrier qm . snd) vars
   let varsCarriers = zip (map fst vars) carriers
   return $ map (VariableAssignment qm) (gVAs varsCarriers)

gVAs :: [(VAR, [CASLTERM])] -> [[(VAR, CASLTERM)]]
gVAs [] = [[]]
gVAs ((v, carrier) : vs) = let
    rs = gVAs vs
    fs = map (\ b -> (v, b)) carrier
    in [f : r | f <- fs, r <- rs]


-- | check whether some formula leads to term generation of a sort
termSort :: CASLFORMULA -> Maybe (SORT, [CASLTERM])
-- sort generation constraint
termSort (Sort_gen_ax constr _) =
  case sorts of
     -- at the moment, we only treat one-sort constraints with constants
     [s] -> if all constant ops
             then Just (s,map mkTerm ops)
             else Nothing
     _ -> Nothing
    where (sorts, ops, _) = recover_Sort_gen_ax constr
          constant (Qual_op_name _ (Op_type _ [] _ _) _) = True
          constant _ = False
          mkTerm op = Application op [] nullRange
-- axiom forcing empty carrier
termSort (Quantification Universal [Var_decl [_] s _] (False_atom _) _) =
  Just (s, [])
termSort _ = Nothing

-- | get the carrier set for a specific sort
getCarrier:: QModel -> SORT -> Result [CASLTERM]
getCarrier qm s =
  case Map.lookup s (carrierSens qm) of
    Nothing -> fail ("sort "++show s++" is not generated")
    Just sens -> case mapMaybe termSort sens of
      [] -> fail ("sort "++show s++" is not generated by constants")
      (_, terms) : _ -> return terms
  -- todo: generalise this


----------------------------------------------------------------------------
-- * Interfacing to Hets prover interface

{- | The Prover implementation. First runs the batch prover (with
  graphical feedback), then starts the GUI prover.  -}
quickCheckProver :: Prover CASLSign CASLFORMULA CASLMor CASL_Sublogics ProofTree
quickCheckProver = mkAutomaticProver "QuickCheck"
  (SL.top { has_part = False, which_logic = SL.FOL })
  quickCheckGUI quickCheckCMDLautomaticBatch

{- |
  Record for prover specific functions. This is used by both GUI and command
  line interface.
-}

atpFun :: String -- ^ theory name
       -> ATPFunctions CASLSign CASLFORMULA CASLMor ProofTree QModel
atpFun _thName = ATPFunctions
    { initialProverState = \ sig sens _ -> insertSens (makeQm sig) sens,
      atpTransSenName = id,
      atpInsertSentence = insertSen,
      goalOutput = \ _ _ _ -> do
            putStrLn "No display of output yet"
            return "",
      proverHelpText =
        "QuickCheck tries to evaluate sentences in term generated models. " ++
        "This only works if your theory contains enough generated or " ++
        "freely generated datatypes.",
      batchTimeEnv = "HETS_SPASS_BATCH_TIME_LIMIT",
      fileExtensions = FileExtensions{problemOutput = ".none1",
                                      proverOutput = ".none2",
                                      theoryConfiguration = ".none3"},
      runProver = runQuickCheck,
      createProverOptions = const [] }

-- ** GUI

{- |
  Invokes the generic prover GUI. SPASS specific functions are omitted by
  data type ATPFunctions.
-}
quickCheckGUI :: String -- ^ theory name
           -> Theory CASLSign CASLFORMULA ProofTree
           -- ^ theory consisting of a signature
           --   and a list of named sentences
           -> [FreeDefMorphism CASLFORMULA CASLMor] -- ^ freeness constraints
           -> IO([ProofStatus ProofTree]) -- ^ proof status for each goal
quickCheckGUI thName th freedefs = genericATPgui (atpFun thName) True
    (proverName quickCheckProver) thName th freedefs emptyProofTree

-- ** command line function

{- |
  Implementation of 'Logic.Prover.proveCMDLautomaticBatch' which provides an
  automatic command line interface to the QuickCheck prover via MathServe.
  QuickCheck specific functions are omitted by data type ATPFunctions.
-}
quickCheckCMDLautomaticBatch ::
           Bool -- ^ True means include proved theorems
        -> Bool -- ^ True means save problem file
        -> MVar (Result.Result [ProofStatus ProofTree])
           -- ^ used to store the result of the batch run
        -> String -- ^ theory name
        -> TacticScript -- ^ default tactic script
        -> Theory CASLSign CASLFORMULA ProofTree -- ^ theory consisting of a
           --   signature and a list of named sentences
        -> [FreeDefMorphism CASLFORMULA CASLMor] -- ^ freeness constraints
        -> IO (ThreadId,MVar ())
           -- ^ fst: identifier of the batch thread for killing it
           --   snd: MVar to wait for the end of the thread
quickCheckCMDLautomaticBatch inclProvedThs saveProblem_batch resultMVar
                        thName defTS th freedefs =
    genericCMDLautomaticBatch (atpFun thName) inclProvedThs saveProblem_batch
        resultMVar (proverName quickCheckProver) thName
        (parseTacticScript batchTimeLimit [] defTS) th freedefs emptyProofTree
