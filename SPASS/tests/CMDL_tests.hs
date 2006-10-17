{- |
  test module similar to GUI_tests, but tests CMDL functions
-}
module CMDL_tests where 

import qualified Common.Lib.Map as Map 
import qualified Common.Lib.Set as Set 
import Common.Result
import qualified Control.Concurrent as Concurrent
import Data.IORef

import GUI.GenericATPState

import Common.AS_Annotation
import qualified Logic.Prover as LProver

import SPASS.Sign
import SPASS.Prove
import SPASS.ProveVampire
import SPASS.ProveMathServ

-- * Definitions of test theories

sign1 :: SPASS.Sign.Sign
sign1 = emptySign {sortMap = Map.insert "s" Nothing Map.empty,
                  predMap = Map.fromList (map (\ (x,y) -> (x, Set.singleton y) ) [("p",["s"]),("q",["s"]),("r",["s"]),("a",["s"])])}

term_x :: SPTerm 
term_x = SPSimpleTerm (SPCustomSymbol "X")

axiom1 :: Named SPTerm
axiom1 = NamedSen "ax" True False (SPQuantTerm SPForall [term_x] (SPComplexTerm SPEquiv [SPComplexTerm (SPCustomSymbol "p") [term_x],SPComplexTerm (SPCustomSymbol "q") [term_x]]))

axiom2 :: Named SPTerm
axiom2 = NamedSen "ax2" True False (SPQuantTerm SPForall [term_x] (SPComplexTerm SPImplies [SPComplexTerm (SPCustomSymbol "q") [term_x],SPComplexTerm (SPCustomSymbol "r") [term_x]]))

axiom3 :: Named SPTerm
axiom3 = NamedSen "b$$-3" True False (SPQuantTerm SPForall [term_x] (SPComplexTerm SPImplies [SPComplexTerm (SPCustomSymbol "q") [term_x],SPComplexTerm (SPCustomSymbol "a") [term_x]]))

goal1 :: Named SPTerm
goal1 = NamedSen "go" False False (SPQuantTerm SPForall [term_x] (SPComplexTerm SPImplies [SPComplexTerm (SPCustomSymbol "q") [term_x],SPComplexTerm (SPCustomSymbol "p") [term_x] ]))

goal2 :: Named SPTerm
goal2 = NamedSen "go2" False False (SPQuantTerm SPForall [term_x] (SPComplexTerm SPImplies [SPComplexTerm (SPCustomSymbol "p") [term_x],SPComplexTerm (SPCustomSymbol "r") [term_x] ]))

goal3 :: Named SPTerm
goal3 = NamedSen "go3" False False (SPQuantTerm SPForall [term_x] (SPComplexTerm SPImplies [SPComplexTerm (SPCustomSymbol "p") [term_x],SPComplexTerm (SPCustomSymbol "a") [term_x] ]))


theory1 :: LProver.Theory SPASS.Sign.Sign SPTerm ATP_ProofTree
theory1 = (LProver.Theory sign1 $ LProver.toThSens [axiom1,-- axiom2,
                         goal1,goal2])

theory2 :: LProver.Theory SPASS.Sign.Sign SPTerm ATP_ProofTree
theory2 = (LProver.Theory sign1 $ LProver.toThSens [axiom1,axiom2,axiom3,
                         goal1,goal2,goal3])

-- A more complicated theory including ExtPartialOrder from Basic/RelationsAndOrders.casl

signExt :: SPASS.Sign.Sign
signExt = emptySign {sortMap = {- Map.insert "Elem" Nothing -} Map.empty,
            funcMap = Map.fromList (map (\ (x,y) -> (x, Set.singleton y))
                                    [("gn_bottom",([],"Elem")),
                                     ("inf",(["Elem", "Elem"],"Elem")),
                                     ("sup",(["Elem", "Elem"],"Elem"))]),
            predMap = Map.fromList (map (\ (x,y) -> (x, Set.singleton y))
                                        [ ("gn_defined",["Elem"]),
                                          ("p__LtEq__",["Elem", "Elem"])] )}

ga_nonEmpty :: Named SPTerm
ga_nonEmpty = NamedSen {senName = "ga_nonEmpty", isAxiom = True, isDef = False, sentence = SPQuantTerm {quantSym = SPExists, variableList = [SPSimpleTerm (SPCustomSymbol "X")], qFormula = SPComplexTerm {symbol = SPCustomSymbol "gn_defined", arguments = [SPSimpleTerm (SPCustomSymbol "X")]}}}


ga_notDefBottom :: Named SPTerm
ga_notDefBottom = NamedSen {senName = "ga_notDefBottom", isAxiom = True, isDef = False, sentence = SPComplexTerm {symbol = SPNot, arguments = [SPComplexTerm {symbol = SPCustomSymbol "gn_defined", arguments = [SPComplexTerm {symbol = SPCustomSymbol "gn_bottom", arguments = []}]}]}}

ga_strictness :: Named SPTerm
ga_strictness = NamedSen {senName = "ga_strictness", isAxiom = True, isDef = False, sentence = SPQuantTerm {quantSym = SPForall, variableList = [SPSimpleTerm (SPCustomSymbol "X_one"),SPSimpleTerm (SPCustomSymbol "X_two")], qFormula = SPComplexTerm {symbol = SPImplies, arguments = [SPComplexTerm {symbol = SPCustomSymbol "gn_defined", arguments = [SPComplexTerm {symbol = SPCustomSymbol "inf", arguments = [SPSimpleTerm (SPCustomSymbol "X_one"),SPSimpleTerm (SPCustomSymbol "X_two")]}]},SPComplexTerm {symbol = SPAnd, arguments = [SPComplexTerm {symbol = SPCustomSymbol "gn_defined", arguments = [SPSimpleTerm (SPCustomSymbol "X_one")]},SPComplexTerm {symbol = SPCustomSymbol "gn_defined", arguments = [SPSimpleTerm (SPCustomSymbol "X_two")]}]}]}}}

ga_strictness_one :: Named SPTerm
ga_strictness_one = NamedSen {senName = "ga_strictness_one", isAxiom = True, isDef = False, sentence = SPQuantTerm {quantSym = SPForall, variableList = [SPSimpleTerm (SPCustomSymbol "X_one"),SPSimpleTerm (SPCustomSymbol "X_two")], qFormula = SPComplexTerm {symbol = SPImplies, arguments = [SPComplexTerm {symbol = SPCustomSymbol "gn_defined", arguments = [SPComplexTerm {symbol = SPCustomSymbol "sup", arguments = [SPSimpleTerm (SPCustomSymbol "X_one"),SPSimpleTerm (SPCustomSymbol "X_two")]}]},SPComplexTerm {symbol = SPAnd, arguments = [SPComplexTerm {symbol = SPCustomSymbol "gn_defined", arguments = [SPSimpleTerm (SPCustomSymbol "X_one")]},SPComplexTerm {symbol = SPCustomSymbol "gn_defined", arguments = [SPSimpleTerm (SPCustomSymbol "X_two")]}]}]}}}

ga_predicate_strictness :: Named SPTerm
ga_predicate_strictness = NamedSen {senName = "ga_predicate_strictness", isAxiom = True, isDef = False, sentence = SPQuantTerm {quantSym = SPForall, variableList = [SPSimpleTerm (SPCustomSymbol "X_one"),SPSimpleTerm (SPCustomSymbol "X_two")], qFormula = SPComplexTerm {symbol = SPImplies, arguments = [SPComplexTerm {symbol = SPCustomSymbol "p__LtEq__", arguments = [SPSimpleTerm (SPCustomSymbol "X_one"),SPSimpleTerm (SPCustomSymbol "X_two")]},SPComplexTerm {symbol = SPAnd, arguments = [SPComplexTerm {symbol = SPCustomSymbol "gn_defined", arguments = [SPSimpleTerm (SPCustomSymbol "X_one")]},SPComplexTerm {symbol = SPCustomSymbol "gn_defined", arguments = [SPSimpleTerm (SPCustomSymbol "X_two")]}]}]}}}

antisym :: Named SPTerm
antisym = NamedSen {senName = "antisym", isAxiom = True, isDef = False, sentence = SPQuantTerm {quantSym = SPForall, variableList = [SPSimpleTerm (SPCustomSymbol "X"),SPSimpleTerm (SPCustomSymbol "Y")], qFormula = SPComplexTerm {symbol = SPImplies, arguments = [SPComplexTerm {symbol = SPAnd, arguments = [SPComplexTerm {symbol = SPCustomSymbol "gn_defined", arguments = [SPSimpleTerm (SPCustomSymbol "X")]},SPComplexTerm {symbol = SPCustomSymbol "gn_defined", arguments = [SPSimpleTerm (SPCustomSymbol "Y")]}]},SPComplexTerm {symbol = SPImplies, arguments = [SPComplexTerm {symbol = SPAnd, arguments = [SPComplexTerm {symbol = SPCustomSymbol "p__LtEq__", arguments = [SPSimpleTerm (SPCustomSymbol "X"),SPSimpleTerm (SPCustomSymbol "Y")]},SPComplexTerm {symbol = SPCustomSymbol "p__LtEq__", arguments = [SPSimpleTerm (SPCustomSymbol "Y"),SPSimpleTerm (SPCustomSymbol "X")]}]},SPComplexTerm {symbol = SPEqual, arguments = [SPSimpleTerm (SPCustomSymbol "X"),SPSimpleTerm (SPCustomSymbol "Y")]}]}]}}}

trans :: Named SPTerm
trans = NamedSen {senName = "trans", isAxiom = True, isDef = False, sentence = SPQuantTerm {quantSym = SPForall, variableList = [SPSimpleTerm (SPCustomSymbol "X"),SPSimpleTerm (SPCustomSymbol "Y"),SPSimpleTerm (SPCustomSymbol "Z")], qFormula = SPComplexTerm {symbol = SPImplies, arguments = [SPComplexTerm {symbol = SPAnd, arguments = [SPComplexTerm {symbol = SPAnd, arguments = [SPComplexTerm {symbol = SPCustomSymbol "gn_defined", arguments = [SPSimpleTerm (SPCustomSymbol "X")]},SPComplexTerm {symbol = SPCustomSymbol "gn_defined", arguments = [SPSimpleTerm (SPCustomSymbol "Y")]}]},SPComplexTerm {symbol = SPCustomSymbol "gn_defined", arguments = [SPSimpleTerm (SPCustomSymbol "Z")]}]},SPComplexTerm {symbol = SPImplies, arguments = [SPComplexTerm {symbol = SPAnd, arguments = [SPComplexTerm {symbol = SPCustomSymbol "p__LtEq__", arguments = [SPSimpleTerm (SPCustomSymbol "X"),SPSimpleTerm (SPCustomSymbol "Y")]},SPComplexTerm {symbol = SPCustomSymbol "p__LtEq__", arguments = [SPSimpleTerm (SPCustomSymbol "Y"),SPSimpleTerm (SPCustomSymbol "Z")]}]},SPComplexTerm {symbol = SPCustomSymbol "p__LtEq__", arguments = [SPSimpleTerm (SPCustomSymbol "X"),SPSimpleTerm (SPCustomSymbol "Z")]}]}]}}}

refl :: Named SPTerm
refl = NamedSen {senName = "refl", isAxiom = True, isDef = False, sentence = SPQuantTerm {quantSym = SPForall, variableList = [SPSimpleTerm (SPCustomSymbol "X")], qFormula = SPComplexTerm {symbol = SPImplies, arguments = [SPComplexTerm {symbol = SPCustomSymbol "gn_defined", arguments = [SPSimpleTerm (SPCustomSymbol "X")]},SPComplexTerm {symbol = SPCustomSymbol "p__LtEq__", arguments = [SPSimpleTerm (SPCustomSymbol "X"),SPSimpleTerm (SPCustomSymbol "X")]}]}}}

inf_def_ExtPartialOrder :: Named SPTerm
inf_def_ExtPartialOrder = NamedSen {senName = "inf_def_ExtPartialOrder", isAxiom = True, isDef = False, sentence = SPQuantTerm {quantSym = SPForall, variableList = [SPSimpleTerm (SPCustomSymbol "X"),SPSimpleTerm (SPCustomSymbol "Y"),SPSimpleTerm (SPCustomSymbol "Z")], qFormula = SPComplexTerm {symbol = SPImplies, arguments = [SPComplexTerm {symbol = SPAnd, arguments = [SPComplexTerm {symbol = SPAnd, arguments = [SPComplexTerm {symbol = SPCustomSymbol "gn_defined", arguments = [SPSimpleTerm (SPCustomSymbol "X")]},SPComplexTerm {symbol = SPCustomSymbol "gn_defined", arguments = [SPSimpleTerm (SPCustomSymbol "Y")]}]},SPComplexTerm {symbol = SPCustomSymbol "gn_defined", arguments = [SPSimpleTerm (SPCustomSymbol "Z")]}]},SPComplexTerm {symbol = SPEquiv, arguments = [SPComplexTerm {symbol = SPEqual, arguments = [SPComplexTerm {symbol = SPCustomSymbol "inf", arguments = [SPSimpleTerm (SPCustomSymbol "X"),SPSimpleTerm (SPCustomSymbol "Y")]},SPSimpleTerm (SPCustomSymbol "Z")]},SPComplexTerm {symbol = SPAnd, arguments = [SPComplexTerm {symbol = SPAnd, arguments = [SPComplexTerm {symbol = SPCustomSymbol "p__LtEq__", arguments = [SPSimpleTerm (SPCustomSymbol "Z"),SPSimpleTerm (SPCustomSymbol "X")]},SPComplexTerm {symbol = SPCustomSymbol "p__LtEq__", arguments = [SPSimpleTerm (SPCustomSymbol "Z"),SPSimpleTerm (SPCustomSymbol "Y")]}]},SPQuantTerm {quantSym = SPForall, variableList = [SPSimpleTerm (SPCustomSymbol "T")], qFormula = SPComplexTerm {symbol = SPImplies, arguments = [SPComplexTerm {symbol = SPCustomSymbol "gn_defined", arguments = [SPSimpleTerm (SPCustomSymbol "T")]},SPComplexTerm {symbol = SPImplies, arguments = [SPComplexTerm {symbol = SPAnd, arguments = [SPComplexTerm {symbol = SPCustomSymbol "p__LtEq__", arguments = [SPSimpleTerm (SPCustomSymbol "T"),SPSimpleTerm (SPCustomSymbol "X")]},SPComplexTerm {symbol = SPCustomSymbol "p__LtEq__", arguments = [SPSimpleTerm (SPCustomSymbol "T"),SPSimpleTerm (SPCustomSymbol "Y")]}]},SPComplexTerm {symbol = SPCustomSymbol "p__LtEq__", arguments = [SPSimpleTerm (SPCustomSymbol "T"),SPSimpleTerm (SPCustomSymbol "Z")]}]}]}}]}]}]}}}

sup_def_ExtPartialOrder :: Named SPTerm
sup_def_ExtPartialOrder = NamedSen {senName = "sup_def_ExtPartialOrder", isAxiom = True, isDef = False, sentence = SPQuantTerm {quantSym = SPForall, variableList = [SPSimpleTerm (SPCustomSymbol "X"),SPSimpleTerm (SPCustomSymbol "Y"),SPSimpleTerm (SPCustomSymbol "Z")], qFormula = SPComplexTerm {symbol = SPImplies, arguments = [SPComplexTerm {symbol = SPAnd, arguments = [SPComplexTerm {symbol = SPAnd, arguments = [SPComplexTerm {symbol = SPCustomSymbol "gn_defined", arguments = [SPSimpleTerm (SPCustomSymbol "X")]},SPComplexTerm {symbol = SPCustomSymbol "gn_defined", arguments = [SPSimpleTerm (SPCustomSymbol "Y")]}]},SPComplexTerm {symbol = SPCustomSymbol "gn_defined", arguments = [SPSimpleTerm (SPCustomSymbol "Z")]}]},SPComplexTerm {symbol = SPEquiv, arguments = [SPComplexTerm {symbol = SPEqual, arguments = [SPComplexTerm {symbol = SPCustomSymbol "sup", arguments = [SPSimpleTerm (SPCustomSymbol "X"),SPSimpleTerm (SPCustomSymbol "Y")]},SPSimpleTerm (SPCustomSymbol "Z")]},SPComplexTerm {symbol = SPAnd, arguments = [SPComplexTerm {symbol = SPAnd, arguments = [SPComplexTerm {symbol = SPCustomSymbol "p__LtEq__", arguments = [SPSimpleTerm (SPCustomSymbol "X"),SPSimpleTerm (SPCustomSymbol "Z")]},SPComplexTerm {symbol = SPCustomSymbol "p__LtEq__", arguments = [SPSimpleTerm (SPCustomSymbol "Y"),SPSimpleTerm (SPCustomSymbol "Z")]}]},SPQuantTerm {quantSym = SPForall, variableList = [SPSimpleTerm (SPCustomSymbol "T")], qFormula = SPComplexTerm {symbol = SPImplies, arguments = [SPComplexTerm {symbol = SPCustomSymbol "gn_defined", arguments = [SPSimpleTerm (SPCustomSymbol "T")]},SPComplexTerm {symbol = SPImplies, arguments = [SPComplexTerm {symbol = SPAnd, arguments = [SPComplexTerm {symbol = SPCustomSymbol "p__LtEq__", arguments = [SPSimpleTerm (SPCustomSymbol "X"),SPSimpleTerm (SPCustomSymbol "T")]},SPComplexTerm {symbol = SPCustomSymbol "p__LtEq__", arguments = [SPSimpleTerm (SPCustomSymbol "Y"),SPSimpleTerm (SPCustomSymbol "T")]}]},SPComplexTerm {symbol = SPCustomSymbol "p__LtEq__", arguments = [SPSimpleTerm (SPCustomSymbol "Z"),SPSimpleTerm (SPCustomSymbol "T")]}]}]}}]}]}]}}}

ga_comm_sup :: Named SPTerm
ga_comm_sup = NamedSen {senName = "ga_comm_sup", isAxiom = False, isDef = False, sentence = SPQuantTerm {quantSym = SPForall, variableList = [SPSimpleTerm (SPCustomSymbol "X"),SPSimpleTerm (SPCustomSymbol "Y")], qFormula = SPComplexTerm {symbol = SPImplies, arguments = [SPComplexTerm {symbol = SPAnd, arguments = [SPComplexTerm {symbol = SPCustomSymbol "gn_defined", arguments = [SPSimpleTerm (SPCustomSymbol "X")]},SPComplexTerm {symbol = SPCustomSymbol "gn_defined", arguments = [SPSimpleTerm (SPCustomSymbol "Y")]}]},SPComplexTerm {symbol = SPEqual, arguments = [SPComplexTerm {symbol = SPCustomSymbol "sup", arguments = [SPSimpleTerm (SPCustomSymbol "X"),SPSimpleTerm (SPCustomSymbol "Y")]},SPComplexTerm {symbol = SPCustomSymbol "sup", arguments = [SPSimpleTerm (SPCustomSymbol "Y"),SPSimpleTerm (SPCustomSymbol "X")]}]}]}}}

ga_comm_inf :: Named SPTerm
ga_comm_inf = NamedSen {senName = "ga_comm_inf", isAxiom = False, isDef = False, sentence = SPQuantTerm {quantSym = SPForall, variableList = [SPSimpleTerm (SPCustomSymbol "X"),SPSimpleTerm (SPCustomSymbol "Y")], qFormula = SPComplexTerm {symbol = SPImplies, arguments = [SPComplexTerm {symbol = SPAnd, arguments = [SPComplexTerm {symbol = SPCustomSymbol "gn_defined", arguments = [SPSimpleTerm (SPCustomSymbol "X")]},SPComplexTerm {symbol = SPCustomSymbol "gn_defined", arguments = [SPSimpleTerm (SPCustomSymbol "Y")]}]},SPComplexTerm {symbol = SPEqual, arguments = [SPComplexTerm {symbol = SPCustomSymbol "inf", arguments = [SPSimpleTerm (SPCustomSymbol "X"),SPSimpleTerm (SPCustomSymbol "Y")]},SPComplexTerm {symbol = SPCustomSymbol "inf", arguments = [SPSimpleTerm (SPCustomSymbol "Y"),SPSimpleTerm (SPCustomSymbol "X")]}]}]}}}

gone :: Named SPTerm
gone = NamedSen {senName = "gone", isAxiom = False, isDef = False, sentence = SPSimpleTerm SPTrue}


theoryExt :: LProver.Theory SPASS.Sign.Sign SPTerm ATP_ProofTree
theoryExt = (LProver.Theory signExt $ LProver.toThSens [ga_nonEmpty, ga_notDefBottom, ga_strictness, ga_strictness_one, ga_predicate_strictness, antisym, trans, refl, inf_def_ExtPartialOrder, sup_def_ExtPartialOrder, gone, ga_comm_sup, ga_comm_inf])

-- * Testing functions

{- |
  Runs a CMDL automatic function (given as parameter) and returns its
  result after being run with given test theory.
-}
runTest :: String -- ^ prover name for proof status in case of error
        -> (String
            -> LProver.Tactic_script
            -> LProver.Theory Sign Sentence ATP_ProofTree
            -> IO (Result ([LProver.Proof_status ATP_ProofTree]))
           )
        -> String -- ^ theory name
        -> LProver.Theory Sign Sentence ATP_ProofTree
        -> IO [LProver.Proof_status ATP_ProofTree]
runTest prName runCMDLProver thName th = 
    do result <- runCMDLProver
                              thName
                              (LProver.Tactic_script (show $ ATPTactic_script {
                                 ts_timeLimit = 20, ts_extraOpts = [] }))
                              th
       maybe (return [LProver.openProof_status "" prName (ATP_ProofTree "")])
             return
             (maybeResult result)

{- |
  Runs a CMDL automatic batch function (given as parameter) and returns its
  result after being run with given test theory.
-}
runTestBatch :: Maybe Int -- ^ seconds to pass before thread will be killed
        -> String -- ^ prover name for proof status in case of error
        -> (Bool
            -> Bool
            -> IORef (Result [LProver.Proof_status ATP_ProofTree])
            -> String
            -> LProver.Tactic_script
            -> LProver.Theory Sign Sentence ATP_ProofTree
            -> IO (Concurrent.ThreadId,Concurrent.MVar ())
           )
        -> String -- ^ theory name
        -> LProver.Theory Sign Sentence ATP_ProofTree
        -> IO [LProver.Proof_status ATP_ProofTree]
runTestBatch waitsec prName runCMDLProver thName th = 
    do resultRef <- newIORef (Result { diags = [], maybeResult = Just [] })
       (threadID, mvar) <- runCMDLProver
                               True True resultRef thName
                               (LProver.Tactic_script (show $ ATPTactic_script {
                                  ts_timeLimit = 10, ts_extraOpts = [] }))
                               th
       maybe (return ()) (\ ws -> do
                Concurrent.threadDelay (ws*1000000)
                Concurrent.killThread threadID) waitsec
       Concurrent.takeMVar mvar

       result <- readIORef resultRef
       maybe (return [LProver.openProof_status "" prName (ATP_ProofTree "")])
             return
             (maybeResult result)

{- |
  Main function doing all tests (combinations of theory and prover) in a row.
  Outputs status lines with information whether test passed or failed.
-}
runTests :: IO ()
runTests = do
    runProveTest Nothing spassProveCMDLautomaticBatch "SPASS" "Foo1" theory1
                 [LProver.Proved (Nothing), LProver.Disproved]
    runProveTest Nothing vampireCMDLautomaticBatch "Vampire" "Foo1" theory1
                 [LProver.Proved (Nothing), LProver.Disproved]
    runProveTest Nothing mathServBrokerCMDLautomaticBatch "MathServ"
                 "Foo1" theory1
                 [LProver.Proved (Nothing), LProver.Disproved]

    runProveTest Nothing spassProveCMDLautomaticBatch "SPASS" "Foo2" theory2
                 [LProver.Proved (Nothing), LProver.Proved (Nothing),
                  LProver.Proved (Nothing)]
    runProveTest Nothing vampireCMDLautomaticBatch "Vampire" "Foo2" theory2
                 [LProver.Proved (Nothing), LProver.Proved (Nothing),
                  LProver.Proved (Nothing)]
    runProveTest Nothing mathServBrokerCMDLautomaticBatch "MathServ"
                 "Foo2" theory2
                 [LProver.Proved (Nothing), LProver.Proved (Nothing),
                  LProver.Proved (Nothing)]

    runProveTest (Just 12) spassProveCMDLautomaticBatch "SPASS"
                 "ExtPartialOrder" theoryExt
                 [LProver.Proved (Nothing), LProver.Open, LProver.Open]
    runProveTest (Just 20) vampireCMDLautomaticBatch "Vampire"
                 "ExtPartialOrder" theoryExt
                 [LProver.Open, LProver.Open, LProver.Open]
    runProveTest (Just 20) mathServBrokerCMDLautomaticBatch "MathServ"
                 "ExtPartialOrder" theoryExt
                 [LProver.Proved (Nothing), LProver.Open, LProver.Open]

                  
{- |
  A single test run of a CMDL batch function running over a given theory.
  Result will be output as status message.
-}
runProveTest :: Maybe Int -- ^ seconds to pass before thread will be killed
              -> (Bool
                  -> Bool
                  -> IORef (Result [LProver.Proof_status ATP_ProofTree])
                  -> String
                  -> LProver.Tactic_script
                  -> LProver.Theory Sign Sentence ATP_ProofTree
                  -> IO (Concurrent.ThreadId,Concurrent.MVar ())
                 )
              -> String -- ^ prover name
              -> String -- ^ theory name
              -> LProver.Theory Sign Sentence ATP_ProofTree
              -> [LProver.GoalStatus] -- ^ list of expected results
              -> IO ()
runProveTest waitsec prFun prName thName th expStatus = do
    putStr $ "Trying " ++ thName ++ " with prover " ++ prName ++ " ... "
    stResult <- runTestBatch waitsec prName prFun thName th
    putStrLn $ if (succeeded stResult expStatus)
                 then "passed" else "failed"
    
{- |
  Checks if a prover run's result matches expected result.
-}
succeeded :: [LProver.Proof_status ATP_ProofTree]
          -> [LProver.GoalStatus]
          -> Bool
succeeded stResult expStatus =
    (length stResult == length expStatus)
    && (foldl (\b (given, expected) -> if (given == expected) then b else False)
              True
              (zip (map (\s -> LProver.goalStatus s) stResult) expStatus))
