{- |
  test module similar to GUI_tests, but tests CMDL functions
-}
module Main where 

import qualified Data.Map as Map 
import qualified Data.Set as Set 
import Common.Result

import GUI.GenericATPState

import Common.AS_Annotation
import qualified Logic.Prover as LProver

import SoftFOL.Sign
import SoftFOL.Prove
import SoftFOL.ProveVampire
import SoftFOL.ProveMathServ

import System.IO (stdout, hSetBuffering, BufferMode(NoBuffering))
import System.Environment (getArgs)
import System.Exit
import qualified Control.Concurrent as Concurrent

-- * Definitions of test theories

sign1 :: SoftFOL.Sign.Sign
sign1 = emptySign {sortMap = Map.insert "s" Nothing Map.empty,
                  predMap = Map.fromList (map (\ (x,y) -> (x, Set.singleton y) ) [("p",["s"]),("q",["s"]),("r",["s"]),("a",["s"])])}

term_x :: SPTerm 
term_x = SPSimpleTerm (SPCustomSymbol "X")

axiom1 :: Named SPTerm
axiom1 = makeNamed "ax" (SPQuantTerm SPForall [term_x] (SPComplexTerm SPEquiv [SPComplexTerm (SPCustomSymbol "p") [term_x],SPComplexTerm (SPCustomSymbol "q") [term_x]]))

axiom2 :: Named SPTerm
axiom2 = makeNamed "ax2" (SPQuantTerm SPForall [term_x] (SPComplexTerm SPImplies [SPComplexTerm (SPCustomSymbol "q") [term_x],SPComplexTerm (SPCustomSymbol "r") [term_x]]))

axiom3 :: Named SPTerm
axiom3 = makeNamed "b$$-3" (SPQuantTerm SPForall [term_x] (SPComplexTerm SPImplies [SPComplexTerm (SPCustomSymbol "q") [term_x],SPComplexTerm (SPCustomSymbol "a") [term_x]]))

goal1 :: Named SPTerm
goal1 = (makeNamed "go" $ SPQuantTerm SPForall [term_x] (SPComplexTerm SPImplies [SPComplexTerm (SPCustomSymbol "q") [term_x],SPComplexTerm (SPCustomSymbol "p") [term_x] ])) { isAxiom = False }

goal2 :: Named SPTerm
goal2 = (makeNamed "go2" $ SPQuantTerm SPForall [term_x] (SPComplexTerm SPImplies [SPComplexTerm (SPCustomSymbol "p") [term_x],SPComplexTerm (SPCustomSymbol "r") [term_x] ])) { isAxiom = False }

goal3 :: Named SPTerm
goal3 = (makeNamed "go3" $ SPQuantTerm SPForall [term_x] (SPComplexTerm SPImplies [SPComplexTerm (SPCustomSymbol "p") [term_x],SPComplexTerm (SPCustomSymbol "a") [term_x] ])) { isAxiom = False }


theory1 :: LProver.Theory SoftFOL.Sign.Sign SPTerm ATP_ProofTree
theory1 = (LProver.Theory sign1 $ LProver.toThSens [axiom1,-- axiom2,
                         goal1,goal2])

theory2 :: LProver.Theory SoftFOL.Sign.Sign SPTerm ATP_ProofTree
theory2 = (LProver.Theory sign1 $ LProver.toThSens [axiom1,axiom2,axiom3,
                         goal1,goal2,goal3])

-- A more complicated theory including ExtPartialOrder from Basic/RelationsAndOrders.casl

signExt :: SoftFOL.Sign.Sign
signExt = emptySign {sortMap = {- Map.insert "Elem" Nothing -} Map.empty,
            funcMap = Map.fromList (map (\ (x,y) -> (x, Set.singleton y))
                                    [("gn_bottom",([],"Elem")),
                                     ("inf",(["Elem", "Elem"],"Elem")),
                                     ("sup",(["Elem", "Elem"],"Elem"))]),
            predMap = Map.fromList (map (\ (x,y) -> (x, Set.singleton y))
                                        [ ("gn_defined",["Elem"]),
                                          ("p__LtEq__",["Elem", "Elem"])] )}

ga_nonEmpty :: Named SPTerm
ga_nonEmpty = makeNamed "ga_nonEmpty" SPQuantTerm {quantSym = SPExists, variableList = [SPSimpleTerm (SPCustomSymbol "X")], qFormula = SPComplexTerm {symbol = SPCustomSymbol "gn_defined", arguments = [SPSimpleTerm (SPCustomSymbol "X")]}}


ga_notDefBottom :: Named SPTerm
ga_notDefBottom = makeNamed "ga_notDefBottom" SPComplexTerm {symbol = SPNot, arguments = [SPComplexTerm {symbol = SPCustomSymbol "gn_defined", arguments = [SPComplexTerm {symbol = SPCustomSymbol "gn_bottom", arguments = []}]}]}

ga_strictness :: Named SPTerm
ga_strictness = makeNamed "ga_strictness" SPQuantTerm {quantSym = SPForall, variableList = [SPSimpleTerm (SPCustomSymbol "X_one"),SPSimpleTerm (SPCustomSymbol "X_two")], qFormula = SPComplexTerm {symbol = SPImplies, arguments = [SPComplexTerm {symbol = SPCustomSymbol "gn_defined", arguments = [SPComplexTerm {symbol = SPCustomSymbol "inf", arguments = [SPSimpleTerm (SPCustomSymbol "X_one"),SPSimpleTerm (SPCustomSymbol "X_two")]}]},SPComplexTerm {symbol = SPAnd, arguments = [SPComplexTerm {symbol = SPCustomSymbol "gn_defined", arguments = [SPSimpleTerm (SPCustomSymbol "X_one")]},SPComplexTerm {symbol = SPCustomSymbol "gn_defined", arguments = [SPSimpleTerm (SPCustomSymbol "X_two")]}]}]}}

ga_strictness_one :: Named SPTerm
ga_strictness_one = makeNamed "ga_strictness_one" SPQuantTerm {quantSym = SPForall, variableList = [SPSimpleTerm (SPCustomSymbol "X_one"),SPSimpleTerm (SPCustomSymbol "X_two")], qFormula = SPComplexTerm {symbol = SPImplies, arguments = [SPComplexTerm {symbol = SPCustomSymbol "gn_defined", arguments = [SPComplexTerm {symbol = SPCustomSymbol "sup", arguments = [SPSimpleTerm (SPCustomSymbol "X_one"),SPSimpleTerm (SPCustomSymbol "X_two")]}]},SPComplexTerm {symbol = SPAnd, arguments = [SPComplexTerm {symbol = SPCustomSymbol "gn_defined", arguments = [SPSimpleTerm (SPCustomSymbol "X_one")]},SPComplexTerm {symbol = SPCustomSymbol "gn_defined", arguments = [SPSimpleTerm (SPCustomSymbol "X_two")]}]}]}}

ga_predicate_strictness :: Named SPTerm
ga_predicate_strictness = makeNamed "ga_predicate_strictness" SPQuantTerm {quantSym = SPForall, variableList = [SPSimpleTerm (SPCustomSymbol "X_one"),SPSimpleTerm (SPCustomSymbol "X_two")], qFormula = SPComplexTerm {symbol = SPImplies, arguments = [SPComplexTerm {symbol = SPCustomSymbol "p__LtEq__", arguments = [SPSimpleTerm (SPCustomSymbol "X_one"),SPSimpleTerm (SPCustomSymbol "X_two")]},SPComplexTerm {symbol = SPAnd, arguments = [SPComplexTerm {symbol = SPCustomSymbol "gn_defined", arguments = [SPSimpleTerm (SPCustomSymbol "X_one")]},SPComplexTerm {symbol = SPCustomSymbol "gn_defined", arguments = [SPSimpleTerm (SPCustomSymbol "X_two")]}]}]}}

antisym :: Named SPTerm
antisym = makeNamed "antisym" SPQuantTerm {quantSym = SPForall, variableList = [SPSimpleTerm (SPCustomSymbol "X"),SPSimpleTerm (SPCustomSymbol "Y")], qFormula = SPComplexTerm {symbol = SPImplies, arguments = [SPComplexTerm {symbol = SPAnd, arguments = [SPComplexTerm {symbol = SPCustomSymbol "gn_defined", arguments = [SPSimpleTerm (SPCustomSymbol "X")]},SPComplexTerm {symbol = SPCustomSymbol "gn_defined", arguments = [SPSimpleTerm (SPCustomSymbol "Y")]}]},SPComplexTerm {symbol = SPImplies, arguments = [SPComplexTerm {symbol = SPAnd, arguments = [SPComplexTerm {symbol = SPCustomSymbol "p__LtEq__", arguments = [SPSimpleTerm (SPCustomSymbol "X"),SPSimpleTerm (SPCustomSymbol "Y")]},SPComplexTerm {symbol = SPCustomSymbol "p__LtEq__", arguments = [SPSimpleTerm (SPCustomSymbol "Y"),SPSimpleTerm (SPCustomSymbol "X")]}]},SPComplexTerm {symbol = SPEqual, arguments = [SPSimpleTerm (SPCustomSymbol "X"),SPSimpleTerm (SPCustomSymbol "Y")]}]}]}}

trans :: Named SPTerm
trans = makeNamed "trans" SPQuantTerm {quantSym = SPForall, variableList = [SPSimpleTerm (SPCustomSymbol "X"),SPSimpleTerm (SPCustomSymbol "Y"),SPSimpleTerm (SPCustomSymbol "Z")], qFormula = SPComplexTerm {symbol = SPImplies, arguments = [SPComplexTerm {symbol = SPAnd, arguments = [SPComplexTerm {symbol = SPAnd, arguments = [SPComplexTerm {symbol = SPCustomSymbol "gn_defined", arguments = [SPSimpleTerm (SPCustomSymbol "X")]},SPComplexTerm {symbol = SPCustomSymbol "gn_defined", arguments = [SPSimpleTerm (SPCustomSymbol "Y")]}]},SPComplexTerm {symbol = SPCustomSymbol "gn_defined", arguments = [SPSimpleTerm (SPCustomSymbol "Z")]}]},SPComplexTerm {symbol = SPImplies, arguments = [SPComplexTerm {symbol = SPAnd, arguments = [SPComplexTerm {symbol = SPCustomSymbol "p__LtEq__", arguments = [SPSimpleTerm (SPCustomSymbol "X"),SPSimpleTerm (SPCustomSymbol "Y")]},SPComplexTerm {symbol = SPCustomSymbol "p__LtEq__", arguments = [SPSimpleTerm (SPCustomSymbol "Y"),SPSimpleTerm (SPCustomSymbol "Z")]}]},SPComplexTerm {symbol = SPCustomSymbol "p__LtEq__", arguments = [SPSimpleTerm (SPCustomSymbol "X"),SPSimpleTerm (SPCustomSymbol "Z")]}]}]}}

refl :: Named SPTerm
refl = makeNamed "refl" SPQuantTerm {quantSym = SPForall, variableList = [SPSimpleTerm (SPCustomSymbol "X")], qFormula = SPComplexTerm {symbol = SPImplies, arguments = [SPComplexTerm {symbol = SPCustomSymbol "gn_defined", arguments = [SPSimpleTerm (SPCustomSymbol "X")]},SPComplexTerm {symbol = SPCustomSymbol "p__LtEq__", arguments = [SPSimpleTerm (SPCustomSymbol "X"),SPSimpleTerm (SPCustomSymbol "X")]}]}}

inf_def_ExtPartialOrder :: Named SPTerm
inf_def_ExtPartialOrder = makeNamed "inf_def_ExtPartialOrder" SPQuantTerm {quantSym = SPForall, variableList = [SPSimpleTerm (SPCustomSymbol "X"),SPSimpleTerm (SPCustomSymbol "Y"),SPSimpleTerm (SPCustomSymbol "Z")], qFormula = SPComplexTerm {symbol = SPImplies, arguments = [SPComplexTerm {symbol = SPAnd, arguments = [SPComplexTerm {symbol = SPAnd, arguments = [SPComplexTerm {symbol = SPCustomSymbol "gn_defined", arguments = [SPSimpleTerm (SPCustomSymbol "X")]},SPComplexTerm {symbol = SPCustomSymbol "gn_defined", arguments = [SPSimpleTerm (SPCustomSymbol "Y")]}]},SPComplexTerm {symbol = SPCustomSymbol "gn_defined", arguments = [SPSimpleTerm (SPCustomSymbol "Z")]}]},SPComplexTerm {symbol = SPEquiv, arguments = [SPComplexTerm {symbol = SPEqual, arguments = [SPComplexTerm {symbol = SPCustomSymbol "inf", arguments = [SPSimpleTerm (SPCustomSymbol "X"),SPSimpleTerm (SPCustomSymbol "Y")]},SPSimpleTerm (SPCustomSymbol "Z")]},SPComplexTerm {symbol = SPAnd, arguments = [SPComplexTerm {symbol = SPAnd, arguments = [SPComplexTerm {symbol = SPCustomSymbol "p__LtEq__", arguments = [SPSimpleTerm (SPCustomSymbol "Z"),SPSimpleTerm (SPCustomSymbol "X")]},SPComplexTerm {symbol = SPCustomSymbol "p__LtEq__", arguments = [SPSimpleTerm (SPCustomSymbol "Z"),SPSimpleTerm (SPCustomSymbol "Y")]}]},SPQuantTerm {quantSym = SPForall, variableList = [SPSimpleTerm (SPCustomSymbol "T")], qFormula = SPComplexTerm {symbol = SPImplies, arguments = [SPComplexTerm {symbol = SPCustomSymbol "gn_defined", arguments = [SPSimpleTerm (SPCustomSymbol "T")]},SPComplexTerm {symbol = SPImplies, arguments = [SPComplexTerm {symbol = SPAnd, arguments = [SPComplexTerm {symbol = SPCustomSymbol "p__LtEq__", arguments = [SPSimpleTerm (SPCustomSymbol "T"),SPSimpleTerm (SPCustomSymbol "X")]},SPComplexTerm {symbol = SPCustomSymbol "p__LtEq__", arguments = [SPSimpleTerm (SPCustomSymbol "T"),SPSimpleTerm (SPCustomSymbol "Y")]}]},SPComplexTerm {symbol = SPCustomSymbol "p__LtEq__", arguments = [SPSimpleTerm (SPCustomSymbol "T"),SPSimpleTerm (SPCustomSymbol "Z")]}]}]}}]}]}]}}

sup_def_ExtPartialOrder :: Named SPTerm
sup_def_ExtPartialOrder = makeNamed "sup_def_ExtPartialOrder" SPQuantTerm {quantSym = SPForall, variableList = [SPSimpleTerm (SPCustomSymbol "X"),SPSimpleTerm (SPCustomSymbol "Y"),SPSimpleTerm (SPCustomSymbol "Z")], qFormula = SPComplexTerm {symbol = SPImplies, arguments = [SPComplexTerm {symbol = SPAnd, arguments = [SPComplexTerm {symbol = SPAnd, arguments = [SPComplexTerm {symbol = SPCustomSymbol "gn_defined", arguments = [SPSimpleTerm (SPCustomSymbol "X")]},SPComplexTerm {symbol = SPCustomSymbol "gn_defined", arguments = [SPSimpleTerm (SPCustomSymbol "Y")]}]},SPComplexTerm {symbol = SPCustomSymbol "gn_defined", arguments = [SPSimpleTerm (SPCustomSymbol "Z")]}]},SPComplexTerm {symbol = SPEquiv, arguments = [SPComplexTerm {symbol = SPEqual, arguments = [SPComplexTerm {symbol = SPCustomSymbol "sup", arguments = [SPSimpleTerm (SPCustomSymbol "X"),SPSimpleTerm (SPCustomSymbol "Y")]},SPSimpleTerm (SPCustomSymbol "Z")]},SPComplexTerm {symbol = SPAnd, arguments = [SPComplexTerm {symbol = SPAnd, arguments = [SPComplexTerm {symbol = SPCustomSymbol "p__LtEq__", arguments = [SPSimpleTerm (SPCustomSymbol "X"),SPSimpleTerm (SPCustomSymbol "Z")]},SPComplexTerm {symbol = SPCustomSymbol "p__LtEq__", arguments = [SPSimpleTerm (SPCustomSymbol "Y"),SPSimpleTerm (SPCustomSymbol "Z")]}]},SPQuantTerm {quantSym = SPForall, variableList = [SPSimpleTerm (SPCustomSymbol "T")], qFormula = SPComplexTerm {symbol = SPImplies, arguments = [SPComplexTerm {symbol = SPCustomSymbol "gn_defined", arguments = [SPSimpleTerm (SPCustomSymbol "T")]},SPComplexTerm {symbol = SPImplies, arguments = [SPComplexTerm {symbol = SPAnd, arguments = [SPComplexTerm {symbol = SPCustomSymbol "p__LtEq__", arguments = [SPSimpleTerm (SPCustomSymbol "X"),SPSimpleTerm (SPCustomSymbol "T")]},SPComplexTerm {symbol = SPCustomSymbol "p__LtEq__", arguments = [SPSimpleTerm (SPCustomSymbol "Y"),SPSimpleTerm (SPCustomSymbol "T")]}]},SPComplexTerm {symbol = SPCustomSymbol "p__LtEq__", arguments = [SPSimpleTerm (SPCustomSymbol "Z"),SPSimpleTerm (SPCustomSymbol "T")]}]}]}}]}]}]}}

ga_comm_sup :: Named SPTerm
ga_comm_sup = (makeNamed "ga_comm_sup" SPQuantTerm {quantSym = SPForall, variableList = [SPSimpleTerm (SPCustomSymbol "X"),SPSimpleTerm (SPCustomSymbol "Y")], qFormula = SPComplexTerm {symbol = SPImplies, arguments = [SPComplexTerm {symbol = SPAnd, arguments = [SPComplexTerm {symbol = SPCustomSymbol "gn_defined", arguments = [SPSimpleTerm (SPCustomSymbol "X")]},SPComplexTerm {symbol = SPCustomSymbol "gn_defined", arguments = [SPSimpleTerm (SPCustomSymbol "Y")]}]},SPComplexTerm {symbol = SPEqual, arguments = [SPComplexTerm {symbol = SPCustomSymbol "sup", arguments = [SPSimpleTerm (SPCustomSymbol "X"),SPSimpleTerm (SPCustomSymbol "Y")]},SPComplexTerm {symbol = SPCustomSymbol "sup", arguments = [SPSimpleTerm (SPCustomSymbol "Y"),SPSimpleTerm (SPCustomSymbol "X")]}]}]}}) { isAxiom = False }

ga_comm_inf :: Named SPTerm
ga_comm_inf = (makeNamed "ga_comm_inf" SPQuantTerm {quantSym = SPForall, variableList = [SPSimpleTerm (SPCustomSymbol "X"),SPSimpleTerm (SPCustomSymbol "Y")], qFormula = SPComplexTerm {symbol = SPImplies, arguments = [SPComplexTerm {symbol = SPAnd, arguments = [SPComplexTerm {symbol = SPCustomSymbol "gn_defined", arguments = [SPSimpleTerm (SPCustomSymbol "X")]},SPComplexTerm {symbol = SPCustomSymbol "gn_defined", arguments = [SPSimpleTerm (SPCustomSymbol "Y")]}]},SPComplexTerm {symbol = SPEqual, arguments = [SPComplexTerm {symbol = SPCustomSymbol "inf", arguments = [SPSimpleTerm (SPCustomSymbol "X"),SPSimpleTerm (SPCustomSymbol "Y")]},SPComplexTerm {symbol = SPCustomSymbol "inf", arguments = [SPSimpleTerm (SPCustomSymbol "Y"),SPSimpleTerm (SPCustomSymbol "X")]}]}]}}) { isAxiom = False }

gone :: Named SPTerm
gone = (makeNamed "gone" $ SPSimpleTerm SPTrue) { isAxiom = False }

theoryExt :: LProver.Theory SoftFOL.Sign.Sign SPTerm ATP_ProofTree
theoryExt = (LProver.Theory signExt $ LProver.toThSens [ga_nonEmpty, ga_notDefBottom, ga_strictness, ga_strictness_one, ga_predicate_strictness, antisym, trans, refl, inf_def_ExtPartialOrder, sup_def_ExtPartialOrder, gone, ga_comm_sup, ga_comm_inf])

-- * Testing functions
main :: IO ()
main = do
     args <- getArgs
     hSetBuffering stdout NoBuffering
     if null args 
        then  runTests
        else runMathServTest

runMathServTest :: IO ()
runMathServTest = do
    pass1 <- 
        runTest mathServBrokerCMDLautomatic "MathServ" "[Test]Foo1" theory1 
                [("go",LProver.Proved Nothing)]
    pass2 <-
        runTest vampireCMDLautomatic "Vampire" "[Test]Foo1" theory1 
                [("go",LProver.Proved Nothing)]
    if pass1 && pass2 
       then exitWith ExitSuccess
       else exitWith (ExitFailure 9)
{- |
  Main function doing all tests (combinations of theory and prover) in a row.
  Outputs status lines with information whether test passed or failed.
-}
runTests :: IO ()
runTests = do
    runTest spassProveCMDLautomatic "SPASS" "[Test]Foo1" theory1 
                [("go",LProver.Proved Nothing)]
    runTest vampireCMDLautomatic "Vampire" "[Test]Foo1" theory1 
                [("go",LProver.Proved Nothing)]
    runTest mathServBrokerCMDLautomatic "MathServ" "[Test]Foo1" theory1 
                [("go",LProver.Proved Nothing)]

    runTest spassProveCMDLautomatic "SPASS" "[Test]Foo2" theory2 
                [("go",LProver.Proved Nothing)]
    runTest vampireCMDLautomatic "Vampire" "[Test]Foo2" theory2 
                [("go",LProver.Proved Nothing)]
    runTest mathServBrokerCMDLautomatic "MathServ" "[Test]Foo2" theory2 
                [("go",LProver.Proved Nothing)]

    runTest spassProveCMDLautomatic "SPASS" "[Test]ExtPartialOrder" theoryExt
                [("gone",LProver.Proved Nothing)]
    runTest vampireCMDLautomatic "Vampire" "[Test]ExtPartialOrder" theoryExt
                [("gone",LProver.Open)]
    runTest mathServBrokerCMDLautomatic "MathServ" 
                "[Test]ExtPartialOrder" theoryExt
                [("gone",LProver.Proved Nothing)]
    
    runTestBatch Nothing spassProveCMDLautomaticBatch "SPASS" 
                 "[Test]Foo1" theory1
                 [("go",LProver.Proved Nothing), 
                  ("go2",LProver.Disproved)]
    runTestBatch Nothing vampireCMDLautomaticBatch "Vampire" 
                 "[Test]Foo1" theory1
                 [("go",LProver.Proved Nothing), 
                  ("go2",LProver.Disproved)]
    runTestBatch Nothing mathServBrokerCMDLautomaticBatch "MathServ"
                 "[Test]Foo1" theory1
                 [("go",LProver.Proved Nothing), 
                  ("go2",LProver.Disproved)]

    runTestBatch Nothing spassProveCMDLautomaticBatch "SPASS" 
                 "[Test]Foo2" theory2
                 (zip ["go","go2","go3"] $ repeat (LProver.Proved Nothing))
    runTestBatch Nothing vampireCMDLautomaticBatch "Vampire" 
                 "[Test]Foo2" theory2
                 (zip ["go","go2","go3"] $ repeat (LProver.Proved Nothing))
    runTestBatch Nothing mathServBrokerCMDLautomaticBatch "MathServ"
                 "[Test]Foo2" theory2
                 (zip ["go","go2","go3"] $ repeat (LProver.Proved Nothing))

    runTestBatch (Just 12) spassProveCMDLautomaticBatch "SPASS"
                 "[Test]ExtPartialOrder" theoryExt
                 (("gone",LProver.Proved Nothing) : 
                  zip ["ga_comm_inf","ga_comm_sup"] (repeat LProver.Open))
    runTestBatch (Just 20) vampireCMDLautomaticBatch "Vampire"
                 "[Test]ExtPartialOrder" theoryExt
                  (zip ["gone","ga_comm_sup"] (repeat LProver.Open))
    runTestBatch (Just 20) mathServBrokerCMDLautomaticBatch "MathServ"
                 "[Test]ExtPartialOrder" theoryExt
                 (("gone",LProver.Proved Nothing) : 
                  zip ["ga_comm_inf","ga_comm_sup"] (repeat LProver.Open))

{- |
  Runs a CMDL automatic function (given as parameter) over a given theory.
  The result will be output as status message.
-}
runTest :: (String
            -> LProver.Tactic_script
            -> LProver.Theory Sign Sentence ATP_ProofTree
            -> IO (Result ([LProver.Proof_status ATP_ProofTree]))
           )
        -> String -- ^ prover name for proof status in case of error
        -> String -- ^ theory name
        -> LProver.Theory Sign Sentence ATP_ProofTree
        -> [(String,LProver.GoalStatus)] -- ^ list of expected results
        -> IO Bool
runTest runCMDLProver prName thName th expStatus = do
    putStr $ "Trying " ++ thName ++ "(automatic) with prover " ++ prName ++ " ... "
    m_result <- runCMDLProver
                           thName
                           (LProver.Tactic_script (show $ ATPTactic_script {
                              ts_timeLimit = 20, ts_extraOpts = [] }))
                           th
    stResult <- maybe (return [LProver.openProof_status "" 
                                         prName (ATP_ProofTree "")])
                      return (maybeResult m_result)
    putStrLn $ if (succeeded stResult expStatus)
                 then "passed" 
                 else ("failed\n"++ (unlines $ map show $ diags m_result))
    return (succeeded stResult expStatus)

{- |
  Runs a CMDL automatic batch function (given as parameter) over a given
  theory. The result will be output as status message.
-}
runTestBatch :: Maybe Int -- ^ seconds to pass before thread will be killed
              -> (Bool
                  -> Bool
                  -> Concurrent.MVar 
                       (Result [LProver.Proof_status ATP_ProofTree])
                  -> String
                  -> LProver.Tactic_script
                  -> LProver.Theory Sign Sentence ATP_ProofTree
                  -> IO (Concurrent.ThreadId,Concurrent.MVar ())
                 )
              -> String -- ^ prover name
              -> String -- ^ theory name
              -> LProver.Theory Sign Sentence ATP_ProofTree
              -> [(String,LProver.GoalStatus)] -- ^ list of expected results
              -> IO ()
runTestBatch waitsec runCMDLProver prName thName th expStatus = do
    putStr $ "Trying " ++ thName ++ "(automaticBatch) with prover " ++ 
             prName ++ " ... "
    resultMVar <- Concurrent.newMVar (return [])
    (threadID, mvar) <- runCMDLProver
                            False False resultMVar thName
                            (LProver.Tactic_script (show $ ATPTactic_script {
                               ts_timeLimit = 10, ts_extraOpts = [] })) 
                            th
    maybe (return ()) (\ ws -> do
             Concurrent.threadDelay (ws*1000000)
             Concurrent.killThread threadID) waitsec
    Concurrent.takeMVar mvar

    m_result <- Concurrent.takeMVar resultMVar
    stResult <- maybe (return [LProver.openProof_status ""
                                         prName (ATP_ProofTree "")])
                      return (maybeResult m_result)
    putStrLn $ if (succeeded stResult expStatus)
                 then "passed" 
                 else ("failed\n" ++ 
                       (unlines $ map show $ diags m_result)++"\n"++
                       (show m_result))

{- |
  Checks if a prover run's result matches expected result.
-}
succeeded :: [LProver.Proof_status ATP_ProofTree]
          -> [(String,LProver.GoalStatus)]
          -> Bool
succeeded stResult expStatus =
    (length stResult == length expStatus) 
    && (foldl (\b givenRes -> maybe False (==(LProver.goalStatus givenRes)) 
                                    (lookup (LProver.goalName givenRes) 
                                            expStatus) 
                              && b) 
              True stResult)
