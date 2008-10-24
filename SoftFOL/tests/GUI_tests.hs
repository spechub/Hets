
-- | some GUI tests to use from ghci
module GUI_tests where

import qualified Data.Map as Map
import qualified Data.Set as Set

import HTk (initHTk, withdrawMainWin,destroy)
import InfoBus (shutdown)

import Common.AS_Annotation
import Logic.Prover

import SoftFOL.Sign
import SoftFOL.Prove


printStatus :: IO [Proof_status ProofTree] -> IO ()
printStatus act = do st <- act
                     putStrLn (show st)

sign1 :: SoftFOL.Sign.Sign
sign1 = emptySign {sortMap = Map.insert "s" Nothing Map.empty,
                  predMap = Map.fromList (map (\ (x,y) -> (x, Set.singleton y) ) [("P",["s"]),("Q",["s"]),("R",["s"]),("A",["s"])])}

term_x :: SPTerm
term_x = SPSimpleTerm (SPCustomSymbol "x")

axiom1 :: Named SPTerm
axiom1 = NamedSen "Ax" True False (SPQuantTerm SPForall [term_x] (SPComplexTerm SPEquiv [SPComplexTerm (SPCustomSymbol "P") [term_x],SPComplexTerm (SPCustomSymbol "Q") [term_x]]))

axiom2 :: Named SPTerm
axiom2 = NamedSen "" True False (SPQuantTerm SPForall [term_x] (SPComplexTerm SPImplies [SPComplexTerm (SPCustomSymbol "Q") [term_x],SPComplexTerm (SPCustomSymbol "R") [term_x]]))

axiom3 :: Named SPTerm
axiom3 = NamedSen "B$$-3" True False (SPQuantTerm SPForall [term_x] (SPComplexTerm SPImplies [SPComplexTerm (SPCustomSymbol "Q") [term_x],SPComplexTerm (SPCustomSymbol "A") [term_x]]))

goal1 :: Named SPTerm
goal1 = NamedSen "Go" False False (SPQuantTerm SPForall [term_x] (SPComplexTerm SPImplies [SPComplexTerm (SPCustomSymbol "Q") [term_x],SPComplexTerm (SPCustomSymbol "P") [term_x] ]))

goal2 :: Named SPTerm
goal2 = NamedSen "Go2" False False (SPQuantTerm SPForall [term_x] (SPComplexTerm SPImplies [SPComplexTerm (SPCustomSymbol "P") [term_x],SPComplexTerm (SPCustomSymbol "R") [term_x] ]))

goal3 :: Named SPTerm
goal3 = NamedSen "Go2" False False (SPQuantTerm SPForall [term_x] (SPComplexTerm SPImplies [SPComplexTerm (SPCustomSymbol "P") [term_x],SPComplexTerm (SPCustomSymbol "A") [term_x] ]))


theory1 :: Theory SoftFOL.Sign.Sign SPTerm ProofTree
theory1 = (Theory sign1 $ toThSens [axiom1,-- axiom2,
                         goal1,goal2])

theory2 :: Theory SoftFOL.Sign.Sign SPTerm ProofTree
theory2 = (Theory sign1 $ toThSens [axiom1,axiom2,axiom3,
                         goal1,goal2,goal3])

runTest :: IO a -> IO a
runTest act =
    do initHTk [withdrawMainWin]
       r <- act
       -- destroy m
       return r

test1 :: IO ()
test1 = printStatus (runTest (spassProveGUI "Foo1" theory1))

test2 :: IO ()
test2 = printStatus (runTest (spassProveGUI "Foo2" theory2))

-- test1b :: IO ()
-- test1b = printStatus (spassProveBatch "Foo" theory1)
