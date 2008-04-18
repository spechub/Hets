module SoftFOL.DirtySoftFolToCaslHax where

import qualified SoftFOL.Sign as FS
import CASL.Sign 
import CASL.AS_Basic_CASL

import Common.Id

transModel :: [FS.SPTerm] -> (Sign () (),[FORMULA ()])
transModel sps = 
    let
        outSig = emptySign ()
    in
      (outSig, [])

analyseTerm :: FS.SPTerm -> (Sign () ()) -> (Sign () (), FORMULA ())
analyseTerm trm inSig = 
    let
        outSig = inSig
    in
    case trm of
      FS.SPQuantTerm qnt vars term -> error ""
      FS.SPComplexTerm sym term    ->
          case sym of
            FS.SPEqual -> 
                let
                    (s1,f1) = analyseAndOutputTerm (head term) inSig
                    (s2,f2) = analyseAndOutputTerm (head $ tail term) inSig
                    os      = s1 `uniteCASLSign` s2
                in
                  (os, Strong_equation f1 f2 nullRange)
            FS.SPTrue  -> (inSig, True_atom nullRange)
            FS.SPFalse -> (inSig, False_atom nullRange)
            FS.SPOr    -> 
                let 
                    (s,f) = unzip $ map (\x -> analyseTerm x inSig) term
                    os    = foldl uniteCASLSign inSig s
                in
                  (os, Disjunction f nullRange)
            FS.SPAnd    -> 
                let 
                    (s,f) = unzip $ map (\x -> analyseTerm x inSig) term
                    os    = foldl uniteCASLSign inSig s
                in
                  (os, Conjunction f nullRange)
            FS.SPNot -> 
                let
                    (s1,f1) = analyseTerm (head term) inSig
                in
                  (s1, Negation f1 nullRange)
            FS.SPImplies -> 
                let
                    (s1,f1) = analyseTerm (head term) inSig
                    (s2,f2) = analyseTerm (head $ tail term) inSig
                    os      = s1 `uniteCASLSign` s2
                in
                  (os, Implication f1 f2 True nullRange)
            FS.SPImplied -> 
                let
                    (s1,f1) = analyseTerm (head term) inSig
                    (s2,f2) = analyseTerm (head $ tail term) inSig
                    os      = s1 `uniteCASLSign` s2
                in
                  (os, Implication f2 f1 True nullRange)
            FS.SPEquiv -> 
                let
                    (s1,f1) = analyseTerm (head term) inSig
                    (s2,f2) = analyseTerm (head $ tail term) inSig
                    os      = s1 `uniteCASLSign` s2
                in
                  (os, Equivalence f2 f1 nullRange)
            _          -> error ("Symbol " ++ show sym ++ "not defined!")

analyseAndOutputTerm :: FS.SPTerm -> (Sign () ()) -> (Sign () (), TERM ())
analyseAndOutputTerm trm inSig = error ""
