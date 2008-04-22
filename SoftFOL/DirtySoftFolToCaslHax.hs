module SoftFOL.DirtySoftFolToCaslHax (transModel) where

import qualified Data.Set as Set
import qualified Data.Map as Map

import qualified SoftFOL.Sign as FS
import CASL.Sign 
import CASL.AS_Basic_CASL

import Common.DocUtils()
import Common.Id

world :: Id
world = stringToId "Object"

transModel :: [(String,FS.SPTerm)] -> (Sign () (),[(String,FORMULA ())])
transModel sps = 
    let
        (outSig, outForms) = unzip $ map (\x-> analyseTerm x (emptySign  ())) sps
        os                 = foldl uniteCASLSign (emptySign ()) outSig
    in
      (os, outForms)

analyseTerm :: (String,FS.SPTerm) -> (Sign () ()) -> (Sign () (), (String,FORMULA ()))
analyseTerm (name,trm) sig = (sig',(name,trm'))
  where (sig',trm') = analyseTermAux trm sig

analyseTermAux :: FS.SPTerm -> (Sign () ()) -> (Sign () (), FORMULA ())
analyseTermAux trm inSig = 
    case trm of
      FS.SPQuantTerm qnt vars term -> 
          let
              (so, fo) = analyseTermAux term inSig
              ov   = map (\x-> Var_decl [x] world nullRange) $ 
                     map (showUnqualified .snd) $ 
                     map (\x -> analyseAndOutputTerm x inSig) vars
          in
          case qnt of
            FS.SPForall -> (so, Quantification Universal ov fo nullRange)
            FS.SPExists -> (so, Quantification Existential ov fo nullRange)
            FS.SPCustomQuantSym _ -> error "You don't know the power of the dark side"
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
                    (s,f) = unzip $ map (\x -> analyseTermAux x inSig) term
                    os    = foldl uniteCASLSign inSig s
                in
                  (os, Disjunction f nullRange)
            FS.SPAnd    -> 
                let 
                    (s,f) = unzip $ map (\x -> analyseTermAux x inSig) term
                    os    = foldl uniteCASLSign inSig s
                in
                  (os, Conjunction f nullRange)
            FS.SPNot -> 
                let
                    (s1,f1) = analyseTermAux (head term) inSig
                in
                  (s1, Negation f1 nullRange)
            FS.SPImplies -> 
                let
                    (s1,f1) = analyseTermAux (head term) inSig
                    (s2,f2) = analyseTermAux (head $ tail term) inSig
                    os      = s1 `uniteCASLSign` s2
                in
                  (os, Implication f1 f2 True nullRange)
            FS.SPImplied -> 
                let
                    (s1,f1) = analyseTermAux (head term) inSig
                    (s2,f2) = analyseTermAux (head $ tail term) inSig
                    os      = s1 `uniteCASLSign` s2
                in
                  (os, Implication f2 f1 True nullRange)
            FS.SPEquiv -> 
                let
                    (s1,f1) = analyseTermAux (head term) inSig
                    (s2,f2) = analyseTermAux (head $ tail term) inSig
                    os      = s1 `uniteCASLSign` s2
                in
                  (os, Equivalence f2 f1 nullRange)
            FS.SPCustomSymbol tok ->
                let
                    (so,fo) = unzip $ map (\x -> analyseAndOutputTerm x inSig)
                              term
                    pt      = replicate (length fo) world
                    ps      = Qual_pred_name (simpleIdToId tok) 
                              (Pred_type pt nullRange) nullRange
                    newS    = (emptySign ())
                              {
                               predMap = Map.singleton (simpleIdToId tok) 
                                         (Set.singleton 
                                                 (PredType pt))
                              }
                    os      = inSig `uniteCASLSign` newS `uniteCASLSign` 
                              (foldl uniteCASLSign (emptySign ()) so)
                in
                  (os, Predication ps fo nullRange)
            _          -> error ("Symbol " ++ show sym ++ "not defined!")

analyseAndOutputTerm :: FS.SPTerm -> (Sign () ()) -> (Sign () (), TERM ())
analyseAndOutputTerm trm inSig = 
    case trm of
      FS.SPQuantTerm _ _ _ -> error "I am your father"
      FS.SPComplexTerm sym term ->                
          case sym of 
            FS.SPCustomSymbol tok ->
                let
                    (so,fo) = unzip $ map (\x -> analyseAndOutputTerm x inSig)
                              term
                    ot      = replicate (length fo) world
                    osy     = Qual_op_name (simpleIdToId tok) 
                              (Op_type Total ot world nullRange) nullRange
                    newS    = if isVar tok then emptySign ()
                              else (emptySign ())
                                   {
                                    opMap = Map.singleton (simpleIdToId tok) 
                                            (Set.singleton 
                                            (OpType Total ot world))
                                   }
                    os      = inSig `uniteCASLSign` newS `uniteCASLSign` 
                              (foldl uniteCASLSign (emptySign ()) so)
                in
                  (os, Application osy fo nullRange)
            FS.SPID -> 
                let 
                    vn = mkSimpleId $ show term
                in
                  (inSig, Qual_var vn world nullRange)
            _       -> error ("Symbol " ++ show sym ++ "not defined!")


isVar :: SIMPLE_ID -> Bool
isVar tok = let c = head $ tokStr tok
            in c>='A' && c<='Z' 

showUnqualified :: TERM f -> SIMPLE_ID
showUnqualified (Simple_id v) = v
showUnqualified (Qual_var v _ _) = v
showUnqualified (Application (Op_name o) [] _) = head $ getTokens o
showUnqualified (Application (Qual_op_name o _ _) [] _) = head $ getTokens o
showUnqualified _ = mkSimpleId "unknown"