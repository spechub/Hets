{- |
Module      :  Comorphisms/CASL_DL2CASL.hs
Description :  Inclusion of CASL_DL into CASL
Copyright   :  (c) Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (via Logic.Logic)

-}

module Comorphisms.CASL_DL2CASL
    (
     CASL_DL2CASL(..)
    )
    where

import Logic.Logic
import Logic.Comorphism
import Common.Id
import qualified Data.Set as Set
import qualified Common.Lib.Rel as Rel
import qualified Data.Map as Map
import Common.AS_Annotation
import Data.List
import Common.Result
import CASL_DL.PredefinedCASLAxioms

--CASL_DL = domain
import CASL_DL.Logic_CASL_DL
import CASL_DL.AS_CASL_DL
import CASL_DL.Sign()
import CASL_DL.PredefinedSign
import CASL_DL.StatAna -- DLSign
import CASL_DL.PredefinedSign
import CASL_DL.Sublogics

--CASL = codomain
import CASL.Logic_CASL
import CASL.AS_Basic_CASL
import CASL.Sign
import CASL.Morphism
import CASL.Sublogic as Sublogic

data CASL_DL2CASL = CASL_DL2CASL deriving Show

instance Language CASL_DL2CASL

instance Comorphism
    CASL_DL2CASL    -- comorphism
    CASL_DL         -- lid domain
    CASL_DL_SL      -- sublogics domain
    DL_BASIC_SPEC   -- Basic spec domain
    DLFORMULA       -- sentence domain
    SYMB_ITEMS      -- symbol items domain
    SYMB_MAP_ITEMS  -- symbol map items domain
    DLSign          -- signature domain
    DLMor           -- morphism domain
    Symbol          -- symbol domain
    RawSymbol       -- rawsymbol domain
    Q_ProofTree     -- proof tree codomain
    CASL            -- lid codomain
    CASL_Sublogics  -- sublogics codomain
    CASLBasicSpec   -- Basic spec codomain
    CASLFORMULA     -- sentence codomain
    SYMB_ITEMS      -- symbol items codomain
    SYMB_MAP_ITEMS  -- symbol map items codomain
    CASLSign        -- signature codomain
    CASLMor         -- morphism codomain
    Symbol          -- symbol codomain
    RawSymbol       -- rawsymbol codomain
    Q_ProofTree     -- proof tree domain
    where
      sourceLogic CASL_DL2CASL    = CASL_DL
      targetLogic CASL_DL2CASL    = CASL
      sourceSublogic CASL_DL2CASL = SROIQ
      mapSublogic CASL_DL2CASL _  = Just $ Sublogic.caslTop
                      { sub_features = LocFilSub
                      , cons_features = emptyMapConsFeature }
      map_symbol  CASL_DL2CASL s  = Set.singleton s
      map_sentence CASL_DL2CASL   = trSentence
      map_morphism CASL_DL2CASL   = mapMor
      map_theory   CASL_DL2CASL   = trTheory
      isInclusionComorphism CASL_DL2CASL = True
      has_model_expansion CASL_DL2CASL = True

-- ^ mapping of morphims, we just forget the
-- ^ additional features
mapMor :: DLMor -> Result CASLMor
mapMor inMor =
    let
        ms = trSign $ msource inMor
        mt = trSign $ mtarget inMor
        sm = sort_map inMor
        fm = fun_map inMor
        pm = pred_map inMor
    in return (embedMorphism () ms mt)
        { sort_map = sm
        , fun_map = fm
        , pred_map = pm }

-- ^ we forget additional information in the signature
projectToCASL :: DLSign -> CASLSign
projectToCASL dls = dls
                    {
                      sentences = []
                    , extendedInfo = ()
                    }

-- ^ Thing is established as the TopSort of all sorts
-- ^ defined in the CASL_DL spec, a predefined signature
-- ^ is added
trSign :: DLSign -> CASLSign
trSign inSig =
    let
        inC = (makeCardResSignature $ projectToCASL inSig) `uniteCASLSign` predefSign
        inSorts  = sortSet inSig
        inData   = sortSet dataSig_CASL
    in
      inC
      {
        sortSet = Set.insert topSort $  Set.insert topSortD $ sortSet inC,
        sortRel =
                  Set.fold (\x -> Rel.insert x topSortD)
                  (Set.fold (\x -> Rel.insert x topSort)
                   (sortRel inC) inSorts) $
                  Set.delete topSortD inData
      }

-- ^ this adds the signature for cardinality restrictions
makeCardResSignature :: CASLSign -> CASLSign
makeCardResSignature cSign =
    let
        pm = predMap cSign
    in
      Map.foldWithKey (\k a b -> uniteCASLSign (addCardResOps k a) b) cSign pm


addCardResOps :: Id -> Set.Set PredType -> Sign () ()
addCardResOps myId spt =
    let
        inOps  = map (\x -> addCardResOp myId x)
                 $ filter (\x -> (length $ predArgs x) == 2) $ Set.toList spt
    in
      foldl (uniteCASLSign) (emptySign ()) inOps


-- ^ this adds the axioms for cardinality restrictions
makeCardAxioms :: CASLSign -> [(Named (FORMULA()))] -> [(Named (FORMULA()))]
makeCardAxioms cSign cAxs =
    let
        pm = predMap cSign
    in
      Map.foldWithKey (\k a b -> (++) (addCardResAxx k a) b) cAxs pm

addCardResAxx :: Id -> Set.Set PredType -> [(Named (FORMULA()))]
addCardResAxx myId spt =
    let
        inOps  = map (\x -> addCardResAx myId x)
                 $ filter (\x -> (length $ predArgs x) == 2) $ Set.toList spt
    in
      foldl (++) [] inOps

-- ^ translation of the signature
-- ^ predefined axioms are added
rtrSign :: DLSign -> Result CASLSign
rtrSign inSig = return $ trSign inSig

-- Translation of theories
trTheory :: (DLSign, [Named (FORMULA DL_FORMULA)]) ->
            Result (CASLSign, [Named (FORMULA ())])
trTheory (inSig, inForms) =
    do
      outForms <- mapR (\x -> trNamedSentence inSig x) inForms
      outSig <- rtrSign inSig
      return (outSig, predefinedAxioms ++ (makeCardAxioms (projectToCASL inSig) outForms))

-- ^ translation of named sentences
trNamedSentence :: DLSign -> Named (FORMULA DL_FORMULA) ->
                   Result (Named (FORMULA ()))
trNamedSentence inSig inForm =
    let
        inAttL = senAttr inForm
        isAxL  = isAxiom inForm
        isDefL = isDef   inForm
        wasThL = wasTheorem inForm
        simpAL = simpAnno inForm
        inSenL = sentence inForm
    in
      do
        outSen <- trSentence inSig inSenL
        return SenAttr
               {
                  senAttr = inAttL
               ,  isAxiom = isAxL
               ,  isDef   = isDefL
               ,  wasTheorem = wasThL
               ,  simpAnno = simpAL
               ,  sentence = outSen
               }


-- ^ translation of sentences
trSentence ::  DLSign -> FORMULA DL_FORMULA -> Result (FORMULA ())
trSentence inSig inF =
      case inF of
        Quantification qf vs frm rn ->
            do
              outF <- trSentence inSig frm
              return (Quantification qf vs (outF) rn)
        Conjunction fns rn ->
            do
              outF <- mapR (\x -> trSentence inSig x) fns
              return (Conjunction outF rn)
        Disjunction fns rn ->
            do
              outF <- mapR (\x -> trSentence inSig x) fns
              return (Disjunction outF rn)
        Implication f1 f2 b rn ->
            do
              out1 <- trSentence inSig f1
              out2 <- trSentence inSig f2
              return (Implication out1 out2 b rn)
        Equivalence f1 f2 rn ->
            do
              out1 <- trSentence inSig f1
              out2 <- trSentence inSig f2
              return (Equivalence out1 out2 rn)
        Negation frm rn ->
            do
              outF <- trSentence inSig frm
              return (Negation outF rn)
        True_atom rn -> do return (True_atom rn)
        False_atom rn -> do return (False_atom rn)
        Predication pr trm rn ->
            do
              ot <- mapR (\x -> trTerm inSig x) trm
              return (Predication pr ot rn)
        Definedness tm rn ->
            do
              ot <- trTerm inSig tm
              return (Definedness ot rn)
        Existl_equation t1 t2 rn ->
            do
              ot1 <- trTerm inSig t1
              ot2 <- trTerm inSig t2
              return (Existl_equation ot1 ot2 rn)
        Strong_equation t1 t2 rn ->
            do
              ot1 <- trTerm inSig t1
              ot2 <- trTerm inSig t2
              return (Strong_equation ot1 ot2 rn)
        Membership t1 st rn ->
            do
              ot <- trTerm inSig t1
              return (Membership ot st rn)
        Mixfix_formula trm ->
             do
              ot <- trTerm inSig trm
              return (Mixfix_formula ot)
        Unparsed_formula str rn ->
            do return (Unparsed_formula str rn)
        Sort_gen_ax cstr ft ->
            do return (Sort_gen_ax cstr ft)
        ExtFORMULA form ->
            case form of
              Cardinality CExact ps trm1 trm2 Nothing _ -> makeEqCardinality inSig ps trm1 trm2
              Cardinality CMin ps trm1 trm2 Nothing _ ->   makeMinCardinality inSig ps trm1 trm2
              Cardinality CMax ps trm1 trm2 Nothing _ ->   makeMaxCardinality inSig ps trm1 trm2
              _ -> fatal_error "Mapping for qualified cardinality expressions not yet implemented" nullRange

makeMinCardinality :: DLSign
                -> PRED_SYMB
                -> TERM DL_FORMULA
                -> TERM DL_FORMULA
                -> Result (FORMULA ())
makeMinCardinality inSig ps trm1 trm2 =
                let
                   (pn, pt) =
                      case ps of
                        Pred_name _ -> error "I sense a disturbance in the force during analysis"
                        Qual_pred_name pname ptype _ -> (pname, ptype)
                   gn_Subject = case pt of Pred_type lst _ -> head $ lst
                   gn_Object  = case pt of Pred_type lst _ -> head $ tail $ lst
               in
                do
                 tv  <- trTerm inSig trm1
                 cnt <- trTerm inSig trm2
                 return $ (Implication
                    (Definedness
                       (Application
                          (Qual_op_name
                             (Id{getTokens =
                                   [Token{tokStr = "gn_setOfPred", tokPos = nullRange},
                                    Token{tokStr = "__", tokPos = nullRange}],
                                 getComps =
                                   [pn],
                                 rangeOfId = nullRange})
                             (Op_type Partial
                                [gn_Subject]
                                (Id{getTokens = [Token{tokStr = "gn_Set", tokPos = nullRange}],
                                    getComps =
                                      [gn_Object],
                                    rangeOfId = nullRange})
                                nullRange)
                             nullRange)
                          [tv]
                          nullRange)
                       nullRange)
                    (Predication
                       (Qual_pred_name
                          (Id{getTokens =
                                [Token{tokStr = "__", tokPos = nullRange},
                                 Token{tokStr = ">=", tokPos = nullRange},
                                 Token{tokStr = "__", tokPos = nullRange}],
                              getComps = [], rangeOfId = nullRange})
                          (Pred_type
                             [Id{getTokens =
                                   [Token{tokStr = "nonNegativeInteger", tokPos = nullRange}],
                                 getComps = [], rangeOfId = nullRange},
                              Id{getTokens =
                                   [Token{tokStr = "nonNegativeInteger", tokPos = nullRange}],
                                 getComps = [], rangeOfId = nullRange}]
                             nullRange)
                          nullRange)
                       [Application
                          (Qual_op_name
                             (Id{getTokens =
                                   [Token{tokStr = "gn_card", tokPos = nullRange},
                                    Token{tokStr = "__", tokPos = nullRange}],
                                 getComps = [], rangeOfId = nullRange})
                             (Op_type Total
                                [Id{getTokens = [Token{tokStr = "gn_Set", tokPos = nullRange}],
                                    getComps =
                                      [gn_Object],
                                    rangeOfId = nullRange}]
                                (Id{getTokens =
                                      [Token{tokStr = "nonNegativeInteger", tokPos = nullRange}],
                                    getComps = [], rangeOfId = nullRange})
                                nullRange)
                             nullRange)
                          [Application
                             (Qual_op_name
                                (Id{getTokens =
                                      [Token{tokStr = "gn_setOfPred", tokPos = nullRange},
                                       Token{tokStr = "__", tokPos = nullRange}],
                                    getComps =
                                      [pn],
                                    rangeOfId = nullRange})
                                (Op_type Partial
                                   [gn_Subject]
                                   (Id{getTokens = [Token{tokStr = "gn_Set", tokPos = nullRange}],
                                       getComps =
                                         [gn_Object],
                                       rangeOfId = nullRange})
                                   nullRange)
                                nullRange)
                             [tv]
                             nullRange]
                          nullRange,
                       cnt]
                       nullRange)
                    True
                    nullRange)

makeEqCardinality :: DLSign
                -> PRED_SYMB
                -> TERM DL_FORMULA
                -> TERM DL_FORMULA
                -> Result (FORMULA ())
makeEqCardinality inSig ps trm1 trm2 =
                let
                   (pn, pt) =
                      case ps of
                        Pred_name _ -> error "I sense a disturbance in the force during analysis"
                        Qual_pred_name pname ptype _ -> (pname, ptype)
                   gn_Subject = case pt of Pred_type lst _ -> head $ lst
                   gn_Object  = case pt of Pred_type lst _ -> head $ tail $ lst
               in
                do
                 tv  <- trTerm inSig trm1
                 cnt <- trTerm inSig trm2
                 return $ (Strong_equation
                    (Application
                       (Qual_op_name
                          (Id{getTokens =
                                [Token{tokStr = "gn_card", tokPos = nullRange},
                                 Token{tokStr = "__", tokPos = nullRange}],
                              getComps = [], rangeOfId = nullRange})
                          (Op_type Total
                             [Id{getTokens = [Token{tokStr = "gn_Set", tokPos = nullRange}],
                                 getComps =
                                   [gn_Object],
                                 rangeOfId = nullRange}]
                             (Id{getTokens =
                                   [Token{tokStr = "nonNegativeInteger", tokPos = nullRange}],
                                 getComps = [], rangeOfId = nullRange})
                             nullRange)
                          nullRange)
                       [Application
                          (Qual_op_name
                             (Id{getTokens =
                                   [Token{tokStr = "gn_setOfPred", tokPos = nullRange},
                                    Token{tokStr = "__", tokPos = nullRange}],
                                 getComps =
                                   [pn],
                                 rangeOfId = nullRange})
                             (Op_type Partial
                                [gn_Subject]
                                (Id{getTokens = [Token{tokStr = "gn_Set", tokPos = nullRange}],
                                    getComps =
                                      [gn_Object],
                                    rangeOfId = nullRange})
                                nullRange)
                             nullRange)
                          [tv]
                          nullRange]
                       nullRange)
                    (cnt)
                    nullRange)

-- ^ predefined axioms for cardinality restrictions
makeMaxCardinality :: DLSign
                -> PRED_SYMB
                -> TERM DL_FORMULA
                -> TERM DL_FORMULA
                -> Result (FORMULA ())
makeMaxCardinality inSig ps trm1 trm2 =
                let
                   (pn, pt) =
                      case ps of
                        Pred_name _ -> error "I sense a disturbance in the force during analysis"
                        Qual_pred_name pname ptype _ -> (pname, ptype)
                   gn_Subject = case pt of Pred_type lst _ -> head $ lst
                   gn_Object  = case pt of Pred_type lst _ -> head $ tail $ lst
               in
                do
                 tv  <- trTerm inSig trm1
                 cnt <- trTerm inSig trm2
                 return $ (Predication
                    (Qual_pred_name
                       (Id{getTokens =
                             [Token{tokStr = "__", tokPos = nullRange},
                              Token{tokStr = "<=", tokPos = nullRange},
                              Token{tokStr = "__", tokPos = nullRange}],
                           getComps = [], rangeOfId = nullRange})
                       (Pred_type
                          [Id{getTokens =
                                [Token{tokStr = "nonNegativeInteger", tokPos = nullRange}],
                              getComps = [], rangeOfId = nullRange},
                           Id{getTokens =
                                [Token{tokStr = "nonNegativeInteger", tokPos = nullRange}],
                              getComps = [], rangeOfId = nullRange}]
                          nullRange)
                       nullRange)
                    [Application
                       (Qual_op_name
                          (Id{getTokens =
                                [Token{tokStr = "gn_card", tokPos = nullRange},
                                 Token{tokStr = "__", tokPos = nullRange}],
                              getComps = [], rangeOfId = nullRange})
                          (Op_type Total
                             [Id{getTokens = [Token{tokStr = "gn_Set", tokPos = nullRange}],
                                 getComps =
                                   [gn_Object],
                                 rangeOfId = nullRange}]
                             (Id{getTokens =
                                   [Token{tokStr = "nonNegativeInteger", tokPos = nullRange}],
                                 getComps = [], rangeOfId = nullRange})
                             nullRange)
                          nullRange)
                       [Application
                          (Qual_op_name
                             (Id{getTokens =
                                   [Token{tokStr = "gn_setOfPred", tokPos = nullRange},
                                    Token{tokStr = "__", tokPos = nullRange}],
                                 getComps =
                                   [pn],
                                 rangeOfId = nullRange})
                             (Op_type Partial
                                [gn_Subject]
                                (Id{getTokens = [Token{tokStr = "gn_Set", tokPos = nullRange}],
                                    getComps =
                                      [gn_Object],
                                    rangeOfId = nullRange})
                                nullRange)
                             nullRange)
                          [tv]
                          nullRange]
                       nullRange,
                    cnt]
                    nullRange)

-- ^ translation of terms
trTerm :: DLSign -> TERM DL_FORMULA -> Result (TERM ())
trTerm inSig inF =
    case inF of
      Simple_id sid -> return (Simple_id sid)
      Qual_var v s rn -> return (Qual_var v s rn)
      Application os tms rn ->
          do
            ot <- mapR (\x -> trTerm inSig x) tms
            return (Application os ot rn)
      Sorted_term trm st rn ->
          do
            ot <- trTerm inSig trm
            return (Sorted_term ot st rn)
      Cast trm st rn ->
          do
            ot <- trTerm inSig trm
            return (Cast ot st rn)
      Conditional t1 frm t2 rn ->
          do
            ot1 <- trTerm inSig t1
            ot2 <- trTerm inSig t2
            of1 <- trSentence inSig frm
            return (Conditional ot1 of1 ot2 rn)
      Unparsed_term str rn -> do return (Unparsed_term str rn)
      Mixfix_qual_pred ps  -> do return (Mixfix_qual_pred ps)
      Mixfix_term trm      ->
          do
            ot <- mapR (\x -> trTerm inSig x) trm
            return (Mixfix_term ot)
      Mixfix_token tok     -> do return (Mixfix_token tok)
      Mixfix_sorted_term st rn -> do return (Mixfix_sorted_term st rn)
      Mixfix_cast st rn    -> do return (Mixfix_cast st rn)
      Mixfix_parenthesized trm rn ->
          do
            ot <- mapR (\x -> trTerm inSig x) trm
            return (Mixfix_parenthesized ot rn)
      Mixfix_bracketed trm rn ->
          do
            ot <- mapR (\x -> trTerm inSig x) trm
            return (Mixfix_bracketed ot rn)
      Mixfix_braced trm rn ->
          do
            ot <-  mapR (\x -> trTerm inSig x) trm
            return (Mixfix_braced ot rn)

-- ^ a lot of predefined code for cardinality restrictions,
-- ^ the predefined natural numbers are used here
addCardResOp :: Id -> PredType -> Sign () ()
addCardResOp gn_predicate pt =
    let
        gn_Subject = head $ predArgs pt
        gn_Object = head $ tail $ predArgs pt
    in
      (emptySign ()){sortSet =
                     Set.fromList
                       [Id [Token "gn_Set" nullRange]
                          [gn_Object]
                          nullRange],
                   sortRel = Rel.fromList [],
                   opMap =
                     Map.fromList
                       [(Id [Token "gn_card" nullRange, Token "__" nullRange] []
                           nullRange,
                         Set.fromList
                           [OpType Total
                              [Id [Token "gn_Set" nullRange]
                                 [gn_Object]
                                 nullRange]
                              (Id [Token "nonNegativeInteger" nullRange] [] nullRange)]),
                        (Id [Token "gn_eset" nullRange] [] nullRange,
                         Set.fromList
                           [OpType Total []
                              (Id [Token "gn_Set" nullRange]
                                 [gn_Object]
                                 nullRange)]),
                        (Id [Token "gn_insert" nullRange] [] nullRange,
                         Set.fromList
                           [OpType Total
                              [Id [Token "gn_Set" nullRange]
                                 [gn_Object]
                                 nullRange,
                              gn_Object]
                              (Id [Token "gn_Set" nullRange]
                                 [gn_Object]
                                 nullRange)]),
                        (Id [Token "gn_setOfPred" nullRange, Token "__" nullRange]
                           [gn_predicate]
                           nullRange,
                         Set.fromList
                           [OpType Partial [gn_Subject]
                              (Id [Token "gn_Set" nullRange]
                                 [gn_Object]
                                 nullRange)])],
                   assocOps = Map.fromList [],
                   predMap =
                     Map.fromList
                       [(Id [Token "gn_contained" nullRange] [] nullRange,
                         Set.fromList
                           [PredType
                              [gn_Object,
                               Id [Token "gn_Set" nullRange]
                                 [gn_Object]
                                 nullRange]]),
                        (gn_predicate,
                         Set.fromList
                           [PredType
                              [gn_Subject,
                               gn_Object]])]}

addCardResAx :: Id -> PredType -> [(Named (FORMULA()))]
addCardResAx predicate pt =
   let
        gn_Subject = tokStr $ head $ getTokens $ head $ predArgs pt
        gn_Object = tokStr $ head $ getTokens $ head $ tail $ predArgs pt
        gn_Predicate = Id{getTokens =
                              (map (\x -> Token{tokStr = tokStr x, tokPos = nullRange}) (getTokens predicate)),
                                   getComps = [], rangeOfId = nullRange}
        axName = "_" ++  show gn_Predicate ++ "_" ++ gn_Subject ++ "_" ++ gn_Object
   in
     [SenAttr{senAttr = "ga_generated_gn_Set[" ++ gn_Object ++ "]", isAxiom = True,
             isDef = False, wasTheorem = False, simpAnno = Nothing,
             sentence =
               Sort_gen_ax
                 [Constraint{newSort =
                               Id{getTokens = [Token{tokStr = "gn_Set", tokPos = nullRange}],
                                  getComps =
                                    [Id{getTokens =
                                          [Token{tokStr = gn_Object, tokPos = nullRange}],
                                        getComps = [], rangeOfId = nullRange}],
                                  rangeOfId = nullRange},
                             opSymbs =
                               [(Qual_op_name
                                   (Id{getTokens = [Token{tokStr = "gn_eset", tokPos = nullRange}],
                                       getComps = [], rangeOfId = nullRange})
                                   (Op_type Total []
                                      (Id{getTokens =
                                            [Token{tokStr = "gn_Set", tokPos = nullRange}],
                                          getComps =
                                            [Id{getTokens =
                                                  [Token{tokStr = gn_Object, tokPos = nullRange}],
                                                getComps = [], rangeOfId = nullRange}],
                                          rangeOfId = nullRange})
                                      nullRange)
                                   nullRange,
                                 []),
                                (Qual_op_name
                                   (Id{getTokens =
                                         [Token{tokStr = "gn_insert", tokPos = nullRange}],
                                       getComps = [], rangeOfId = nullRange})
                                   (Op_type Total
                                      [Id{getTokens =
                                            [Token{tokStr = "gn_Set", tokPos = nullRange}],
                                          getComps =
                                            [Id{getTokens =
                                                  [Token{tokStr = gn_Object, tokPos = nullRange}],
                                                getComps = [], rangeOfId = nullRange}],
                                          rangeOfId = nullRange},
                                       Id{getTokens =
                                            [Token{tokStr = gn_Object, tokPos = nullRange}],
                                          getComps = [], rangeOfId = nullRange}]
                                      (Id{getTokens =
                                            [Token{tokStr = "gn_Set", tokPos = nullRange}],
                                          getComps =
                                            [Id{getTokens =
                                                  [Token{tokStr = gn_Object, tokPos = nullRange}],
                                                getComps = [], rangeOfId = nullRange}],
                                          rangeOfId = nullRange})
                                      nullRange)
                                   nullRange,
                                 [0, - 1])],
                             origSort =
                               Id{getTokens = [Token{tokStr = "gn_Set", tokPos = nullRange}],
                                  getComps =
                                    [Id{getTokens =
                                          [Token{tokStr = gn_Object, tokPos = nullRange}],
                                        getComps = [], rangeOfId = nullRange}],
                                  rangeOfId = nullRange}}]
                 False},
     SenAttr{senAttr = "gn_exp_rule"++axName, isAxiom = True, isDef = False,
             wasTheorem = False, simpAnno = Nothing,
             sentence =
               Quantification Universal
                 [Var_decl [Token{tokStr = "gn_x", tokPos = nullRange}]
                    (Id{getTokens = [Token{tokStr = gn_Object, tokPos = nullRange}],
                        getComps = [], rangeOfId = nullRange})
                    nullRange]
                 (Negation
                    (Predication
                       (Qual_pred_name
                          (Id{getTokens =
                                [Token{tokStr = "gn_contained", tokPos = nullRange}],
                              getComps = [], rangeOfId = nullRange})
                          (Pred_type
                             [Id{getTokens = [Token{tokStr = gn_Object, tokPos = nullRange}],
                                 getComps = [], rangeOfId = nullRange},
                              Id{getTokens = [Token{tokStr = "gn_Set", tokPos = nullRange}],
                                 getComps =
                                   [Id{getTokens =
                                         [Token{tokStr = gn_Object, tokPos = nullRange}],
                                       getComps = [], rangeOfId = nullRange}],
                                 rangeOfId = nullRange}]
                             nullRange)
                          nullRange)
                       [Qual_var (Token{tokStr = "gn_x", tokPos = nullRange})
                          (Id{getTokens = [Token{tokStr = gn_Object, tokPos = nullRange}],
                              getComps = [], rangeOfId = nullRange})
                          nullRange,
                        Application
                          (Qual_op_name
                             (Id{getTokens = [Token{tokStr = "gn_eset", tokPos = nullRange}],
                                 getComps = [], rangeOfId = nullRange})
                             (Op_type Total []
                                (Id{getTokens = [Token{tokStr = "gn_Set", tokPos = nullRange}],
                                    getComps =
                                      [Id{getTokens =
                                            [Token{tokStr = gn_Object, tokPos = nullRange}],
                                          getComps = [], rangeOfId = nullRange}],
                                    rangeOfId = nullRange})
                                nullRange)
                             nullRange)
                          []
                          nullRange]
                       nullRange)
                    nullRange)
                 nullRange},
     SenAttr{senAttr = "gn_ax2"++axName, isAxiom = True, isDef = False,
             wasTheorem = False, simpAnno = Nothing,
             sentence =
               Quantification Universal
                 [Var_decl
                    [Token{tokStr = "gn_x", tokPos = nullRange},
                     Token{tokStr = "gn_y", tokPos = nullRange}]
                    (Id{getTokens = [Token{tokStr = gn_Object, tokPos = nullRange}],
                        getComps = [], rangeOfId = nullRange})
                    nullRange,
                  Var_decl [Token{tokStr = "gn_M", tokPos = nullRange}]
                    (Id{getTokens = [Token{tokStr = "gn_Set", tokPos = nullRange}],
                        getComps =
                          [Id{getTokens = [Token{tokStr = gn_Object, tokPos = nullRange}],
                              getComps = [], rangeOfId = nullRange}],
                        rangeOfId = nullRange})
                    nullRange]
                 (Equivalence
                    (Predication
                       (Qual_pred_name
                          (Id{getTokens =
                                [Token{tokStr = "gn_contained", tokPos = nullRange}],
                              getComps = [], rangeOfId = nullRange})
                          (Pred_type
                             [Id{getTokens = [Token{tokStr = gn_Object, tokPos = nullRange}],
                                 getComps = [], rangeOfId = nullRange},
                              Id{getTokens = [Token{tokStr = "gn_Set", tokPos = nullRange}],
                                 getComps =
                                   [Id{getTokens =
                                         [Token{tokStr = gn_Object, tokPos = nullRange}],
                                       getComps = [], rangeOfId = nullRange}],
                                 rangeOfId = nullRange}]
                             nullRange)
                          nullRange)
                       [Qual_var (Token{tokStr = "gn_x", tokPos = nullRange})
                          (Id{getTokens = [Token{tokStr = gn_Object, tokPos = nullRange}],
                              getComps = [], rangeOfId = nullRange})
                          nullRange,
                        Application
                          (Qual_op_name
                             (Id{getTokens = [Token{tokStr = "gn_insert", tokPos = nullRange}],
                                 getComps = [], rangeOfId = nullRange})
                             (Op_type Total
                                [Id{getTokens = [Token{tokStr = "gn_Set", tokPos = nullRange}],
                                    getComps =
                                      [Id{getTokens =
                                            [Token{tokStr = gn_Object, tokPos = nullRange}],
                                          getComps = [], rangeOfId = nullRange}],
                                    rangeOfId = nullRange},
                                 Id{getTokens = [Token{tokStr = gn_Object, tokPos = nullRange}],
                                    getComps = [], rangeOfId = nullRange}]
                                (Id{getTokens = [Token{tokStr = "gn_Set", tokPos = nullRange}],
                                    getComps =
                                      [Id{getTokens =
                                            [Token{tokStr = gn_Object, tokPos = nullRange}],
                                          getComps = [], rangeOfId = nullRange}],
                                    rangeOfId = nullRange})
                                nullRange)
                             nullRange)
                          [Qual_var (Token{tokStr = "gn_M", tokPos = nullRange})
                             (Id{getTokens = [Token{tokStr = "gn_Set", tokPos = nullRange}],
                                 getComps =
                                   [Id{getTokens =
                                         [Token{tokStr = gn_Object, tokPos = nullRange}],
                                       getComps = [], rangeOfId = nullRange}],
                                 rangeOfId = nullRange})
                             nullRange,
                           Qual_var (Token{tokStr = "gn_y", tokPos = nullRange})
                             (Id{getTokens = [Token{tokStr = gn_Object, tokPos = nullRange}],
                                 getComps = [], rangeOfId = nullRange})
                             nullRange]
                          nullRange]
                       nullRange)
                    (Disjunction
                       [Strong_equation
                          (Qual_var (Token{tokStr = "gn_x", tokPos = nullRange})
                             (Id{getTokens = [Token{tokStr = gn_Object, tokPos = nullRange}],
                                 getComps = [], rangeOfId = nullRange})
                             nullRange)
                          (Qual_var (Token{tokStr = "gn_y", tokPos = nullRange})
                             (Id{getTokens = [Token{tokStr = gn_Object, tokPos = nullRange}],
                                 getComps = [], rangeOfId = nullRange})
                             nullRange)
                          nullRange,
                        Predication
                          (Qual_pred_name
                             (Id{getTokens =
                                   [Token{tokStr = "gn_contained", tokPos = nullRange}],
                                 getComps = [], rangeOfId = nullRange})
                             (Pred_type
                                [Id{getTokens = [Token{tokStr = gn_Object, tokPos = nullRange}],
                                    getComps = [], rangeOfId = nullRange},
                                 Id{getTokens = [Token{tokStr = "gn_Set", tokPos = nullRange}],
                                    getComps =
                                      [Id{getTokens =
                                            [Token{tokStr = gn_Object, tokPos = nullRange}],
                                          getComps = [], rangeOfId = nullRange}],
                                    rangeOfId = nullRange}]
                                nullRange)
                             nullRange)
                          [Qual_var (Token{tokStr = "gn_x", tokPos = nullRange})
                             (Id{getTokens = [Token{tokStr = gn_Object, tokPos = nullRange}],
                                 getComps = [], rangeOfId = nullRange})
                             nullRange,
                           Qual_var (Token{tokStr = "gn_M", tokPos = nullRange})
                             (Id{getTokens = [Token{tokStr = "gn_Set", tokPos = nullRange}],
                                 getComps =
                                   [Id{getTokens =
                                         [Token{tokStr = gn_Object, tokPos = nullRange}],
                                       getComps = [], rangeOfId = nullRange}],
                                 rangeOfId = nullRange})
                             nullRange]
                          nullRange]
                       nullRange)
                    nullRange)
                 nullRange},
     SenAttr{senAttr = "gn_Ax3"++axName, isAxiom = True, isDef = False,
             wasTheorem = False, simpAnno = Nothing,
             sentence =
               Quantification Universal
                 [Var_decl
                    [Token{tokStr = "gn_M", tokPos = nullRange},
                     Token{tokStr = "gn_N", tokPos = nullRange}]
                    (Id{getTokens = [Token{tokStr = "gn_Set", tokPos = nullRange}],
                        getComps =
                          [Id{getTokens = [Token{tokStr = gn_Object, tokPos = nullRange}],
                              getComps = [], rangeOfId = nullRange}],
                        rangeOfId = nullRange})
                    nullRange]
                 (Equivalence
                    (Strong_equation
                       (Qual_var (Token{tokStr = "gn_M", tokPos = nullRange})
                          (Id{getTokens = [Token{tokStr = "gn_Set", tokPos = nullRange}],
                              getComps =
                                [Id{getTokens = [Token{tokStr = gn_Object, tokPos = nullRange}],
                                    getComps = [], rangeOfId = nullRange}],
                              rangeOfId = nullRange})
                          nullRange)
                       (Qual_var (Token{tokStr = "gn_N", tokPos = nullRange})
                          (Id{getTokens = [Token{tokStr = "gn_Set", tokPos = nullRange}],
                              getComps =
                                [Id{getTokens = [Token{tokStr = gn_Object, tokPos = nullRange}],
                                    getComps = [], rangeOfId = nullRange}],
                              rangeOfId = nullRange})
                          nullRange)
                       nullRange)
                    (Quantification Universal
                       [Var_decl [Token{tokStr = "gn_z", tokPos = nullRange}]
                          (Id{getTokens = [Token{tokStr = gn_Object, tokPos = nullRange}],
                              getComps = [], rangeOfId = nullRange})
                          nullRange]
                       (Equivalence
                          (Predication
                             (Qual_pred_name
                                (Id{getTokens =
                                      [Token{tokStr = "gn_contained", tokPos = nullRange}],
                                    getComps = [], rangeOfId = nullRange})
                                (Pred_type
                                   [Id{getTokens =
                                         [Token{tokStr = gn_Object, tokPos = nullRange}],
                                       getComps = [], rangeOfId = nullRange},
                                    Id{getTokens = [Token{tokStr = "gn_Set", tokPos = nullRange}],
                                       getComps =
                                         [Id{getTokens =
                                               [Token{tokStr = gn_Object, tokPos = nullRange}],
                                             getComps = [], rangeOfId = nullRange}],
                                       rangeOfId = nullRange}]
                                   nullRange)
                                nullRange)
                             [Qual_var (Token{tokStr = "gn_z", tokPos = nullRange})
                                (Id{getTokens = [Token{tokStr = gn_Object, tokPos = nullRange}],
                                    getComps = [], rangeOfId = nullRange})
                                nullRange,
                              Qual_var (Token{tokStr = "gn_M", tokPos = nullRange})
                                (Id{getTokens = [Token{tokStr = "gn_Set", tokPos = nullRange}],
                                    getComps =
                                      [Id{getTokens =
                                            [Token{tokStr = gn_Object, tokPos = nullRange}],
                                          getComps = [], rangeOfId = nullRange}],
                                    rangeOfId = nullRange})
                                nullRange]
                             nullRange)
                          (Predication
                             (Qual_pred_name
                                (Id{getTokens =
                                      [Token{tokStr = "gn_contained", tokPos = nullRange}],
                                    getComps = [], rangeOfId = nullRange})
                                (Pred_type
                                   [Id{getTokens =
                                         [Token{tokStr = gn_Object, tokPos = nullRange}],
                                       getComps = [], rangeOfId = nullRange},
                                    Id{getTokens = [Token{tokStr = "gn_Set", tokPos = nullRange}],
                                       getComps =
                                         [Id{getTokens =
                                               [Token{tokStr = gn_Object, tokPos = nullRange}],
                                             getComps = [], rangeOfId = nullRange}],
                                       rangeOfId = nullRange}]
                                   nullRange)
                                nullRange)
                             [Qual_var (Token{tokStr = "gn_z", tokPos = nullRange})
                                (Id{getTokens = [Token{tokStr = gn_Object, tokPos = nullRange}],
                                    getComps = [], rangeOfId = nullRange})
                                nullRange,
                              Qual_var (Token{tokStr = "gn_N", tokPos = nullRange})
                                (Id{getTokens = [Token{tokStr = "gn_Set", tokPos = nullRange}],
                                    getComps =
                                      [Id{getTokens =
                                            [Token{tokStr = gn_Object, tokPos = nullRange}],
                                          getComps = [], rangeOfId = nullRange}],
                                    rangeOfId = nullRange})
                                nullRange]
                             nullRange)
                          nullRange)
                       nullRange)
                    nullRange)
                 nullRange},
     SenAttr{senAttr = "gn_Ax4"++axName, isAxiom = True, isDef = False,
             wasTheorem = False, simpAnno = Nothing,
             sentence =
               Strong_equation
                 (Application
                    (Qual_op_name
                       (Id{getTokens =
                             [Token{tokStr = "gn_card", tokPos = nullRange},
                              Token{tokStr = "__", tokPos = nullRange}],
                           getComps = [], rangeOfId = nullRange})
                       (Op_type Total
                          [Id{getTokens = [Token{tokStr = "gn_Set", tokPos = nullRange}],
                              getComps =
                                [Id{getTokens = [Token{tokStr = gn_Object, tokPos = nullRange}],
                                    getComps = [], rangeOfId = nullRange}],
                              rangeOfId = nullRange}]
                          (Id{getTokens = [Token{tokStr = "nonNegativeInteger", tokPos = nullRange}],
                              getComps = [], rangeOfId = nullRange})
                          nullRange)
                       nullRange)
                    [Application
                       (Qual_op_name
                          (Id{getTokens = [Token{tokStr = "gn_eset", tokPos = nullRange}],
                              getComps = [], rangeOfId = nullRange})
                          (Op_type Total []
                             (Id{getTokens = [Token{tokStr = "gn_Set", tokPos = nullRange}],
                                 getComps =
                                   [Id{getTokens =
                                         [Token{tokStr = gn_Object, tokPos = nullRange}],
                                       getComps = [], rangeOfId = nullRange}],
                                 rangeOfId = nullRange})
                             nullRange)
                          nullRange)
                       []
                       nullRange]
                    nullRange)
                 (Application
                    (Qual_op_name
                       (Id{getTokens = [Token{tokStr = "0", tokPos = nullRange}],
                           getComps = [], rangeOfId = nullRange})
                       (Op_type Total []
                          (Id{getTokens = [Token{tokStr = "nonNegativeInteger", tokPos = nullRange}],
                              getComps = [], rangeOfId = nullRange})
                          nullRange)
                       nullRange)
                    []
                    nullRange)
                 nullRange},
     SenAttr{senAttr = "gn_Ax5"++axName, isAxiom = True, isDef = False,
             wasTheorem = False, simpAnno = Nothing,
             sentence =
               Quantification Universal
                 [Var_decl [Token{tokStr = "gn_x", tokPos = nullRange}]
                    (Id{getTokens = [Token{tokStr = gn_Object, tokPos = nullRange}],
                        getComps = [], rangeOfId = nullRange})
                    nullRange,
                  Var_decl [Token{tokStr = "gn_M", tokPos = nullRange}]
                    (Id{getTokens = [Token{tokStr = "gn_Set", tokPos = nullRange}],
                        getComps =
                          [Id{getTokens = [Token{tokStr = gn_Object, tokPos = nullRange}],
                              getComps = [], rangeOfId = nullRange}],
                        rangeOfId = nullRange})
                    nullRange]
                 (Strong_equation
                    (Application
                       (Qual_op_name
                          (Id{getTokens =
                                [Token{tokStr = "gn_card", tokPos = nullRange},
                                 Token{tokStr = "__", tokPos = nullRange}],
                              getComps = [], rangeOfId = nullRange})
                          (Op_type Total
                             [Id{getTokens = [Token{tokStr = "gn_Set", tokPos = nullRange}],
                                 getComps =
                                   [Id{getTokens =
                                         [Token{tokStr = gn_Object, tokPos = nullRange}],
                                       getComps = [], rangeOfId = nullRange}],
                                 rangeOfId = nullRange}]
                             (Id{getTokens = [Token{tokStr = "nonNegativeInteger", tokPos = nullRange}],
                                 getComps = [], rangeOfId = nullRange})
                             nullRange)
                          nullRange)
                       [Application
                          (Qual_op_name
                             (Id{getTokens = [Token{tokStr = "gn_insert", tokPos = nullRange}],
                                 getComps = [], rangeOfId = nullRange})
                             (Op_type Total
                                [Id{getTokens = [Token{tokStr = "gn_Set", tokPos = nullRange}],
                                    getComps =
                                      [Id{getTokens =
                                            [Token{tokStr = gn_Object, tokPos = nullRange}],
                                          getComps = [], rangeOfId = nullRange}],
                                    rangeOfId = nullRange},
                                 Id{getTokens = [Token{tokStr = gn_Object, tokPos = nullRange}],
                                    getComps = [], rangeOfId = nullRange}]
                                (Id{getTokens = [Token{tokStr = "gn_Set", tokPos = nullRange}],
                                    getComps =
                                      [Id{getTokens =
                                            [Token{tokStr = gn_Object, tokPos = nullRange}],
                                          getComps = [], rangeOfId = nullRange}],
                                    rangeOfId = nullRange})
                                nullRange)
                             nullRange)
                          [Qual_var (Token{tokStr = "gn_M", tokPos = nullRange})
                             (Id{getTokens = [Token{tokStr = "gn_Set", tokPos = nullRange}],
                                 getComps =
                                   [Id{getTokens =
                                         [Token{tokStr = gn_Object, tokPos = nullRange}],
                                       getComps = [], rangeOfId = nullRange}],
                                 rangeOfId = nullRange})
                             nullRange,
                           Qual_var (Token{tokStr = "gn_x", tokPos = nullRange})
                             (Id{getTokens = [Token{tokStr = gn_Object, tokPos = nullRange}],
                                 getComps = [], rangeOfId = nullRange})
                             nullRange]
                          nullRange]
                       nullRange)
                    (Conditional
                       (Application
                          (Qual_op_name
                             (Id{getTokens =
                                   [Token{tokStr = "gn_card", tokPos = nullRange},
                                    Token{tokStr = "__", tokPos = nullRange}],
                                 getComps = [], rangeOfId = nullRange})
                             (Op_type Total
                                [Id{getTokens = [Token{tokStr = "gn_Set", tokPos = nullRange}],
                                    getComps =
                                      [Id{getTokens =
                                            [Token{tokStr = gn_Object, tokPos = nullRange}],
                                          getComps = [], rangeOfId = nullRange}],
                                    rangeOfId = nullRange}]
                                (Id{getTokens = [Token{tokStr = "nonNegativeInteger", tokPos = nullRange}],
                                    getComps = [], rangeOfId = nullRange})
                                nullRange)
                             nullRange)
                          [Qual_var (Token{tokStr = "gn_M", tokPos = nullRange})
                             (Id{getTokens = [Token{tokStr = "gn_Set", tokPos = nullRange}],
                                 getComps =
                                   [Id{getTokens =
                                         [Token{tokStr = gn_Object, tokPos = nullRange}],
                                       getComps = [], rangeOfId = nullRange}],
                                 rangeOfId = nullRange})
                             nullRange]
                          nullRange)
                       (Predication
                          (Qual_pred_name
                             (Id{getTokens =
                                   [Token{tokStr = "gn_contained", tokPos = nullRange}],
                                 getComps = [], rangeOfId = nullRange})
                             (Pred_type
                                [Id{getTokens = [Token{tokStr = gn_Object, tokPos = nullRange}],
                                    getComps = [], rangeOfId = nullRange},
                                 Id{getTokens = [Token{tokStr = "gn_Set", tokPos = nullRange}],
                                    getComps =
                                      [Id{getTokens =
                                            [Token{tokStr = gn_Object, tokPos = nullRange}],
                                          getComps = [], rangeOfId = nullRange}],
                                    rangeOfId = nullRange}]
                                nullRange)
                             nullRange)
                          [Qual_var (Token{tokStr = "gn_x", tokPos = nullRange})
                             (Id{getTokens = [Token{tokStr = gn_Object, tokPos = nullRange}],
                                 getComps = [], rangeOfId = nullRange})
                             nullRange,
                           Qual_var (Token{tokStr = "gn_M", tokPos = nullRange})
                             (Id{getTokens = [Token{tokStr = "gn_Set", tokPos = nullRange}],
                                 getComps =
                                   [Id{getTokens =
                                         [Token{tokStr = gn_Object, tokPos = nullRange}],
                                       getComps = [], rangeOfId = nullRange}],
                                 rangeOfId = nullRange})
                             nullRange]
                          nullRange)
                       (Application
                          (Qual_op_name
                             (Id{getTokens = [Token{tokStr = "suc", tokPos = nullRange}],
                                 getComps = [], rangeOfId = nullRange})
                             (Op_type Total
                                [Id{getTokens = [Token{tokStr = "nonNegativeInteger", tokPos = nullRange}],
                                    getComps = [], rangeOfId = nullRange}]
                                (Id{getTokens = [Token{tokStr = "nonNegativeInteger", tokPos = nullRange}],
                                    getComps = [], rangeOfId = nullRange})
                                nullRange)
                             nullRange)
                          [Application
                             (Qual_op_name
                                (Id{getTokens =
                                      [Token{tokStr = "gn_card", tokPos = nullRange},
                                       Token{tokStr = "__", tokPos = nullRange}],
                                    getComps = [], rangeOfId = nullRange})
                                (Op_type Total
                                   [Id{getTokens = [Token{tokStr = "gn_Set", tokPos = nullRange}],
                                       getComps =
                                         [Id{getTokens =
                                               [Token{tokStr = gn_Object, tokPos = nullRange}],
                                             getComps = [], rangeOfId = nullRange}],
                                       rangeOfId = nullRange}]
                                   (Id{getTokens = [Token{tokStr = "nonNegativeInteger", tokPos = nullRange}],
                                       getComps = [], rangeOfId = nullRange})
                                   nullRange)
                                nullRange)
                             [Qual_var (Token{tokStr = "gn_M", tokPos = nullRange})
                                (Id{getTokens = [Token{tokStr = "gn_Set", tokPos = nullRange}],
                                    getComps =
                                      [Id{getTokens =
                                            [Token{tokStr = gn_Object, tokPos = nullRange}],
                                          getComps = [], rangeOfId = nullRange}],
                                    rangeOfId = nullRange})
                                nullRange]
                             nullRange]
                          nullRange)
                       nullRange)
                    nullRange)
                 nullRange},
     SenAttr{senAttr = "gn_Ax6"++axName, isAxiom = True, isDef = False,
             wasTheorem = False, simpAnno = Nothing,
             sentence =
               Quantification Universal
                 [Var_decl [Token{tokStr = "x", tokPos = nullRange}]
                    (Id{getTokens = [Token{tokStr = gn_Subject, tokPos = nullRange}],
                        getComps = [], rangeOfId = nullRange})
                    nullRange]
                 (Equivalence
                    (Definedness
                       (Application
                          (Qual_op_name
                             (Id{getTokens =
                                   [Token{tokStr = "gn_setOfPred", tokPos = nullRange},
                                    Token{tokStr = "__", tokPos = nullRange}],
                                 getComps =
                                   [gn_Predicate],
                                 rangeOfId = nullRange})
                             (Op_type Partial
                                [Id{getTokens = [Token{tokStr = gn_Subject, tokPos = nullRange}],
                                    getComps = [], rangeOfId = nullRange}]
                                (Id{getTokens = [Token{tokStr = "gn_Set", tokPos = nullRange}],
                                    getComps =
                                      [Id{getTokens =
                                            [Token{tokStr = gn_Object, tokPos = nullRange}],
                                          getComps = [], rangeOfId = nullRange}],
                                    rangeOfId = nullRange})
                                nullRange)
                             nullRange)
                          [Qual_var (Token{tokStr = "x", tokPos = nullRange})
                             (Id{getTokens = [Token{tokStr = gn_Subject, tokPos = nullRange}],
                                 getComps = [], rangeOfId = nullRange})
                             nullRange]
                          nullRange)
                       nullRange)
                    (Quantification Existential
                       [Var_decl [Token{tokStr = "s", tokPos = nullRange}]
                          (Id{getTokens = [Token{tokStr = "gn_Set", tokPos = nullRange}],
                              getComps =
                                [Id{getTokens = [Token{tokStr = gn_Object, tokPos = nullRange}],
                                    getComps = [], rangeOfId = nullRange}],
                              rangeOfId = nullRange})
                          nullRange]
                       (Quantification Universal
                          [Var_decl [Token{tokStr = "y", tokPos = nullRange}]
                             (Id{getTokens = [Token{tokStr = gn_Object, tokPos = nullRange}],
                                 getComps = [], rangeOfId = nullRange})
                             nullRange]
                          (Equivalence
                             (Predication
                                (Qual_pred_name
                                   (gn_Predicate)
                                   (Pred_type
                                      [Id{getTokens =
                                            [Token{tokStr = gn_Subject, tokPos = nullRange}],
                                          getComps = [], rangeOfId = nullRange},
                                       Id{getTokens =
                                            [Token{tokStr = gn_Object, tokPos = nullRange}],
                                          getComps = [], rangeOfId = nullRange}]
                                      nullRange)
                                   nullRange)
                                [Qual_var (Token{tokStr = "x", tokPos = nullRange})
                                   (Id{getTokens =
                                         [Token{tokStr = gn_Subject, tokPos = nullRange}],
                                       getComps = [], rangeOfId = nullRange})
                                   nullRange,
                                 Qual_var (Token{tokStr = "y", tokPos = nullRange})
                                   (Id{getTokens =
                                         [Token{tokStr = gn_Object, tokPos = nullRange}],
                                       getComps = [], rangeOfId = nullRange})
                                   nullRange]
                                nullRange)
                             (Predication
                                (Qual_pred_name
                                   (Id{getTokens =
                                         [Token{tokStr = "gn_contained", tokPos = nullRange}],
                                       getComps = [], rangeOfId = nullRange})
                                   (Pred_type
                                      [Id{getTokens =
                                            [Token{tokStr = gn_Object, tokPos = nullRange}],
                                          getComps = [], rangeOfId = nullRange},
                                       Id{getTokens =
                                            [Token{tokStr = "gn_Set", tokPos = nullRange}],
                                          getComps =
                                            [Id{getTokens =
                                                  [Token{tokStr = gn_Object, tokPos = nullRange}],
                                                getComps = [], rangeOfId = nullRange}],
                                          rangeOfId = nullRange}]
                                      nullRange)
                                   nullRange)
                                [Qual_var (Token{tokStr = "y", tokPos = nullRange})
                                   (Id{getTokens =
                                         [Token{tokStr = gn_Object, tokPos = nullRange}],
                                       getComps = [], rangeOfId = nullRange})
                                   nullRange,
                                 Qual_var (Token{tokStr = "s", tokPos = nullRange})
                                   (Id{getTokens = [Token{tokStr = "gn_Set", tokPos = nullRange}],
                                       getComps =
                                         [Id{getTokens =
                                               [Token{tokStr = gn_Object, tokPos = nullRange}],
                                             getComps = [], rangeOfId = nullRange}],
                                       rangeOfId = nullRange})
                                   nullRange]
                                nullRange)
                             nullRange)
                          nullRange)
                       nullRange)
                    nullRange)
                 nullRange},
     SenAttr{senAttr = "gn_Ax7"++axName, isAxiom = True, isDef = False,
             wasTheorem = False, simpAnno = Nothing,
             sentence =
               Quantification Universal
                 [Var_decl [Token{tokStr = "x", tokPos = nullRange}]
                    (Id{getTokens = [Token{tokStr = gn_Subject, tokPos = nullRange}],
                        getComps = [], rangeOfId = nullRange})
                    nullRange]
                 (Implication
                    (Definedness
                       (Application
                          (Qual_op_name
                             (Id{getTokens =
                                   [Token{tokStr = "gn_setOfPred", tokPos = nullRange},
                                    Token{tokStr = "__", tokPos = nullRange}],
                                 getComps =
                                   [gn_Predicate],
                                 rangeOfId = nullRange})
                             (Op_type Partial
                                [Id{getTokens = [Token{tokStr = gn_Subject, tokPos = nullRange}],
                                    getComps = [], rangeOfId = nullRange}]
                                (Id{getTokens = [Token{tokStr = "gn_Set", tokPos = nullRange}],
                                    getComps =
                                      [Id{getTokens =
                                            [Token{tokStr = gn_Object, tokPos = nullRange}],
                                          getComps = [], rangeOfId = nullRange}],
                                    rangeOfId = nullRange})
                                nullRange)
                             nullRange)
                          [Qual_var (Token{tokStr = "x", tokPos = nullRange})
                             (Id{getTokens = [Token{tokStr = gn_Subject, tokPos = nullRange}],
                                 getComps = [], rangeOfId = nullRange})
                             nullRange]
                          nullRange)
                       nullRange)
                    (Quantification Universal
                       [Var_decl [Token{tokStr = "y", tokPos = nullRange}]
                          (Id{getTokens = [Token{tokStr = gn_Object, tokPos = nullRange}],
                              getComps = [], rangeOfId = nullRange})
                          nullRange]
                       (Equivalence
                          (Predication
                             (Qual_pred_name
                                (gn_Predicate)
                                (Pred_type
                                   [Id{getTokens =
                                         [Token{tokStr = gn_Subject, tokPos = nullRange}],
                                       getComps = [], rangeOfId = nullRange},
                                    Id{getTokens =
                                         [Token{tokStr = gn_Object, tokPos = nullRange}],
                                       getComps = [], rangeOfId = nullRange}]
                                   nullRange)
                                nullRange)
                             [Qual_var (Token{tokStr = "x", tokPos = nullRange})
                                (Id{getTokens = [Token{tokStr = gn_Subject, tokPos = nullRange}],
                                    getComps = [], rangeOfId = nullRange})
                                nullRange,
                              Qual_var (Token{tokStr = "y", tokPos = nullRange})
                                (Id{getTokens = [Token{tokStr = gn_Object, tokPos = nullRange}],
                                    getComps = [], rangeOfId = nullRange})
                                nullRange]
                             nullRange)
                          (Predication
                             (Qual_pred_name
                                (Id{getTokens =
                                      [Token{tokStr = "gn_contained", tokPos = nullRange}],
                                    getComps = [], rangeOfId = nullRange})
                                (Pred_type
                                   [Id{getTokens =
                                         [Token{tokStr = gn_Object, tokPos = nullRange}],
                                       getComps = [], rangeOfId = nullRange},
                                    Id{getTokens = [Token{tokStr = "gn_Set", tokPos = nullRange}],
                                       getComps =
                                         [Id{getTokens =
                                               [Token{tokStr = gn_Object, tokPos = nullRange}],
                                             getComps = [], rangeOfId = nullRange}],
                                       rangeOfId = nullRange}]
                                   nullRange)
                                nullRange)
                             [Qual_var (Token{tokStr = "y", tokPos = nullRange})
                                (Id{getTokens = [Token{tokStr = gn_Object, tokPos = nullRange}],
                                    getComps = [], rangeOfId = nullRange})
                                nullRange,
                              Application
                                (Qual_op_name
                                   (Id{getTokens =
                                         [Token{tokStr = "gn_setOfPred", tokPos = nullRange},
                                          Token{tokStr = "__", tokPos = nullRange}],
                                       getComps =
                                         [gn_Predicate],
                                       rangeOfId = nullRange})
                                   (Op_type Partial
                                      [Id{getTokens =
                                            [Token{tokStr = gn_Subject, tokPos = nullRange}],
                                          getComps = [], rangeOfId = nullRange}]
                                      (Id{getTokens =
                                            [Token{tokStr = "gn_Set", tokPos = nullRange}],
                                          getComps =
                                            [Id{getTokens =
                                                  [Token{tokStr = gn_Object, tokPos = nullRange}],
                                                getComps = [], rangeOfId = nullRange}],
                                          rangeOfId = nullRange})
                                      nullRange)
                                   nullRange)
                                [Qual_var (Token{tokStr = "x", tokPos = nullRange})
                                   (Id{getTokens =
                                         [Token{tokStr = gn_Subject, tokPos = nullRange}],
                                       getComps = [], rangeOfId = nullRange})
                                   nullRange]
                                nullRange]
                             nullRange)
                          nullRange)
                       nullRange)
                    True
                    nullRange)
                 nullRange}]
