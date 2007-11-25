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
import CASL_DL.CASL_DLHelpers

--CASL_DL = domain
import CASL_DL.Logic_CASL_DL
import CASL_DL.AS_CASL_DL
import CASL_DL.Sign()
import CASL_DL.PredefinedSign
import CASL_DL.StatAna -- DLSign
import CASL_DL.PredefinedSign

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
    ()              -- sublogics domain
    DL_BASIC_SPEC   -- Basic spec domain
    DLFORMULA       -- sentence domain
    SYMB_ITEMS      -- symbol items domain
    SYMB_MAP_ITEMS  -- symbol map items domain
    DLSign          -- signature domain
    DLMor           -- morphism domain
    Symbol          -- symbol domain
    RawSymbol       -- rawsymbol domain
    ()              -- proof tree codomain
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
      sourceSublogic CASL_DL2CASL = ()
      mapSublogic CASL_DL2CASL _  = Just $ Sublogic.top
      map_symbol  CASL_DL2CASL s  = Set.singleton s
      map_sentence CASL_DL2CASL   = trSentence
      map_morphism CASL_DL2CASL   = mapMor
      map_theory   CASL_DL2CASL   = trTheory

mapMor :: DLMor -> Result CASLMor
mapMor inMor =
    let
        ms = trSign $ msource inMor
        mt = trSign $ mtarget inMor
        sm = sort_map inMor
        fm = fun_map inMor
        pm = pred_map inMor
        em = extended_map inMor
    in
      return $ Morphism
                 {
                   msource = ms
                 , mtarget = mt
                 , sort_map = sm
                 , fun_map = fm
                 , pred_map = pm
                 , extended_map = ()
                 }

projectToCASL :: DLSign -> CASLSign
projectToCASL dls = dls 
                    {
                      sentences = []
                    , extendedInfo = ()
                    }

trSign :: DLSign -> CASLSign
trSign inSig = 
    let
        inC = (makeCardResSignature $ projectToCASL inSig) `uniteCASLSign` predCardResSig
        inD = projectToCASL predefinedSign
        mergedS  = inC `uniteCASLSign` inD 
        inSorts  = sortSet inSig
        inData   = sortSet dataSig_CASL
    in
      mergedS 
      {
        sortRel = Rel.delete topSortD topSortD $ 
                  Set.fold (\x -> Rel.insert x topSortD) 
                  (Set.fold (\x -> Rel.insert x topSort) 
                   (sortRel inSig) inSorts)
                  inData
      }

makeCardResSignature :: CASLSign -> CASLSign
makeCardResSignature cSign =
    let 
        pm = predMap cSign
        om = opMap cSign
    in
      case (Map.size pm > 0) of
        True ->
            cSign 
            {
              opMap = Map.foldWithKey (\k a b -> Map.union (addCardResOps k a) b) om pm
            }
        False -> cSign

addCardResOps :: Id -> Set.Set PredType -> OpMap
addCardResOps myId spt =
    let
        inOps  = map (\x -> addCardResOp myId x)
                 $ filter (\x -> (length $ predArgs x) == 2) $ Set.toList spt
    in
      case concat $ map Map.keys inOps of
        [] -> Map.fromList []
        _  ->
            Map.fromList 
             [
              (head $ concat $ map Map.keys inOps
              ,foldl (Set.union) Set.empty $
               concat $ map Map.elems inOps
              )
             ]

addCardResOp :: Id -> PredType -> OpMap
addCardResOp myId pt = 
      Map.fromList
             [(Id [Token "gn_setOfPred" nullRange]
               [myId]
               nullRange,
               Set.fromList
               [OpType Partial 
                           [
                            head $ predArgs pt
                           ]
                (Id [Token "gn_Set" nullRange]
                 [
                  head $ tail $ predArgs pt
                 ]
                 nullRange)])]

rtrSign :: DLSign -> Result CASLSign
rtrSign inSig = return $ trSign inSig

-- Translation of theories
trTheory :: (DLSign, [Named (FORMULA DL_FORMULA)]) ->
            Result (CASLSign, [Named (FORMULA ())])
trTheory (inSig, inForms) = 
    do
      outForms <- mapR (\x -> trNamedSentence inSig x) inForms 
      outSig <- rtrSign inSig
      return (outSig, predCardResAx ++ outForms)

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
    

-- translation of sentences
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
              Cardinality CExact ps trm1 trm2 rn ->
                  return (True_atom nullRange)
              Cardinality CMin ps trm1 trm2 rn ->
                  return (True_atom nullRange)
              Cardinality CMax ps trm1 trm2 rn ->
                  return (True_atom nullRange)

-- translation of terms
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
