{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances, DeriveDataTypeable, FlexibleContexts #-}
{- |
Module      :  ./GenHyb/GenComor
Description :  Instance of class Logic for rigid CASL


Instance of class Logic for rigid logic.
-}

module GenHyb.GenComor where

import Logic.Logic
import Logic.Comorphism
--import Logic.SemConstr
import qualified Data.Set as Set
import qualified Data.Map as Map
import Common.ProofTree
import Common.Result
import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.Id
import qualified Common.Lib.MapSet as MapSet


import Control.Monad (foldM)
--import Data.List(partition)

-- CASL
import qualified CASL.Logic_CASL as CLogic
import qualified CASL.AS_Basic_CASL as CBasic
import qualified CASL.Sign as CSign
import qualified CASL.Morphism as CMor
import CASL.Sublogic 
import qualified CASL.Induction as CInd

-- generic hybrid logic
import qualified GenHyb.GenTypes as GTypes
import qualified GenHyb.GenMethods as GMethods

-- import Debug.Trace

-- methods only on CASL types, copied from HPAR2CASL

getVarSorts :: Set.Set CBasic.SORT -> CBasic.CASLFORMULA -> Set.Set CBasic.SORT
getVarSorts oldS sen = 
 case sen of
  CBasic.Quantification _ vdecls f _ -> Set.union (Set.fromList $ map (\(CBasic.Var_decl _ s _) -> s) vdecls) $ getVarSorts oldS f
  CBasic.Junction _ fs _ -> foldl (\s f -> getVarSorts s f) oldS fs
  CBasic.Relation f1 _ f2 _ -> Set.union (getVarSorts oldS f1) (getVarSorts oldS f2)
  CBasic.Negation f _ -> getVarSorts oldS f
  CBasic.Atom _ _ -> oldS
  CBasic.Definedness _ _ -> oldS
  CBasic.Predication _ _ _ -> oldS
  CBasic.Equation _ _ _ _ -> oldS
  _ -> error $ "GenHyb.GenComor.getVarSorts: Illegal argument " ++  show sen

addSortToOpType :: Id -> CBasic.OP_TYPE -> CBasic.OP_TYPE
addSortToOpType stStr (CBasic.Op_type k w s r1) = CBasic.Op_type k (stStr:w) s r1

addSortToPredType :: Id -> CBasic.PRED_TYPE -> CBasic.PRED_TYPE
addSortToPredType stStr (CBasic.Pred_type w r1) = CBasic.Pred_type (stStr : w) r1

addVarToTerm :: Id -> CBasic.VAR -> CBasic.TERM () -> CBasic.TERM ()
addVarToTerm stStr v t = case t of
 CBasic.Qual_var _ _ _ -> t
 CBasic.Application (CBasic.Qual_op_name f o r2) args r -> 
   CBasic.Application (CBasic.Qual_op_name f (addSortToOpType stStr o) r2) ((CBasic.Qual_var v stStr nullRange):(map (addVarToTerm stStr v) args)) r
 _ -> error $ "GenHyb.GenComor.addVarToTerm: can't add var to term " ++ show t

addX :: Id -> CBasic.VAR -> CBasic.CASLFORMULA -> CBasic.CASLFORMULA
addX stStr v sen = case sen of
  CBasic.Quantification q vdecls f r -> CBasic.Quantification q vdecls (addX stStr v f) r
  CBasic.Junction j fs r -> CBasic.Junction j (map (addX stStr v) fs) r
  CBasic.Relation f1 rel f2 r -> CBasic.Relation (addX stStr v f1) rel (addX stStr v f2) r
  CBasic.Negation f r -> CBasic.Negation (addX stStr v f) r
  CBasic.Atom _ _ -> sen
  CBasic.Definedness t r -> CBasic.Definedness (addVarToTerm stStr v t) r
  CBasic.Predication (CBasic.Qual_pred_name p t r2) terms r -> 
    CBasic.Predication (CBasic.Qual_pred_name p (addSortToPredType stStr t) r2) ((CBasic.Qual_var v stStr nullRange):(map (addVarToTerm stStr v) terms)) r
  CBasic.Equation t1 eq t2 r -> CBasic.Equation (addVarToTerm stStr v t1) eq (addVarToTerm stStr v t2) r
  _ -> error $ "Illegal argument for addX in HPAR2CASL.hs: " ++  show sen

replaceVarAppls :: CBasic.VAR -> CBasic.SORT -> CBasic.CASLFORMULA -> CBasic.CASLFORMULA
replaceVarAppls v s sen = case sen of
  CBasic.Quantification q vdecls f r -> CBasic.Quantification q vdecls (replaceVarAppls v s f) r
  CBasic.Junction j fs r -> CBasic.Junction j (map (replaceVarAppls v s) fs) r
  CBasic.Relation f1 rel f2 r -> CBasic.Relation (replaceVarAppls v s f1) rel (replaceVarAppls v s f2) r
  CBasic.Negation f r -> CBasic.Negation (replaceVarAppls v s f) r
  CBasic.Atom _ _ -> sen
  CBasic.Definedness t r -> CBasic.Definedness (replTermWithVar v s t) r
  CBasic.Predication p terms r -> CBasic.Predication p (map (replTermWithVar v s) terms) r
  CBasic.Equation t1 eq t2 r -> CBasic.Equation (replTermWithVar v s t1) eq (replTermWithVar v s t2) r
  _ -> error $ "Illegal argument for replaceVarAppls in HPAR2CASL.hs: " ++  show sen

replTermWithVar :: CBasic.VAR -> CBasic.SORT -> CBasic.TERM () -> CBasic.TERM ()
replTermWithVar v s t = case t of 
  CBasic.Application op@(CBasic.Qual_op_name f _o _r2) args r -> 
     if simpleIdToId v == f 
        then CBasic.Qual_var v s nullRange
        else CBasic.Application op (map (replTermWithVar v s) args) r                   
  _ -> t

-- map theory

mapTheoryConstr :: (Comorphism cid lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
                  CLogic.CASL CASL_Sublogics
                  CLogic.CASLBasicSpec CBasic.CASLFORMULA CBasic.SYMB_ITEMS CBasic.SYMB_MAP_ITEMS
                  CSign.CASLSign
                  CMor.CASLMor
                  CSign.Symbol CMor.RawSymbol ProofTree,
                   Logic hlid hsublogics hbasic_spec hsen
                    hsymb_items hsymb_map_items (GTypes.HSign sig)
                    hmor hsym hraw_sym hproof_tree)
                   => 
                      cid    -- base comorphism
                   -> hlid   -- hybrid logic, source of the generated comorphism. we only need it to 
                             -- 1. check that the data logic fits
                             -- 2. get its semantic constraints
                   -> (GTypes.HSign sig, [Named (GTypes.HFORMULA sen symb_items raw_sym)]) -- the theory
                   ->  Result (CSign.CASLSign, [Named CBasic.CASLFORMULA]) 
mapTheoryConstr cid hlid (hsig, nhsens) = do
 -- 0. preliminaries
 let baseLid = sourceLogic cid
     mapBTheory = map_theory cid
     mapBSen = map_sentence cid
 -- TODO: check that the data_logic of hlid is actually baseLid
 -- 1. map base signature
 (csig, csens) <- mapBTheory (GTypes.baseSig hsig, [])
 -- 2. auxiliaries
 let st = genName $ "ST_" ++ show hlid
     v = genToken "X"
     domain = genName $ "domain_" ++ show hlid
     -- baseLid = case data_logic hLid of
     --           Nothing -> error $ "data logic not set for hybrid logic " ++ show hLid -- should never happen
     --           Just (Logic l) -> l
  -- 3. variables in \Gamma_\Sigma
     cvars = foldl (\vars asen -> getVarSorts vars $ sentence asen) Set.empty csens 
  -- 4. e -> forall gn_X : gn_ST . e(X) 
     csens' = -- trace ("cvars:" ++ show cvars) $ 
              map (\f -> f { sentence = CBasic.Quantification CBasic.Universal [CBasic.Var_decl [v] st nullRange] (addX st v $ sentence f) nullRange} ) csens
  -- 5. this one has gn_ST
 stsig <- CSign.addSymbToSign (CSign.emptySign ()) $ CSign.Symbol st CSign.SortAsItemType
  -- 6. this one has [S_\Sigma]
 sortsig <- foldM (\aSig x -> CSign.addSymbToSign aSig $ CSign.Symbol x CSign.SortAsItemType) 
                   stsig $ Set.toList $ CSign.sortSet csig
 -- 7. this one has \overline{Nom}
 nomsig <- foldM (\aSig x -> CSign.addSymbToSign aSig $ CSign.Symbol x $ CSign.OpAsItemType $ CSign.OpType CBasic.Total [] st) 
                  sortsig $ GTypes.noms hsig
  -- 8. this one has [F_\Sigma]
 opsig <- foldM (\aSig (i, CSign.OpType k w s) -> CSign.addSymbToSign aSig $ CSign.Symbol i $ CSign.OpAsItemType $ CSign.OpType k (st:w) s)
                 nomsig $ MapSet.toPairList $ CSign.opMap csig
   -- 9. this is D_F_\Sigma
 let domsens = 
                foldl (\sens (f, o@(CSign.OpType _ w s)) -> 
                          let ydecl = CBasic.mkVarDecl (genToken "w") st
                              xsdecl = map (\(si, ii) -> CBasic.mkVarDecl (genToken $ "x" ++ show ii) si) $ zip w [1::Int ..]
                              df = CBasic.mkForall [ydecl] $
                                   CBasic.mkForall xsdecl $
                                   CBasic.mkImpl 
                                    (CBasic.conjunct $ map (\xidecl -> case xidecl of 
                                                                         CBasic.Var_decl [xi] si _ -> 
                                                                           CBasic.mkPredication (CBasic.mkQualPred domain $ CBasic.Pred_type [st, si] nullRange)
                                                                                                [CBasic.Qual_var (genToken "w") st nullRange,
                                                                                                 CBasic.Qual_var xi si nullRange]
                                                                         _ -> error "domsens"
                                                           ) xsdecl
                                    ) 
                                    (CBasic.mkPredication (CBasic.mkQualPred domain $ CBasic.Pred_type [st, s] nullRange) 
                                                          [CBasic.Qual_var (genToken "w") st nullRange,
                                                           CBasic.mkAppl (CBasic.Qual_op_name f (addSortToOpType st $ CSign.toOP_TYPE o) nullRange) 
                                                                         (map CBasic.toQualVar $ ydecl:xsdecl) 
                                                          ]
                                    )
                          in (makeNamed ("ga_domain_"++show f) df):sens
                      ) 
                      [] $ MapSet.toPairList $ CSign.opMap csig
   -- 10. this one has [P_\Sigma]
 predsig <- foldM (\aSig (i, CSign.PredType w) -> CSign.addSymbToSign aSig $ CSign.Symbol i $ CSign.PredAsItemType $ CSign.PredType (st:w))
                   opsig $ MapSet.toPairList $ CSign.predMap csig
  -- 11. this one has D_s
 domsig <- foldM (\aSig s -> CSign.addSymbToSign aSig $ CSign.Symbol domain $ CSign.PredAsItemType $ CSign.PredType [st, s])
            predsig $ Set.toList $ CSign.sortSet csig
  -- 12. this one has \overline{\Lambda}
 lamsig <- foldM (\aSig (l, x) -> CSign.addSymbToSign aSig $ CSign.Symbol l $ CSign.PredAsItemType $ CSign.PredType $ take x $ repeat st)
            domsig $ Map.toList $ GTypes.mods hsig 
 -- 13. translate sentences from HPAR to CASL
 let ncsens = map (mapNamedSentence (show hlid) mapBTheory mapBSen baseLid hsig) nhsens
 -- 14. add constraints as CASL sentences 
 constrsens <- foldM (\l1 sc -> do 
                         l2 <- constr_to_sens hlid hsig (show hlid) sc
                         return $ l1 ++ l2) [] $ sem_constr hlid   
     -- 15. this is V(\Gamma_Sigma)
 let makeVSen s = makeNamed ("ga_V_"++show s)
                   $ CBasic.mkForall [CBasic.mkVarDecl (genToken "w") st, CBasic.mkVarDecl (genToken "x") s] 
                   $ CBasic.mkPredication (CBasic.mkQualPred domain $ CBasic.Pred_type [st, s] nullRange)
                                                                                                [CBasic.Qual_var (genToken "w") st nullRange,
                                                                                                 CBasic.Qual_var (genToken "x") s nullRange]
     vsens = map makeVSen $ Set.toList cvars 
 -- 16. return results
 -- trace (concatMap (\x -> show x ++ "\n") ncsens) $ 
 return (lamsig, csens' ++ vsens ++ domsens ++ ncsens ++ constrsens)


mapNamedSentence :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree =>
                    String -> -- name of the hybrid logic, for generated names
                    ((sig, [Named sen]) -> Result (CSign.CASLSign, [Named CBasic.CASLFORMULA])) ->  
                    (sig -> sen -> Result CBasic.CASLFORMULA) -> 
                    lid ->
                    GTypes.HSign sig -> Named (GTypes.HFORMULA sen symb_items raw_sym) -> Named CBasic.CASLFORMULA
mapNamedSentence hl mapBTheory mapBSen baseLid hsig nsen = nsen {sentence = mapHSentence hl mapBTheory mapBSen baseLid hsig $ sentence nsen}

mapHSentence :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree =>
                String -> 
                ((sig, [Named sen]) -> Result (CSign.CASLSign, [Named CBasic.CASLFORMULA])) -> 
                (sig -> sen -> Result CBasic.CASLFORMULA) -> 
                lid ->
                GTypes.HSign sig -> GTypes.HFORMULA sen symb_items raw_sym -> CBasic.CASLFORMULA
mapHSentence hl mapBTheory mapBSen baseLid hsig hsen = 
 let 
  x = genToken "X"
  st = genName $ "ST_" ++ hl
  hth = GMethods.HTheoryAna hsig Set.empty [] [] emptyGlobalAnnos []
 in CBasic.mkForall [CBasic.mkVarDecl x st] $ 
       mapSentenceAux hl mapBTheory mapBSen baseLid hth x st hsen

isVar :: Token -> GMethods.HTheoryAna sig sen symb_items raw_sym sym -> Bool
isVar nom hth = 
 let nomVars = concatMap (\x -> case x of 
                                 GTypes.ASymbol (GTypes.HSymb n GTypes.Nom) -> [n]
                                 _ -> []) $ 
               GMethods.hVars hth
 in (simpleIdToId nom) `elem` nomVars

mapSentenceAux :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree =>
                  String ->
                  ((sig, [Named sen]) -> Result (CSign.CASLSign, [Named CBasic.CASLFORMULA])) ->
                  (sig -> sen -> Result CBasic.CASLFORMULA) ->
                  lid ->
                  GMethods.HTheoryAna sig sen symb_items raw_sym sym ->
                  CBasic.VAR -> CBasic.SORT ->
                  GTypes.HFORMULA sen symb_items raw_sym -> CBasic.CASLFORMULA
mapSentenceAux hl mapBTheory mapBSen baseLid hth x st hsen = case hsen of
 GTypes.Nominal _s b i _ -> CBasic.mkStEq 
                          (CBasic.Qual_var x st nullRange) $ 
                          if b then CBasic.Qual_var i st nullRange
                          else CBasic.Application (CBasic.mkQualOp (simpleIdToId i) $ CBasic.Op_type CBasic.Total [] st nullRange) [] nullRange
 GTypes.Base_formula f _ -> let
   hsig = GMethods.hSign hth 
   Result ds f' = mapBSen (GTypes.baseSig hsig) f
  in case f' of
      Nothing  -> error $ "can't translate sentence: " ++ show ds
      Just f'' -> addX st x f''
 GTypes.AtState _s nom hf _ -> 
                            let cf = mapSentenceAux hl mapBTheory mapBSen baseLid hth x st hf 
                                t = if isVar nom hth then CBasic.Qual_var nom st nullRange else 
                                      CBasic.mkAppl (CBasic.mkQualOp (simpleIdToId nom) $ CBasic.Op_type CBasic.Total [] st nullRange) []
                            in CInd.substitute x st t cf 
                         -- mapSentenceAux i st sen does not work, because i should not be a var. apply a substitution of x with i instead 
 GTypes.Negation hf _ -> CBasic.Negation (mapSentenceAux hl mapBTheory mapBSen baseLid hth x st hf) nullRange
 GTypes.Conjunction hfs _ -> CBasic.Junction CBasic.Con (map (mapSentenceAux hl mapBTheory mapBSen baseLid hth x st) hfs) nullRange
 GTypes.Disjunction hfs _ -> CBasic.Junction CBasic.Dis (map (mapSentenceAux hl mapBTheory mapBSen baseLid hth x st) hfs) nullRange
 GTypes.Implication hf1 hf2 _ -> CBasic.Relation (mapSentenceAux hl mapBTheory mapBSen baseLid hth x st hf1) 
                                                 CBasic.Implication 
                                                 (mapSentenceAux hl mapBTheory mapBSen baseLid hth x st hf2) 
                                                 nullRange
 GTypes.Equivalence hf1 hf2 _ -> CBasic.Relation (mapSentenceAux hl mapBTheory mapBSen baseLid hth x st hf1) 
                                                 CBasic.Equivalence 
                                                 (mapSentenceAux hl mapBTheory mapBSen baseLid hth x st hf2) 
                                                 nullRange
 GTypes.BoxFormula _s md hf _ -> CBasic.mkForall [CBasic.mkVarDecl (genToken "Y") st] $ 
                                               CBasic.mkImpl 
                                                 (CBasic.mkPredication (CBasic.mkQualPred (simpleIdToId md) $ CBasic.Pred_type [st,st] nullRange) 
                                                                       [CBasic.Qual_var x st nullRange, CBasic.Qual_var (genToken "Y") st nullRange]) $ 
                                                 mapSentenceAux hl mapBTheory mapBSen baseLid hth (genToken "Y") st hf
 GTypes.DiamondFormula _s md hf _ -> CBasic.mkExist [CBasic.mkVarDecl (genToken "Y") st] $ 
                                               CBasic.Junction CBasic.Con 
                                                 [CBasic.mkPredication (CBasic.mkQualPred (simpleIdToId md) $ CBasic.Pred_type [st,st] nullRange) 
                                                                       [CBasic.Qual_var x st nullRange, CBasic.Qual_var (genToken "Y") st nullRange],
                                                  mapSentenceAux hl mapBTheory mapBSen baseLid hth (genToken "Y") st hf]
                                                 nullRange
 GTypes.QuantNominals q noms hf _ -> (case q of 
                                          GTypes.HUniversal _ -> CBasic.mkForall
                                          GTypes.HExistential _ -> CBasic.mkExist) 
                                      (map (\n -> CBasic.mkVarDecl n st) noms)
                                      $ mapSentenceAux hl mapBTheory mapBSen baseLid
                                          (hth{GMethods.hVars = foldl (\l n -> (GTypes.ASymbol $ GTypes.HSymb (simpleIdToId n) GTypes.Nom):l) (GMethods.hVars hth) noms}) 
                                          x st hf 
 GTypes.QuantVarsParse _ _ _ _ -> error "GenHyb.GenComor.mapSentenceAux: sentence not parsed"
 GTypes.QuantVars q vars hf _ -> let 
   hsig = GMethods.hSign hth
   domainSen xi si = CBasic.mkPredication (CBasic.mkQualPred (genName $ "domain_" ++ hl) $ CBasic.Pred_type [st, si] nullRange)
                                           [CBasic.Qual_var x st nullRange,
                                            CBasic.mkAppl (CBasic.Qual_op_name (simpleIdToId xi) (addSortToOpType st $ CBasic.Op_type CBasic.Total [] si nullRange) nullRange) 
                                                           [CBasic.Qual_var x st nullRange]]
   baseSig = GTypes.baseSig hsig
   Result ds resTh = mapBTheory (baseSig, [])
   (_, csens) = case resTh of
                  Nothing -> error $ "could not translate theory:" ++ show ds
                  Just th -> th
   addVarAsConst bSig vi = 
    let Result ds' resTh' = add_symb_to_sign baseLid bSig vi 
    in case resTh' of 
         Nothing ->  error $ "could not add variable as constant:" ++ show ds'
         Just th -> th
   getCSens vi = let
     Result ds'' resTh'' = mapBTheory (addVarAsConst baseSig vi, [])
    in case resTh'' of
         Nothing -> error $ "could not translate theory with added variable:" ++ show ds''
         Just (_, sens) -> sens
   --  keep the sentences that appear only in the second list of sentences
   gamma_xi vi = map (\f -> f { sentence = CBasic.Quantification CBasic.Universal [CBasic.Var_decl [genToken "w"] st nullRange] (addX st (genToken "w") $ sentence f) nullRange} )
                     $ filter (\s -> not (s `elem` csens)) $ getCSens vi
   vis = map (\v -> case raw_to_symbol baseLid v of 
                      Nothing -> error $ "could not convert raw to symbol"
                      Just y -> y) vars
   baseSigVars = foldl addVarAsConst baseSig vis
   hsig' = hsig {GTypes.baseSig = baseSigVars}
   cvars = map (\rs -> case raw_to_var baseLid rs of
                        Nothing -> error $ "could not convert symbol to variable: " ++ show rs
                        Just (v, s) -> (v, s) ) vars
   senWithVarAppl = CBasic.mkImpl 
                     (CBasic.Junction CBasic.Con (
                                      (map sentence $ 
                                          concatMap gamma_xi vis
                                      ) ++ (map (\(xi,si) -> domainSen xi si) cvars)
                                                 ) 
                                      nullRange
                     )
                    $ mapSentenceAux hl mapBTheory mapBSen baseLid (hth {GMethods.hSign = hsig'}) x st hf
   senRepl = foldl (\csen (xi,si) -> replaceVarAppls xi si csen) senWithVarAppl cvars
  in (case q of 
       GTypes.HUniversal _ -> CBasic.mkForall
       GTypes.HExistential _ -> CBasic.mkExist)
      (map (\(v,s) -> CBasic.mkVarDecl v s) cvars) senRepl
     

