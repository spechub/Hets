{- |
Module      :  $Header$
Description :  translate VSE to S-Expressions
Copyright   :  (c) C. Maeder, DFKI 2008
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

translation of VSE to S-Expressions
-}

module VSE.ToSExpr where

import VSE.As
import VSE.Ana
import VSE.Fold

import CASL.AS_Basic_CASL
import CASL.Fold
import CASL.Sign
import CASL.ToSExpr

import Common.AS_Annotation
import Common.Id
import Common.LibName
import Common.ProofUtils
import Common.SExpr

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Char (toLower)
import Data.List(sortBy)

addUniformRestr :: Sign f Procs -> [Named Sentence] ->
                   (Sign f Procs, [Named Sentence])
addUniformRestr sig nsens = let
  namedConstr = filter (\ns -> case sentence ns of
                                ExtFORMULA
                                 (Ranged
                                   (RestrictedConstraint _ _ _)
                                  _) -> True
                                _ -> False ) nsens
  restrConstr = map sentence namedConstr
  restrToSExpr (procs, tSens)
               (ExtFORMULA
                 (Ranged (RestrictedConstraint constrs restr _flag) _r)) =
   let
    (genSorts, genOps, _maps) = recover_Sort_gen_ax constrs
    genUniform sorts ops s = let
      hasResSort sn (Qual_op_name _ opType _) = res_OP_TYPE opType == sn
      hasResSort _ _ = error "should have qual names"
      ctors = sortBy (\ (Qual_op_name _ (Op_type _ args1 _ _) _)
                        (Qual_op_name _ (Op_type _ args2 _ _) _) ->
                        if length args1 < length args2 then LT else GT) $
              filter (hasResSort s) ops
      genCodeForCtor (Op_name _ ) _ = error "should have qual names"
      genCodeForCtor (Qual_op_name ctor (Op_type _ args sn _) _) prg = let
        decls = genVars args
        vs = map (\ (i, a) -> Var_decl [i] a nullRange) decls
        recCalls = map (\(i, x) ->
                         Ranged (Call (Predication
                                        (Qual_pred_name
                                          (gnUniformName s)
                                         (Pred_type [x] nullRange) nullRange)
                                        [Qual_var i x nullRange] nullRange
                                      )) nullRange) $
                   filter (flip elem sorts . snd) decls
        recCallsSeq = if null recCalls then Ranged Skip nullRange else
                      foldr1 (\p1 p2 -> Ranged (Seq p1 p2) nullRange) recCalls
        in case recCalls of
         [] -> Ranged (
                Block (Var_decl [yVar] s nullRange : vs)
              (Ranged (Seq
                (Ranged
                   (Assign yVar (Qual_var xVar sn nullRange)
                    ) nullRange)
                (Ranged (Seq (Ranged
                                   (Assign
                                     yVar
                                     (Application
                                      (Qual_op_name
                                      ctor
                                     (Op_type Partial args sn nullRange)
                                     nullRange)
                                      (map toQualVar vs)
                                      nullRange))
                                   nullRange)
                        (Ranged (If (Strong_equation
                               (Application
                                 (
                                  Qual_op_name
                                   (gnEqName s)
                                   (Op_type Partial [s,s]
                                    uBoolean nullRange)
                                  nullRange
                                 ) [Qual_var
                                      xVar
                                      s nullRange,
                                     Qual_var
                                      yVar
                                      s nullRange
                                    ] nullRange)
                               aTrue nullRange)
                          (Ranged Skip nullRange)
                          prg)nullRange))
                nullRange )) nullRange) ) nullRange
         _ -> Ranged (
                 Block (Var_decl [yVar] s nullRange : vs)
                (Ranged (Seq (Ranged (Assign yVar
                                      (Qual_var xVar sn nullRange)
                                     ) nullRange)
                             (Ranged
                              (Seq recCallsSeq
                               (Ranged (Seq
                                  (Ranged
                                    (Assign
                                      yVar
                                     (Application
                                      (Qual_op_name
                                     ctor
                                     (Op_type Partial args sn nullRange)
                                     nullRange)
                                      (map toQualVar vs)
                                      nullRange))
                                   nullRange)
                                (Ranged (If (Strong_equation
                                 ( Application
                                 ( Qual_op_name
                                   (gnEqName s)
                                   (Op_type Partial [s,s]
                                    uBoolean nullRange)
                                  nullRange
                                 ) [Qual_var
                                      xVar
                                      s nullRange,
                                     Qual_var
                                      yVar
                                      s nullRange
                                    ] nullRange)
                                aTrue nullRange)
                               (Ranged Skip nullRange) prg) nullRange))
                               nullRange )) nullRange)) nullRange) ) nullRange
                             in
     [makeNamed "" $  ExtFORMULA $
     Ranged (Defprocs  [
      Defproc Proc (gnUniformName s) [xVar]
      (Ranged (
        Block [] ( foldr genCodeForCtor (Ranged Abort nullRange)
                   ctors)
              ) nullRange
      )
      nullRange])
     nullRange,
     (makeNamed "" $
     Quantification Universal [Var_decl [xVar] s nullRange]
      (Implication
       ( ExtFORMULA $ Ranged
          (Dlformula Diamond ( Ranged
            (Call $ Predication
              (Qual_pred_name
                (Map.findWithDefault (gnRestrName s) s restr)
                (Pred_type [s] nullRange) nullRange)
               [Qual_var xVar s nullRange] nullRange) nullRange)
            (True_atom nullRange))
          nullRange)
       ( ExtFORMULA $ Ranged
          (Dlformula Diamond (Ranged
            (Call $ Predication
              (Qual_pred_name (gnUniformName s)
                (Pred_type [s] nullRange) nullRange)
               [Qual_var xVar s nullRange] nullRange) nullRange)
            (True_atom nullRange))
          nullRange) True nullRange) nullRange) {isAxiom = False}]
    procDefs = concatMap (genUniform genSorts genOps) genSorts
    procs' = Map.fromList $
             map (\s -> (gnUniformName s,
                         Profile [Procparam In s] Nothing)) genSorts
   in
    (Map.union procs procs', tSens ++ procDefs)
  restrToSExpr _ _ = error "should not be anything than restricted constraints"
  (newProcs, trSens) = foldl restrToSExpr (Map.empty, []) restrConstr
                            in
 (sig{
   predMap = addMapSet (predMap sig) $ procsToPredMap $ Procs newProcs,

   extendedInfo = Procs $ Map.union newProcs (procsMap $ extendedInfo sig)},
  nameAndDisambiguate $
    trSens ++ filter (not . flip elem namedConstr) nsens)

namedSenToSExpr :: Sign f Procs -> Named Sentence -> SExpr
namedSenToSExpr sig ns =
  SList
    [ SSymbol "asentence"
    , SSymbol $ transString $ senAttr ns
    , SSymbol $ if isAxiom ns then "axiom" else "obligation"
    , SSymbol $ if isAxiom ns then "proved" else "open"
    , senToSExpr sig $ sentence ns ]

senToSExpr :: Sign f Procs -> Sentence -> SExpr
senToSExpr sig s = let ns = sentenceToSExpr sig s in case s of
    ExtFORMULA (Ranged (Defprocs _) _) ->
        SList [SSymbol "defprocs-sentence", ns]
    Sort_gen_ax _ _ ->
        SList [SSymbol "generatedness-sentence", ns]
    _ -> SList [SSymbol "formula-sentence", ns]

sentenceToSExpr :: Sign f Procs -> Sentence -> SExpr
sentenceToSExpr sign = let sig = addSig const sign boolSig in
  foldFormula $ sRec sig $ dlFormulaToSExpr sig

dlFormulaToSExpr :: Sign f Procs -> Dlformula -> SExpr
dlFormulaToSExpr sig = vseFormsToSExpr sig . unRanged

vseFormsToSExpr :: Sign f Procs -> VSEforms -> SExpr
vseFormsToSExpr sig vf = case vf of
  Dlformula b p s ->
    SList [SSymbol $ case b of
         Box -> "box"
         Diamond -> "diamond", progToSExpr sig p, sentenceToSExpr sig s]
  Defprocs ds ->
    SList $ SSymbol "defprocs" : map (defprocToSExpr sig) ds
  RestrictedConstraint _ _ _ ->
   error "restricted constraints should be handled separately"

vDeclToSExpr :: Sign f Procs -> VarDecl -> SExpr
vDeclToSExpr sig (VarDecl v s m _) =
  let vd@(SList [_, w, ty]) = varDeclToSExpr (v, s) in
  case m of
    Nothing -> vd
    Just trm -> SList [ SSymbol "vardecl", w, ty
                      , foldTerm (sRec sig $ error "vDeclToSExpr") trm ]

procIdToSSymbol :: Sign f Procs -> Id -> SExpr
procIdToSSymbol sig n = case lookupProc n sig of
        Nothing -> error "procIdToSSymbol"
        Just pr -> case profileToOpType pr of
          Just ot -> opIdToSSymbol sig n ot
          _ -> predIdToSSymbol sig n $ profileToPredType pr

progToSExpr :: Sign f Procs -> Program -> SExpr
progToSExpr sig = let
  pRec = sRec sig (error "progToSExpr")
  termToSExpr = foldTerm pRec
  formToSExpr = foldFormula pRec
  in foldProg FoldRec
  { foldAbort = const $ SSymbol "abort"
  , foldSkip = const $ SSymbol "skip"
  , foldAssign = \ _ v t ->
      SList [SSymbol "assign", varToSSymbol v, termToSExpr t]
  , foldCall = \ (Ranged _ r) f ->
      case f of
        Predication (Qual_pred_name i _ _) ts _ ->
          SList $ SSymbol "call" : procIdToSSymbol sig i : map termToSExpr ts
        _ -> sfail "Call" r
  , foldReturn = \ _ t -> SList [SSymbol "return", termToSExpr t]
  , foldBlock = \ (Ranged (Block vs p) _) _ _ ->
      let (vds, q) = addInits (toVarDecl vs) p
          ps = progToSExpr sig q
          nvs = map (vDeclToSExpr sig) vds
      in if null nvs then ps else SList [SSymbol "vblock", SList nvs, ps]
  , foldSeq = \ _ s1 s2 -> SList [SSymbol "seq", s1, s2]
  , foldIf = \ _ c s1 s2 -> SList [SSymbol "if", formToSExpr c, s1, s2]
  , foldWhile = \ _ c s -> SList [SSymbol "while", formToSExpr c, s] }

defprocToSExpr :: Sign f Procs -> Defproc -> SExpr
defprocToSExpr sig (Defproc k n vs p _) = SList
    [ SSymbol $ case k of
        Proc -> "defproc"
        Func -> "deffuncproc"
    , procIdToSSymbol sig n
    , SList $ map varToSSymbol vs
    , progToSExpr sig p ]

paramToSExpr :: Procparam -> SExpr
paramToSExpr (Procparam k s) = SList
  [ SSymbol $ map toLower $ show k
  , sortToSSymbol s ]

procsToSExprs :: (Id -> Bool) -> Sign f Procs -> [SExpr]
procsToSExprs f sig =
    map (\ (n, pr@(Profile as _)) -> case profileToOpType pr of
      Nothing -> SList
        [ SSymbol "procedure"
        , predIdToSSymbol sig n $ profileToPredType pr
        , SList $ map paramToSExpr as ]
      Just ot -> SList
        [ SSymbol "funcprocedure"
        , opIdToSSymbol sig n ot
        , SList $ map sortToSSymbol $ opArgs ot
        , sortToSSymbol $ opRes ot ])
    $ Map.toList $ Map.filterWithKey (\ i _ -> f i)
    $ procsMap $ extendedInfo sig

vseSignToSExpr :: Sign f Procs -> SExpr
vseSignToSExpr sig =
  let e = extendedInfo sig in
    SList $ SSymbol "signature" : sortSignToSExprs sig
      : predMapToSExprs sig (diffMapSet (predMap sig) $ procsToPredMap e)
      ++ opMapToSExprs sig (diffOpMapSet (opMap sig) $ procsToOpMap e)
      ++ procsToSExprs (const True) sig

qualVseSignToSExpr :: SIMPLE_ID -> LibId -> Sign f Procs -> SExpr
qualVseSignToSExpr nodeId libId sig =
  let e = extendedInfo sig in
    SList $ SSymbol "signature" : sortSignToSExprs sig
          { sortSet = Set.filter (isQualNameFrom nodeId libId)
            $ sortSet sig }
      : predMapToSExprs sig
            (Map.filterWithKey (\ i _ -> isQualNameFrom nodeId libId i)
            $ diffMapSet (predMap sig) $ procsToPredMap e)
      ++ opMapToSExprs sig
            (Map.filterWithKey (\ i _ -> isQualNameFrom nodeId libId i)
            $ diffOpMapSet (opMap sig) $ procsToOpMap e)
      ++ procsToSExprs (isQualNameFrom nodeId libId) sig
