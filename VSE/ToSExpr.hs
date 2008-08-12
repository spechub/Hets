{- |
Module      :  $Header$
Description :  translate VSE to S-Expressions
Copyright   :  (c) C. Maeder, DFKI 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt

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
import Common.SExpr

import qualified Data.Map as Map
import Data.Char (toLower)

namedSenToSExpr :: Sign f Procs -> Named Sentence -> SExpr
namedSenToSExpr sig ns =
  SList
    [ SSymbol "asentence"
    , SSymbol $ transString $ senAttr ns
    , SSymbol $ if isAxiom ns then "axiom" else "lemma"
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

procsToSExprs :: Sign f Procs -> [SExpr]
procsToSExprs sig =
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
    $ Map.toList $ procsMap $ extendedInfo sig

vseSignToSExpr :: Sign f Procs -> SExpr
vseSignToSExpr sig =
  let e = extendedInfo sig in
    SList $ SSymbol "signature" : sortSignToSExprs sig
      : predMapToSExprs sig (diffMapSet (predMap sig) $ procsToPredMap e)
      ++ opMapToSExprs sig (diffMapSet (opMap sig) $ procsToOpMap e)
      ++ procsToSExprs sig
