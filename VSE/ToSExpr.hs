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

import CASL.AS_Basic_CASL
import CASL.Fold
import CASL.Sign
import CASL.ToSExpr

import Common.AS_Annotation
import Common.Id
import Common.Result
import Common.SExpr

import qualified Data.Map as Map
import Data.Char (toLower)

namedSenToSExpr :: Sign f Procs -> Named Sentence -> Result SExpr
namedSenToSExpr sig ns = do
  t <- senToSExpr sig $ sentence ns
  return $ SList
    [ SSymbol "asentence"
    , SSymbol $ transString $ senAttr ns
    , SSymbol $ if isAxiom ns then "axiom" else "lemma"
    , SSymbol $ if isAxiom ns then "proved" else "open"
    , t ]

senToSExpr :: Sign f Procs -> Sentence -> Result SExpr
senToSExpr sig s = do
  ns <- sentenceToSExpr sig s
  return $ case s of
    ExtFORMULA (Ranged (Defprocs _) _) ->
        SList [SSymbol "defprocs-sentence", ns]
    Sort_gen_ax _ _ ->
        SList [SSymbol "generatedness-sentence", ns]
    _ -> SList [SSymbol "formula-sentence", ns]

sentenceToSExpr :: Sign f Procs -> Sentence -> Result SExpr
sentenceToSExpr sig = foldFormula $ sRec sig $ dlFormulaToSExpr sig

dlFormulaToSExpr :: Sign f Procs -> Dlformula -> Result SExpr
dlFormulaToSExpr sig = vseFormsToSExpr sig . unRanged

vseFormsToSExpr :: Sign f Procs -> VSEforms -> Result SExpr
vseFormsToSExpr sig vf = case vf of
  Dlformula b p s -> do
    sp <- progToSExpr sig p
    ns <- sentenceToSExpr sig s
    return $ SList [SSymbol $ case b of
         Box -> "box"
         Diamond -> "diamond", sp, ns]
  Defprocs ds -> do
    nds <- mapM (defprocToSExpr sig) ds
    return $ SList $ SSymbol "defprocs" : nds

vDeclToSExpr :: Sign f Procs -> VarDecl -> Result SExpr
vDeclToSExpr sig (VarDecl v s m _) =
  let vd@(SList [_, w, ty]) = varDeclToSExpr (v, s) in
  case m of
    Nothing -> return vd
    Just trm -> do
      nt <- foldTerm (sRec sig $ error "vDeclToSExpr") trm
      return $ SList [SSymbol "vardecl", w, ty, nt]

procIdToSSymbol :: Sign f Procs -> Id -> SExpr
procIdToSSymbol sig n = case lookupProc n sig of
        Nothing -> error "procIdToSSymbol"
        Just pr -> case profileToOpType pr of
          Just ot -> opIdToSSymbol sig n ot
          _ -> predIdToSSymbol sig n $ profileToPredType pr

progToSExpr :: Sign f Procs -> Program -> Result SExpr
progToSExpr sig = let
  pRec = sRec sig (error "progToSExpr")
  termToSExpr = foldTerm pRec
  formToSExpr = foldFormula pRec
  in foldProg FoldRec
  { foldAbort = const $ return $ SSymbol "abort"
  , foldSkip = const $ return $ SSymbol "skip"
  , foldAssign = \ _ v t -> do
      nt <- termToSExpr t
      return $ SList [SSymbol "assign", varToSSymbol v, nt]
  , foldCall = \ (Ranged _ r) f ->
      case f of
        Predication (Qual_pred_name i _ _) ts _ -> do
          nts <- mapM termToSExpr ts
          return $ SList $ SSymbol "call" : procIdToSSymbol sig i : nts
        _ -> sfail "Call" r
  , foldReturn = \ _ t -> do
      nt <- termToSExpr t
      return $ SList [SSymbol "return", nt]
  , foldBlock = \ (Ranged (Block vs p) _) _ _ -> do
      let (vds, q) = addInits (toVarDecl vs) p
      ps <- progToSExpr sig q
      nvs <- mapM (vDeclToSExpr sig) vds
      return $ if null nvs then ps else SList [SSymbol "vblock", SList nvs, ps]
  , foldSeq = \ _ p1 p2 -> do
      s1 <- p1
      s2 <- p2
      return $ SList [SSymbol "seq", s1, s2]
  , foldIf = \ _ c p1 p2 -> do
      f <- formToSExpr c
      s1 <- p1
      s2 <- p2
      return $ SList [SSymbol "if", f, s1, s2]
  , foldWhile = \ _ c p -> do
      f <- formToSExpr c
      s <- p
      return $ SList [SSymbol "while", f, s] }

defprocToSExpr :: Sign f Procs -> Defproc -> Result SExpr
defprocToSExpr sig (Defproc k n vs p _) = do
  s <- progToSExpr sig p
  return $ SList
    [ SSymbol $ case k of
        Proc -> "defproc"
        Func -> "deffuncproc"
    , procIdToSSymbol sig n
    , SList $ map varToSSymbol vs
    , s ]

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
