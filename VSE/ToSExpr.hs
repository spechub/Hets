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

import Common.SExpr
import Common.Result

toSExpr :: Sign f Procs -> Sentence -> Result SExpr
toSExpr sig s = do
  ns <- sentenceToSExpr sig s
  return $ case s of
    ExtFORMULA (Ranged (Defprocs _) _) ->
        SList [SSymbol "defprocs-sentence", ns]
    Sort_gen_ax _ _ ->
        SList [SSymbol "generatedness-sentence", ns]
    _ -> SList [SSymbol "formula-sentence", ns]

sentenceToSExpr :: Sign f Procs -> Sentence -> Result SExpr
sentenceToSExpr sig = foldFormula $ sRec True sig $ dlFormulaToSExpr sig

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
      nt <- foldTerm (sRec False sig $ error "vDeclToSExpr") trm
      return $ SList [SSymbol "vardecl", w, ty, nt]

progToSExpr :: Sign f Procs -> Program -> Result SExpr
progToSExpr sig = let
  pRec = sRec False sig (error "progToSExpr")
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
        Predication p ts _ -> do
          nts <- mapM termToSExpr ts
          return $ SList $ SSymbol "call" : predToSSymbol sig p : nts
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
defprocToSExpr sig (Defproc k n vs p r) = do
  s <- progToSExpr sig p
  return $ SList
    [ SSymbol $ case k of
        Proc -> "defproc"
        Func -> "deffuncproc"
    , case lookupProc n sig of
        Nothing -> error "defprocToSExpr"
        Just pr -> case profileToOpType pr of
          Just ot -> opToSSymbol sig $ Qual_op_name n (toOP_TYPE ot) r
          _ -> predToSSymbol sig $ Qual_pred_name n
               (toPRED_TYPE $ profileToPredType pr) r
    , SList $ map varToSSymbol vs
    , s ]
