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

import CASL.AS_Basic_CASL
import CASL.Fold
import CASL.Sign
import CASL.ToSExpr

import Common.SExpr
import Common.Result

toSExpr :: Sign f Procs -> Sentence -> Result SExpr
toSExpr sig s = case s of
    ExtFORMULA (Ranged (Defprocs ds) _) -> do
      nds <- mapM (defprocToSExpr sig) ds
      return $ SList $ SSymbol "defprocs-sentence" : nds
    _ -> do
      ns <- sentenceToSExpr sig s
      return $ SList $ SSymbol "formula-sentence" : [ns]

sentenceToSExpr :: Sign f Procs -> Sentence -> Result SExpr
sentenceToSExpr sig = foldFormula $ sRec True sig $ dlFormulaToSExpr sig

dlFormulaToSExpr :: Sign f Procs -> Dlformula -> Result SExpr
dlFormulaToSExpr sig = vseFormsToSExpr sig . unRanged

vseFormsToSExpr :: Sign f Procs -> VSEforms -> Result SExpr
vseFormsToSExpr sig vf = case vf of
  Dlformula b p s -> do
    sp <- progToSExpr sig p
    ns <- sentenceToSExpr sig s
    return $ SList $ SSymbol (case b of
         Box -> "box"
         Diamond -> "diamond") : [sp, ns]
  Defprocs ds -> do
    nds <- mapM (defprocToSExpr sig) ds
    return $ SList nds

progToSExpr :: Sign f Procs -> Program -> Result SExpr
progToSExpr = undefined

defprocToSExpr :: Sign f Procs -> Defproc -> Result SExpr
defprocToSExpr = undefined

