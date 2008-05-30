{- |
Module      :  $Header$
Copyright   :  (c) C. Maeder, DFKI Bremen 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

analysis of VSE logic extension of CASL
-}

module VSE.Ana where

import qualified Data.Map as Map

import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.ExtSign
import Common.Id
import Common.Result
import Common.Lib.State

import CASL.AS_Basic_CASL
import CASL.Sign
import CASL.MixfixParser
import CASL.Overload
import CASL.StaticAna

import VSE.As

type Procs = Map.Map Id Profile

basicAna
  :: (BASIC_SPEC () Procdecls Dlformula,
      Sign Dlformula Procs, GlobalAnnos)
  -> Result (BASIC_SPEC () Procdecls Dlformula,
             ExtSign (Sign Dlformula Procs) Symbol,
             [Named Sentence])
basicAna =
    basicAnalysis minExpForm (const return) anaProcDecls anaMix

anaMix :: Mix () Procdecls Dlformula Procs
anaMix = emptyMix

minExpForm :: Min Dlformula Procs
minExpForm sig (Ranged f r) = case f of
  Dlformula b p s -> do
    n <- minExpFORMULA minExpForm sig s
    return $ Ranged (Dlformula b p n) r
  Defprocs ps -> return $ Ranged (Defprocs ps) r

anaProcDecls :: Ana Procdecls () Procdecls Dlformula Procs
anaProcDecls _ ds@(Procdecls ps _) = do
  mapM_ (anaProcDecl . item) ps
  return ds

anaProcDecl :: Sigentry -> State (Sign Dlformula Procs) ()
anaProcDecl (Procedure i p q) = case p of
   Profile a r -> do
     updateExtInfo (\ m ->
       let n = Map.insert i p m in case Map.lookup i m of
         Just o -> if p == o then
           hint n ("repeated procedure " ++ showId i "") q
           else warning n ("redeclared procedure " ++ showId i "") q
         Nothing -> return n)
     case r of
       Just s -> addOp (emptyAnno ())
                 (OpType Partial (map (\ (Procparam In t) -> t) a) s) i
       _ -> return ()
