{- |
Module      :  $Header$
Description :  Static analysis for object logics defined in LF
Copyright   :  (c) Kristina Sojakova, DFKI Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  k.sojakova@jacobs-university.de
Stability   :  experimental
Portability :  portable
-}
module LF.AnalysisOL where

import LF.AS
import LF.Sign
import LF.Morphism
import LF.Analysis
import LF.Twelf2GR
import LF.Framework

import Common.ExtSign
import Common.GlobalAnnotations
import Common.AS_Annotation
import Common.Result
import Common.Doc
import Common.DocUtils

import System.IO.Unsafe

import qualified Data.Map as Map

-- basic analysis for object logics of LF
basicAnalysisOL :: Morphism -> (BASIC_SPEC, Sign, GlobalAnnos) ->
                   Result (BASIC_SPEC, ExtSign Sign Symbol, [Named EXP])
basicAnalysisOL ltruth (bs@(Basic_spec items), initsig, _) = do
  let (sig,sens) = unsafePerformIO $ makeSigSenOL ltruth initsig items
  let syms = getSymbols sig
  let fs = makeNamedForms sens $ map r_annos $ getSenItems items
  return (bs, ExtSign sig syms, fs)

-- constructs the signatures and sentences
makeSigSenOL :: Morphism -> Sign -> [Annoted BASIC_ITEM] ->
                IO (Sign,[(NAME,Sentence)])
makeSigSenOL ltruth sig items = do
  -- make a Twelf file
  let sen_type = case mapSymbol sen_type_symbol ltruth of
                      Nothing -> error "Sentence type cannot be constructed."
                      Just t -> show $ pretty t
  let lSyn = target ltruth
  let imp = mkRead $ sigBase lSyn
  let cont1 = if (sig == lSyn) then "" else
        (show $ vcat $ map pretty $ getLocalDefs lSyn) ++ "\n"
  let cont2 = printSigItems $ getSigItems items
  let cont3 = printSenItems sen_type $ getSenItems items
  let s1 = mkSig gen_sig1 $ mkIncl (sigModule lSyn) ++ cont1 ++ cont2
  let s2 = mkSig gen_sig2 $ mkIncl gen_sig1 ++ cont3
  let contents = imp ++ "\n" ++ s1 ++ "\n" ++ s2
  writeFile gen_file contents
  
  -- run Twelf on the created file
  libs <- twelf2SigMor gen_file
  
  -- construct the signature and sentences
  let sig1 = getSigFromLibs gen_sig1 libs
  let sig2 = getSigFromLibs gen_sig2 libs
  let sens = map (\ (s,(v,_)) -> (symName s, v)) $ getAnnoSyms $
                getLocalDefs sig2
  return (sig1,sens)

-----------------------------------------------------------------
-----------------------------------------------------------------

{- converts a mapping of raw symbols to a mapping of symbols to expressions
   annotated with their type -}
mapAnalysisOL :: Morphism -> Map.Map String String -> Sign ->
                 Map.Map Symbol (EXP,EXP)
mapAnalysisOL ltruth m sig = unsafePerformIO $ mapAnalysisOLIO ltruth m sig

mapAnalysisOLIO :: Morphism -> Map.Map String String -> Sign ->
                   IO (Map.Map Symbol (EXP,EXP))
mapAnalysisOLIO ltruth m sig = do
  -- make a Twelf file
  let cont1 = show $ pretty sig
  let cont2 = concat $ map (\ (k,v) -> k ++ " = " ++ v ++ ".\n") $ Map.toList m
  let lSyn = target ltruth
  let imp = mkRead $ sigBase lSyn

  let s1 = mkSig gen_sig1 $ mkIncl (sigModule lSyn) ++ cont1
  let s2 = mkSig gen_sig2 $ mkIncl gen_sig1 ++ cont2
  let contents = imp ++ "\n" ++ s1 ++ "\n" ++ s2
  writeFile gen_file contents

  -- run Twelf on the created file
  libs <- twelf2SigMor gen_file
  
  -- construct the mapping
  let sig' = getSigFromLibs gen_sig2 libs
  return $ Map.fromList $ getAnnoSyms $ getLocalDefs sig'
