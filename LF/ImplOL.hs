{- |
Module      :  $Header$
Description :  Implementation of functions necessary to instantiate
               Logic.hs for object logics defined in LF
Copyright   :  (c) Kristina Sojakova, DFKI Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  k.sojakova@jacobs-university.de
Stability   :  experimental
Portability :  portable
-}
module LF.ImplOL
  ( basicAnalysisOL
  , inducedFromToMorphismOL
  ) where

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
                      Nothing -> error $ badSenTypeError
                      Just t -> show $ pretty t
  let lSyn = target ltruth
  let imp = mkRead $ sigBase lSyn
  let cont1 = if (sig == lSyn || (null $ getLocalDefs sig)) then "" else
        (show $ vcat $ map pretty $ getLocalDefs sig) ++ "\n"
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
  let sens = getSens sig2
  return (sig1,sens)

-----------------------------------------------------------------
-----------------------------------------------------------------

-- induced_from_to_morphism for object logics
inducedFromToMorphismOL :: Morphism -> Map.Map RAW_SYM RAW_SYM ->
                           ExtSign Sign Symbol -> ExtSign Sign Symbol ->
                           Result Morphism
inducedFromToMorphismOL ltruth m (ExtSign sig1 _) (ExtSign sig2 _) =
  inducedFromToMorphism (translMapAnalysisOL ltruth m sig1 sig2) sig1 sig2

{- converts a mapping of raw symbols to a mapping of symbols to expressions
   annotated with their type -}
translMapAnalysisOL :: Morphism -> Map.Map RAW_SYM RAW_SYM -> Sign ->
                       Sign -> Map.Map Symbol (EXP,EXP)
translMapAnalysisOL ltruth m sig1 sig2 =
  let syms = getUnknownSyms (Map.keys m) sig1
      in if not (null syms) then error $ badSymsError syms else
         unsafePerformIO $ codAnalysisOL ltruth m sig2

codAnalysisOL :: Morphism -> Map.Map RAW_SYM RAW_SYM -> Sign ->
                 IO (Map.Map Symbol (EXP,EXP))
codAnalysisOL ltruth m sig2 = do
  -- make a Twelf file
  let cont1 = (show $ pretty sig2) ++ "\n"
  let cont2 = concat $ map (\ (k,v) -> (genPref k) ++ " = " ++ v ++ ".\n") $
                 Map.toList m
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
  return $ getMap sig'

---------------------------------------------------------------------------
---------------------------------------------------------------------------

-- ERROR MESSAGES
badSenTypeError :: String
badSenTypeError = "Sentence type cannot be constructed."
