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
  let contents = makeFileOL ltruth sig (getSigItems items) (getSenItems items)
  writeFile gen_file contents
  libs <- twelf2SigMor gen_file
  getSigSen libs
 
{- constructs the contents of a Twelf file used to analyze the signature
   and sentences -}
makeFileOL :: Morphism -> Sign -> [Annoted BASIC_ITEM] ->
              [Annoted BASIC_ITEM] -> String
makeFileOL ltruth sig sig_items sen_items = do
  let sen_type = case mapSymbol sen_type_symbol ltruth of
                   Nothing -> error "Sentence type cannot be constructed."
                   Just t -> show $ pretty t
      lSyn = target ltruth
      locals = filter (\ d -> isLocalSym (getSym d) sig) $ getDefs sig
      imp = mkRead $ fromLibName $ sigBase lSyn
      cont1 = if (sig == lSyn) then "" else (show $ vcat $ map pretty locals) ++ "\n"
      cont2 = printSigItems sig_items
      cont3 = printSenItems sen_type sen_items
      sig1 = mkSig gen_sig1 $ mkIncl (sigModule lSyn) ++ cont1 ++ cont2
      sig2 = mkSig gen_sig2 $ mkIncl gen_sig1 ++ cont3
      in imp ++ "\n" ++ sig1 ++ "\n" ++ sig2
