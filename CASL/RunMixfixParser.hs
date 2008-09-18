{- |
Module      :  $Header$
Description :  make mixfix analysis checkable by RunParsers
Copyright   :  (c) Klaus Lüttich, Christian Maeder and Uni Bremen 2002-2003
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

Make mixfix analysis checkable by RunParsers
-}

module CASL.RunMixfixParser where

import Common.AnnoState
import Common.GlobalAnnotations
import Common.Result
import Common.Doc
import Common.DocUtils
import Common.ExampleMixIds
import CASL.Formula
import CASL.ShowMixfix
import CASL.MixfixParser
import CASL.AS_Basic_CASL

myIdSets :: IdSets
myIdSets = mkIdSets (mkIds stdOpsL) stdPreds

resolveForm :: GlobalAnnos -> AParser () (Result (FORMULA ()))
resolveForm ga =
      resolveFormula id (const $ const return) ga (makeRules ga myIdSets)
                         `fmap` formula []

resolveTerm :: GlobalAnnos -> AParser () (Result (TERM ()))
resolveTerm ga =
      resolveMixfix id (const $ const return) ga (makeRules ga myIdSets)
                        `fmap` term []

-- | a helper type to pretty print (wrapped) strings
data WrapString = WrapString String
instance Show WrapString where
    showsPrec _ (WrapString s) _ = s

instance Pretty WrapString where
    pretty (WrapString s) = text s

testTerm :: AParser () WrapString
testTerm = do t <- term [] :: AParser () (TERM ())
              return $ WrapString $ showDoc (mapTerm id t) ""

testTermMix :: GlobalAnnos -> AParser () WrapString
testTermMix ga = do Result ds mt <- resolveTerm ga
                    return $ WrapString $
                        case mt of
                        Just t -> showGlobalDoc ga (mapTerm id t) ""
                        _ -> show ds

testFormula :: AParser () WrapString
testFormula = do f <- formula [] :: AParser () (FORMULA ())
                 return $ WrapString $ showDoc (mapFormula id  f) ""

testFormulaMix :: GlobalAnnos -> AParser () WrapString
testFormulaMix ga = do Result ds m <- resolveForm ga
                       return $ WrapString $
                           case m of
                           Just f -> showGlobalDoc ga (mapFormula id f) ""
                           _ -> show ds
