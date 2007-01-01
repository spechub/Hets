{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Christian Maeder and Uni Bremen 2002-2003
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  experimental
Portability :  portable

Description :  make mixfix analysis checkable by RunParsers

-}

module CASL.RunMixfixParser where

import Common.AnnoState
import CASL.MixfixParser
import CASL.AS_Basic_CASL
import Common.GlobalAnnotations
import qualified Common.Lib.Set as Set
import Common.Id
import Common.Result
import Common.Lexer
import Common.Doc
import Common.DocUtils

import Common.Token
import CASL.Formula
import CASL.ShowMixfix

-- start testing
stdOpsL, stdPredsL :: [String]

stdOpsL = ["__^__", "__*__", "__+__", "[__]","__div__","__mod__", "__rem__",
        "__-__", "+__", "__E__", "__@@__", "[]", "__::__", "__:::__",
        "-__", "__!"] ++
          [ "____p", "q____","____x____", "{____}",
          "repeat__until__", "while__do__od",
            "__where__but__", "__where__done",
           "__ --> __", "__{__}--__-->{__}__"]
         ++ ["A[a[c,d],b]", "B[a[c,d],b]", "__B[a[c,d],b]__",
             "a[c,d]", "__a[c,d]__", "A[a]", "A__B",
             "A__", "__[a]", "__p",
             "__[__]__", "[__]__", "__[__]"]

stdPredsL = ["__<__", "__<=__", "__>__", "__>=__", "__!=__", "__<>__",
             "__/=__", "even__", "odd__", "__isEmpty",
            "__<=__<=__"]

mkIds :: [String] -> Set.Set Id
mkIds = Set.fromList . map (parseString $ parseId [])

stdOps, stdPreds :: Set.Set Id
stdOps = mkIds stdOpsL
stdPreds = mkIds stdPredsL

myIdSets :: IdSets
myIdSets = mkIdSets (mkIds stdOpsL) $ mkIds stdPredsL

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

testTerm ::  AParser () WrapString
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
