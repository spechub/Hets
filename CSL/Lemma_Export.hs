{- |
Module      :  $Header$
Description :  Generation of Lemmata for CMDs
Copyright   :  (c) Dominik Dietrich, DFKI Bremen, 2010
License     :  GPLv2 or higher

Maintainer  :  Dominik.Dietrich@dfki.de
Stability   :  provisional
Portability :  portable

Interface for Reduce CAS system.
-}

module CSL.Lemma_Export where

import Common.AS_Annotation
import CSL.AS_BASIC_CSL

-- | generate name for generated lemma out of name of theorem
ganame :: Named CMD -> String
ganame cmd = "ga_" ++ (senAttr cmd)

-- | generates lemma in form of a named CMD for namedcmd that resulted in CAS answer casresult
genLemmaFactor :: Named CMD -> EXPRESSION -> Named CMD
genLemmaFactor namedcmd casresult = makeNamed lemmaname lemma
    where Cmd _ exps = sentence namedcmd
          lemma = Cmd "=" [head exps, casresult]
          lemmaname = (ganame namedcmd)

-- | generates lemma in form of a named CMD for namedcmd that resulted in CAS answer casresult
genLemmaSolve :: Named CMD -> EXPRESSION -> Named CMD
genLemmaSolve namedcmd casresult = makeNamed lemmaname lemma
    where Cmd _ exps = sentence namedcmd
          lemma = Cmd "=" [head exps, casresult]
          lemmaname = (ganame namedcmd)

-- | generates lemma in form of a named CMD for namedcmd that resulted in CAS answer casresult
genLemmaSimplify :: Named CMD -> EXPRESSION -> Named CMD
genLemmaSimplify namedcmd casresult = makeNamed lemmaname lemma
    where Cmd _ exps = sentence namedcmd
          lemma = Cmd "=" [head exps, casresult]
          lemmaname = (ganame namedcmd)

-- | generates lemma in form of a named CMD for namedcmd that resulted in CAS answer casresult
genLemmaAsk :: Named CMD -> EXPRESSION -> Named CMD
genLemmaAsk namedcmd casresult = makeNamed lemmaname lemma
      where Cmd _ exps = sentence namedcmd
            lemma = Cmd "=" [head exps, casresult]
            lemmaname = (ganame namedcmd)

-- | generates lemma in form of a named CMD for namedcmd that resulted in CAS answer casresult
genLemmaRemainder :: Named CMD -> EXPRESSION -> Named CMD
genLemmaRemainder namedcmd casresult = makeNamed lemmaname lemma
    where Cmd _ exps = sentence namedcmd
          lemma = Cmd "=" [head exps, casresult]
          lemmaname = (ganame namedcmd)

-- | generates lemma in form of a named CMD for namedcmd that resulted in CAS answer casresult
genLemmaInt :: Named CMD -> EXPRESSION -> Named CMD
genLemmaInt namedcmd casresult = makeNamed lemmaname lemma
    where Cmd _ exps = sentence namedcmd
          lemma = Cmd "=" [head exps, casresult]
          lemmaname = (ganame namedcmd)

