{- |
Module      :  $Header$
Description :  test driver for static analysis
Copyright   :  (c) Christian Maeder and Uni Bremen 2003
License     :  GPLv2 or higher

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

parse and call static analysis
-}

module HasCASL.RunStaticAna where

import HasCASL.Le
import HasCASL.As
import HasCASL.AsToLe(anaBasicSpec)
import HasCASL.ParseItem(basicSpec)
import HasCASL.ProgEq
import HasCASL.SimplifyTerm
import HasCASL.Builtin

import Common.Lib.State
import Common.Doc
import Common.DocUtils
import Common.RunParsers
import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.AnnoState

bParser :: GlobalAnnos -> AParser () (BasicSpec, Env)
bParser ga = do b <- basicSpec
                return $ runState (anaBasicSpec ga b) initialEnv

anaParser :: StringParser
anaParser ga = do (a, e) <- bParser ga
                  let ne = e { sentences = map
                         (mapNamed $ simplifySentence e) $ sentences e }
                  return $ show $ toText (addBuiltins ga)
                             $ pretty a $+$ pretty ne

type SenParser = GlobalAnnos -> AParser () [Named Sentence]

senParser :: SenParser
senParser = fmap (reverse . sentences . snd) . bParser

transParser :: SenParser
transParser = fmap ( ( \ e -> map (mapNamed (translateSen e)) $ reverse $
                       sentences e) . snd) . bParser

printSen :: SenParser -> StringParser
printSen p ga = fmap (show . toText (addBuiltins ga) .
  vcat . map (pretty . fromLabelledSen)) $ p ga
