{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Uni Bremen 2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

   
   The comorphism functions for HasCASL2Haskell
-}

module ToHaskell.FromHasCASL where

import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.Result

import HasCASL.Le

import ParseMonad
import LexerOptions
import PropLexer
import PropParser as HsParser
import PNT
import PropPosSyntax hiding (ModuleName, Id, HsName)
import qualified NewPrettyPrint as HatPretty

import Haskell.HatAna
import Haskell.HatParser

import ToHaskell.TranslateAna
import Data.List ((\\))

mapSingleSentence :: Env -> Sentence -> Result (HsDeclI PNT)
mapSingleSentence sign sen = do
    (_, l) <- mapTheory (sign, [NamedSen "" sen])
    case l of 
      [] -> fail "sentence was not translated"
      [s] -> return $ sentence s
      _ -> do (_, o) <- mapTheory (sign, [])
              case l \\ o of
                [] -> fail "not a new sentence"
                [s] -> return $ sentence s
                _ -> fail "several sentences resulted"

mapTheory :: (Env, [Named Sentence]) -> Result (Sign, [Named (HsDeclI PNT)])
mapTheory (sig, csens) = do
    let hs = translateSig sig
	ps = concatMap (translateSentence sig) csens
	cs = cleanSig hs ps
    (_, _, hsig, sens) <- 
            hatAna (HsDecls (preludeDecls ++ cs ++ map sentence ps),
                            emptySign, emptyGlobalAnnos)
    return (diffSign hsig preludeSign, filter noInstance sens \\ preludeSens) 

noInstance :: Named (HsDeclI PNT) -> Bool
noInstance s = case basestruct $ struct $ sentence s of
               Just (HsInstDecl _ _ _ _ _) -> False
               Just (HsFunBind _ ms) -> all (\ m -> case m of
                     HsMatch _ n _ _ _ ->  let i = HatPretty.pp n in
                           take 3 i /= "$--" && 
                           take 9 i /= "default__" && 
                           i /= "shows" && 
                           i /= "showArgument") ms
               _ -> True

preludeSign :: Sign
preludeSign = fst preludeTheory

preludeSens :: [Named (HsDeclI PNT)]
preludeSens = snd preludeTheory

preludeTheory :: (Sign, [Named (HsDeclI PNT)])
preludeTheory = case maybeResult $ hatAna 
                (HsDecls preludeDecls, emptySign, emptyGlobalAnnos) of
                Just (_, _, hs, sens) -> (hs, sens) 
                _ -> error "preludeTheory"

preludeDecls :: [HsDecl]
preludeDecls = let ts = pLexerPass0 lexerflags0 
                        -- adjust line number of 'preludeString =' by hand!
                        (replicate 90 '\n' ++ preludeString)
   in case parseTokens (HsParser.parse) "ToHaskell/FromHasCASL.hs" ts of
      Just (HsModule _ _ _ _ ds) -> ds
      _ -> error "preludeDecls"

preludeString :: String
preludeString =
 "module Prelude where\n\
 \data Char\n\
 \\n\
 \data (->) a b\n\
 \\n\
 \data [a] = [] | (:) { head :: a , tail :: [a] }\n\
 \\n\
 \type  String = [Char]\n\
 \\n\
 \foreign import primError       :: String -> a\n\
 \\n\
 \error            :: String -> a\n\
 \error = primError \n\
 \\n\
 \data  ()  =  () \n\
 \\n\
 \data  (a,b)\n\
 \   =  (,) a b\n\
 \\n\
 \data  (a,b,c)\n\
 \   =  (,,) a b c\n\
 \\n\
 \data  (a,b,c, d)\n\
 \   =  (,,,) a b c d\n\
 \data Unit = Unit\n\
 \type Pred a = a -> Unit\n\
 \\n\
 \bottom :: a\n\
 \bottom = error \"bottom\"\n\
 \\n\
 \a___2_S_B_2 :: (Unit, Unit) -> Unit\n\
 \a___2_S_B_2 = bottom\n\
 \ \n\
 \a___2_L_E_G_2 :: (Unit, Unit) -> Unit\n\
 \a___2_L_E_G_2 = bottom\n\
 \ \n\
 \a___2_E_2 :: (a, a) -> Unit\n\
 \a___2_E_2 = bottom\n\
 \ \n\
 \a___2_E_G_2 :: (Unit, Unit) -> Unit\n\
 \a___2_E_G_2 (a, b) = bottom\n\
 \ \n\
 \a___2_Ee_E_2 :: (a, a) -> Unit\n\
 \a___2_Ee_E_2 = bottom\n\
 \ \n\
 \a___2_B_S_2 :: (Unit, Unit) -> Unit\n\
 \a___2_B_S_2 = bottom\n\
 \\n\
 \a___2if_2 :: (Unit, Unit) -> Unit\n\
 \a___2if_2 (a, b) = bottom\n\
 \\n\
 \a___2when_2else_2 :: (a, Unit, a) -> a\n\
 \a___2when_2else_2 (a, b, c) = bottom\n\
 \\n\
 \not_2 :: Unit -> Unit\n\
 \not_2 = bottom\n\
 \\n\
 \def_2 :: a -> Unit\n\
 \def_2 a = bottom\n\
 \ \n\
 \false :: Unit\n\
 \false = bottom\n\
 \\n\
 \true :: Unit\n\
 \true = bottom"
