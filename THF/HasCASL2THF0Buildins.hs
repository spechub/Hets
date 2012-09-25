{- |
Module      :  $Header$
Description :  create legal THF mixfix identifier
Copyright   :  (c) A. Tsogias, DFKI Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Alexis.Tsogias@dfki.de
Stability   :  provisional
Portability :  portable

translations for the buildins of HasCasl
-}

module THF.HasCASL2THF0Buildins where

import Common.AS_Annotation
import Common.DocUtils
import Common.Result
import Common.Id

import HasCASL.Builtin

import THF.As
import THF.Cons
import THF.Sign
import THF.ParseTHF0
import THF.Translate
import THF.PrintTHF ()

import Text.ParserCombinators.Parsec

import Data.Maybe
import qualified Data.Set as Set
import qualified Data.Map as Map

--------------------------------------------------------------------------------
-- Assumps
--------------------------------------------------------------------------------

preDefHCAssumps :: Set.Set Id -> ConstMap
preDefHCAssumps ids =
    let asl = [ (botId,       botci)
              , (defId,       defci)
              , (notId,       o2ci)
              , (negId,       o2ci)
{-            , (whenElse,    "hcc" ++ show whenElse) -}
              , (trueId,      o1ci)
              , (falseId,     o1ci)
              , (eqId,        a2o1ci)
              , (exEq,        a2o1ci)
              , (resId,       resci)
              , (andId,       o3ci)
              , (orId,        o3ci)
              , (eqvId,       o3ci)
              , (implId,      o3ci)
              , (infixIf,     o3ci) ]
    in Map.fromList $ map
            (\ (i, tf) ->  let c = (fromJust . maybeResult . transAssumpId) i
                           in (c , tf c))
            (filter (\ (i, _) -> Set.member i ids) asl)

o1ci :: Constant -> ConstInfo
o1ci c = ConstInfo
    { constId   = c
    , constName = mkConstsName c
    , constType = OType
    , constAnno = Null }

o2ci :: Constant -> ConstInfo
o2ci c = ConstInfo
    { constId   = c
    , constName = mkConstsName c
    , constType = MapType OType OType
    , constAnno = Null }

o3ci :: Constant -> ConstInfo
o3ci c = ConstInfo
    { constId   = c
    , constName = mkConstsName c
    , constType = MapType OType (MapType OType OType)
    , constAnno = Null }

a2o1ci :: Constant -> ConstInfo
a2o1ci c = ConstInfo
    { constId   = c
    , constName = mkConstsName c
    , constType = MapType (VType "A") (MapType (VType "A") OType)
    , constAnno = Null }

resci :: Constant -> ConstInfo
resci c = ConstInfo
    { constId   = c
    , constName = mkConstsName c
    , constType = MapType (VType "A") (MapType (VType "B") (VType "A"))
    , constAnno = Null }

botci :: Constant -> ConstInfo
botci c = ConstInfo
    { constId   = c
    , constName = mkConstsName c
    , constType = OType
    , constAnno = Null }

defci :: Constant -> ConstInfo
defci c = ConstInfo
    { constId   = c
    , constName = mkConstsName c
    , constType = MapType (VType "A") OType
    , constAnno = Null }

--------------------------------------------------------------------------------
-- Axioms
--------------------------------------------------------------------------------

preDefAxioms :: Set.Set Id -> [Named SentenceTHF]
preDefAxioms ids =
    let axl = [ (notId,       notFS)
              , (negId,       notFS)
              , (trueId,      trueFS)
              , (falseId,     falseFS)
              , (andId,       andFS)
              , (orId,        orFS)
              , (eqvId,       eqvFS)
              , (implId,      implFS)
              , (infixIf,     ifFS)
              , (eqId,        eqFS)
              , (exEq,        eqFS)
              , (resId,       resFS)
              , (botId,       botFS)
              , (defId,       defFS)
{-            , (whenElse,    "hcc" ++ show whenElse) -} ]
    in map (\ (i, fs) -> mkNSD
                (fromJust $ maybeResult $ transAssumpId i) fs)
           (filter (\ (i, _) -> Set.member i ids) axl)

mkNSD :: Constant -> (Constant -> String) -> Named SentenceTHF
mkNSD c f =
    let s = Sentence
            { senRole       = Definition
            , senFormula    = genTHFFormula c f
            , senAnno       = Null }
    in SenAttr
        { senAttr = (show . pretty . mkDefName) c
        , isAxiom = True
        , isDef = True
        , wasTheorem = False
        , simpAnno = Nothing
        , attrOrigin = Nothing
        , sentence = s }

genTHFFormula :: Constant -> (Constant -> String) -> THFFormula
genTHFFormula c f = case parse parseTHF0 "" (f c) of
        Left _ -> error ("Fatal error while generating the predefinied Sentence"
                    ++ " for: " ++ show (pretty c))
        Right x -> thfFormulaAF $ head x

--------------------------------------------------------------------------------
-- formulas as Strings
--------------------------------------------------------------------------------

notFS :: Constant -> String
notFS c =
    let ns = (show . pretty . mkDefName) c
        cs = (show . pretty) c
    in encTHF (ns ++ defnS ++ cs ++ " = (^ [A : $o] : ~(A))")

falseFS :: Constant -> String
falseFS c =
    let ns = (show . pretty . mkDefName) c
        cs = (show . pretty) c
    in encTHF (ns ++ defnS ++ cs ++ " = $false")

trueFS :: Constant -> String
trueFS c =
    let ns = (show . pretty . mkDefName) c
        cs = (show . pretty) c
    in encTHF (ns ++ defnS ++ cs ++ " = $true")

andFS :: Constant -> String
andFS c =
    let ns = (show . pretty . mkDefName) c
        cs = (show . pretty) c
    in encTHF (ns ++ defnS ++ cs ++ " = (^ [X : $o, Y : $o] : (X & Y))")

orFS :: Constant -> String
orFS c =
    let ns = (show . pretty . mkDefName) c
        cs = (show . pretty) c
    in encTHF (ns ++ defnS ++ cs ++ " = (^ [X : $o, Y : $o] : (X | Y))")

eqvFS :: Constant -> String
eqvFS c =
    let ns = (show . pretty . mkDefName) c
        cs = (show . pretty) c
    in encTHF (ns ++ defnS ++ cs ++ " = (^ [X : $o, Y : $o] : (X <=> Y))")

implFS :: Constant -> String
implFS c =
    let ns = (show . pretty . mkDefName) c
        cs = (show . pretty) c
    in encTHF (ns ++ defnS ++ cs ++ " = (^ [X : $o, Y : $o] : (X => Y))")

ifFS :: Constant -> String
ifFS c =
    let ns = (show . pretty . mkDefName) c
        cs = (show . pretty) c
    in encTHF (ns ++ defnS ++ cs ++ " = (^ [X : $o, Y : $o] : (Y => X))")

eqFS :: Constant -> String
eqFS c =
    let ns = (show . pretty . mkDefName) c
        cs = (show . pretty) c
    in encTHF (ns ++ defnS ++ cs ++ " = (^ [X : A, Y : A] : (X = Y))")

resFS :: Constant -> String
resFS c =
    let ns = (show . pretty . mkDefName) c
        cs = (show . pretty) c
    in encTHF (ns ++ defnS ++ cs ++ " = (^ [X : A, Y : B] : X)")

botFS :: Constant -> String
botFS c =
    let ns = (show . pretty . mkDefName) c
        cs = (show . pretty) c
    in encTHF (ns ++ defnS ++ cs ++ " = $false")

defFS :: Constant -> String
defFS c =
    let ns = (show . pretty . mkDefName) c
        cs = (show . pretty) c
    in encTHF (ns ++ defnS ++ cs ++ " = (^ [X : A] : $true)")

defnS :: String
defnS = ", definition, "

encTHF :: String -> String
encTHF s = "thf(" ++ s ++ ")."
