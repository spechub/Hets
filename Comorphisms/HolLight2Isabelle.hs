{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances #-}
{- |
Module      :  $Header$
Description :  translating from HolLight to Isabelle
Copyright   :  (c) M. Codescu, DFKI 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Mihai.Codescu@dfki.de
Stability   :  provisional
Portability :  portable

-}

module Comorphisms.HolLight2Isabelle where

import Logic.Comorphism
import Logic.Logic

import qualified Isabelle.IsaSign as IsaSign
import Isabelle.Logic_Isabelle
import Isabelle.IsaConsts as IsaConsts
import Isabelle.Translate

import Common.Result
import Common.AS_Annotation

import qualified Data.Map as Map
import qualified Data.Set as Set

import HolLight.Sign
import HolLight.Sentence
import HolLight.Term
import HolLight.Logic_HolLight
import HolLight.Sublogic
import HolLight.Helper

import Debug.Trace (trace)

data HolLight2Isabelle = HolLight2Isabelle deriving Show

instance Language HolLight2Isabelle

instance Comorphism HolLight2Isabelle
          HolLight
          HolLightSL                -- sublogic
          ()                        -- basic_spec
          Sentence                  -- sentence
          ()                        -- symb_items
          ()                        -- symb_map_items
          Sign                      -- sign
          HolLightMorphism          -- morphism
          ()                        -- symbol
          ()                        -- raw_symbol
          ()                        -- proof_tree
          Isabelle () () IsaSign.Sentence () ()
          IsaSign.Sign
          IsabelleMorphism () () ()  where
   sourceLogic _ = HolLight
   sourceSublogic _ = Top
   targetLogic _ = Isabelle
   mapSublogic _ _ = Just ()
   map_theory HolLight2Isabelle = mapTheory
   map_morphism = error "nyi"
   map_sentence HolLight2Isabelle = mapSentence

-- mapping sentences

mapSentence :: Sign -> Sentence -> Result IsaSign.Sentence
mapSentence _ s = return $ mapHolSen s

mapHolSen :: Sentence -> IsaSign.Sentence
mapHolSen (Sentence _n t _p) = IsaSign.Sentence{
                                  IsaSign.isSimp = False
                                 ,IsaSign.isRefuteAux = False
                                 ,IsaSign.metaTerm =
                                    IsaSign.Term $ translateTerm t
                                 , IsaSign.thmProof = Nothing
                                      }

tp2DTyp :: HolType -> IsaSign.DTyp
tp2DTyp tp = IsaSign.Hide{
                IsaSign.typ = tp2Typ tp,
                IsaSign.kon = IsaSign.TCon,
                IsaSign.arit = Nothing
              }

reduceTuples :: [Term] -> [Term]
reduceTuples l = foldl (\acc t -> case t of
                                    (Comb (Comb (Const "," _ _) a) b) -> (reduceTuples [a,b])++acc
                                    _ ->t:acc) [] l

constMap :: Map.Map String IsaSign.VName
constMap = Map.fromList [("+",IsaConsts.plusV)
                        ,("-",IsaConsts.minusV)
                        ,("*",IsaConsts.timesV)
                        ,("!",IsaSign.mkVName IsaConsts.allS)
                        ,("?",IsaSign.mkVName IsaConsts.exS)
                        ,("?!",IsaSign.mkVName IsaConsts.ex1S)
                        ,("=",IsaConsts.eqV)
                        ,("<=>",IsaConsts.eqV)
                        ,("/\\",IsaConsts.conjV)
                        ,("\\/",IsaConsts.disjV)
                        ,("==>",IsaConsts.implV)
                        ,("~",IsaConsts.notV)
                        ,("F",IsaSign.mkVName IsaConsts.cTrue)
                        ,("T",IsaSign.mkVName IsaConsts.cFalse)
                        ]

ignore :: [String]
ignore = ["+","-","*",",","!","?","?!","=","<=>","/\\","\\/","==>"]

transConstS :: String -> HolType -> IsaSign.VName
transConstS s t = case Map.lookup s constMap of
                   Just v -> v
                   Nothing -> IsaSign.mkVName $ typedName s t

typedName :: String -> HolType -> String
typedName s t = transConstStringT bs $ s ++ "_" ++ (show $ pp_print_type t)

translateTerm :: Term -> IsaSign.Term
-- translateTerm (Comb (Comb (Const "," _ _) a) b) = IsaSign.Tuplex (map translateTerm (reduceTuples [a,b])) IsaSign.NotCont
translateTerm (Comb (Comb (Const "," _ _) a) b) = IsaSign.Tuplex [translateTerm a, translateTerm b] IsaSign.NotCont
translateTerm (Var s tp _) = IsaSign.Free $ (transConstS s tp)
translateTerm (Const s tp _) = IsaSign.Const (transConstS s tp) $ tp2DTyp tp
translateTerm (Comb tm1 tm2) = IsaSign.App (translateTerm tm1)
                                          (translateTerm tm2)
                                          IsaSign.NotCont
translateTerm (Abs tm1 tm2) = IsaSign.Abs (translateTerm tm1)
                                          (translateTerm tm2)
                                          IsaSign.NotCont

-- mapping theories

mapTheory :: (Sign, [Named Sentence]) ->
             Result(IsaSign.Sign, [Named IsaSign.Sentence])
mapTheory (sig, n_sens) = let
  sig' = mapSign sig
  n_sens' = map mapNamedSen n_sens
                          in return (sig', n_sens')

bs = IsaSign.MainHC_thy

mapSign :: Sign -> IsaSign.Sign
mapSign (Sign t o) = IsaSign.emptySign{
                       IsaSign.baseSig = IsaSign.MainHC_thy,
                       IsaSign.constTab = mapOps o,
                       IsaSign.tsig = mapTypes t 
                      }

mapOps :: Map.Map String (Set.Set HolType) -> IsaSign.ConstTab
mapOps f = Map.fromList
             $ map (\(x,y) -> (transConstS x y, tp2Typ y))
             $ concatMap (\(x, s) -> Set.toList $ Set.map (\a -> (x,a)) s)
             $ Map.toList (foldl (\m i -> Map.delete i m) f ignore)

tp2Typ :: HolType -> IsaSign.Typ
tp2Typ (TyVar s) = IsaSign.Type (transTypeStringT bs s) holType []
tp2Typ (TyApp s tps) = case tps of
  [a1, a2] | s == "fun" -> mkFunType (tp2Typ a1) (tp2Typ a2)
  [] | s == "bool" -> boolType
  _ -> IsaSign.Type (transTypeStringT bs s) holType $ map tp2Typ tps

arity2tp :: Int -> [(IsaSign.IsaClass, [(IsaSign.Typ, IsaSign.Sort)])]
arity2tp i = [(isaTerm,foldl (\l t -> t:l) []
                       (take i (map (\k -> (IsaSign.TFree ("'a" ++ show (k)) [],[isaTerm]))
                                (iterate (1+) 1))))]

mapTypes :: Map.Map String Int -> IsaSign.TypeSig
mapTypes tps = IsaSign.emptyTypeSig {
                IsaSign.arities = Map.fromList $ map extractTypeName (Map.toList (Map.delete "bool" tps))}
 where
    extractTypeName (s,a) = (transTypeStringT bs s , [(isaTerm, [])])
    extractTypeName (s,a) = (transTypeStringT bs s, [(isaTerm, [])])


mapNamedSen :: Named Sentence -> Named IsaSign.Sentence
mapNamedSen n_sen = let
 sen = sentence n_sen
 trans = mapHolSen sen
                    in
 n_sen{sentence = trans}

