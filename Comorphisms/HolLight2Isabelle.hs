{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances, DeriveGeneric #-}
{- |
Module      :  ./Comorphisms/HolLight2Isabelle.hs
Description :  translating from HolLight to Isabelle
Copyright   :  (c) Jonathan von Schroeder and M. Codescu, DFKI 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  jonathan.von_schroeder@dfki.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

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

import qualified Data.HashMap.Strict as Map
import Data.List ((\\))

import HolLight.Sign
import HolLight.Sentence
import HolLight.Term
import HolLight.Logic_HolLight
import HolLight.Sublogic
import HolLight.Helper

import GHC.Generics (Generic)
import Data.Hashable


data HolLight2Isabelle = HolLight2Isabelle deriving (Show, Generic)

instance Hashable HolLight2Isabelle

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
          IsabelleMorphism () () () where
   sourceLogic _ = HolLight
   sourceSublogic _ = Top
   targetLogic _ = Isabelle
   mapSublogic _ _ = Just ()
   map_theory HolLight2Isabelle = mapTheory
   map_sentence HolLight2Isabelle = mapSentence

-- mapping sentences

mapSentence :: Sign -> Sentence -> Result IsaSign.Sentence
mapSentence _ s = return $ mapHolSen s

mapHolSen :: Sentence -> IsaSign.Sentence
mapHolSen (Sentence t _) = IsaSign.Sentence {
                                  IsaSign.isSimp = False
                                 , IsaSign.isRefuteAux = False
                                 , IsaSign.metaTerm =
                                    IsaSign.Term $ translateTerm t (allVars t)
                                 , IsaSign.thmProof = Nothing
                                      }

tp2DTyp :: HolType -> IsaSign.DTyp
tp2DTyp tp = IsaSign.Hide {
                IsaSign.typ = tp2Typ tp,
                IsaSign.kon = IsaSign.TCon,
                IsaSign.arit = Nothing
              }

constMap :: Map.HashMap String IsaSign.VName
constMap = Map.fromList [("+", IsaConsts.plusV)
                        , ("-", IsaConsts.minusV)
                        , ("*", IsaConsts.timesV)
                        , ("!", IsaConsts.mkVName IsaConsts.allS)
                        , ("?", IsaConsts.mkVName IsaConsts.exS)
                        , ("?!", IsaConsts.mkVName IsaConsts.ex1S)
                        , ("=", IsaConsts.eqV)
                        , ("<=>", IsaConsts.eqV)
                        , ("/\\", IsaConsts.conjV)
                        , ("\\/", IsaConsts.disjV)
                        , ("==>", IsaConsts.implV)
                        , ("~", IsaConsts.notV)
                        , ("T", IsaConsts.mkVName IsaConsts.cTrue)
                        , ("F", IsaConsts.mkVName IsaConsts.cFalse)
                        ]

notIgnore :: [String]
notIgnore = ["+", "-", "*"]

ignore :: [String]
ignore = map fst (Map.toList constMap) \\ notIgnore

transConstS :: String -> HolType -> IsaSign.VName
transConstS s t = case (Map.lookup s constMap, elem s notIgnore) of
                   (Just v, False) -> v
                   (_, _) -> IsaConsts.mkVName $ typedName s t

typedName :: String -> HolType -> String
typedName s _t = transConstStringT bs s -- ++ "_" ++ (show $ pp_print_type t)

unpack_gabs :: Term -> [String] -> (IsaSign.Term, [IsaSign.Term], IsaSign.Term, IsaSign.Term)
unpack_gabs t vs = case unpack_gabs' t vs [] of
                    Just (q, vars, tm) ->
                     let (pat, res) = case tm of
                                       Comb (Comb (Const "GEQ" _ _)
                                        (Comb (Var "f" _ _) pat1)) res1 -> (pat1, res1)
                                       _ -> error "unpack_gabs failed"
                     in (q, vars, translateTerm pat vs, translateTerm res vs)
                    Nothing -> error "unpack_gabs' failed"

unpack_gabs' :: Term -> [String] -> [IsaSign.Term] -> Maybe (IsaSign.Term, [IsaSign.Term], Term)
unpack_gabs' (Comb c@(Const "!" _ _) (Abs v@(Var {}) tm)) vs vars =
  case unpack_gabs' tm vs (translateTerm v vs : vars) of
    Just r -> Just r
    Nothing -> Just (translateTerm c vs, translateTerm v vs : vars, tm)
unpack_gabs' _ _ _ = Nothing

makeForAll :: IsaSign.Term -> [IsaSign.Term] -> IsaSign.Term -> IsaSign.Term
makeForAll _ [] t = t
makeForAll q (v : vs) t = IsaSign.App q
                         (IsaSign.Abs v
                           (makeForAll q vs t)
                           IsaSign.NotCont)
                         IsaSign.NotCont

handleGabs :: Bool -> Term -> [String] -> IsaSign.Term
handleGabs b t vs = case t of
 (Comb (Const "GABS" _ _) (Abs (Var "f" _ _) tm)) ->
   let (q, vars, pat, res) = unpack_gabs tm vs in
   let n = IsaSign.Free $ IsaConsts.mkVName (freeName (varNames vars ++ vs)) in
   let t1 = IsaSign.Abs n
             (IsaSign.Case n [(pat, res)])
             IsaSign.NotCont
   in if b then makeForAll q vars (IsaSign.App q t1
                                    IsaSign.NotCont)
      else t1
 _ -> error "handleGabs failed"

mkAbs :: Term -> [String] -> IsaSign.Term
mkAbs t vs = let name = freeName vs in
             IsaSign.Abs
              (IsaSign.Free (IsaConsts.mkVName name))
              (IsaSign.App (translateTerm t (name : vs))
                (IsaSign.Free (IsaConsts.mkVName name))
                IsaSign.NotCont)
              IsaSign.NotCont

mkQuantifier :: Term -> [String] -> IsaSign.Term
mkQuantifier t vs = let name = freeName vs in
                    IsaSign.Abs
                     (IsaSign.Free (IsaConsts.mkVName name))
                     (IsaSign.App (translateTerm t (name : vs))
                       (IsaSign.Abs
                        (IsaSign.Free (IsaConsts.mkVName name))
                        (IsaSign.Free (IsaConsts.mkVName name))
                        IsaSign.NotCont)
                       IsaSign.NotCont)
                     IsaSign.NotCont

isAppT :: HolType -> Bool
isAppT (TyApp _ _) = True
isAppT _ = False

isQuantifier :: Term -> Bool
isQuantifier (Const c _ _) = elem c ["!", "?", "?!"]
isQuantifier _ = False

varNames :: [IsaSign.Term] -> [String]
varNames [] = []
varNames (IsaSign.Free s : vs) = IsaSign.orig s : varNames vs
varNames (_ : vs) = varNames vs

allVars :: Term -> [String]
allVars (Comb a b) = allVars a ++ allVars b
allVars (Abs a b) = allVars a ++ allVars b
allVars (Const {}) = []
allVars (Var s _ _) = [s]

translateTerm :: Term -> [String] -> IsaSign.Term
translateTerm (Comb (Comb (Const "," _ _) a) b) vs =
  IsaSign.Tuplex [translateTerm a vs, translateTerm b vs] IsaSign.NotCont
translateTerm (Var s tp _) _ = IsaSign.Free $ transConstS s tp
translateTerm (Const s tp _) _ = IsaSign.Const (transConstS s tp) $ tp2DTyp tp
translateTerm (Comb (Const "!" _ _) t@(Comb (Const "GABS" _ _) _)) vs =
  handleGabs True t vs
translateTerm t@(Comb (Const "GABS" _ _) (Abs (Var "f" _ _) _)) vs =
  handleGabs False t vs
translateTerm (Comb (Comb (Comb (Const "COND" _ _) i) t) e) vs =
  IsaSign.If (translateTerm i vs) (translateTerm t vs)
             (translateTerm e vs) IsaSign.NotCont
translateTerm (Comb c1@(Const c tp _) t) vs = if isAbs t || (isAppT tp &&
  not (isQuantifier t) && not (isQuantifier c1) && c /= "@")
                                           then IsaSign.App
                                                (translateTerm c1 vs)
                                                (translateTerm t vs)
                                                IsaSign.NotCont
                                          else IsaSign.App (translateTerm c1 vs)
                                                (if isQuantifier t
                                                 then mkQuantifier t vs
                                                 else mkAbs t vs)
                                                IsaSign.NotCont
translateTerm (Comb tm1 tm2) vs = IsaSign.App (translateTerm tm1 vs)
                                (translateTerm tm2 vs)
                                IsaSign.NotCont
translateTerm (Abs tm1 tm2) vs = IsaSign.Abs (translateTerm tm1 vs)
                                          (translateTerm tm2 vs)
                                          IsaSign.NotCont

-- mapping theories

mapTheory :: (Sign, [Named Sentence]) ->
             Result (IsaSign.Sign, [Named IsaSign.Sentence])
mapTheory (sig, n_sens) = let
  sig' = mapSign sig
  n_sens' = map mapNamedSen n_sens
                          in return (sig', n_sens')
bs :: IsaSign.BaseSig
bs = IsaSign.MainHC_thy

mapSign :: Sign -> IsaSign.Sign
mapSign (Sign t o) = IsaSign.emptySign {
                          IsaSign.baseSig = IsaSign.MainHC_thy,
                          IsaSign.constTab = mapOps o,
                          IsaSign.tsig = mapTypes t
                         }

mapOps :: Map.HashMap String HolType -> IsaSign.ConstTab
mapOps f = Map.fromList
             $ map (\ (x, y) -> (transConstS x y, tp2Typ y))
             $ Map.toList (foldl (flip Map.delete) f ignore)

tp2Typ :: HolType -> IsaSign.Typ
tp2Typ (TyVar ('\'' : s')) = IsaSign.TFree ('\'' : transTypeStringT bs s')
                              holType
tp2Typ (TyVar s) = IsaSign.Type (transTypeStringT bs s) holType []
tp2Typ (TyApp s tps) = case tps of
  [a1, a2] | s == "fun" -> mkFunType (tp2Typ a1) (tp2Typ a2)
  [] | s == "bool" -> boolType
  _ -> IsaSign.Type (transTypeStringT bs s) holType $ map tp2Typ tps

arity2tp :: Int -> [(IsaSign.IsaClass, [(IsaSign.Typ, IsaSign.Sort)])]
arity2tp i = [(isaTerm, map (\ k -> (IsaSign.TFree ("'a" ++ show k) [],
  [isaTerm])) [1 .. i])]

mapTypes :: Map.HashMap String Int -> IsaSign.TypeSig
mapTypes tps = IsaSign.emptyTypeSig {
                    IsaSign.arities = Map.fromList $ map extractTypeName
                  $ Map.toList $ foldr Map.delete tps
                       ["bool", "fun", "prod"] }
 where
    extractTypeName (s, arity) = (transTypeStringT bs s, arity2tp arity)

mapNamedSen :: Named Sentence -> Named IsaSign.Sentence
mapNamedSen n_sen = let
 sen = sentence n_sen
 trans = mapHolSen sen
                    in
 n_sen {sentence = trans}
