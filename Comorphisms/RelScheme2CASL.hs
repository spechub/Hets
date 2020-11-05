{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  ./Comorphisms/RelScheme2CASL.hs
Description :  Comorphism from RelScheme to CASL
Copyright   :  (c) Dominik Luecke and Uni Bremen 2007
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

The translating comorphism from DL to CASL_DL basically this is an
identity comorphism from SROIQ(D) to SROIQ(D)
-}

module Comorphisms.RelScheme2CASL
    (
     RelScheme2CASL (..)
    )
    where

import Logic.Logic
import Logic.Comorphism

import Common.AS_Annotation
import Common.Id
import Common.ProofTree
import Common.Result
import Common.Utils (number)
import qualified Common.Lib.MapSet as MapSet
import qualified Common.Lib.Rel as Rel

import qualified Data.Set as Set
import qualified Data.HashMap.Lazy as Map

-- RelScheme
import RelationalScheme.Logic_Rel as LRel
import RelationalScheme.AS as ARel
import qualified RelationalScheme.Sign as SRel

-- CASL = codomain
import CASL.Logic_CASL
import CASL.AS_Basic_CASL
import CASL.Sublogic as SL
import CASL.Sign
import CASL.Morphism

data RelScheme2CASL = RelScheme2CASL deriving (Show)

instance Language RelScheme2CASL

instance Comorphism
    RelScheme2CASL      -- comorphism
    RelScheme              -- lid domain
    ()              -- sublogics domain
    RSScheme         -- Basic spec domain
    Sentence     -- sentence domain
    ()              -- symbol items domain
    ()              -- symbol map items domain
    SRel.Sign        -- signature domain
    SRel.RSMorphism  -- morphism domain
    SRel.RSSymbol    -- symbol domain
    SRel.RSRawSymbol -- rawsymbol domain
    ()              -- proof tree codomain
    CASL         -- lid codomain
    CASL_Sublogics              -- sublogics codomain
    CASLBasicSpec   -- Basic spec codomain
    CASLFORMULA       -- sentence codomain
    SYMB_ITEMS      -- symbol items codomain
    SYMB_MAP_ITEMS  -- symbol map items codomain
    CASLSign          -- signature codomain
    CASLMor           -- morphism codomain
    Symbol          -- symbol codomain
    RawSymbol       -- rawsymbol codomain
    ProofTree              -- proof tree domain
        where
          sourceLogic RelScheme2CASL = RelScheme
          sourceSublogic RelScheme2CASL = ()
          targetLogic RelScheme2CASL = CASL
          mapSublogic RelScheme2CASL _ = Just SL.caslTop
          map_theory RelScheme2CASL = map_RelScheme_theory
          map_morphism RelScheme2CASL = return . mapMorphism
          map_sentence RelScheme2CASL = mapSen
          isInclusionComorphism RelScheme2CASL = True

map_RelScheme_theory :: (SRel.Sign, [Named Sentence])
                     -> Result (CASLSign, [Named CASLFORMULA])
map_RelScheme_theory (sig, n_sens) = do
     let tsign = mapSign sig
     tax <- mapM genAxioms $ Set.toList $ SRel.tables sig
     tsens <- mapM (mapNamedSen sig) n_sens
     return (tsign, concat (tsens : tax))

mapSign :: SRel.Sign -> CASLSign
mapSign sig = let
 (sorts, ops, preds) = genCASLSig (Set.toList $ SRel.tables sig)
                                Set.empty MapSet.empty MapSet.empty
              in (emptySign ()) {
                  sortRel = Rel.fromKeysSet sorts,
                  opMap = ops,
                  predMap = preds
                 }

mapMorphism :: SRel.RSMorphism -> CASLMor
mapMorphism phi = let
  ssign = mapSign $ SRel.domain phi
                  in
  Morphism {
   msource = ssign,
   mtarget = mapSign $ SRel.codomain phi,
   sort_map = Map.empty,
   op_map = Map.fromList $
     map (\ (tab, (c1, c2)) -> let
          t : _ = filter (\ tb -> SRel.t_name tb == tab) $
              Set.toList $ SRel.tables $ SRel.domain phi
          types = getTypes t
          resType = stringToId $ show $ SRel.c_data $
                    head $ filter (\ col -> SRel.c_name col == c1) $
                    SRel.columns t
          fname = stringToId $ show tab ++ '_' : show c1
          ftype = mkTotOpType types resType
          rname = stringToId $
                  show (SRel.table_map phi Map.! tab) ++ '_' : show c2
                            in
            ((fname, ftype), (rname, Partial))
                               )
     $ concatMap (\ (x, f) -> map (\ y -> (x, y)) $ Map.toList $ SRel.col_map f)
       $ Map.toList $ SRel.column_map phi,
   pred_map = Map.fromList $ concatMap
               (\ (i, pSet) ->
                     [((i, pt), SRel.table_map phi Map.! i)
                             | pt <- pSet]) $
               MapSet.toList $ predMap ssign,
   extended_map = ()
}

genCASLSig :: [SRel.RSTable] -> Set.Set SORT -> OpMap -> PredMap
  -> (Set.Set SORT, OpMap, PredMap)
genCASLSig tabList sorts ops preds = case tabList of
  [] -> (sorts, ops, preds)
  t : tList -> let
   arity = getTypes t
   sorts' = Set.fromList arity
   ops' =
    MapSet.fromList $
     map ( \ c -> (stringToId $ show (SRel.t_name t) ++ '_'
                                : show (SRel.c_name c),
                  [OpType Total arity $ stringToId $ show $ SRel.c_data c]))
     $ SRel.columns t
   preds' = MapSet.insert (SRel.t_name t)
                       (PredType arity) preds
             in genCASLSig tList
                           (Set.union sorts sorts')
                           (MapSet.union ops ops')
                           preds'

genAxioms :: SRel.RSTable -> Result [Named CASLFORMULA]
genAxioms tab =
  if Set.null $ SRel.t_keys tab then projections tab else do
          axK <- axiomsForKeys tab
          axP <- projections tab
          return $ axK ++ axP

genTypedVars :: Char -> [Id] -> [(Token, Id)]
genTypedVars c = map (\ (t, n) -> (genToken (c : show n), t)) . number

axiomsForKeys :: SRel.RSTable -> Result [Named CASLFORMULA]
axiomsForKeys tab = do
 let
  types = getTypes tab
  vars_x = genTypedVars 'x' types
  vars_y = genTypedVars 'y' types
  qual_vars = map (uncurry mkVarTerm)
  qXs = qual_vars vars_x
  qYs = qual_vars vars_y
  conjuncts = zipWith mkStEq qXs qYs
  keys = Set.toList $ SRel.t_keys tab
  keysEqual = map (\ (cid, ctype) -> let
                  qualOp = mkQualOp
                     (stringToId $ show (SRel.t_name tab) ++ '_' : show cid)
                     (Op_type Total types (stringToId $ show ctype) nullRange)
                  in mkStEq
                         (mkAppl qualOp qXs)
                         (mkAppl qualOp qYs)
                  ) keys
 return [makeNamed "" $ mkForall
            (map (uncurry mkVarDecl) $ vars_x ++ vars_y)
            (mkImpl
              (let qualPred = mkQualPred
                     (SRel.t_name tab)
                     (Pred_type types nullRange)
               in conjunct
                ([ mkPredication qualPred qXs
                 , mkPredication qualPred qYs ]
                 ++ keysEqual)
              )
              (conjunct conjuncts)
            )
          ]

getTypes :: SRel.RSTable -> [Id]
getTypes = map (stringToId . show . SRel.c_data) . SRel.columns

projections :: SRel.RSTable -> Result [Named CASLFORMULA]
projections tab = let
  types = getTypes tab
  vars_x = genTypedVars 'x' types
  vardecls = map (uncurry mkVarDecl)
  qual_vars = map (uncurry mkVarTerm)
  fields = map (show . SRel.c_name) $ SRel.columns tab
  projAx c (vRes, typeRes) = makeNamed "" $ mkForall
             (vardecls vars_x)
             (mkStEq
               (mkAppl
                  (mkQualOp
                     (stringToId $ show (SRel.t_name tab) ++ '_' : c)
                     (Op_type Total types typeRes nullRange)
                    )
                  (qual_vars vars_x)
                  )
                  (mkVarTerm vRes typeRes)
               )
  in return $ zipWith projAx fields vars_x


mapNamedSen :: SRel.Sign -> Named Sentence -> Result (Named CASLFORMULA)
mapNamedSen sign n_sens =
    let
        s = sentence n_sens
    in
      do
        ts <- mapSen sign s
        return $ n_sens {sentence = ts}

mapSen :: SRel.Sign -> Sentence -> Result CASLFORMULA
mapSen sign sen = let
  linkedcols = zip (map column $ r_lhs sen)
                   (map column $ r_rhs sen)
  rtableName : _ = map table $ r_rhs sen
  ltableName : _ = map table $ r_lhs sen
  ltable : _ = filter (\ t -> SRel.t_name t == ltableName) $
           Set.toList $ SRel.tables sign
  rtable : _ = filter (\ t -> SRel.t_name t == rtableName) $
           Set.toList $ SRel.tables sign
  allRcols = number $ SRel.columns rtable
  typesL = getTypes ltable
  typesR = getTypes rtable
  vars_x = genTypedVars 'x' typesL
  vardecls = map (uncurry mkVarDecl)
  qual_vars = map (uncurry mkVarTerm)
  quantif = case r_type sen of
             RSone_to_one -> Unique_existential
             _ -> Existential
  (decls, terms) = foldl (\ (dList, tList) (c, i) ->
                    if SRel.c_name c `elem` map snd linkedcols then let
                       ti = mkAppl
                             (mkQualOp
                               (stringToId $
                                 show ltableName ++ "_" ++
                                 show (fst $ head $
                                  filter (\ (_, y) -> y == SRel.c_name c)
                                  linkedcols))
                               (Op_type
                                 Total
                                 typesL
                                 (stringToId $ show $ SRel.c_data c)
                                  nullRange)
                                )
                             (qual_vars vars_x)
                             in (dList, ti : tList)
                     else let
                       di = mkVarDecl
                             (genToken $ 'y' : show i)
                             (stringToId $ show $ SRel.c_data c)
                       ti = toQualVar di
                             in (di : dList, ti : tList)
                           ) ([], []) allRcols

  in return $ mkForall (vardecls vars_x) $ mkImpl
                    (mkPredication
                       (mkQualPred ltableName
                          (Pred_type typesL nullRange)
                          ) (qual_vars vars_x)
                       )

                    $ Quantification quantif (reverse decls)
                       (mkPredication
                          (mkQualPred rtableName
                             (Pred_type typesR nullRange)
                          )
                          (reverse terms)
                       ) nullRange
