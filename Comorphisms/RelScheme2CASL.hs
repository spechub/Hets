{- |
Module      :  $Header$
Description :  Comorphism from RelScheme to CASL
Copyright   :  (c) Dominik Luecke and Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

The translating comorphism from DL to CASL_DL basically this is an
identity comorphism from SROIQ(D) to SROIQ(D)
-}

module Comorphisms.RelScheme2CASL
    (
     RelScheme2CASL(..)
    )
    where

import Logic.Logic
import Logic.Comorphism
import Common.AS_Annotation
import Common.Result
import Common.Id
import qualified Data.Set as Set
import qualified Data.Map as Map

-- RelScheme
import RelationalScheme.Logic_Rel as LRel
import RelationalScheme.AS as ARel
import qualified RelationalScheme.Sign as SRel

--CASL = codomain
import CASL.Logic_CASL
import CASL.AS_Basic_CASL
import CASL.Sublogic as SL
import CASL.Sign
import CASL.Morphism

import Data.List(nub)

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
    Q_ProofTree              -- proof tree domain
        where
          sourceLogic RelScheme2CASL    = RelScheme
          sourceSublogic RelScheme2CASL = ()
          targetLogic RelScheme2CASL    = CASL
          mapSublogic RelScheme2CASL _  = Just SL.caslTop
          map_theory RelScheme2CASL     = map_RelScheme_theory
          map_morphism RelScheme2CASL   = error "map_morphism RelScheme2CASL"
          map_sentence RelScheme2CASL = mapSen


map_RelScheme_theory :: (SRel.Sign, [Named Sentence])
                     -> Result (CASLSign, [Named CASLFORMULA])
map_RelScheme_theory (sig, n_sens) = do
     let (sorts,ops,preds) = genCASLSig (Set.toList $ SRel.tables sig)
                                                Set.empty Map.empty Map.empty
         tsign = (emptySign ()){
                  sortSet = sorts,
                  opMap = ops,
                  predMap = preds
                 }
     tax <- sequence $ map genAxioms $ Set.toList $ SRel.tables sig
     tsens <- sequence $  map (mapNamedSen sig) n_sens
     return (tsign, concat (tsens:tax))

genCASLSig :: [SRel.RSTable] ->
              Set.Set SORT ->
              Map.Map Id (Set.Set OpType) ->
              Map.Map Id (Set.Set PredType) ->
              (Set.Set SORT,
               Map.Map Id (Set.Set OpType),
               Map.Map Id (Set.Set PredType)
              )
genCASLSig tabList sorts ops preds=
 case tabList of
  [] -> (sorts, ops, preds)
  t:tList -> let
              sorts' =  Set.fromList $ map stringToId $ map show $
                        nub $ map SRel.c_data $ SRel.columns t
              ops' = let
                       arity = map stringToId $ map show $ map SRel.c_data $
                               SRel.columns t
                     in Map.fromList $
                         map (
                          \c -> (stringToId $
                                  (show $ SRel.t_name t) ++ "_"
                                  ++ (show $ SRel.c_name c),
                                 Set.singleton $
                                 OpType{opKind = Total,
                                        opArgs = arity,
                                        opRes = stringToId $
                                                show $ SRel.c_data c
                                 })
                         ) $ SRel.columns t
              preds' = Map.insert (SRel.t_name t)
                        (Set.singleton $ PredType $ map stringToId $
                        map show $ map SRel.c_data $
                        SRel.columns t) preds
             in genCASLSig tList
                           (Set.union sorts sorts')
                           (Map.union ops ops')
                           preds'

genAxioms :: SRel.RSTable -> Result [Named CASLFORMULA]
genAxioms tab = do
  case (Set.null $ SRel.t_keys tab) of
    True ->  projections tab
    _ -> do
          axK <- axiomsForKeys tab
          axP <- projections tab
          return $ axK ++ axP

axiomsForKeys :: SRel.RSTable -> Result [Named CASLFORMULA]
axiomsForKeys tab = do
 let
  types = map stringToId $ map show $ map SRel.c_data $ SRel.columns tab
  vars_x = map (\(t,n) -> (genToken ("x"++ (show n)), t)) $
           zip types [1::Int ..]
  vars_y = map (\(t,n) -> (genToken ("y"++ (show n)), t)) $
           zip types [1::Int ..]
  vardecls = map (\(v,t) -> Var_decl [v] t nullRange)
  qual_vars = map (\(v,t) -> Qual_var v t nullRange )
  conjuncts = map (\(x,y) -> Strong_equation x y nullRange) $
              zip (qual_vars vars_x)(qual_vars vars_y)
  keys = Set.toList $ SRel.t_keys tab
  keysEqual = map (\(cid, ctype) -> Strong_equation
                          (Application
                             (Qual_op_name (stringToId $ (show $ SRel.t_name tab)++ "_" ++ (show cid))
                                (Op_type Total types (stringToId $ show ctype) nullRange)
                                nullRange) (qual_vars vars_x)
                             nullRange)
                          (Application
                             (Qual_op_name (stringToId $ (show $ SRel.t_name tab)++ "_" ++ (show cid))
                                (Op_type Total types (stringToId $ show ctype) nullRange)
                                nullRange) (qual_vars vars_y)
                             nullRange)
                          nullRange) keys
 return $ [makeNamed "" $ Quantification Universal
            ((vardecls vars_x) ++ (vardecls vars_y))
                 (Implication
                    (Conjunction
                       ([Predication
                          (Qual_pred_name (SRel.t_name tab) (Pred_type types nullRange)
                             nullRange)
                          (qual_vars vars_x)
                          nullRange,
                         Predication
                          (Qual_pred_name (SRel.t_name tab) (Pred_type types nullRange)
                             nullRange)
                          (qual_vars vars_y)
                          nullRange] ++ keysEqual)
                       nullRange)
                    (Conjunction
                       conjuncts
                       nullRange)
                    True
                    nullRange)
                 nullRange]

projections :: SRel.RSTable -> Result [Named CASLFORMULA]
projections tab = do
 let
  types = map stringToId $ map show $ map SRel.c_data $ SRel.columns tab
  vars_x = map (\(t,n) -> (genToken ("x"++ (show n)), t)) $
           zip types [1::Int ..]
  vardecls = map (\(v,t) -> Var_decl [v] t nullRange)
  qual_vars = map (\(v,t) -> Qual_var v t nullRange )
  fields = map show $ map SRel.c_name $ SRel.columns tab
  projAx (c, (vRes,typeRes)) = makeNamed "" $
            Quantification Universal
            (vardecls vars_x)
                   (Strong_equation
                    (Application
                       (Qual_op_name (stringToId $ (show $ SRel.t_name tab)++ "_" ++ c)
                          (Op_type Total types typeRes nullRange)
                          nullRange) (qual_vars vars_x)
                       nullRange)
                    (Qual_var vRes typeRes nullRange)
                    nullRange)
            nullRange
 return $ map projAx $ zip fields vars_x


mapNamedSen :: SRel.Sign -> Named Sentence -> Result (Named CASLFORMULA)
mapNamedSen sign n_sens =
    let
        s = sentence n_sens
    in
      do
        ts <- mapSen sign s
        return $ n_sens {sentence = ts}

mapSen :: SRel.Sign -> Sentence -> Result CASLFORMULA
mapSen sign sen = do
 let
  linkedcols = zip (map column $ r_lhs sen) (map column $ r_rhs sen)
  rtableName = head $ map table $ r_rhs sen
  ltableName = head $ map table $ r_lhs sen
  rtable = head $ filter (\t -> SRel.t_name t == rtableName) $ Set.toList $
           SRel.tables sign
  allRcols = zip (SRel.columns rtable) [1::Int ..]

  types = map stringToId $ map show $ map SRel.c_data $ SRel.columns rtable
  vars_x = map (\(t,n) -> (genToken ("x"++ (show n)), t)) $
           zip types [1::Int ..]
  vardecls = map (\(v,t) -> Var_decl [v] t nullRange)
  qual_vars = map (\(v,t) -> Qual_var v t nullRange )
  quantif = case r_type sen of
             RSone_to_one -> Unique_existential
             _ -> Existential

  (decls,terms) = foldl (\(dList,tList) (c,i) ->
                          case SRel.c_name c `elem` (map snd linkedcols) of
                           True -> let
                                    ti = Application
                                          (Qual_op_name (stringToId $ (show ltableName) ++ "_" ++ (show $ fst $ head $ filter(\(_,y) -> y == SRel.c_name c) linkedcols))
                                           (Op_type Total types (stringToId $ show $ SRel.c_data c) nullRange)
                                           nullRange) (qual_vars vars_x)
                                          nullRange
                                   in
                                    (dList,ti:tList)
                           _ -> let
                                  di = Var_decl [genToken ("y"++ (show i))] (stringToId $ show $ SRel.c_data c) nullRange
                                  ti = Qual_var (genToken ("y"++ (show i))) (stringToId $ show $ SRel.c_data c) nullRange
                                in (di:dList,ti:tList)
                           ) ([],[]) allRcols

 return $ Quantification Universal (vardecls vars_x)
          (Implication
                    (Predication
                       (Qual_pred_name ltableName
                          (Pred_type types nullRange)
                          nullRange) (qual_vars vars_x)
                       nullRange)

                    (Quantification quantif (reverse decls)
                       (Predication
                          (Qual_pred_name rtableName
                             (Pred_type types nullRange)
                             nullRange)
                          (reverse terms)
                          nullRange)
                       nullRange)

                    True
                    nullRange)
            nullRange

