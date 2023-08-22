{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  ./Comorphisms/CASL2PCFOL.hs
Description :  coding out subsorting
Copyright   :  (c) Zicheng Wang, Liam O'Reilly, C. Maeder Uni Bremen 2002-2009
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

Coding out subsorting (SubPCFOL= -> PCFOL=),
   following Chap. III:3.1 of the CASL Reference Manual
-}

module Comorphisms.CASL2PCFOL where

import Logic.Logic
import Logic.Comorphism

import qualified Data.Set as Set

import qualified Common.Lib.Rel as Rel
import Common.AS_Annotation
import Common.Id
import Common.ProofTree

-- CASL
import CASL.Logic_CASL
import CASL.AS_Basic_CASL
import CASL.Sign
import CASL.Morphism
import CASL.Sublogic as Sublogic
import CASL.Inject
import CASL.Project
import CASL.Monoton

-- | The identity of the comorphism
data CASL2PCFOL = CASL2PCFOL deriving Show

instance Language CASL2PCFOL -- default definition is okay

instance Comorphism CASL2PCFOL
               CASL CASL_Sublogics
               CASLBasicSpec CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CASLSign
               CASLMor
               Symbol RawSymbol ProofTree
               CASL CASL_Sublogics
               CASLBasicSpec CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CASLSign
               CASLMor
               Symbol RawSymbol ProofTree where
    sourceLogic CASL2PCFOL = CASL
    sourceSublogic CASL2PCFOL = Sublogic.caslTop
    targetLogic CASL2PCFOL = CASL
    mapSublogic CASL2PCFOL sl = Just $
                                if has_sub sl then -- subsorting is coded out
                                      sl { sub_features = NoSub
                                         , has_part = True
                                         , which_logic = max Horn
                                                         $ which_logic sl
                                         , has_eq = True}
                                  else sl
    map_theory CASL2PCFOL = mkTheoryMapping ( \ sig ->
      let e = encodeSig sig in
      return (e, map (mapNamed $ injFormula id) (monotonicities sig)
                 ++ generateAxioms sig))
      (map_sentence CASL2PCFOL)
    map_morphism CASL2PCFOL mor = return
      (mor { msource = encodeSig $ msource mor,
              mtarget = encodeSig $ mtarget mor })
      -- other components need not to be adapted!
    map_sentence CASL2PCFOL _ = return . f2Formula
    map_symbol CASL2PCFOL _ = Set.singleton . id
    has_model_expansion CASL2PCFOL = True
    is_weakly_amalgamable CASL2PCFOL = True

-- | Add injection, projection and membership symbols to a signature
encodeSig :: Sign f e -> Sign f e
encodeSig sig
  = if Rel.noPairs rel then sig else
      sig {sortRel = Rel.fromKeysSet $ sortSet sig, opMap = projOpMap}
  where
        rel = Rel.irreflex $ sortRel sig
        relSet = Rel.toSet rel
        total (s, s') = mkTotOpType [s] s'
        partial (s, s') = (if Rel.member s' s rel then id else mkPartial)
          $ total (s', s)
        setinjOptype = Set.map total relSet
        setprojOptype = Set.map partial relSet
        injOpMap = Set.fold (\ t -> addOpTo (uniqueInjName $ toOP_TYPE t) t)
          (opMap sig) setinjOptype
        projOpMap = Set.fold (\ t -> addOpTo (uniqueProjName $ toOP_TYPE t) t)
          injOpMap setprojOptype
    -- membership predicates are coded out

-- | Make the name for the embedding or projecton injectivity axiom
mkInjectivityName :: String -> SORT -> SORT -> String
mkInjectivityName = mkAxName . (++ "_injectivity")

-- | Make the name for the embedding injectivity axiom
mkEmbInjName :: SORT -> SORT -> String
mkEmbInjName = mkInjectivityName "embedding"

-- | Make the name for the projection injectivity axiom
mkProjInjName :: SORT -> SORT -> String
mkProjInjName = mkInjectivityName "projection"

-- | create a quantified injectivity implication
mkInjectivity :: (TERM f -> TERM f) -> VAR_DECL -> VAR_DECL -> FORMULA f
mkInjectivity f vx vy =
  mkForall [vx, vy] $ mkInjImpl f (toQualVar vx) $ toQualVar vy

-- | create an injectivity implication over x and y
mkInjImpl :: (TERM f -> TERM f) -> TERM f -> TERM f -> FORMULA f
mkInjImpl f x y = mkImpl (mkExEq (f x) (f y)) (mkExEq x y)

-- | apply injection function
injectTo :: TermExtension f => SORT -> TERM f -> TERM f
injectTo s q = injectUnique nullRange q s

-- | apply (a partial) projection function
projectTo :: TermExtension f => SORT -> TERM f -> TERM f
projectTo s q = projectUnique Partial nullRange q s

{- | Make the named sentence for the embedding injectivity axiom from s to s'
i.e., forall x,y:s . inj(x)=e=inj(y) => x=e=y -}
mkEmbInjAxiom :: TermExtension f => SORT -> SORT -> Named (FORMULA f)
mkEmbInjAxiom s s' =
    makeNamed (mkEmbInjName s s')
      $ mkInjectivity (injectTo s') (mkVarDeclStr "x" s) $ mkVarDeclStr "y" s

{- | Make the named sentence for the projection injectivity axiom from s' to s
i.e., forall x,y:s . pr(x)=e=pr(y) => x=e=y -}
mkProjInjAxiom :: TermExtension f => SORT -> SORT -> Named (FORMULA f)
mkProjInjAxiom s s' =
    makeNamed (mkProjInjName s' s)
      $ mkInjectivity (projectTo s) (mkVarDeclStr "x" s') $ mkVarDeclStr "y" s'

-- | Make the name for the projection axiom
mkProjName :: SORT -> SORT -> String
mkProjName = mkAxName "projection"

-- | create a quantified existential equation over x of sort s
mkXExEq :: SORT -> (TERM f -> TERM f) -> (TERM f -> TERM f) -> FORMULA f
mkXExEq s fl fr = let
  vx = mkVarDeclStr "x" s
  qualX = toQualVar vx
  in mkForall [vx] $ mkExEq (fl qualX) (fr qualX)

{- | Make the named sentence for the projection axiom from s' to s
i.e., forall x:s . pr(inj(x))=e=x -}
mkProjAxiom :: TermExtension f => SORT -> SORT -> Named (FORMULA f)
mkProjAxiom s s' = makeNamed (mkProjName s' s)
    $ mkXExEq s (projectTo s . injectTo s') id

-- | Make the name for the transitivity axiom from s to s' to s''
mkTransAxiomName :: SORT -> SORT -> SORT -> String
mkTransAxiomName s s' s'' =
  mkAxName "transitivity" s s' ++ "_to_" ++ show s''

{- | Make the named sentence for the transitivity axiom from s to s' to s''
i.e., forall x:s . inj(inj(x))=e=inj(x) -}
mkTransAxiom :: TermExtension f => SORT -> SORT -> SORT -> Named (FORMULA f)
mkTransAxiom s s' s'' = makeNamed (mkTransAxiomName s s' s'')
    $ mkXExEq s (injectTo s'' . injectTo s') $ injectTo s''

-- | Make the name for the identity axiom from s to s'
mkIdAxiomName :: SORT -> SORT -> String
mkIdAxiomName = mkAxName "identity"

{- | Make the named sentence for the identity axiom from s to s'
i.e., forall x:s . inj(inj(x))=e=x -}
mkIdAxiom :: TermExtension f => SORT -> SORT -> Named (FORMULA f)
mkIdAxiom s s' = makeNamed (mkIdAxiomName s s')
    $ mkXExEq s (injectTo s . injectTo s') id

generateAxioms :: TermExtension f => Sign f e -> [Named (FORMULA f)]
generateAxioms sig = concatMap (\ s ->
    concatMap (\ s' ->
      [mkIdAxiom s s' | Set.member s $ supersortsOf s' sig ]
      ++ mkEmbInjAxiom s s' : mkProjInjAxiom s s' : mkProjAxiom s s'
      : map (mkTransAxiom s s') (filter (/= s) $ realSupers s'))
    $ realSupers s) $ Set.toList $ sortSet sig
    where
        realSupers so = Set.toList $ supersortsOf so sig

f2Formula :: TermExtension f => FORMULA f -> FORMULA f
f2Formula = projFormula Partial id . injFormula id

t2Term :: TermExtension f => TERM f -> TERM f
t2Term = projTerm Partial id . injTerm id
