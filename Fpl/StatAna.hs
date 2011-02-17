{- |
Module      :  $Header$
Description :  static basic analysis for FPL
Copyright   :  (c) Christian Maeder, DFKI GmbH 2011
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable
-}

module Fpl.StatAna where

import Fpl.As
import Fpl.Sign

import CASL.Sign
import CASL.MixfixParser
import CASL.StaticAna
import CASL.AS_Basic_CASL
import CASL.ShowMixfix
import CASL.Overload
import CASL.Quantification

import Common.AS_Annotation
import Common.ExtSign
import Common.GlobalAnnotations
import Common.Lib.State
import Common.Result

import Control.Monad

import qualified Data.Set as Set

type FplSign = Sign TermExt SignExt

basicFplAnalysis
  :: (FplBasicSpec, FplSign, GlobalAnnos)
  -> Result (FplBasicSpec, ExtSign FplSign Symbol, [Named FplForm])
basicFplAnalysis =
    basicAnalysis minFplTerm anaFplExt (const return) mixFplAna

mixFplAna :: Mix FplExt () TermExt SignExt
mixFplAna = emptyMix
    { getBaseIds = fplIds
    , putParen = mapTermExt
    , mixResolve = resolveTermExt
    }

fplIds :: FplExt -> IdSets
fplIds fe = case fe of
  FplSortItems sis _ -> unite $ map (fplSortIds . item) sis
  FplOpItems ois _ -> unite $ map (fplOpIds . item) ois

fplSortIds :: FplSortItem -> IdSets
fplSortIds si = case si of
  FreeType dt -> (ids_DATATYPE_DECL dt, Set.empty)
  CaslSortItem _ -> emptyIdSets

fplOpIds :: FplOpItem -> IdSets
fplOpIds oi = let e = Set.empty in case oi of
  FunOp (FunDef i vs _ _ _) -> let s = Set.singleton i in
      (if null vs then (s, e) else (e, s), e)
  CaslOpItem o -> (ids_OP_ITEM o, e)

-- | put parens around terms
mapTermExt :: TermExt -> TermExt
mapTermExt te = case te of
  FixDef fd -> FixDef $ mapFunDef fd
  Case o l r -> Case (mapTerm mapTermExt o)
    (map (\ (p, t) -> (mapTerm mapTermExt p, mapTerm mapTermExt t)) l) r
  Let fd t r -> Let (mapFunDef fd) (mapTerm mapTermExt t) r
  IfThenElse i t e r -> IfThenElse (mapFormula mapTermExt i)
    (mapTerm mapTermExt t) (mapTerm mapTermExt e) r

-- | put parens around final term
mapFunDef :: FunDef -> FunDef
mapFunDef (FunDef o vs s at r) =
  FunDef o vs s (fmap (mapTerm mapTermExt) at) r

resolveTermExt :: MixResolve TermExt
resolveTermExt ga ids te = case te of
  FixDef fd -> fmap FixDef $ resolveFunDef ga ids fd
  Case o l r -> do
    ro <- resolveMixTrm mapTermExt resolveTermExt ga ids o
    -- CHECK: consider pattern variables
    rl <- mapM (\ (p, t) -> liftM2 (,)
          (resolveMixTrm mapTermExt resolveTermExt ga ids p)
          $ resolveMixTrm mapTermExt resolveTermExt ga ids t) l
    return $ Case ro rl r
  Let fd t r -> do
    -- add function name for recursive mixfix analysis
    rfd <- resolveFunDef ga ids fd
    rt <- resolveMixTrm mapTermExt resolveTermExt ga ids t
    return $ Let rfd rt r
  IfThenElse i t e r -> do
    ri <- resolveMixFrm mapTermExt resolveTermExt ga ids i
    rt <- resolveMixTrm mapTermExt resolveTermExt ga ids t
    re <- resolveMixTrm mapTermExt resolveTermExt ga ids e
    return $ IfThenElse ri rt re r

-- | resolve overloading in rhs and assume function to be in the signature
resolveFunDef :: MixResolve FunDef
resolveFunDef ga ids (FunDef o vs s at r) = do
  nt <- resolveMixTrm mapTermExt resolveTermExt ga
    (extendRules (varDeclTokens vs) ids) $ item at
  return $ FunDef o vs s (replaceAnnoted nt at) r

funDefToOpDefn :: FunDef -> OP_ITEM TermExt
funDefToOpDefn (FunDef o vs s nt r) = Op_defn o (Op_head Total vs s r) nt r

opDefnToFunDefn :: FunDef -> OP_ITEM TermExt -> FunDef
opDefnToFunDefn def oi = case oi of
  Op_defn o (Op_head Total vs s _) nt r -> FunDef o vs s nt r
  _ -> def

minFplTerm :: Min TermExt SignExt
minFplTerm sig te = case te of
  FixDef fd -> fmap FixDef $ minFunDef sig fd
  Case o l r -> do
    ro <- oneExpTerm minFplTerm sig o
    -- assume unique type of top-level term for now
    let s = sortOfTerm ro
    -- CHECK: consider pattern variables
    rl <- mapM (\ (p, t) -> liftM2 (,)
          (oneExpTerm minFplTerm sig $ Sorted_term p s r)
          $ oneExpTerm minFplTerm sig $ Sorted_term t s r) l
    return $ Case ro rl r
  Let fd@(FunDef o vs s _ q) t r -> do
    let newSign = execState
          (addOp (emptyAnno o)
           (toOpType $ Op_type Total (sortsOfArgs vs) s q) o)
          sig
    rfd <- minFunDef newSign fd
    rt <- oneExpTerm minFplTerm sig t
    return $ Let rfd rt r
  IfThenElse i t e r -> do
    ri <- minExpFORMULA minFplTerm sig i
    Strong_equation rt re _ <-
        minExpFORMULAeq minFplTerm sig Strong_equation t e r
    return $ IfThenElse ri rt re r

-- | type check rhs and assume function to be in the signature
minFunDef :: Sign TermExt SignExt -> FunDef -> Result FunDef
minFunDef sig (FunDef o vs s at r) = do
  let newSign = execState (mapM_ addVars vs) sig
  nt <- oneExpTerm minFplTerm newSign $ Sorted_term (item at) s r
  return $ FunDef o vs s (replaceAnnoted nt at) r

getDDSorts :: [Annoted FplSortItem] -> [SORT]
getDDSorts = foldl (\ l si -> case item si of
  FreeType (Datatype_decl s _ _) -> s : l
  CaslSortItem _ -> l) []

anaFplExt :: Ana FplExt FplExt () TermExt SignExt
anaFplExt mix fe = case fe of
  FplSortItems ais r -> do
    mapM_ (\ s -> addSort NonEmptySorts (emptyAnno s) s)
      $ getDDSorts ais
    ns <- mapAnM (anaFplSortItem mix) ais
    closeSubsortRel
    return $ FplSortItems ns r
  FplOpItems ais r -> do
    ns <- mapAnM (anaFplOpItem mix) ais
    return $ FplOpItems ns r

anaFplSortItem :: Ana FplSortItem FplExt () TermExt SignExt
anaFplSortItem mix si = case si of
  FreeType dt -> do
    ana_DATATYPE_DECL Free dt
    return si
  CaslSortItem s -> fmap (CaslSortItem . item)
    $ ana_SORT_ITEM minFplTerm mix NonEmptySorts $ emptyAnno s

anaFplOpItem :: Ana FplOpItem FplExt () TermExt SignExt
anaFplOpItem mix oi = case oi of
  FunOp fd ->
    fmap (FunOp . opDefnToFunDefn fd . item)
      $ ana_OP_ITEM minFplTerm mix
      $ emptyAnno $ funDefToOpDefn fd
  CaslOpItem o -> fmap (CaslOpItem . item)
    $ ana_OP_ITEM minFplTerm mix (emptyAnno o)

-- free variables or only extracted from analysed terms
instance FreeVars TermExt where
  freeVarsOfExt s te = case te of
    FixDef fd -> freeFunDefVars s fd
    Case o l _ -> Set.unions $ freeTermVars s o
      : map (\ (p, t) -> Set.difference (freeTermVars s t) $ freeTermVars s p) l
    Let fd t _ -> Set.union (freeFunDefVars s fd) $ freeTermVars s t
    IfThenElse f t e _ -> Set.unions
      $ freeVars s f : map (freeTermVars s) [t, e]

freeFunDefVars :: Sign TermExt e -> FunDef -> VarSet
freeFunDefVars s (FunDef _ vs _ at _) = Set.difference
  (freeTermVars s $ item at) $ Set.fromList $ flatVAR_DECLs vs
