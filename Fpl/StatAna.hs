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
import CASL.SimplifySen

import Common.AS_Annotation
import Common.DocUtils
import Common.ExtSign
import Common.GlobalAnnotations
import Common.Id
import Common.Lib.State
import Common.Result

import Control.Monad

import qualified Data.Set as Set
import qualified Data.Map as Map

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
  FunOp (FunDef i (Op_head _ vs _ _) _ _) -> let s = Set.singleton i in
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
mapFunDef (FunDef o h at r) =
  FunDef o h (fmap (mapTerm mapTermExt) at) r

{- | The is the plugin function for the mixfix analysis. Due to patterns there
may be unknown simple identifiers that are turned to constants and later by
the overload resolution to variables. Obviously, such variables cannot be fed
into the mixfix analysis like all other known variables. Proper mixfix
identifiers in local let bindings are currently not fed into the mixfix
analysis! If such a non-simple identifier is globally unknown the analysis may
reject valid terms. -}
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
resolveFunDef ga ids (FunDef o h@(Op_head _ vs _ _) at r) = do
  nt <- resolveMixTrm mapTermExt resolveTermExt ga
    (extendRules (varDeclTokens vs) ids) $ item at
  return $ FunDef o h (replaceAnnoted nt at) r

funDefToOpDefn :: FunDef -> OP_ITEM TermExt
funDefToOpDefn (FunDef o h nt r) = Op_defn o h nt r

opDefnToFunDefn :: FunDef -> OP_ITEM TermExt -> FunDef
opDefnToFunDefn def oi = case oi of
  Op_defn o h nt r -> FunDef o h nt r
  _ -> def

{- | This functions tries to recognize variables in case-patterns (application
terms) after overload resolution.  Currently any operation in the signature is
(wrongly) regarded as constructor.  A further limitation is that a unique sort
is needed as input that is taken from the term between @case@ and @of@.  Also
uniqueness (linearity) of all variables is not checked yet. -}
resolvePattern :: FplSign -> (SORT, FplTerm) -> Result ([VAR_DECL], FplTerm)
resolvePattern sign (resSort, term) =
  let err msg = fail $ msg ++ " " ++ showDoc term "" in
  case term of
  Application opSym args p ->
    let ide@(Id ts _ _) = opSymbName opSym in
    case filter ( \ oTy@(OpType _ oArgs oRes) -> length oArgs == length args
                    && (leqSort sign resSort oRes || leqSort sign oRes resSort)
                    && case opSym of
                         Qual_op_name _ symTy _ ->
                             leqF sign oTy $ toOpType symTy
                         _ -> True
                    )
         $ Set.toList $ Map.findWithDefault Set.empty ide $ opMap sign of
      [] -> if null args && isSimpleId ide then
                let v = Var_decl [head ts] resSort $ posOfId ide
                in return ([v], toQualVar v)
            else err "unresolved pattern"
      [OpType k as r] -> do
        l <- mapM (resolvePattern sign) $ zip as args
        return (concatMap fst l,
          Application (Qual_op_name ide (Op_type k as r p) p) (map snd l) p)
      _ -> err "ambiguous pattern"
  Qual_var v s r -> if leqSort sign s resSort then
      return ([Var_decl [v] s r], term)
    else err "wrong type of pattern variable"
  Sorted_term t s r -> if leqSort sign s resSort then do
      (vs, nt) <- resolvePattern sign (s, t)
      return (vs, Sorted_term nt s r)
    else err "wrong typed pattern"
  _ -> err "unexpected pattern"

{- | perform overload resolution after mixfix analysis. Case expressions are
not fully checked yet. The type of patterns is deduced from the top term, but
it is not checked, if the rhs types of all branches are compatible. -}
minFplTerm :: Min TermExt SignExt
minFplTerm sig te = case te of
  FixDef fd -> fmap FixDef $ minFunDef sig fd
  Case o l r -> do
    ro <- oneExpTerm minFplTerm sig o
    -- assume unique type of top-level term for now
    let s = sortOfTerm ro
    rl <- mapM (\ (p, t) -> do
          (vs, np) <- resolvePattern sig (s, p)
          let newSign = execState (mapM_ addVars vs) sig
          rt <- oneExpTerm minFplTerm newSign t
          return (np, rt)) l
    return $ Case ro rl r
  Let fd@(FunDef o h _ _) t r -> do
    let newSign = execState
          (addOp (emptyAnno o)
           (toOpType $ headToType h) o)
          sig
    rfd <- minFunDef newSign fd
    rt <- oneExpTerm minFplTerm newSign t
    return $ Let rfd rt r
  IfThenElse i t e r -> do
    ri <- minExpFORMULA minFplTerm sig i
    Strong_equation rt re _ <-
        minExpFORMULAeq minFplTerm sig Strong_equation t e r
    return $ IfThenElse ri rt re r

-- | type check rhs and assume function to be in the signature
minFunDef :: Sign TermExt SignExt -> FunDef -> Result FunDef
minFunDef sig (FunDef o h@(Op_head _ vs s _) at r) = do
  let newSign = execState (mapM_ addVars vs) sig
  nt <- oneExpTerm minFplTerm newSign $ Sorted_term (item at) s r
  return $ FunDef o h (replaceAnnoted nt at) r

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
  FunOp (FunDef i oh@(Op_head _ vs r _) at ps) -> do
    let ty = headToType oh
        lb = getRLabel at
    addOp (emptyAnno i) (toOpType ty) i
    e <- get -- save
    put e { varMap = Map.empty }
    mapM_ addVars vs
    sign <- get
    put e -- restore
    let Result ds mt = anaTerm minFplTerm mix sign r ps $ item at
    addDiags ds
    case mt of
      Nothing -> return $ CaslOpItem $ Op_decl [i] ty [] ps
      Just (resT, anaT) -> do
        addSentences
          [(makeNamed lb $ ExtFORMULA $ FixDef
           $ FunDef i oh at { item = anaT } ps)
           { isAxiom = notImplied at, isDef = True }]
        return $ FunOp $ FunDef i oh at { item = resT } ps
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
freeFunDefVars s (FunDef _ (Op_head _ vs _ _) at _) = Set.difference
  (freeTermVars s $ item at) $ Set.fromList $ flatVAR_DECLs vs

instance TermExtension TermExt where
    optTermSort te = case te of
      Case _ ((_, t) : _) _ -> optTermSort t
      Let _ t _ -> optTermSort t
      IfThenElse _ t _ _ -> optTermSort t
      _ -> Nothing

simplifyTermExt :: FplSign -> TermExt -> TermExt
simplifyTermExt s te = let rec = simplifyTerm minFplTerm simplifyTermExt in
  case te of
    FixDef fd -> FixDef $ simplifyFunDef s fd
    Case o l r -> Case (rec s o)
      (map (\ (p, t) -> let
                vs = freeTermVars s p
                newSign = execState
                  (mapM_ (uncurry $ flip addVar) $ Set.toList vs) s
                in (rec newSign p, rec newSign t)) l) r
    Let fd@(FunDef o h _ _) t r ->
      let newSign = execState (addOp (emptyAnno o) (toOpType $ headToType h) o)
            s
      in Let (simplifyFunDef newSign fd)
            (rec newSign t) r
    IfThenElse f t e r -> IfThenElse
      (simplifySen minFplTerm simplifyTermExt s f) (rec s t) (rec s e) r

simplifyFunDef :: FplSign -> FunDef -> FunDef
simplifyFunDef sig (FunDef o h@(Op_head _ vs _ _) at r) =
   let newSign = execState (mapM_ addVars vs) sig
   in FunDef o h (fmap (simplifyTerm minFplTerm simplifyTermExt newSign) at) r
