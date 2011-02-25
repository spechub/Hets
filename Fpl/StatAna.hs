{- |
Module      :  $Header$
Description :  static basic analysis for FPL
Copyright   :  (c) Christian Maeder, DFKI GmbH 2011
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

basic static analysis for FPL

missing: mixfix analysis for patterns could be specialized, local mixfix
identifiers are not supported yet, different constructor sets for the same
sort are not considered. Subsort embedding constructors are ignored.

-}

module Fpl.StatAna
  ( basicFplAnalysis
  , minFplTerm
  , simplifyTermExt
  ) where

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
import Common.Utils

import Control.Monad

import qualified Data.Set as Set
import qualified Data.Map as Map

basicFplAnalysis
  :: (FplBasicSpec, FplSign, GlobalAnnos)
  -> Result (FplBasicSpec, ExtSign FplSign Symbol, [Named FplForm])
basicFplAnalysis (b, s, ga) =
    fmap (\ (r, ExtSign t syms, sens) ->
       (r, ExtSign (delBuiltins t) syms, sens))
    $ basicAnalysis minFplTerm anaFplExt (const return) mixFplAna
    (b, addBuiltins s, ga)

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
mapTermExt te = let rec = mapTerm mapTermExt in case te of
  FixDef fd -> FixDef $ mapFunDef fd
  Case o l r -> Case (rec o)
    (map (\ (p, t) -> (rec p, rec t)) l) r
  Let fd t r -> Let (mapFunDef fd) (rec t) r
  IfThenElse i t e r -> IfThenElse (rec i) (rec t) (rec e) r
  EqTerm t e r -> EqTerm (rec t) (rec e) r
  BoolTerm t -> BoolTerm (rec t)

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
resolveTermExt ga ids te =
  let recAux = resolveMixTrm mapTermExt resolveTermExt ga
      rec = recAux ids
  in case te of
  FixDef fd -> fmap FixDef $ resolveFunDef ga ids fd
  Case o l r -> do
    ro <- rec o
    -- CHECK: consider pattern variables
    rl <- mapM (\ (p, t) -> liftM2 (,)
          (rec p)
          $ rec t) l
    return $ Case ro rl r
  Let fd@(FunDef o _ _ _) t r -> do
    rfd <- resolveFunDef ga ids fd
    rt <- recAux (addIdToRules o ids) t
    return $ Let rfd rt r
  IfThenElse i t e r -> do
    ri <- rec i
    rt <- rec t
    re <- rec e
    return $ IfThenElse ri rt re r
  EqTerm t e r -> do
    rt <- rec t
    re <- rec e
    return $ EqTerm rt re r
  BoolTerm t -> fmap BoolTerm $ rec t

-- | resolve overloading in rhs and assume function to be in the signature
resolveFunDef :: MixResolve FunDef
resolveFunDef ga ids (FunDef o h@(Op_head _ vs _ _) at r) = do
  nt <- resolveMixTrm mapTermExt resolveTermExt ga
    (addIdToRules o $ extendRules (varDeclTokens vs) ids) $ item at
  return $ FunDef o h (replaceAnnoted nt at) r

-- | get constructors for input sort
getConstrs :: FplSign -> SORT -> OpMap
getConstrs sign resSort = Map.filter (not . Set.null)
  $ Map.map (Set.filter $ leqSort sign resSort . opRes)
         $ constr $ extendedInfo sign

{- | This functions tries to recognize variables in case-patterns (application
terms) after overload resolution.  A current limitation is that a unique sort
is needed as input that is taken from the term between @case@ and @of@. -}
resolvePattern :: FplSign -> (SORT, FplTerm) -> Result ([VAR_DECL], FplTerm)
resolvePattern sign (resSort, term) =
  let err msg = fail $ msg ++ " " ++ showDoc term "" in
  case term of
  Application opSym args p ->
    let ide@(Id ts _ _) = opSymbName opSym in
    case filter ( \ oTy -> length (opArgs oTy) == length args
                    && case opSym of
                         Qual_op_name _ symTy _ ->
                             leqF sign oTy $ toOpType symTy
                         _ -> True
                    )
         $ Set.toList $ Map.findWithDefault Set.empty ide
         $ getConstrs sign resSort of
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

addFunToSign :: FunDef -> State FplSign ()
addFunToSign (FunDef o h _ _) = addOp (emptyAnno o) (toOpType $ headToType h) o

{- | perform overload resolution after mixfix analysis. The type of patterns
is deduced from the top term. Overlapping or exhaustive patterns are not
recognized yet. -}
minFplTerm :: Min TermExt SignExt
minFplTerm sig te = case te of
  FixDef fd -> fmap FixDef $ minFunDef sig fd
  Case o l r -> do
    ro <- oneExpTerm minFplTerm sig o
    -- assume unique type of top-level term for now
    let s = sortOfTerm ro
    rl <- mapM (\ (p, t) -> do
          (vs, np) <- resolvePattern sig (s, p)
          appendDiags $ checkUniqueness . map fst $ flatVAR_DECLs vs
          let newSign = execState (mapM_ addVars vs) sig
          rt <- minExpTerm minFplTerm newSign t
          return (np, rt)) l
    let (ps, tts) = unzip rl
        cSupers tl = case tl of
          [] -> True
          hd : rt -> all (haveCommonSupersorts True sig
             (sortOfTerm hd) . sortOfTerm) rt && cSupers rt
    nts <- isUnambiguous (globAnnos sig) (map snd l)
      (map (filter cSupers . combine) $ combine tts) r
    let nl = zip ps nts
        minSort sl = if Set.null sl then Set.empty else
           let (hd, rt) = Set.deleteFindMin sl
           in Set.unions . map (Set.fromList . minimalSupers sig hd)
                    . Set.toList $ Set.insert hd $ minSort rt
        mSort = minSort . Set.fromList $ map sortOfTerm nts
    case Set.toList mSort of
      [tSort] -> do
         fl <- mapM (\ (p, t) -> do
            let pvs = freeTermVars sig p
                tvs = freeTermVars sig t
                unused = Set.difference pvs tvs
            unless (Set.null unused) $
              appendDiags $ map (mkDiag Warning "unused pattern variables")
                     $ Set.toList unused
            return (p, mkSorted sig t tSort r)) nl
         return $ Case ro fl r
      sl -> mkError ("no common supersort for case terms: " ++ show sl) r
  Let fd t r -> do
    let newSign = execState (addFunToSign fd) sig
    rfd <- minFunDef newSign fd
    rt <- oneExpTerm minFplTerm newSign t
    return $ Let rfd rt r
  IfThenElse i t e r -> do
    ri <- oneExpTerm minFplTerm sig $ Sorted_term i boolSort r
    Strong_equation rt re _ <-
        minExpFORMULAeq minFplTerm sig Strong_equation t e r
    return $ IfThenElse ri rt re r
  EqTerm t e r -> do
    Strong_equation rt re _ <-
        minExpFORMULAeq minFplTerm sig Strong_equation t e r
    return $ EqTerm rt re r
  BoolTerm t -> fmap BoolTerm $ oneExpTerm minFplTerm sig t

-- | type check rhs and assume function to be in the signature
minFunDef :: Sign TermExt SignExt -> FunDef -> Result FunDef
minFunDef sig fd@(FunDef o h@(Op_head _ vs s _) at r) = do
  let newSign = execState (mapM_ addVars vs >> addFunToSign fd) sig
      varSign = execState (mapM_ addVars vs) $ emptySign emptyFplSign
  nt <- oneExpTerm minFplTerm newSign $ Sorted_term (item at) s r
  appendDiags $ warnUnusedVars " function " varSign $ freeTermVars newSign nt
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
  FreeType dt@(Datatype_decl s aalts _) -> do
    ana_DATATYPE_DECL Free dt
    sign <- get
    let cm = getConstrs sign s
    updateExtInfo $ \ cs -> foldM
      (\ e aa -> let a = item aa in if isConsAlt a then do
            let (c, ty, _) = getConsType s a
            unless (Map.null cm)
              $ if Set.member (mkPartial ty)
                    $ makePartial $ Map.findWithDefault Set.empty c cm
                then appendDiags [mkDiag Warning "repeated constructor" c]
                else mkError "illegal new constructor" c
            return e { constr = addOpTo c ty $ constr e }
      else mkError "unexpected subsort embedding" a) cs aalts
    return si
  CaslSortItem s -> fmap (CaslSortItem . item)
    $ ana_SORT_ITEM minFplTerm mix NonEmptySorts $ emptyAnno s

anaFplOpItem :: Ana FplOpItem FplExt () TermExt SignExt
anaFplOpItem mix oi = case oi of
  FunOp fd@(FunDef i oh@(Op_head _ vs r _) at ps) -> do
    let ty = headToType oh
        lb = getRLabel at
    addFunToSign fd
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

freeFunDefVars :: Sign TermExt e -> FunDef -> VarSet
freeFunDefVars s (FunDef _ (Op_head _ vs _ _) at _) = Set.difference
  (freeTermVars s $ item at) $ Set.fromList $ flatVAR_DECLs vs

instance TermExtension TermExt where
  freeVarsOfExt s te = case te of
    FixDef fd -> freeFunDefVars s fd
    Case o l _ -> Set.unions $ freeTermVars s o
      : map (\ (p, t) -> Set.difference (freeTermVars s t) $ freeTermVars s p) l
    Let fd t _ -> Set.union (freeFunDefVars s fd) $ freeTermVars s t
    IfThenElse f t e _ -> Set.unions $ map (freeTermVars s) [f, t, e]
    EqTerm t e _ -> Set.unions $ map (freeTermVars s) [t, e]
    BoolTerm t -> freeTermVars s t

  optTermSort te = case te of
      Case _ ((_, t) : _) _ -> optTermSort t
      Let _ t _ -> optTermSort t
      IfThenElse _ t _ _ -> optTermSort t
      EqTerm _ _ _ -> Just boolSort
      BoolTerm t -> optTermSort t
      _ -> Nothing -- all others are formulas
  termToFormula t = let s = sortOfTerm t in
        if s == boolSort
        then return $ ExtFORMULA $ BoolTerm t
        else fail $ "expected boolean term but found sort: " ++ show s

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
    Let fd t r ->
      let newSign = execState (addFunToSign fd) s
      in Let (simplifyFunDef newSign fd)
            (rec newSign t) r
    IfThenElse f t e r -> IfThenElse (rec s f) (rec s t) (rec s e) r
    EqTerm t e r -> EqTerm (rec s t) (rec s e) r
    BoolTerm t -> BoolTerm (rec s t)

simplifyFunDef :: FplSign -> FunDef -> FunDef
simplifyFunDef sig fd@(FunDef o h@(Op_head _ vs _ _) at r) =
   let newSign = execState (mapM_ addVars vs >> addFunToSign fd) sig
   in FunDef o h (fmap (simplifyTerm minFplTerm simplifyTermExt newSign) at) r
