{- |
Module      :  $Header$
Description :  static analysis of VSE parts
Copyright   :  (c) C. Maeder, DFKI Bremen 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

analysis of VSE logic extension of CASL
-}

module VSE.Ana where

import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set

import qualified Common.Lib.Rel as Rel
import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.ExtSign
import Common.Id
import Common.Result
import Common.Lib.State

import CASL.AS_Basic_CASL
import CASL.Fold
import CASL.Sign
import CASL.MixfixParser
import CASL.MapSentence as MapSen
import CASL.Morphism
import CASL.Overload
import CASL.Quantification
import CASL.StaticAna
import CASL.ShowMixfix as Paren
import CASL.SimplifySen

import VSE.As

lookupProc :: Id -> Sign f Procs -> Maybe Profile
lookupProc i sig = Map.lookup i $ procsMap $ extendedInfo sig

basicAna
  :: (BASIC_SPEC () Procdecls Dlformula,
      Sign Dlformula Procs, GlobalAnnos)
  -> Result (BASIC_SPEC () Procdecls Dlformula,
             ExtSign (Sign Dlformula Procs) Symbol,
             [Named Sentence])
basicAna =
    basicAnalysis minExpForm (const return) anaProcdecls anaMix

anaMix :: Mix () Procdecls Dlformula Procs
anaMix = emptyMix
  { putParen = parenDlFormula
  , mixResolve = resolveDlformula }

-- | put parens around ambiguous mixfix formulas (for error messages)
parenDlFormula :: Dlformula -> Dlformula
parenDlFormula (Ranged f r) = case f of
  Dlformula b p s ->
    let n = mapFormula parenDlFormula s
    in Ranged (Dlformula b (parenProg p) n) r
  Defprocs ps -> Ranged (Defprocs $ map parenDefproc ps) r

mapProg :: (TERM () -> TERM ()) -> (FORMULA () -> FORMULA ())
        -> FoldRec Program
mapProg mt mf = mapRec
  { foldAssign = \ (Ranged _ r) v t -> Ranged (Assign v $ mt t) r
  , foldCall = \ (Ranged _ r) f -> Ranged (Call $ mf f) r
  , foldReturn = \ (Ranged _ r) t -> Ranged (Return $ mt t) r
  , foldIf = \ (Ranged _ r) c p1 p2 -> Ranged (If (mf c) p1 p2) r
  , foldWhile = \ (Ranged _ r) c p -> Ranged (While (mf c) p) r }

parenProg :: Program -> Program
parenProg = foldProg $ mapProg (Paren.mapTerm id) $ mapFormula id

parenDefproc :: Defproc -> Defproc
parenDefproc (Defproc k i vs p r) = Defproc k i vs (parenProg p) r

procsToOpPredMaps :: Procs -> (Map.Map Id (Set.Set PredType), OpMap)
procsToOpPredMaps (Procs m) =
  foldr (\ (n, pr) (pm, om) -> case profileToOpType pr of
          Just ot -> ( Rel.setInsert n (funProfileToPredType pr) pm
                     , Rel.setInsert n ot om)
          Nothing -> (Rel.setInsert n (profileToPredType pr) pm, om))
  (Map.empty, Map.empty) $ Map.toList m

-- | resolve mixfix applications of terms and formulas
resolveDlformula :: MixResolve Dlformula
resolveDlformula ga rules (Ranged f r) = case f of
  Dlformula b p s -> do
    np <- resolveProg ga rules p
    n <- resolveMixFrm id resolveDlformula ga rules s
    return $ Ranged (Dlformula b np n) r
  Defprocs ps -> do
    nps <- mapM (resolveDefproc ga rules) ps
    return $ Ranged (Defprocs nps) r

resolveT :: MixResolve (TERM ())
resolveT = resolveMixTrm id (mixResolve emptyMix)

resolveF :: MixResolve (FORMULA ())
resolveF = resolveMixFrm id (mixResolve emptyMix)

resolveProg :: MixResolve Program
resolveProg ga rules p@(Ranged prg r) = case prg of
  Abort -> return p
  Skip -> return p
  Assign v t -> do
    nt <- resolveT ga rules t
    return $ Ranged (Assign v nt) r
  Call f -> do
    nf <- resolveF ga rules f
    return $ Ranged (Call nf) r
  Return t -> do
    nt <- resolveT ga rules t
    return $ Ranged (Return nt) r
  Block vs q -> do
    np <- resolveProg ga rules q
    return $ Ranged (Block vs np) r
  Seq p1 p2 -> do
    p3 <- resolveProg ga rules p1
    p4 <- resolveProg ga rules p2
    return $ Ranged (Seq p3 p4) r
  If f p1 p2 -> do
    c <- resolveF ga rules f
    p3 <- resolveProg ga rules p1
    p4 <- resolveProg ga rules p2
    return $ Ranged (If c p3 p4) r
  While f q -> do
    c <- resolveF ga rules f
    np <- resolveProg ga rules q
    return $ Ranged (While c np) r

resolveDefproc :: MixResolve Defproc
resolveDefproc ga rules (Defproc k i vs p r) = do
  np <- resolveProg ga rules p
  return $ Defproc k i vs np r

-- | resolve overloading and type check terms and formulas
minExpForm :: Min Dlformula Procs
minExpForm sign (Ranged f r) = let sig = castSign sign in case f of
  Dlformula b p s -> do
    np <- minExpProg Set.empty Nothing sig p
    n <- minExpFORMULA minExpForm sig s
    return $ Ranged (Dlformula b np n) r
  Defprocs ps -> do
    nps <- mapM (minProcdecl sig) ps
    return $ Ranged (Defprocs nps) r

oneExpT :: Sign () Procs -> TERM () -> Result (TERM ())
oneExpT = oneExpTerm (const return)

minExpF :: Sign () Procs -> FORMULA () -> Result (FORMULA ())
minExpF = minExpFORMULA (const return)

checkRec :: Record f Bool Bool
checkRec = (constRecord (const False) and True)
  { foldQuantification = \ _ _ _ _ _ -> False
  , foldDefinedness = \ _ _ _ -> False
  , foldExistl_equation = \ _ _ _ _ -> False
  , foldMembership = \ _ _ _ _ -> False
  , foldCast = \ _ _ _ _ -> False
  , foldConditional = \ _ _ _ _ _ -> False }

minExpProg :: Set.Set VAR -> Maybe SORT -> Sign () Procs
           -> Program -> Result Program
minExpProg invars res sig p@(Ranged prg r) = let
  checkCond f = if foldFormula checkRec f then return f else
                    mkError "illegal formula" f
  checkTerm t = if foldTerm checkRec t then return t else
                    mkError "illegal term" t
  in case prg of
  Abort -> return p
  Skip -> return p
  Assign v t -> case Map.lookup v $ varMap sig of
    Nothing -> Result [mkDiag Error "undeclared program variable" v] Nothing
    Just s -> do
      nt <- oneExpT sig $ Sorted_term t s r
      checkTerm nt
      if Set.member v invars then
         Result [mkDiag Warning "assignment to input variable" v] $ Just ()
         else return ()
      return $ Ranged (Assign v nt) r
  Call f -> case f of
    Predication ps ts _ -> let i = predSymbName ps in
      case lookupProc i sig of
        Nothing -> Result [mkDiag Error "unknown procedure" i] Nothing
        Just (Profile l re) -> let
          nl = case re of
             Nothing -> l
             Just s -> l ++ [Procparam Out s]
          in if length nl /= length ts then
          Result [mkDiag Error "non-matching number of parameters for" i]
          Nothing
             else do
          if length l < length nl then
            Result [mkDiag Warning "function used as procedure" i] $ Just ()
            else return ()
          nf <- minExpF sig f
          checkCond nf
          return $ Ranged (Call nf) r
    _ -> Result [mkDiag Error "no procedure call" f] Nothing
  Return t -> case res of
    Nothing -> Result [mkDiag Error "unexpected return statement" t] Nothing
    Just s -> do
      nt <- oneExpT sig $ Sorted_term t s r
      checkTerm nt
      return $ Ranged (Return nt) r
  Block vs q -> do
    let (_, sign') = runState (mapM_ addVars vs) sig { envDiags = [] }
    Result (envDiags sign') $ Just ()
    np <- minExpProg invars res sign' q
    return $ Ranged (Block vs np) r
  Seq p1 p2 -> do
    p3 <- minExpProg invars res sig p1
    p4 <- minExpProg invars res sig p2
    return $ Ranged (Seq p3 p4) r
  If f p1 p2 -> do
    c <- minExpF sig f
    checkCond c
    p3 <- minExpProg invars res sig p1
    p4 <- minExpProg invars res sig p2
    return $ Ranged (If c p3 p4) r
  While f q -> do
    c <- minExpF sig f
    checkCond c
    np <- minExpProg invars res sig q
    return $ Ranged (While c np) r

minProcdecl :: Sign () Procs -> Defproc -> Result Defproc
minProcdecl sig (Defproc k i vs p r) = case lookupProc i sig of
    Nothing -> Result [mkDiag Error "unknown procedure" i] Nothing
    Just (Profile l re) -> if length vs /= length l then
      Result [mkDiag Error "unknown procedure" i] Nothing
      else do
        let invars = Set.fromList $ map fst $
              filter (\ (_, Procparam j _) -> j == In) $ zip vs l
        np <- minExpProg invars re sig { varMap = Map.fromList $ zipWith
                (\ v (Procparam _ s) -> (v, s)) vs l } p
        return $ Defproc k i vs np r

-- | analyse and add procedure declarations
anaProcdecls :: Ana Procdecls () Procdecls Dlformula Procs
anaProcdecls _ ds@(Procdecls ps _) = do
  mapM_ (anaProcdecl . item) ps
  return ds

anaProcdecl :: Sigentry -> State (Sign Dlformula Procs) ()
anaProcdecl (Procedure i p@(Profile ps _) q) = do
     updateExtInfo (\ (Procs m) ->
       let n = Procs $ Map.insert i p m in case Map.lookup i m of
         Just o -> if p == o then
           hint n ("repeated procedure " ++ showId i "") q
           else warning n ("redeclared procedure " ++ showId i "") q
         Nothing -> return n)
     case profileToOpType p of
       Just t -> do
         if all (\ (Procparam j _) -> j == In) ps then return () else
            addDiags [mkDiag Warning "function must have IN params only" i]
         addOp (emptyAnno ()) t i
         e <- get
         put e { predMap = Rel.setInsert i (funProfileToPredType p)
                 $ predMap e }
       _ -> addPred (emptyAnno ()) (profileToPredType p) i

paramsToArgs :: [Procparam] -> [SORT]
paramsToArgs = map (\ (Procparam _ s) -> s)

profileToPredType :: Profile -> PredType
profileToPredType (Profile a _) = PredType $ paramsToArgs a

funProfileToPredType :: Profile -> PredType
funProfileToPredType (Profile a r) = case r of
  Nothing -> error "funProfileToPredType"
  Just s -> PredType $ paramsToArgs a ++ [s]

profileToOpType :: Profile -> Maybe OpType
profileToOpType (Profile a r) = case r of
  Nothing -> Nothing
  Just s -> Just $ OpType Partial (paramsToArgs a) s

castSign :: Sign f e -> Sign a e
castSign s = s { sentences = [] }

castMor :: Morphism f e b -> Morphism a e b
castMor m = m
  { msource = castSign $ msource m
  , mtarget = castSign $ mtarget m }

-- | apply a morphism
mapMorProg :: Morphism f Procs () -> Program -> Program
mapMorProg mor = let m = castMor mor in
  foldProg (mapProg (MapSen.mapTerm (const id) m)
    $ mapSen (const id) m)
    { foldBlock = \ (Ranged _ r) vs p ->
        Ranged (Block (map (mapVars m) vs) p) r
    , foldCall = \ (Ranged _ r) f ->
        Ranged (Call $ MapSen.mapSen (const id) m f) r }

mapProcId :: Morphism f Procs () -> Id -> Id
mapProcId m i = case lookupProc i $ msource m of
  Just p -> mapProcIdProfile m i p
  Nothing -> error $ "VSE.mapProcId unknown " ++ show i

mapProcIdProfile :: Morphism f Procs () -> Id -> Profile -> Id
mapProcIdProfile m i p = case profileToOpType p of
  Just t -> fst $ mapOpSym (sort_map m) (fun_map m) (i, t)
  Nothing -> fst $ mapPredSym (sort_map m) (pred_map m)
    (i, profileToPredType p)

mapMorDefproc :: Morphism f Procs () -> Defproc -> Defproc
mapMorDefproc m (Defproc k i vs p r) =
  Defproc k (mapProcId m i) vs (mapMorProg m p) r

mapDlformula :: MapSen Dlformula Procs ()
mapDlformula m (Ranged f r) = case f of
  Dlformula b p s ->
    let n = mapSen mapDlformula m s
    in Ranged (Dlformula b (mapMorProg m p) n) r
  Defprocs ps -> Ranged (Defprocs $ map (mapMorDefproc m) ps) r

-- | simplify fully qualified terms and formulas for pretty printing sentences
simpProg :: Sign () e -> Program -> Program
simpProg sig =
  foldProg (mapProg (simplifyTerm dummyMin (const id) sig)
  $ simplifySen dummyMin (const id) sig)
    { foldBlock = \ (Ranged (Block vs p) r) _ _ ->
                  Ranged (Block vs $ simpProg
                           (execState (mapM_ addVars vs) sig) p) r }

simpDefproc :: Sign () Procs -> Defproc -> Defproc
simpDefproc sign (Defproc k i vs p r) =
  let sig = case lookupProc i sign of
              Nothing -> sign
              Just (Profile l _) -> if length vs /= length l then sign
                else sign { varMap = Map.fromList $ zipWith
                            (\ v (Procparam _ s) -> (v, s)) vs l }
  in Defproc k i vs (simpProg sig p) r

simpDlformula :: Sign Dlformula Procs -> Dlformula -> Dlformula
simpDlformula sign (Ranged f r) = let sig = castSign sign in case f of
  Dlformula b p s -> let
    q = simpProg sig p
    n = simplifySen minExpForm simpDlformula sign s
    in Ranged (Dlformula b q n) r
  Defprocs ps -> Ranged (Defprocs $ map (simpDefproc sig) ps) r

-- | free variables to be universally bound on the top level
freeProgVars :: Sign () e -> Program -> VarSet
freeProgVars sig = foldProg FoldRec
  { foldAbort = const Set.empty
  , foldSkip = const Set.empty
  , foldAssign = \ _ v t -> (case Map.lookup v $ varMap sig of
      Just s -> Set.insert (v, s)
      Nothing -> Set.insert (v, sortOfTerm t)) $ freeTermVars sig t
  , foldCall = \ _ f -> freeVars sig f
  , foldReturn = \ _ t -> freeTermVars sig t
  , foldBlock = \ (Ranged (Block vs p) _) _ _ ->
      Set.difference (freeProgVars (execState (mapM_ addVars vs) sig) p)
        $ Set.fromList $ flatVAR_DECLs vs
  , foldSeq = \ _ p1 p2 -> Set.union p1 p2
  , foldIf = \ _ c p1 p2 -> Set.union (freeVars sig c)
             $ Set.union p1 p2
  , foldWhile = \ _ c p -> Set.union (freeVars sig c) p }

freeDlVars :: Sign Dlformula e -> Dlformula -> VarSet
freeDlVars sig (Ranged f _) = case f of
  Dlformula _ p s -> Set.union (freeProgVars (castSign sig) p) $
          freeVars sig s
  Defprocs _ -> Set.empty

instance GetRange (Ranged a) where
  getRange (Ranged _ r) = r

instance FreeVars Dlformula where
  freeVarsOfExt = freeDlVars

-- | adjust procs map in morphism target signature
correctTarget :: Morphism f Procs () -> Morphism f Procs ()
correctTarget m = let tar = mtarget m in m
  { mtarget = correctSign tar
    { extendedInfo = Procs $ Map.fromList
      $ map (\ (i, p) -> (mapProcIdProfile m i p, mapProfile (sort_map m) p))
      $ Map.toList $ procsMap $ extendedInfo tar }
  , msource = correctSign $ msource m }

correctSign :: Sign f Procs -> Sign f Procs
correctSign sig = sig
  { extendedInfo = Procs $ Map.filterWithKey (\ i p -> case profileToOpType p of
         Just t -> case Map.lookup i $ opMap sig of
           Just s -> Set.member t s || Set.member t { opKind = Total } s
           Nothing -> False
         Nothing -> case Map.lookup i $ predMap sig of
           Just s -> Set.member (profileToPredType p) s
           Nothing -> False) $ procsMap $ extendedInfo sig }

mapProfile ::  Sort_map -> Profile -> Profile
mapProfile m (Profile l r) = Profile
  (map (\ (Procparam k s) -> Procparam k $ mapSort m s) l)
  $ fmap (mapSort m) r
