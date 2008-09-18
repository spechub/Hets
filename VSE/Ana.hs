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

module VSE.Ana
  ( VSESign
  , uTrue
  , uFalse
  , aTrue
  , aFalse
  , uBoolean
  , constBoolType
  , boolSig
  , lookupProc
  , procsToOpMap
  , procsToPredMap
  , profileToOpType
  , profileToPredType
  , checkCases
  , basicAna
  , mapDlformula
  , minExpForm
  , simpDlformula
  , correctTarget
  , toSen
  ) where

import Data.Char (toLower)
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
import VSE.Fold

type VSESign = Sign Dlformula Procs

getVariables :: Sentence -> Set.Set Token
getVariables = foldFormula $ getVarsRec $ getVSEVars . unRanged

getVarsRec :: (f -> Set.Set Token) -> Record f (Set.Set Token) (Set.Set Token)
getVarsRec f =
  (constRecord f Set.unions Set.empty)
  { foldQuantification = \ _ _ vs r _ -> Set.union r
      $ Set.fromList $ map fst $ flatVAR_DECLs vs
  , foldQual_var = \ _ v _ _ -> Set.singleton v }

getVSEVars :: VSEforms -> Set.Set Token
getVSEVars vf = case vf of
  Dlformula _ p s -> Set.union (getProgVars p) $ getVariables s
  Defprocs l -> Set.unions $ map getDefprogVars l
  _ -> Set.empty -- no variables in a sort generation constraint

getProgVars :: Program -> Set.Set Token
getProgVars =
  let rec = getVarsRec $ const Set.empty
      getTermVars = foldTerm rec
      getCondVars = foldFormula rec
  in foldProg (progToSetRec getTermVars getCondVars)
  { foldAssign = \ _ v t -> Set.insert v $ getTermVars t
  , foldBlock = \ _ vs p -> Set.union p
      $ Set.fromList $ map fst $ flatVAR_DECLs vs }

getDefprogVars :: Defproc -> Set.Set Token
getDefprogVars (Defproc _ _ vs p _) = Set.union (getProgVars p)
  $ Set.fromList vs

tokenToLower :: Token -> Token
tokenToLower (Token s r) = Token (map toLower s) r

idToLower :: Id -> Id
idToLower (Id ts cs r) = Id (map tokenToLower ts) (map idToLower cs) r

hasMany :: Set.Set a -> Bool
hasMany s = Set.size s > 1

getCases :: String -> Set.Set Id -> [Diagnosis]
getCases msg =
  map (mkDiag Error ("overlapping " ++ msg ++ " identifiers") . Set.toList)
  . filter hasMany . Map.elems
  . Set.fold (\ i -> Rel.setInsert (idToLower i) i) Map.empty

getCaseDiags :: Sign f e -> [Diagnosis]
getCaseDiags sig =
  getCases "sort" (sortSet sig)
  ++ getCases "op or function" (Map.keysSet $ opMap sig)
  ++ getCases "pred or proc" (Map.keysSet $ predMap sig)

uBoolean :: Id
uBoolean = stringToId "Boolean"

uTrue :: Id
uTrue = stringToId "True"

uFalse :: Id
uFalse = stringToId "False"

tBoolean :: OP_TYPE
tBoolean = Op_type Total [] uBoolean nullRange

constBoolType :: OpType
constBoolType = toOpType tBoolean

qBoolean :: Id -> OP_SYMB
qBoolean c = Qual_op_name c tBoolean nullRange

qTrue :: OP_SYMB
qTrue = qBoolean uTrue

qFalse :: OP_SYMB
qFalse = qBoolean uFalse

mkConstAppl :: OP_SYMB -> TERM f
mkConstAppl o = Application o [] nullRange

aTrue :: TERM f
aTrue = mkConstAppl qTrue

aFalse :: TERM f
aFalse = mkConstAppl qFalse

uOpMap :: OpMap
uOpMap = Map.fromList $ map (\ c -> (c, Set.singleton constBoolType))
  [uFalse, uTrue]

boolSig :: Sign f Procs
boolSig = (emptySign emptyProcs)
  { sortSet = Set.singleton uBoolean
  , opMap = uOpMap }

lookupProc :: Id -> Sign f Procs -> Maybe Profile
lookupProc i sig = Map.lookup i $ procsMap $ extendedInfo sig

procsSign :: Sign f Procs -> Sign f Procs
procsSign sig = (emptySign emptyProcs)
 { predMap = procsToPredMap $ extendedInfo sig }

-- | add procs as predicate
addProcs :: Sign f Procs -> Sign f Procs
addProcs sig = addSig const sig $ procsSign sig

-- | remove procs as predicate
subProcs :: Sign f Procs -> Sign f Procs
subProcs sig = diffSig const sig $ procsSign sig

checkCases :: Sign f e -> [Named Sentence] -> [Diagnosis]
checkCases sig2 sens = getCaseDiags sig2 ++ concatMap
    (getCases "var" . Set.map simpleIdToId . getVariables . sentence) sens

basicAna
  :: (BASIC_SPEC () Procdecls Dlformula,
      Sign Dlformula Procs, GlobalAnnos)
  -> Result (BASIC_SPEC () Procdecls Dlformula,
             ExtSign (Sign Dlformula Procs) Symbol,
             [Named Sentence])
basicAna (bs, sig, ga) = do
  let sigIn = subProcs $ addSig const sig boolSig
  (bs2, ExtSign sig2 syms, sens) <-
    basicAnalysis minExpForm (const return) anaProcdecls anaMix
        (bs, sigIn, ga)
  appendDiags $ checkCases sig2 sens
  appendDiags $ map
    (\ i -> mkDiag Error "illegal predicate declaration for procedure" i)
    $ Map.keys $ interMapSet (diffMapSet (predMap sig2) $ predMap sigIn)
    $ procsToPredMap $ extendedInfo sig2
  let sig3 = diffSig const sig2 boolSig
  appendDiags $ map (\ i -> mkDiag Error "illegal overloading of" i)
    $ Set.toList $ Set.intersection (Map.keysSet $ opMap sig3)
    $ Map.keysSet uOpMap
  return (bs2, ExtSign (addProcs $ diffSig const sig2 boolSig) syms, sens)

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
  _ -> Ranged f r -- no mixfix formulas?

parenProg :: Program -> Program
parenProg = foldProg $ mapProg (Paren.mapTerm id) $ mapFormula id

parenDefproc :: Defproc -> Defproc
parenDefproc (Defproc k i vs p r) = Defproc k i vs (parenProg p) r

procsToPredMap :: Procs -> Map.Map Id (Set.Set PredType)
procsToPredMap (Procs m) =
  foldr (\ (n, pr@(Profile _ mr)) pm -> case mr of
          Nothing -> Rel.setInsert n (profileToPredType pr) pm
          Just _ -> pm) Map.empty $ Map.toList m

procsToOpMap :: Procs -> OpMap
procsToOpMap (Procs m) =
  foldr (\ (n, pr) om -> case profileToOpType pr of
          Just ot -> Rel.setInsert n ot om
          Nothing -> om) Map.empty $ Map.toList m

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
  _ -> return $ Ranged f r -- no mixfix?

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
    n <- minExpFORMULA minExpForm sign s
    return $ Ranged (Dlformula b np n) r
  Defprocs ps -> do
    nps <- mapM (minProcdecl sig) ps
    return $ Ranged (Defprocs nps) r
  _ -> fail "nyi for restricted constraints"

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
        Just pr@(Profile l re) -> let
          nl = case re of
             Nothing -> l
             Just s -> l ++ [Procparam Out s]
          in if length nl /= length ts then
          Result [mkDiag Error "non-matching number of parameters for" i]
          Nothing
             else do
          sign <- if length l < length nl then
            Result [mkDiag Warning "function used as procedure" i] $ Just
              sig { predMap = Rel.setInsert i (funProfileToPredType pr)
                    $ predMap sig }
            else return sig { predMap = Rel.setInsert i (profileToPredType pr)
                    $ predMap sig }
          nf <- minExpF sign f
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
anaProcdecl (Procedure i p@(Profile ps mr) q) = do
     e <- get
     let prM = predMap e
         l = Map.findWithDefault Set.empty i prM
         ea = emptyAnno ()
         isPred = case mr of
           Nothing -> Set.member (profileToPredType p) l
           _ -> False
     updateExtInfo (\ pm@(Procs m) ->
       let n = Procs $ Map.insert i p m in case Map.lookup i m of
         Just o -> if p == o then
           hint n ("repeated procedure " ++ showId i "") q
           else plain_error pm
             ("cannot change profile of procedure " ++ showId i "") q
         Nothing -> if isPred then plain_error pm
           ("cannot change predicate to procedure " ++ showId i "") q
           else return n)
     case profileToOpType p of
       Just t -> do
         if all (\ (Procparam j _) -> j == In) ps then return () else
            addDiags [mkDiag Warning "function must have IN params only" i]
         addOp ea t i
       _ -> if isPred then return () else
            addAnnoSet ea $ Symbol i $ PredAsItemType $ profileToPredType p

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
    , foldCall = \ (Ranged _ r) f -> case f of
     Predication (Qual_pred_name i (Pred_type args r1) r2) ts r3 ->
      case lookupProc i $ msource mor of
        Nothing -> error "mapMorProg"
        Just pr -> let
          j = mapProcIdProfile mor i pr
          nargs = map (mapSrt mor) args
          nts = map (MapSen.mapTerm (const id) m) ts
          in Ranged (Call $ Predication
                (Qual_pred_name j (Pred_type nargs r1) r2) nts r3) r
     _ -> error $ "mapMorProg " ++ show f }

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
  RestrictedConstraint constr restr flag ->
   Ranged
    (RestrictedConstraint
       (map (MapSen.mapConstr m) constr)
       (Map.fromList $ map (\(s,i) -> (sort_map m Map.! s, mapProcId m i)) $
        Map.toList restr)
    flag ) r

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
  RestrictedConstraint _ _ _  -> Ranged f r
    -- how should this be for restricted constraints?

-- | free variables to be universally bound on the top level
freeProgVars :: Sign () e -> Program -> VarSet
freeProgVars sig = let ft = freeTermVars sig in
  foldProg (progToSetRec ft (freeVars sig))
  { foldAssign = \ _ v t -> (case Map.lookup v $ varMap sig of
      Just s -> Set.insert (v, s)
      Nothing -> Set.insert (v, sortOfTerm t)) $ ft t
  , foldBlock = \ (Ranged (Block vs p) _) _ _ ->
      Set.difference (freeProgVars (execState (mapM_ addVars vs) sig) p)
        $ Set.fromList $ flatVAR_DECLs vs }

freeDlVars :: Sign Dlformula e -> Dlformula -> VarSet
freeDlVars sig (Ranged f _) = case f of
  Dlformula _ p s -> Set.union (freeProgVars (castSign sig) p) $
          freeVars sig s
  Defprocs _ -> Set.empty
  RestrictedConstraint _ _ _  -> Set.empty

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

mapProfile :: Sort_map -> Profile -> Profile
mapProfile m (Profile l r) = Profile
  (map (\ (Procparam k s) -> Procparam k $ mapSort m s) l)
  $ fmap (mapSort m) r

toSen :: CASLFORMULA -> Sentence
toSen = foldFormula $ mapRecord (error "CASL2VSEImport.mapSen")
