{- |
Module      :  $Header$
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

import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.ExtSign
import Common.Id
import Common.Result
import Common.Lib.State

import CASL.AS_Basic_CASL
import CASL.Sign
import CASL.MixfixParser
import CASL.MapSentence as MapSen
import CASL.Morphism
import CASL.Overload
import CASL.StaticAna
import CASL.ShowMixfix as Paren
import CASL.SimplifySen

import VSE.As

type Procs = Map.Map Id Profile

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
  { getExtIds = \ e -> (Map.keysSet $ Map.filter
                        (\ (Profile _ m) -> isJust m) e, Set.empty)
  , putParen = parenDlFormula
  , mixResolve = resolveDlformula }

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
  , foldCall = \ (Ranged _ r) i ts -> Ranged (Call i $ map mt ts) r
  , foldReturn = \ (Ranged _ r) t -> Ranged (Return $ mt t) r
  , foldIf = \ (Ranged _ r) c p1 p2 -> Ranged (If (mf c) p1 p2) r
  , foldWhile = \ (Ranged _ r) c p -> Ranged (While (mf c) p) r }

parenProg :: Program -> Program
parenProg = foldProg $ mapProg (Paren.mapTerm id) $ mapFormula id

parenDefproc :: Defproc -> Defproc
parenDefproc (Defproc k i vs p r) = Defproc k i vs (parenProg p) r

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
  Call i ts -> do
    nts <- mapM (resolveT ga rules) ts
    return $ Ranged (Call i nts) r
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

minExpForm :: Min Dlformula Procs
minExpForm sign (Ranged f r) = let sig = castSign sign in case f of
  Dlformula b p s -> do
    np <- minExpProg Nothing sig p
    n <- minExpFORMULA minExpForm sig s
    return $ Ranged (Dlformula b np n) r
  Defprocs ps -> do
    nps <- mapM (minProcdecl sig) ps
    return $ Ranged (Defprocs nps) r

oneExpT :: Sign () Procs -> TERM () -> Result (TERM ())
oneExpT = oneExpTerm (const return)

minExpF :: Sign () Procs -> FORMULA () -> Result (FORMULA ())
minExpF = minExpFORMULA (const return)

minExpProg :: Maybe SORT -> Sign () Procs -> Program -> Result Program
minExpProg res sig p@(Ranged prg r) = case prg of
  Abort -> return p
  Skip -> return p
  Assign v t -> case Map.lookup v $ varMap sig of
    Nothing -> Result [mkDiag Error "undeclared program variable" v] Nothing
    Just s -> do
      nt <- oneExpT sig $ Sorted_term t s r
      return $ Ranged (Assign v nt) r
  Call i ts -> case Map.lookup i $ extendedInfo sig of
    Nothing -> Result [mkDiag Error "unknown procedure" i] Nothing
    Just (Profile l re) ->
      let nl = case re of
             Nothing -> l
             Just s -> l ++ [Procparam Out s]
      in if length nl /= length ts then
        Result [mkDiag Error "non-matching number of parameters for" i]
        Nothing
      else do
        if length l < length nl then
          Result [mkDiag Warning "function used as procedure" i] $ Just ()
          else return ()
        nts <- mapM (oneExpT sig)
          $ zipWith (\ t (Procparam _ s) -> Sorted_term t s r) ts nl
        return $ Ranged (Call i nts) r
  Return t -> case res of
    Nothing -> Result [mkDiag Error "unexpected return statement" t] Nothing
    Just s -> do
      nt <- oneExpT sig $ Sorted_term t s r
      return $ Ranged (Return nt) r
  Block vs q -> do
    let (_, sign') = runState (mapM_ addVars vs) sig { envDiags = [] }
    Result (envDiags sign') $ Just ()
    np <- minExpProg res sign' q
    return $ Ranged (Block vs np) r
  Seq p1 p2 -> do
    p3 <- minExpProg res sig p1
    p4 <- minExpProg res sig p2
    return $ Ranged (Seq p3 p4) r
  If f p1 p2 -> do
    c <- minExpF sig f
    p3 <- minExpProg res sig p1
    p4 <- minExpProg res sig p2
    return $ Ranged (If c p3 p4) r
  While f q -> do
    c <- minExpF sig f
    np <- minExpProg res sig q
    return $ Ranged (While c np) r

minProcdecl :: Sign () Procs -> Defproc -> Result Defproc
minProcdecl sig (Defproc k i vs p r) = case Map.lookup i $ extendedInfo sig of
    Nothing -> Result [mkDiag Error "unknown procedure" i] Nothing
    Just (Profile l re) -> if length vs /= length l then
      Result [mkDiag Error "unknown procedure" i] Nothing
      else do
        np <- minExpProg re sig { varMap = Map.fromList $ zipWith
                (\ v (Procparam _ s) -> (v, s)) vs l } p
        return $ Defproc k i vs np r

anaProcdecls :: Ana Procdecls () Procdecls Dlformula Procs
anaProcdecls _ ds@(Procdecls ps _) = do
  mapM_ (anaProcdecl . item) ps
  return ds

anaProcdecl :: Sigentry -> State (Sign Dlformula Procs) ()
anaProcdecl (Procedure i p q) = do
     updateExtInfo (\ m ->
       let n = Map.insert i p m in case Map.lookup i m of
         Just o -> if p == o then
           hint n ("repeated procedure " ++ showId i "") q
           else warning n ("redeclared procedure " ++ showId i "") q
         Nothing -> return n)
     case profileToOpType p of
       Just t -> addOp (emptyAnno ()) t i
       _ -> return ()

profileToOpType :: Profile -> Maybe OpType
profileToOpType (Profile a r) = case r of
  Nothing -> Nothing
  Just s -> Just $ OpType Partial (map (\ (Procparam In t) -> t) a) s

castSign :: Sign f e -> Sign a e
castSign s = s { sentences = [] }

castMor :: Morphism f e b -> Morphism a e b
castMor m = m
  { msource = castSign $ msource m
  , mtarget = castSign $ mtarget m }

mapMorProg :: Morphism f e () -> Program -> Program
mapMorProg m = foldProg $ mapProg (MapSen.mapTerm (const id) $ castMor m)
  $ mapSen (const id) $ castMor m

mapMorDefproc :: Morphism f e () -> Defproc -> Defproc
mapMorDefproc m (Defproc k i vs p r) = Defproc k i vs (mapMorProg m p) r

mapDlformula :: MapSen Dlformula Procs ()
mapDlformula m (Ranged f r) = case f of
  Dlformula b p s ->
    let n = mapSen mapDlformula m s
    in Ranged (Dlformula b (mapMorProg m p) n) r
  Defprocs ps -> Ranged (Defprocs $ map (mapMorDefproc m) ps) r

simpProg :: Sign () e -> Program -> Program
simpProg sig =
  foldProg (mapProg (simplifyTerm dummyMin (const id) sig)
  $ simplifySen dummyMin (const id) sig)
    { foldBlock = \ (Ranged (Block vs p) r) _ _ ->
                  Ranged (Block vs $ simpProg
                           (execState (mapM_ addVars vs) sig) p) r }

simpDefproc :: Sign () Procs -> Defproc -> Defproc
simpDefproc sign (Defproc k i vs p r) =
  let sig = case Map.lookup i $ extendedInfo sign of
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
