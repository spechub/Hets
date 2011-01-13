{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  $Header$
Description :  matching of terms modulo definition expansion
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  ewaryst.schulz@dfki.de
Stability   :  experimental
Portability :  non-portable (see extensions)

Matching of terms modulo constant definition expansion and constraints
-}

module HasCASL.MatchingWithDefinitions where

import HasCASL.Subst
import HasCASL.PrintSubst

import HasCASL.As
import HasCASL.Le
import HasCASL.PrintAs ()

import Common.Id
import Common.ConvertGlobalAnnos()
import Common.Doc
import Common.DocUtils

import qualified Data.Map as Map
import qualified Data.Set as Set

-- For candidate generation and DG navigation
import Data.List
import Data.Maybe

import Static.DGNavigation

import Logic.Grothendieck
import Logic.Coerce

import HasCASL.Logic_HasCASL

{- | We need two classes:

   1. A class for lookup definitions and checking for good functions

   2. A class for storing the match (substitution plus constraints)
-}

class DefStore a where
    isGood :: a -> Term -> Bool
    isMapable :: a -> (Id, TypeScheme) -> Bool
    getDefinition :: a -> (Id, TypeScheme) -> Maybe Term
    getEnv :: a -> Env
    logMsg :: a -> Doc -> IO ()

class Match a where
    addMatch :: a -> SubstConst -> Term -> a
    addConstraint :: a -> Term -> Term -> a


newtype DefinitionStore = DefinitionStore (Env, Set.Set Symbol)

initialDefStore :: Env -> Set.Set Symbol -> DefinitionStore
initialDefStore e syms = DefinitionStore (e, syms)

instance DefStore DefinitionStore where
    isGood _ _ = True
    isMapable (DefinitionStore (e, syms)) (opid, typ) =
        Set.member (idToOpSymbol e opid typ) syms
    getDefinition (DefinitionStore (e, _)) = getOpDefinition e
    getEnv (DefinitionStore (e, _)) = e
--    logMsg _ _ = return () 
    logMsg def d = let e = getEnv def
                   in appendFile "/tmp/matcher.out" $ (++"\n") $ show
                          $ useGlobalAnnos (globAnnos e) d
                               

newtype MatchResult = MatchResult (Subst, [(Term, Term)]) deriving Show

getMatchResult :: MatchResult -> (Subst, [(Term, Term)])
getMatchResult (MatchResult x) = x

emptyMatchResult :: MatchResult
emptyMatchResult = MatchResult (emptySubstitution, [])

instance PrettyInEnv MatchResult where
    prettyInEnv e (MatchResult (sb, ctrts)) =
        text "Match"
                 <> vcat [ text "result", prettyInEnv e sb
                         , text "Constraints", prettyTermMapping e ctrts ]


instance Match MatchResult where
    addMatch mr@(MatchResult (sb, ctrts)) sc t =
        case lookupContent sb sc of
             Just t' | t == t' -> mr
                     | otherwise ->
                         addConstraint mr t t'
             _ -> MatchResult (addTerm sb sc t, ctrts)

    addConstraint (MatchResult (sb, ctrts)) t1 t2 = MatchResult (sb, (t1, t2):ctrts)




{- | The rules of matching:

   f,g are functions
   c is a constant
   v is a variable
   t1, t2 are arbitrary terms
   "good" functions are the list-constructor, the solidworks datatype constructors and all other constructors.

   f != g

   1a. f(x_i) f(y_i) -> match x_i y_i,                  if f is a "good" function
                        AddConstraint f(x_i) = f(y_i),  otherwise

   1b. f(...) g(...) -> AddConstraint f(...) = g(...)

   2a. c t2 -> match t1 t2,           if c is defined by term t1
               AddMatch c t2,         if c is mapable
               AddConstraint c = t2,  otherwise

   2b. t1 c -> match t1 t2,           if c is defined by term t2
               AddConstraint t1 = c,  otherwise

   3. v t2 -> AddMatch v t2

-}
match :: (DefStore d, Match a) => d -> a -> Term -> Term -> IO (Either String a)
match def mtch t1 t2 =
    case (t1, t2) of
      -- handle the 'skip-cases' first
      (TypedTerm term _ _ _, _) -> match' term t2 -- logg "typed1" $ match' term t2
      (_, TypedTerm term _ _ _) -> match' t1 term -- logg "typed2" $ match' t1 term

      -- check for clash, handle constraints and definition expansion
      (ApplTerm f1 a1 _, _) ->
          case t2 of
            ApplTerm f2 a2 _
                -- 1a1.
                | f1 == f2 && isGood def f1 -> logg msg1a1 $ match' a1 a2
                -- 1a2., 1b.
                | otherwise -> logg msg1a21b addLocalConstraint

            -- eventually 2b.
            _ -> logg msg2b $ tryDefExpand2

      (TupleTerm l _, _) -> 
          case t2 of
            TupleTerm l' _ | length l == length l' ->
                               logg msg1aT $ matchfold mtch $ zip l l'
                           | otherwise ->
                               logg "tclash" $ tupleClash
            -- eventually 2b.
            _ -> logg msg2bT $ tryDefExpand2

      -- 3.: add the mapping v->t2 to output
      (QualVar v, _) -> logg "mapped" $ addMapping v
      -- 2a.: follow the definition of pattern
      (QualOp _ (PolyId opid _ _) typ _ _ _, _) ->
          logg msg2a $ tryDefExpand1 (opid, typ)

      -- all other terms are not expected and accepted here
      _ -> return $ Left "match: unhandled term"

      where match' = match def mtch
            -- The definition expansion application case
            -- (for ApplTerm and TupleTerm) is handled uniformly
            tryDefExpand1 oi = case getTermDef t1 of
                                 Just t1' -> match' t1' t2
                                 _ | isMapable def oi -> addMapping oi
                                   | otherwise -> addLocalConstraint

            tryDefExpand2 = case getTermDef t2 of
                             Just t2' -> match' t1 t2'
                             _ -> addLocalConstraint

            getTermDef t = getTermOp t >>= getDefinition def
            addLocalConstraint
                -- Do not add constraints for equal terms
                | t1 == t2 = return $ Right mtch
                | otherwise = return $ Right $ addConstraint mtch t1 t2
            addMapping t = return $ Right $ addMatch mtch (toSC t) t2
            matchfold mtch' (x:l) = do
                    res <- uncurry (match def mtch') x
                    case res of
                      Right mtch'' -> matchfold mtch'' l
                      err -> return $ err
            matchfold mtch' [] = return $ Right mtch'
            --clash = return $ Left $ "match: Clash for " ++ show (pretty (t1,t2))
            tupleClash = return $ Left $ "match: Clash for tuples "
                         ++ show (pretty (t1,t2))

            -- Logging stuff
            logg s a = do
                    let e = getEnv def
                    logMsg def $ text "Log" <+> text s
                               $++$ text "t1:" $+$ prettyInEnv e t1 $++$ text "t2:"
                               $+$ prettyInEnv e t2 $++$ text "==============="
                    a
            msg1a1 = "1a1: good same function"
            msg1a21b = "1a2, 1b: not good or not same function"
            msg1aT = "1aT: tuple: same tuple"
            msg2bT = "2bT:"
            msg2a = "2a: pattern constant"
            msg2b = "2b: term constant"


------------------------- term tools -------------------------

getTermOp :: Term -> Maybe (Id, TypeScheme)
getTermOp (QualOp _ (PolyId opid _ _) typ _ _ _) = Just (opid, typ)
getTermOp _ = Nothing

getOpInfo :: Env -> (Id, TypeScheme) -> Maybe OpInfo
getOpInfo e (opid, typ) =
    case Map.lookup opid (assumps e) of
      Just soi ->
          let fs = Set.filter f soi
          in if Set.null fs then Nothing
             else Just $ Set.findMin fs
      _ -> Nothing
    where
      f oi = opType oi == typ

getOpDefinition :: Env -> (Id, TypeScheme) -> Maybe Term
getOpDefinition e t =
    case fmap opDefn $ getOpInfo e t of
      Just (Definition _ t') -> Just t'
      _ -> Nothing


-- * Match Candidates

-- ** 1. Injections

newtype Injection a b = Injection [(a, b)]

instance (Show a, Show b) => Show (Injection a b) where
    show (Injection l) = "{" ++ intercalate ", " (map sf l) ++ "}"
        where sf (x, y) = show x ++ " --> " ++ show y

toList :: Injection a b -> [(a, b)]
toList (Injection l) = l

insertMapping :: (a, b) -> Injection a b -> Injection a b
insertMapping p (Injection l) = Injection (p:l)

combine :: Injection a b -> Injection a b -> Injection a b
combine (Injection l) (Injection l') = Injection (l++l')

singleton :: (a, b) -> Injection a b
singleton p = Injection [p]

-- Build all injections from source list to target list
injections :: [a] -> [b] -> [Injection a b]
injections l l'
    | length l > length l' = []
    | otherwise =
        case l of
          [] -> [Injection []]
          [x] ->  [ singleton (x, y) | y <- l' ]
          x:xl ->  f [] l'
              where
                f a (y:b) = f (y:a) b ++ 
                            (map (insertMapping (x,y)) $ injections xl $ a ++ b)
                f _ [] = []

crossInjs :: [[Injection a b]] -> [Injection a b]
crossInjs = crosscombine combine

-- Build all combinations from the list of lists
crosscombine :: (a -> a -> a) -> [[a]] -> [a]
crosscombine _ [] = []
crosscombine _ [x] = x
crosscombine f cl@(x:l) 
    | any null cl  = []
    | otherwise = [ f a b | a <- x, b <- crosscombine f l ]

-- ** 2. Candidates from operators

{- | Candidate generation
 a. For a symbol set make a map from Types to 'MatchOp'-lists: 'typePartition'

 b. From two such maps make a list of 'Injection's, each injection is a candidate
    (a list of 'MatchOp' pairs, wich will be matched using their definitions):
    'candidatesAux'
-}
type MatchOp = (Id, TypeScheme, Term)

instance PrettyInEnv MatchOp where
    prettyInEnv e (opid, typ, t) = pretty opid <> text ":" <+> pretty typ
                                   <+> text "=" <+> prettyInEnv e t

candType :: MatchOp -> TypeScheme
candType (_, typ, _) = typ

candTerm :: MatchOp -> Term
candTerm (_, _, t) = t

-- *** a.
typePartition :: ((Id, TypeScheme) -> Maybe Term) -- ^ Definiens extractor
              -> (TypeScheme -> Bool) -- ^ Filter predicate for types
              -> Set.Set Symbol -- ^ MatchOp symbol set
              -> Map.Map TypeScheme [MatchOp]
typePartition df tPred s =
    Map.fromListWith (++) $ mapMaybe g $ Set.toList s
        where f x = let typ = candType x
                    in if tPred typ then Just (typ, [x]) else Nothing
              g x = candFromSymbol df x >>= f

candFromSymbol :: ((Id, TypeScheme) -> Maybe Term) -- ^ Definiens extractor
             -> Symbol -> Maybe MatchOp
candFromSymbol df (Symbol {symName = opid, symType = OpAsItemType typ}) =
    fmap ((,,) opid typ) $ df (opid, typ)
candFromSymbol _ _ = Nothing

-- *** b.
candidatesAux :: Map.Map TypeScheme [MatchOp]
           -> Map.Map TypeScheme [MatchOp]
           -> [Injection MatchOp MatchOp]
candidatesAux patMap cMap = crossInjs $ Map.foldWithKey f [] patMap where
    f typ l injL = let l' = Map.findWithDefault err typ cMap
                       err = error $ "candidates: No concrete ops for type: "
                             ++ (show $ pretty typ)
                   in injections l l' : injL

candidates :: ((Id, TypeScheme) -> Maybe Term) -- ^ Definiens extractor
           -> (TypeScheme -> Bool) -- ^ Filter predicate for types
           -> Set.Set Symbol -> Set.Set Symbol -> [[(MatchOp, MatchOp)]]
candidates df tPred s1 s2 = map toList $ candidatesAux tp1 tp2
    where (tp1, tp2) = (typePartition df tPred s1, typePartition df tPred s2)

-- ** 3. Matching of candidates
matchCandidate :: (DefStore d) => d -> [(MatchOp, MatchOp)]
               -> IO (Either String MatchResult)
matchCandidate def = f emptyMatchResult where
    f mtch [] = return $ Right mtch
    f mtch ((pat, c):l) = do
      let e = getEnv def
      logMsg def $ text "Matching Candidate Pattern"
                 $+$ prettyInEnv e pat $+$ text " with" $+$ prettyInEnv e c
      res <- match def mtch (candTerm pat) $ candTerm c
      case res of
        Right mtch' -> f mtch' l
        x -> return x


matchCandidates :: (DefStore d) => d -> [[(MatchOp, MatchOp)]]
               -> IO (Either String MatchResult, [[(MatchOp, MatchOp)]])
matchCandidates _ [] = return (Left "matchCandidates: Out of candidates", [])
matchCandidates def (cand:l) = do
  res <- matchCandidate def cand
  case res of
    Left _ -> matchCandidates def l
    x -> return (x, l)


getCandidates :: (DefStore d, DevGraphNavigator nav) =>
                 d -> nav
                   -> (TypeScheme -> Bool) -- ^ Filter predicate for types
                   -> String -- ^ Name of pattern spec
                   -> String -- ^ Name of concrete spec
                   -> Maybe [[(MatchOp, MatchOp)]]
getCandidates def dgnav tFilter patN cN =
    let
        mGp = fromSearchResult (getNamedSpec patN) getLocalSyms dgnav
        mGc = fromSearchResult (getNamedSpec cN) getLocalSyms dgnav
        pSyms = Set.map gsymToSym $ fromJust mGp
        cSyms = Set.map gsymToSym $ fromJust mGc
        cands = candidates (getDefinition def) tFilter pSyms cSyms
    in if isJust mGp && isJust mGc then Just cands else Nothing


-- | Utility function for symbol conversion
gsymToSym :: G_symbol -> Symbol
gsymToSym (G_symbol lid sym) = coerceSymbol lid HasCASL sym

{- | The main matching function using specifications:

   The pattern specification is expected to be a parameterized specification
   containing the constants to be mapped in the actual parameter specification.
   
   The candidates for the matching stem from those operators which have a
   definition and a certain type satisfying the given type predicate.
   A typical such predicate is:

   '(flip elem ["typename1", "typename2", ...]) . show . pretty'

   Only operators with the same type can be matched, and all possible
   combinations of matching candidates are computed.
   With the given Number (> 0) you can constrain the number of candidates to
   try before giving up the matching (0 means all candidates).

   If one candidate gives a correct match result the following candidates are
   not tried and the 'MatchResult' is returned together with the list of non
   tried candidates.
-}
matchSpecs :: (DefStore d, DevGraphNavigator nav) =>
              d -> nav
                -> (TypeScheme -> Bool) -- ^ Filter predicate for types
                -> Int -- ^ Number of candidates to try
                -> String -- ^ Name of pattern spec
                -> String -- ^ Name of concrete spec
                -> IO (Either String MatchResult, [[(MatchOp, MatchOp)]])
matchSpecs def dgnav tFilter n patN cN =
    case getCandidates def dgnav tFilter patN cN of
      Nothing -> return (Left "matchSpecs: specs not found.", [])
      Just cl
          | null cl ->
              return (Left "matchSpecs: no candidates available.", [])
          | otherwise -> do
        let (cands, remC) = if n > 0 then splitAt n cl else (cl, [])
        (mr, l) <- matchCandidates def cands
        return (mr, l ++ remC)
