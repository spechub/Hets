{-# LANGUAGE ExistentialQuantification, DeriveDataTypeable
  , GeneralizedNewtypeDeriving #-}
{- |
Module      :  $Header$
Description :  theory datastructure for development graphs
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2006
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable(Logic)

theory datastructure for development graphs
-}

module Static.GTheory where

import Logic.Prover
import Logic.Logic
import Logic.ExtSign
import Logic.Grothendieck
import Logic.Comorphism
import Logic.Coerce

import qualified Common.OrderedMap as OMap

import ATerm.Lib
import Common.AnnoState (emptyAnnos)
import Common.Lib.Graph as Tree
import Common.Amalgamate -- for now
import Common.Keywords
import Common.AS_Annotation
import Common.Doc
import Common.DocUtils
import Common.ExtSign
import Common.GlobalAnnotations
import Common.Parsec
import Common.Result
import Common.Utils

import Data.Graph.Inductive.Graph as Graph

import Text.ParserCombinators.Parsec

import qualified Data.Map as Map
import qualified Data.Set as Set

import Data.Maybe
import Data.Typeable

import Control.Monad (foldM)
import Control.Exception

-- a theory index describing a set of sentences
newtype ThId = ThId Int
  deriving (Typeable, Show, Eq, Ord, Enum, ShATermConvertible)

startThId :: ThId
startThId = ThId 0

-- | Grothendieck theories with lookup indices
data G_theory = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree => G_theory
    { gTheoryLogic :: lid
    , gTheorySign :: ExtSign sign symbol
    , gTheorySignIdx :: SigId -- ^ index to lookup 'G_sign' (using 'signOf')
    , gTheorySens :: ThSens sentence (AnyComorphism, BasicProof)
    , gTheorySelfIdx :: ThId -- ^ index to lookup this 'G_theory' in theory map
    } deriving Typeable

createGThWith :: G_theory -> SigId -> ThId -> G_theory
createGThWith (G_theory gtl gts _ _ _) si = G_theory gtl gts si noSens

coerceThSens ::
   ( Logic lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
           sign1 morphism1 symbol1 raw_symbol1 proof_tree1
   , Logic lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
           sign2 morphism2 symbol2 raw_symbol2 proof_tree2
   , Monad m, Typeable b)
   => lid1 -> lid2 -> String -> ThSens sentence1 b -> m (ThSens sentence2 b)
coerceThSens = primCoerce

instance Eq G_theory where
  G_theory l1 sig1 ind1 sens1 ind1' == G_theory l2 sig2 ind2 sens2 ind2' =
     G_sign l1 sig1 ind1 == G_sign l2 sig2 ind2
     && (ind1' > startThId && ind2' > startThId && ind1' == ind2'
         || coerceThSens l1 l2 "" sens1 == Just sens2)

instance Show G_theory where
  show (G_theory _ sign _ sens _) =
     shows sign $ '\n' : show sens

instance Pretty G_theory where
  pretty g = prettyGTheorySL g $+$ prettyGTheory g

prettyGTheorySL :: G_theory -> Doc
prettyGTheorySL g = keyword logicS <+> structId (show $ sublogicOfTh g)

prettyGTheory :: G_theory -> Doc
prettyGTheory g = case simplifyTh g of
     G_theory lid sign@(ExtSign s _) _ sens _ -> let l = toNamedList sens in
         if null l && ext_is_subsig lid sign (ext_empty_signature lid) then
             specBraces Common.Doc.empty else
         print_sign lid s $++$ vsep (map (print_named lid) l)

-- | compute sublogic of a theory
sublogicOfTh :: G_theory -> G_sublogics
sublogicOfTh (G_theory lid (ExtSign sigma _) _ sens _) =
  let sub = foldl join
                  (minSublogic sigma)
                  (map snd $ OMap.toList $
                   OMap.map (minSublogic . sentence)
                       sens)
   in G_sublogics lid sub

-- | get theorem names with their best proof results
getThGoals :: G_theory -> [(String, Maybe BasicProof)]
getThGoals (G_theory _ _ _ sens _) = map toGoal . OMap.toList
    $ OMap.filter (not . isAxiom) sens
  where toGoal (n, st) = let ts = thmStatus st in
               (n, if null ts then Nothing else Just $ maximum $ map snd ts)

-- | get axiom names plus True for former theorem
getThAxioms :: G_theory -> [(String, Bool)]
getThAxioms (G_theory _ _ _ sens _) = map
    (\ (k, s) -> (k, wasTheorem s))
    $ OMap.toList $ OMap.filter isAxiom sens


-- | simplify a theory (throw away qualifications)
simplifyTh :: G_theory -> G_theory
simplifyTh (G_theory lid sigma@(ExtSign s _) ind1 sens ind2) =
    G_theory lid sigma ind1
      (OMap.map (mapValue $ simplify_sen lid s) sens) ind2

-- | apply a comorphism to a theory
mapG_theory :: AnyComorphism -> G_theory -> Result G_theory
mapG_theory (Comorphism cid) (G_theory lid (ExtSign sign _) ind1 sens ind2) =
  do
  bTh <- coerceBasicTheory lid (sourceLogic cid)
    ("unapplicable comorphism '" ++ language_name cid ++ "'\n")
    (sign, toNamedList sens)
  (sign', sens') <- wrapMapTheory cid bTh
  return $ G_theory (targetLogic cid) (mkExtSign sign')
         ind1 (toThSens sens') ind2

-- | Translation of a G_theory along a GMorphism
translateG_theory :: GMorphism -> G_theory -> Result G_theory
translateG_theory (GMorphism cid _ _ morphism2 _)
                      (G_theory lid (ExtSign sign _) _ sens _) = do
  let tlid = targetLogic cid
  bTh <- coerceBasicTheory lid (sourceLogic cid)
                    "translateG_theory" (sign, toNamedList sens)
  (_, sens'') <- wrapMapTheory cid bTh
  sens''' <- mapM (mapNamedM $ map_sen tlid morphism2) sens''
  return $ G_theory tlid (mkExtSign $ cod morphism2)
             startSigId (toThSens sens''') startThId

-- | Join the sentences of two G_theories
joinG_sentences :: Monad m => G_theory -> G_theory -> m G_theory
joinG_sentences (G_theory lid1 sig1 ind sens1 _)
                    (G_theory lid2 sig2 _ sens2 _) = do
  sens2' <- coerceThSens lid2 lid1 "joinG_sentences" sens2
  sig2' <- coerceSign lid2 lid1 "joinG_sentences" sig2
  return $ assert (plainSign sig1 == plainSign sig2')
             $ G_theory lid1 sig1 ind (joinSens sens1 sens2') startThId

-- | flattening the sentences form a list of G_theories
flatG_sentences :: Monad m => G_theory -> [G_theory] -> m G_theory
flatG_sentences = foldM joinG_sentences

-- | Get signature of a theory
signOf :: G_theory -> G_sign
signOf (G_theory lid sign ind _ _) = G_sign lid sign ind

-- | create theory without sentences
noSensGTheory :: Logic lid sublogics basic_spec sentence symb_items
    symb_map_items sign morphism symbol raw_symbol proof_tree
    => lid -> ExtSign sign symbol -> SigId -> G_theory
noSensGTheory lid sig si = G_theory lid sig si noSens startThId

data BasicProof =
  forall lid sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree =>
        BasicProof lid (ProofStatus proof_tree)
     | Guessed
     | Conjectured
     | Handwritten
     deriving Typeable

instance Eq BasicProof where
  Guessed == Guessed = True
  Conjectured == Conjectured = True
  Handwritten == Handwritten = True
  BasicProof lid1 p1 == BasicProof lid2 p2 =
    coerceProofStatus lid1 lid2 "Eq BasicProof" p1 == Just p2
  _ == _ = False

instance Ord BasicProof where
    Guessed <= _ = True
    Conjectured <= x = case x of
                       Guessed -> False
                       _ -> True
    Handwritten <= x = case x of
                       Guessed -> False
                       Conjectured -> False
                       _ -> True
    BasicProof lid1 pst1 <= x =
        case x of
        BasicProof lid2 pst2
            | isProvedStat pst1 && not (isProvedStat pst2) -> False
            | not (isProvedStat pst1) && isProvedStat pst2 -> True
            | otherwise -> case primCoerce lid1 lid2 "" pst1 of
                           Nothing -> False
                           Just pst1' -> pst1' <= pst2
        _ -> False

instance Show BasicProof where
  show (BasicProof _ p1) = show p1
  show Guessed = "Guessed"
  show Conjectured = "Conjectured"
  show Handwritten = "Handwritten"

-- | test a theory sentence
isProvenSenStatus :: SenStatus a (AnyComorphism, BasicProof) -> Bool
isProvenSenStatus = any (isProvedBasically . snd) . thmStatus

isProvedBasically :: BasicProof -> Bool
isProvedBasically b = case b of
  BasicProof _ pst -> isProvedStat pst
  _ -> False

getValidAxioms
  :: G_theory -- ^ old global theory
  -> G_theory -- ^ new global theory
  -> [String] -- ^ unchanged axioms
getValidAxioms
  (G_theory lid1 _ _ sens1 _)
  (G_theory lid2 _ _ sens2 _) =
  case coerceThSens lid1 lid2 "" sens1 of
    Nothing -> []
    Just sens -> OMap.keys $ OMap.filterWithKey (\ k s ->
      case OMap.lookup k sens of
        Just s2 -> isAxiom s && isAxiom s2 && sentence s == sentence s2
        _ -> False) sens2

invalidateProofs
  :: G_theory -- ^ old global theory
  -> G_theory -- ^ new global theory
  -> G_theory -- ^ local theory with proven goals
  -> G_theory -- ^ new local theory with deleted proofs
invalidateProofs oTh nTh (G_theory lid sig si sens _) =
  let vAxs = getValidAxioms oTh nTh
      validProofs (_, bp) = case bp of
        BasicProof _ pst -> all (`elem` vAxs) $ usedAxioms pst
        _ -> True
      newSens = OMap.map
        (\ s -> if isAxiom s then s else
             s { senAttr = ThmStatus $ filter validProofs
                   $ thmStatus s }) sens
  in G_theory lid sig si newSens startThId

{- | mark sentences as proven if an identical axiom or other proven sentence
     is part of the same theory. -}
proveSens :: Logic lid sublogics basic_spec sentence symb_items
    symb_map_items sign morphism symbol raw_symbol proof_tree
    => lid -> ThSens sentence (AnyComorphism, BasicProof)
           -> ThSens sentence (AnyComorphism, BasicProof)
proveSens lid sens = let
  (axs, ths) = OMap.partition (\ s -> isAxiom s || isProvenSenStatus s) sens
  in Map.union axs $ proveSensAux lid axs ths

proveLocalSens :: G_theory -> G_theory -> G_theory
proveLocalSens (G_theory glid _ _ gsens _) lth@(G_theory lid sig ind sens _) =
  case coerceThSens glid lid "proveLocalSens" gsens of
    Just lsens -> G_theory lid sig ind
      (proveSensAux lid (OMap.filter (\ s -> isAxiom s || isProvenSenStatus s)
       lsens) sens) startThId
    Nothing -> lth

{- | mark sentences as proven if an identical axiom or other proven sentence
     is part of a given global theory. -}
proveSensAux :: Logic lid sublogics basic_spec sentence symb_items
    symb_map_items sign morphism symbol raw_symbol proof_tree
    => lid -> ThSens sentence (AnyComorphism, BasicProof)
           -> ThSens sentence (AnyComorphism, BasicProof)
           -> ThSens sentence (AnyComorphism, BasicProof)
proveSensAux lid axs ths = let
  axSet = Map.fromList $ map (\ (n, s) -> (sentence s, n)) $ OMap.toList axs
  in Map.mapWithKey (\ i e -> let sen = OMap.ele e in
         case Map.lookup (sentence sen) axSet of
           Just ax ->
             e { OMap.ele = sen { senAttr = ThmStatus $
                   ( Comorphism $ mkIdComorphism lid $ top_sublogic lid
                   , BasicProof lid
                     (openProofStatus i "hets" $ empty_proof_tree lid)
                     { usedAxioms = [ax]
                     , goalStatus = Proved True }) : thmStatus sen } }
           _ -> e) ths

{- | mark all sentences of a local theory that have been proven via a prover
over a global theory (with the same signature) as proven.  Also mark
duplicates of proven sentences as proven.  Assume that the sentence names of
the local theory are identical to the global theory. -}
propagateProofs :: G_theory -> G_theory -> G_theory
propagateProofs locTh@(G_theory lid1 sig ind lsens _)
  (G_theory lid2 _ _ gsens _) =
  case coerceThSens lid2 lid1 "" gsens of
    Just ps ->
      if Map.null ps then locTh else
          G_theory lid1 sig ind
            (proveSens lid1 $ Map.union (Map.intersection ps lsens) lsens)
            startThId
    Nothing -> error "propagateProofs"

-- | Grothendieck diagrams
type GDiagram = Gr G_theory (Int, GMorphism)

-- | checks whether a connected GDiagram is homogeneous

isHomogeneousGDiagram :: GDiagram -> Bool
isHomogeneousGDiagram = all (\ (_, _, (_, phi)) -> isHomogeneous phi) . labEdges

-- | homogenise a GDiagram to a targeted logic

homogeniseGDiagram :: Logic lid sublogics
                           basic_spec sentence symb_items symb_map_items
                           sign morphism symbol raw_symbol proof_tree
                  => lid     -- ^ the target logic to be coerced to
                  -> GDiagram    -- ^ the GDiagram to be homogenised
                  -> Result (Gr sign (Int, morphism))

homogeniseGDiagram targetLid diag = do
  let convertNode (n, gth) = do
       G_sign srcLid extSig _ <- return $ signOf gth
       extSig' <- coerceSign srcLid targetLid "" extSig
       return (n, plainSign extSig')
      convertEdge (n1, n2, (nr, GMorphism cid _ _ mor _ ))
        = if isIdComorphism (Comorphism cid) then
            do mor' <- coerceMorphism (targetLogic cid) targetLid "" mor
               return (n1, n2, (nr, mor'))
          else fail $
               "Trying to coerce a morphism between different logics.\n" ++
               "Heterogeneous specifications are not fully supported yet."
      convertNodes cDiag [] = return cDiag
      convertNodes cDiag (lNode : lNodes) = do
                  convNode <- convertNode lNode
                  let cDiag' = insNode convNode cDiag
                  convertNodes cDiag' lNodes
      convertEdges cDiag [] = return cDiag
      convertEdges cDiag (lEdge : lEdges) = do
                  convEdge <- convertEdge lEdge
                  let cDiag' = insEdge convEdge cDiag
                  convertEdges cDiag' lEdges
      dNodes = labNodes diag
      dEdges = labEdges diag
       -- insert converted nodes to an empty diagram
  cDiag <- convertNodes Graph.empty dNodes
       -- insert converted edges to the diagram containing only nodes
  convertEdges cDiag dEdges

{- | Coerce GMorphisms in the list of (diagram node, GMorphism) pairs
to morphisms in given logic -}
homogeniseSink :: Logic lid sublogics
                         basic_spec sentence symb_items symb_map_items
                         sign morphism symbol raw_symbol proof_tree
                => lid -- ^ the target logic to which morphisms will be coerced
                -> [(Node, GMorphism)] -- ^ the list of edges to be homogenised
                -> Result [(Node, morphism)]
homogeniseSink targetLid dEdges =
     -- See homogeniseDiagram for comments on implementation.
       let convertMorphism (n, GMorphism cid _ _ mor _) =
               if isIdComorphism (Comorphism cid) then
                  do mor' <- coerceMorphism (targetLogic cid) targetLid "" mor
                     return (n, mor')
               else fail $
               "Trying to coerce a morphism between different logics.\n" ++
                "Heterogeneous specifications are not fully supported yet."
           convEdges [] = return []
           convEdges (e : es) = do
             ce <- convertMorphism e
             ces <- convEdges es
             return (ce : ces)
       in convEdges dEdges


{- amalgamabilty check for heterogeneous diagrams
currently only checks whether the diagram is
homogeneous and if so, calls amalgamability check
for the specific logic -}

gEnsuresAmalgamability :: [CASLAmalgOpt] -- the options
                       -> GDiagram -- the diagram
                       -> [(Int, GMorphism)] -- the sink
                       -> Result Amalgamates
gEnsuresAmalgamability options gd sink =
  if isHomogeneousGDiagram gd && all (isHomogeneous . snd) sink then
      case labNodes gd of
       (_, G_theory lid _ _ _ _) : _ -> do
          diag <- homogeniseGDiagram lid gd
          sink' <- homogeniseSink lid sink
          ensures_amalgamability lid (options, diag, sink', Graph.empty)
       _ -> error "heterogeneous amalgability check: no nodes"
    else error "heterogeneous amalgability check not yet implemented"

data BasicExtResponse = Failure Bool  -- True means fatal (give up)
  | Success G_theory Int (Set.Set G_symbol) Bool

extendByBasicSpec :: String -> G_theory -> (BasicExtResponse, String)
extendByBasicSpec str gt@(G_theory lid eSig@(ExtSign sign syms) si sens _) =
  let tstr = trimLeft str in
  if null tstr then (Success gt 0 Set.empty True, "") else
  case parse_basic_spec lid of
    Nothing -> (Failure True, "missing basic spec parser")
    Just p -> case basic_analysis lid of
      Nothing -> (Failure True, "missing basic analysis")
      Just f -> case runParser (p << eof) (emptyAnnos ()) "" tstr of
        Left err -> (Failure False, show err)
        Right bs -> let
          Result ds res = f (bs, sign, emptyGlobalAnnos)
          in case res of
            Nothing -> (Failure False, showRelDiags 1 ds)
            Just (_, ExtSign sign2 syms2, sens2) ->
              let Result es mm = inclusion lid sign2 sign
                  sameSig = isJust mm
                  finExtSign = ExtSign sign2 $ Set.union syms syms2
              in
              (Success (G_theory lid (if sameSig then eSig else finExtSign)
                      (if sameSig then si else startSigId)
                      (joinSens (toThSens sens2) sens) startThId)
                      (length sens2)
                      (Set.map (G_symbol lid) $ Set.difference syms2 syms)
                      sameSig
              , if sameSig then if null sens2 then "" else
                            show (vcat $ map (print_named lid) sens2)
                       else showRelDiags 1 es)
