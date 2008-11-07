{-# OPTIONS -cpp #-}
{- |
Module      :  $Header$
Description :  the logic graph
Copyright   :  (c)  Till Mossakowski and Uni Bremen 2003
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  till@informatik.uni-bremen.de
Stability   :  unstable
Portability :  non-portable

Assembles all the logics and comorphisms into a graph.
   The modules for the Grothendieck logic are logic graph indepdenent,
   and here is the logic graph that is used to instantiate these.
   Since the logic graph depends on a large number of modules for the
   individual logics, this separation of concerns (and possibility for
   separate compilation) is quite useful.

   Comorphisms are either logic inclusions, or normal comorphisms.
     The former are assembled in inclusionList, the latter in normalList.
     An inclusion is an institution comorphism with the following properties:

     * the signature translation is an embedding of categories

     * the sentence translations are injective

     * the model translations are isomorphisms

   References:

   The FLIRTS home page: <http://www.informatik.uni-bremen.de/flirts>

   T. Mossakowski:
   Relating CASL with Other Specification Languages:
        the Institution Level
   Theoretical Computer Science 286, p. 367-475, 2002.
-}

module Comorphisms.LogicGraph
    ( logicGraph
    , lookupComorphism_in_LG
    , comorphismList
    , inclusionList
    , lookupSquare_in_LG
    ) where

import Data.Maybe
import Data.List
import qualified Data.Map as Map

import Common.Result
import Logic.Logic
import Logic.Grothendieck
import Logic.Comorphism
import Logic.Modification
import Logic.Morphism
import Modifications.ModalEmbedding

import Comorphisms.CASL2PCFOL
import Comorphisms.CASL2SubCFOL
import Comorphisms.CASL2HasCASL
import Comorphisms.HasCASL2HasCASL
import Comorphisms.CFOL2IsabelleHOL
import Comorphisms.SuleCFOL2SoftFOL
import Comorphisms.Prop2CASL
import Comorphisms.HasCASL2IsabelleHOL
import Comorphisms.PCoClTyConsHOL2IsabelleHOL
import Comorphisms.PCoClTyConsHOL2PairsInIsaHOL
import Comorphisms.HasCASL2PCoClTyConsHOL
import Comorphisms.CASL2TopSort
#ifdef CASLEXTENSIONS
import Comorphisms.CoCFOL2IsabelleHOL
import Comorphisms.CoCASL2CoPCFOL
import Comorphisms.CoCASL2CoSubCFOL
import Comorphisms.CASL2Modal
import Comorphisms.Modal2CASL
import Comorphisms.CASL2CoCASL
import Comorphisms.CASL2CspCASL
import Comorphisms.CspCASL2Modal
import Comorphisms.CspCASL2IsabelleHOL
import Comorphisms.CASL_DL2CASL
import Comorphisms.DL2CASL_DL
import Comorphisms.RelScheme2CASL
import Comorphisms.CASL2VSERefine
import Comorphisms.CASL2VSEImport
#endif
#ifndef NOOWLLOGIC
import Comorphisms.OWL2CASL
import Comorphisms.OWL2DL
#endif

#ifdef PROGRAMATICA
import Comorphisms.HasCASL2Haskell
import Comorphisms.Haskell2IsabelleHOLCF
#endif
-- This needs to be seperated for utils/InlineAxioms/InlineAxioms.hs
import Comorphisms.LogicList

addComorphismName :: AnyComorphism -> (String, AnyComorphism)
addComorphismName c@(Comorphism cid) = (language_name cid, c)

addInclusionNames :: AnyComorphism -> ((String, String), AnyComorphism)
addInclusionNames c@(Comorphism cid) =
  ((language_name $ sourceLogic cid, language_name $ targetLogic cid), c)

addUnionNames :: (AnyComorphism, AnyComorphism)
              -> ((String, String), (AnyComorphism, AnyComorphism))
addUnionNames (c1@(Comorphism cid1), c2@(Comorphism cid2)) =
  ( (language_name $ sourceLogic cid1, language_name $ sourceLogic cid2)
  , (c1, c2))

addMorphismName :: AnyMorphism -> (String, AnyMorphism)
addMorphismName m@(Morphism cid) = (language_name cid, m)

addModificationName :: AnyModification -> (String,AnyModification)
addModificationName m@(Modification cid) = (language_name cid, m)

comorphismList :: [AnyComorphism]
comorphismList =
    [ Comorphism CASL2HasCASL
    , Comorphism CFOL2IsabelleHOL
    , Comorphism Prop2CASL
#ifdef CASLEXTENSIONS
    , Comorphism CASL2Modal
    , Comorphism Modal2CASL
    , Comorphism CASL2CoCASL
    , Comorphism CASL2CspCASL
    , Comorphism CspCASL2Modal
    , Comorphism CspCASL2IsabelleHOL
    , Comorphism CASL_DL2CASL
    , Comorphism CoCASL2CoPCFOL
    , Comorphism CoCASL2CoSubCFOL
    , Comorphism CoCFOL2IsabelleHOL
    , Comorphism DL2CASL_DL
    , Comorphism RelScheme2CASL
    , Comorphism CASL2VSEImport
    , Comorphism CASL2VSERefine
#endif
#ifndef NOOWLLOGIC
    , Comorphism OWL2CASL
    , Comorphism OWL2DL
#endif
#ifdef PROGRAMATICA
    , Comorphism HasCASL2Haskell
    , Comorphism Haskell2IsabelleHOLCF
    , Comorphism Haskell2IsabelleHOL
#endif
    , Comorphism PCoClTyConsHOL2IsabelleHOL
    , Comorphism PCoClTyConsHOL2PairsInIsaHOL
    , Comorphism HasCASL2IsabelleHOL
    , Comorphism SuleCFOL2SoftFOLInduction
    , Comorphism HasCASL2PCoClTyConsHOL
    , Comorphism HasCASL2HasCASL
    , Comorphism SuleCFOL2SoftFOL
    , Comorphism CASL2PCFOL
    , Comorphism $ CASL2SubCFOL True FormulaDependent -- unique bottoms
    , Comorphism $ CASL2SubCFOL False SubsortBottoms -- keep free types
    , Comorphism $ CASL2SubCFOL False NoMembershipOrCast -- keep free types
    , Comorphism CASL2TopSort ]

inclusionList :: [AnyComorphism]
inclusionList =
    filter (\ (Comorphism cid) -> isInclusionComorphism cid) comorphismList

addComps :: Map.Map (String, String) AnyComorphism
         -> Map.Map (String, String) AnyComorphism
addComps cm = Map.unions
   $ cm : map (\ ((l1, l2), c1) ->
         Map.foldWithKey (\ (l3, l4) c2 m -> if l3 == l2 then
              case compComorphism c1 c2 of
                Just c3 -> Map.insert (l1, l4) c3 m
                _ -> m
              else m) (Map.empty) cm) (Map.toList cm)

addCompsN :: Map.Map (String, String) AnyComorphism
          -> Map.Map (String, String) AnyComorphism
addCompsN m = let n = addComps m in
    if Map.keys m == Map.keys n then m else addCompsN n

{- | Unions of logics, represented as pairs of inclusions.
     Entries only necessary for non-trivial unions
     (a trivial union is a union of a sublogic with a superlogic).
-}
unionList :: [(AnyComorphism, AnyComorphism)]
unionList = []

morphismList :: [AnyMorphism]
morphismList = [] -- for now

modificationList :: [AnyModification]
modificationList = [Modification MODAL_EMBEDDING]

squareMap :: Map.Map (AnyComorphism, AnyComorphism) [Square]
squareMap = Map.empty --for now

logicGraph :: LogicGraph
logicGraph = emptyLogicGraph
    { logics = Map.fromList $ map addLogicName $ logicList
        ++ concatMap (\ (Comorphism cid) ->
             [Logic $ sourceLogic cid, Logic $ targetLogic cid])
           comorphismList
    , comorphisms = Map.fromList $ map addComorphismName comorphismList
    , inclusions = addCompsN $ Map.fromList
        $ map addInclusionNames inclusionList
    , unions = Map.fromList $ map addUnionNames unionList
    , morphisms = Map.fromList $ map addMorphismName morphismList
    , modifications = Map.fromList $ map addModificationName modificationList
    , squares = squareMap }

lookupSquare :: AnyComorphism -> AnyComorphism -> LogicGraph -> Result [Square]
lookupSquare com1 com2 lg = maybe (fail "lookupSquare") return $ do
                            sqL1 <- Map.lookup (com1, com2) $ squares lg
                            sqL2 <- Map.lookup (com2, com1) $ squares lg
                            return $ nub $ sqL1 ++ (map mirrorSquare sqL2)
 -- Here have to update to nub $ .. ++ ..
 -- after i write equality for AnyModifications (equality for Squares nyi)

lookupSquare_in_LG :: AnyComorphism -> AnyComorphism -> Result [Square]
lookupSquare_in_LG com1 com2 = lookupSquare com1 com2 logicGraph


lookupComorphism_in_LG :: String -> Result AnyComorphism
lookupComorphism_in_LG coname = lookupComorphism coname logicGraph
