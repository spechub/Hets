{-# LANGUAGE CPP #-}
{- |
Module      :  ./Comorphisms/LogicGraph.hs
Description :  the logic graph
Copyright   :  (c)  Till Mossakowski and Uni Bremen 2003
License     :  GPLv2 or higher, see LICENSE.txt

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
    , lookupQTA_in_LG
    ) where

import qualified Data.Map as Map

import Common.Result
import Logic.Logic
import Logic.Grothendieck
import Logic.Comorphism
import Logic.Modification
import Logic.Morphism
import Modifications.ModalEmbedding

import Comorphisms.THFP2THF0
import Comorphisms.THFP_P2THFP
import Comorphisms.THFP_P2HasCASL
import Comorphisms.HasCASL2THFP_P
import Comorphisms.CASL2PCFOL
import Comorphisms.CASL2SubCFOL
import Comorphisms.CASL2HasCASL
import Comorphisms.HasCASL2HasCASL
import Comorphisms.CFOL2IsabelleHOL
import Comorphisms.CommonLogic2IsabelleHOL
import Comorphisms.HolLight2Isabelle
import Comorphisms.SuleCFOL2SoftFOL
import Comorphisms.SuleCFOL2TPTP
import Comorphisms.Prop2CASL
import Comorphisms.CASL2Prop
import Comorphisms.HasCASL2IsabelleHOL
import Comorphisms.PCoClTyConsHOL2IsabelleHOL
import Comorphisms.MonadicHasCASLTranslation
import Comorphisms.PCoClTyConsHOL2PairsInIsaHOL
import Comorphisms.HasCASL2PCoClTyConsHOL
import Comorphisms.CASL2TopSort
import Comorphisms.DFOL2CASL
import Comorphisms.QBF2Prop
import Comorphisms.Prop2QBF
import Comorphisms.CSMOF2CASL
import Comorphisms.QVTR2CASL

import Comorphisms.CASL2Hybrid
import Comorphisms.Hybrid2CASL


#ifdef CASLEXTENSIONS
import Comorphisms.CoCFOL2IsabelleHOL
import Comorphisms.CoCASL2CoPCFOL
import Comorphisms.CoCASL2CoSubCFOL
import Comorphisms.CASL2Modal
import Comorphisms.CASL2ExtModal
import Comorphisms.Modal2CASL
import Comorphisms.ExtModal2CASL
import Comorphisms.ExtModal2ExtModalNoSubsorts
import Comorphisms.ExtModal2ExtModalTotal
import Comorphisms.ExtModal2HasCASL
import Comorphisms.CASL2CoCASL
import Comorphisms.CASL2CspCASL
import Comorphisms.CspCASL2Modal
import CspCASL.Comorphisms
import Comorphisms.CASL_DL2CASL
import Comorphisms.RelScheme2CASL
import Comorphisms.CASL2Skolem
import Comorphisms.CASL2Prenex
import Comorphisms.CASL2NNF
import Comorphisms.CASL2VSE
import Comorphisms.CASL2VSERefine
import Comorphisms.CASL2VSEImport
import Comorphisms.Maude2CASL
import Comorphisms.CommonLogic2CASL
import CommonLogic.Sublogic
import Comorphisms.CommonLogicModuleElimination
import Comorphisms.Prop2CommonLogic
import Comorphisms.SoftFOL2CommonLogic
import Comorphisms.Adl2CASL
#endif
#ifndef NOOWLLOGIC
import OWL2.DMU2OWL2
import OWL2.OWL22CASL
import OWL2.CASL2OWL
import OWL2.OWL22CommonLogic
import OWL2.Propositional2OWL2
#ifdef CASLEXTENSIONS
import Comorphisms.ExtModal2OWL
#endif
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

addModificationName :: AnyModification -> (String, AnyModification)
addModificationName m@(Modification cid) = (language_name cid, m)

comorphismList :: [AnyComorphism]
comorphismList =
    [ Comorphism CASL2HasCASL
    , Comorphism CFOL2IsabelleHOL
    , Comorphism CommonLogic2IsabelleHOL
    , Comorphism HolLight2Isabelle
    , Comorphism Prop2CASL
    , Comorphism CASL2Prop
    , Comorphism DFOL2CASL
    , Comorphism HasCASL2THFP_P
    , Comorphism THFP2THF0
    , Comorphism THFP_P2HasCASL
    , Comorphism THFP_P2THFP
    , Comorphism CASL2Hybrid
    , Comorphism Hybrid2CASL
#ifdef CASLEXTENSIONS
    , Comorphism CASL2Modal
    , Comorphism CASL2ExtModal
    , Comorphism Modal2CASL
    , Comorphism ExtModal2CASL
    , Comorphism ExtModal2ExtModalNoSubsorts
    , Comorphism ExtModal2ExtModalTotal
    , Comorphism ExtModal2HasCASL
    , Comorphism CASL2CoCASL
    , Comorphism CASL2CspCASL
    , Comorphism CspCASL2Modal
    , Comorphism cspCASLTrace
    , Comorphism cspCASLFailure
    , Comorphism CASL_DL2CASL
    , Comorphism CoCASL2CoPCFOL
    , Comorphism CoCASL2CoSubCFOL
    , Comorphism CoCFOL2IsabelleHOL
    , Comorphism RelScheme2CASL
    , Comorphism CASL2VSE
    , Comorphism CASL2VSEImport
    , Comorphism CASL2VSERefine
    , Comorphism CASL2Skolem
    , Comorphism CASL2NNF
    , Comorphism CASL2Prenex
    , Comorphism Maude2CASL
    , Comorphism (CL2CFOL folsl {compact = False})
    , Comorphism (CL2CFOL fullclsl)
    , Comorphism (CL2CFOL folsl)
    , Comorphism (CL2CFOL fullclsl {compact = True})
    , Comorphism CommonLogicModuleElimination
    , Comorphism Prop2CommonLogic
    , Comorphism SoftFOL2CommonLogic
    , Comorphism Adl2CASL
#endif
#ifndef NOOWLLOGIC
    , Comorphism OWL22CASL
    , Comorphism OWL22CommonLogic
    , Comorphism DMU2OWL2
    , Comorphism CASL2OWL
    , Comorphism Propositional2OWL2
#ifdef CASLEXTENSIONS
    , Comorphism ExtModal2OWL
#endif
#endif
#ifdef PROGRAMATICA
    , Comorphism HasCASL2Haskell
    , Comorphism Haskell2IsabelleHOLCF
    , Comorphism Haskell2IsabelleHOL
#endif
    , Comorphism PCoClTyConsHOL2IsabelleHOL
    , Comorphism MonadicHasCASL2IsabelleHOL
    , Comorphism PCoClTyConsHOL2PairsInIsaHOL
    , Comorphism HasCASL2IsabelleHOL
    , Comorphism suleCFOL2SoftFOLInduction
    , Comorphism suleCFOL2SoftFOLInduction2
    , Comorphism HasCASL2PCoClTyConsHOL
    , Comorphism HasCASL2HasCASL
    , Comorphism suleCFOL2SoftFOL
    , Comorphism suleCFOL2TPTP
    , Comorphism CASL2PCFOL
    , Comorphism $ CASL2SubCFOL True FormulaDependent -- unique bottoms
    , Comorphism $ CASL2SubCFOL False SubsortBottoms -- keep free types
    , Comorphism $ CASL2SubCFOL False NoMembershipOrCast -- keep free types
    , Comorphism CASL2TopSort
    , Comorphism QBF2Prop
    , Comorphism Prop2QBF
    , Comorphism CSMOF2CASL
    , Comorphism QVTR2CASL ]

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
              else m) Map.empty cm) (Map.toList cm)

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
squareMap = Map.empty -- for now

logicGraph :: LogicGraph
logicGraph = emptyLogicGraph
    { logics = Map.fromList $ map addLogicName (logicList
        ++ concatMap (\ (Comorphism cid) ->
             [Logic $ sourceLogic cid, Logic $ targetLogic cid])
           comorphismList)
    , comorphisms = Map.fromList $ map addComorphismName comorphismList
    , inclusions = addCompsN $ Map.fromList
        $ map addInclusionNames inclusionList
    , unions = Map.fromList $ map addUnionNames unionList
    , morphisms = Map.fromList $ map addMorphismName morphismList
    , modifications = Map.fromList $ map addModificationName modificationList
    , squares = squareMap
    , qTATranslations =
       Map.fromList $ map (\ x@(Comorphism c) -> (show (sourceLogic c), x))
                       qtaList}

lookupSquare_in_LG :: AnyComorphism -> AnyComorphism -> Result [Square]
lookupSquare_in_LG com1 com2 = lookupSquare com1 com2 logicGraph

lookupComorphism_in_LG :: String -> Result AnyComorphism
lookupComorphism_in_LG coname = lookupComorphism coname logicGraph

-- translations to logics with quotient term algebra implemented
qtaList :: [AnyComorphism]
qtaList = [
#ifdef CASLEXTENSIONS
  Comorphism Maude2CASL
#endif
  ]

lookupQTA_in_LG :: String -> Result AnyComorphism
lookupQTA_in_LG coname =
 let
   qta = qTATranslations logicGraph
 in if coname `elem` Map.keys qta then
        return $ Map.findWithDefault (error "") coname qta
      else fail "no translation found"
