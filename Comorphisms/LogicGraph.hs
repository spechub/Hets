{-# OPTIONS -cpp #-}
{- |
Module      :  $Header$
Copyright   :  (c)  Till Mossakowski and Uni Bremen 2003
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  till@tzi.de
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

   The FLIRTS home page: <http://www.tzi.de/flirts>

   T. Mossakowski:
   Relating CASL with Other Specification Languages:
        the Institution Level
   Theoretical Computer Science 286, p. 367-475, 2002.
-}

module Comorphisms.LogicGraph
    ( defaultLogic
    , logicList
    , logicGraph
    , lookupComorphism_in_LG
    , comorphismList
    ) where

import Common.Result
import Logic.Logic
import Logic.Prover (prover_sublogic)
import Logic.Comorphism
import Logic.Grothendieck
import Logic.Coerce
import Comorphisms.CASL2PCFOL
import Comorphisms.CASL2SubCFOL
import Comorphisms.CASL2HasCASL
import Comorphisms.HasCASL2HasCASL
import Comorphisms.CFOL2IsabelleHOL
import Comorphisms.CASL2SoftFOL
import Comorphisms.Prop2CASL
import Comorphisms.HasCASL2IsabelleHOL
import Comorphisms.PCoClTyConsHOL2IsabelleHOL
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
#endif
#ifdef PROGRAMATICA
import Comorphisms.HasCASL2Haskell
import Comorphisms.Haskell2IsabelleHOLCF
#endif

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe (fromJust)
import Data.List
import Debug.Trace

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

inclusionList :: [AnyComorphism]
inclusionList =
    [ Comorphism CASL2HasCASL
    , Comorphism CFOL2IsabelleHOL
    , Comorphism Prop2CASL
#ifdef CASLEXTENSIONS
    , Comorphism CASL2Modal
    , Comorphism Modal2CASL
    , Comorphism CASL2CoCASL
    , Comorphism CASL2CspCASL
#endif
    , Comorphism PCoClTyConsHOL2IsabelleHOL
    , Comorphism HasCASL2IsabelleHOL
    ]

normalList :: [AnyComorphism]
normalList =
    [ Comorphism SuleCFOL2SoftFOLInduction
    , Comorphism HasCASL2HasCASL
    , Comorphism SuleCFOL2SoftFOL
#ifdef CASLEXTENSIONS
    , Comorphism CoCASL2CoPCFOL
    , Comorphism CoCASL2CoSubCFOL
    , Comorphism CoCFOL2IsabelleHOL
    , Comorphism CspCASL2Modal -- not stable yet
#endif
#ifdef PROGRAMATICA
    , Comorphism HasCASL2Haskell
    , Comorphism Haskell2IsabelleHOLCF
    , Comorphism Haskell2IsabelleHOL
#endif
    , Comorphism CASL2PCFOL
    , Comorphism CASL2SubCFOL
    , Comorphism CASL2TopSort
    ]

comorphismList :: [AnyComorphism]
comorphismList = inclusionList ++ normalList

{- | Unions of logics, represented as pairs of inclusions.
     Entries only necessary for non-trivial unions
     (a trivial union is a union of a sublogic with a superlogic).
-}
unionList :: [(AnyComorphism, AnyComorphism)]
unionList = []

logicGraph :: LogicGraph
logicGraph = LogicGraph
    { logics = Map.fromList $ map addLogicName logicList
    , comorphisms = Map.fromList $ map addComorphismName comorphismList
    , inclusions = Map.fromList $ map addInclusionNames inclusionList
    , unions = Map.fromList $ map addUnionNames unionList
    }

lookupComorphism_in_LG :: String -> Result AnyComorphism
lookupComorphism_in_LG coname = lookupComorphism coname logicGraph
