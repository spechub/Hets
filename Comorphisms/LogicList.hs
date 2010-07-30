{-# LANGUAGE CPP #-}
{- |
Module      :  $Header$
Description :  Assembles all the logics into a list, as a prerequisite
  for the logic graph
Copyright   :  (c)  Till Mossakowski and Uni Bremen 2003
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (existential types)

Assembles all the logics into a list, as a prerequisite for the logic graph.
   The modules for the Grothendieck logic are logic graph indepdenent,
   and here is the logic graph that is used to instantiate these.
   Since the logic graph depends on a large number of modules for the
   individual logics, this separation of concerns (and possibility for
   separate compilation) is quite useful.

   References:

   J. A. Goguen, R. M. Burstall: Institutions:
     Abstract Model Theory for Specification and Programming,
     Journal of the Association for Computing Machinery 39, p. 95-146.

   J. Meseguer: General logics. Logic Colloquium 87, p. 275-329, North Holland.

   Todo:
   Add many many logics.
-}

module Comorphisms.LogicList
    ( logicList
    , addLogicName
    , defaultLogic
    , preLogicGraph
    ) where

import qualified Data.Map as Map
import Logic.Logic
import Logic.Grothendieck
import CASL.Logic_CASL  -- also serves as default logic
import HasCASL.Logic_HasCASL
import Propositional.Logic_Propositional
import QBF.Logic_QBF
#ifdef PROGRAMATICA
import Haskell.Logic_Haskell
#endif
import Isabelle.Logic_Isabelle
import SoftFOL.Logic_SoftFOL
#ifdef CASLEXTENSIONS
import Adl.Logic_Adl
import Modal.Logic_Modal
import ExtModal.Logic_ExtModal
import CoCASL.Logic_CoCASL
import CspCASL.Logic_CspCASL
import COL.Logic_COL ()
import CASL_DL.Logic_CASL_DL
import ConstraintCASL.Logic_ConstraintCASL
import VSE.Logic_VSE
-- no CASL extension, but omit them as non-essential
import RelationalScheme.Logic_Rel
import Temporal.Logic_Temporal
import DFOL.Logic_DFOL
import LF.Logic_LF
import Framework.Logic_Framework
import Comorphisms.DynLogicList
--import OMDoc.Logic_OMDoc ()
import Maude.Logic_Maude
import CSL.Logic_CSL
import CommonLogic.Logic_CommonLogic
#endif
#ifndef NOOWLLOGIC
import DMU.Logic_DMU
import OWL.Logic_OWL
#endif

logicList :: [AnyLogic]
logicList =
  [ Logic CASL
  , Logic HasCASL
  , Logic Isabelle
  , Logic SoftFOL
  , Logic Propositional
  , Logic QBF
#ifdef PROGRAMATICA
  , Logic Haskell
#endif
#ifdef CASLEXTENSIONS
  , Logic Adl
  , Logic CoCASL
  , Logic ExtModal
  , Logic Modal
  , Logic cspCASL
  , Logic traceCspCASL
  , Logic failureCspCASL
  , Logic CASL_DL
  , Logic ConstraintCASL
  , Logic VSE
  , Logic RelScheme
  , Logic Temporal
  , Logic DFOL
  , Logic LF
  , Logic Framework
  , Logic Maude
  , Logic CSL
  , Logic CommonLogic
#endif
#ifndef NOOWLLOGIC
  , Logic DMU
  , Logic OWL
#endif
  ] ++ dynLogicList

addLogicName :: AnyLogic -> (String,AnyLogic)
addLogicName l@(Logic lid) = (language_name lid, l)

defaultLogic :: AnyLogic
defaultLogic = Logic CASL

preLogicGraph :: LogicGraph
preLogicGraph =
  emptyLogicGraph { logics = Map.fromList $ map addLogicName logicList }
