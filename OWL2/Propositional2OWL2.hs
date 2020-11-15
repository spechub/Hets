{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances, DeriveGeneric #-}
{- |
Module      :  ./OWL2/Propositional2OWL2.hs
Description :  Comorphism from Propostional Logic to OWL 2
Copyright   :  (c) Felix Gabriel Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisional
Portability :  non-portable (via Logic.Logic)
-}

module OWL2.Propositional2OWL2 where

import Common.ProofTree
import Logic.Logic
import Logic.Comorphism

import Common.AS_Annotation
import Common.Id
import Common.Result

import OWL2.AS
import Common.IRI
import OWL2.Keywords
import OWL2.MS
import OWL2.Translate
import qualified OWL2.Morphism as OWLMor
import qualified OWL2.ProfilesAndSublogics as OWLSub
import qualified OWL2.Sign as OWLSign
import qualified OWL2.Logic_OWL2 as OWLLogic
import qualified OWL2.Symbols as OWLSym

import qualified Propositional.Logic_Propositional as PLogic
import Propositional.AS_BASIC_Propositional
import qualified Propositional.Sublogic as PSL
import qualified Propositional.Sign as PSign
import qualified Propositional.Morphism as PMor
import qualified Propositional.Symbol as PSymbol

import qualified Data.HashSet as Set
import GHC.Generics (Generic)
import Data.Hashable

data Propositional2OWL2 = Propositional2OWL2 deriving (Show, Generic)

instance Hashable Propositional2OWL2

instance Language Propositional2OWL2

instance Comorphism Propositional2OWL2
    PLogic.Propositional
    PSL.PropSL
    BASIC_SPEC
    FORMULA
    SYMB_ITEMS
    SYMB_MAP_ITEMS
    PSign.Sign
    PMor.Morphism
    PSymbol.Symbol
    PSymbol.Symbol
    ProofTree
    OWLLogic.OWL2
    OWLSub.ProfSub
    OntologyDocument
    Axiom
    OWLSym.SymbItems
    OWLSym.SymbMapItems
    OWLSign.Sign
    OWLMor.OWLMorphism
    Entity
    OWLSym.RawSymb
    ProofTree
    where
        sourceLogic Propositional2OWL2 = PLogic.Propositional
        sourceSublogic Propositional2OWL2 = PSL.top
        targetLogic Propositional2OWL2 = OWLLogic.OWL2
        mapSublogic Propositional2OWL2 = Just . mapSub -- TODO
        map_theory Propositional2OWL2 = mapTheory
        isInclusionComorphism Propositional2OWL2 = True
        has_model_expansion Propositional2OWL2 = True

mkOWLDeclaration :: ClassExpression -> Axiom
mkOWLDeclaration ex = PlainAxiom (ClassEntity $ Expression $ setPrefix "owl"
    $ mkIRI thingS) $ ListFrameBit (Just SubClass) $ ExpressionBit [([], ex)]

tokToIRI :: Token -> IRI
tokToIRI = idToIRI . simpleIdToId

mapFormula :: FORMULA -> ClassExpression
mapFormula f = case f of
    False_atom _ -> Expression $ mkIRI nothingS
    True_atom _ -> Expression $ mkIRI thingS
    Predication p -> Expression $ tokToIRI p
    Negation nf _ -> ObjectComplementOf $ mapFormula nf
    Conjunction fl _ -> ObjectJunction IntersectionOf $ map mapFormula fl
    Disjunction fl _ -> ObjectJunction UnionOf $ map mapFormula fl
    Implication a b _ -> ObjectJunction UnionOf [ObjectComplementOf
                $ mapFormula a, mapFormula b]
    Equivalence a b _ -> ObjectJunction IntersectionOf $ map mapFormula
                [Implication a b nullRange, Implication b a nullRange]

mapPredDecl :: PRED_ITEM -> [Axiom]
mapPredDecl (Pred_item il _) = map (mkOWLDeclaration . Expression
    . tokToIRI) il

mapAxiomItems :: Annoted FORMULA -> Axiom
mapAxiomItems = mkOWLDeclaration . mapFormula . item

mapBasicItems :: BASIC_ITEMS -> [Axiom]
mapBasicItems bi = case bi of
    Pred_decl p -> mapPredDecl p
    Axiom_items al -> map mapAxiomItems al

mapBasicSpec :: BASIC_SPEC -> [Axiom]
mapBasicSpec (Basic_spec il) = concatMap (mapBasicItems . item) il

mapSign :: PSign.Sign -> OWLSign.Sign
mapSign ps = OWLSign.emptySign {OWLSign.concepts = Set.fromList
    $ map idToIRI $ Set.toList $ PSign.items ps}

mapTheory :: (PSign.Sign, [Named FORMULA])
    -> Result (OWLSign.Sign, [Named Axiom])
mapTheory (psig, fl) = return (mapSign psig, map
    (mapNamed $ mkOWLDeclaration . mapFormula) fl)

mapSub :: PSL.PropSL -> OWLSub.ProfSub
mapSub _ = OWLSub.topS
