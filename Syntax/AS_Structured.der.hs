{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  $Header$
Description :  abstract syntax of CASL structured specifications
Copyright   :  (c) Klaus Luettich, Uni Bremen 2002-2006
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable(Grothendieck)

Abstract syntax of HetCASL (heterogeneous) structured specifications
   Follows Sect. II:2.2.3 of the CASL Reference Manual.
-}

module Syntax.AS_Structured where

-- DrIFT command:
{-! global: GetRange !-}

import Common.Id
import Common.IRI
import Common.AS_Annotation

import Data.Typeable
import qualified Data.Set as Set

import Logic.Logic
import Logic.Grothendieck
    ( G_basic_spec
    , G_symb_items_list
    , G_symb_map_items_list
    , LogicGraph
    , setCurLogic
    , setSyntax )

-- for spec-defn and view-defn see AS_Library

data SPEC = Basic_spec G_basic_spec Range
          | EmptySpec Range
          | Extraction (Annoted SPEC) EXTRACTION
          | Translation (Annoted SPEC) RENAMING
          | Reduction (Annoted SPEC) RESTRICTION
          | Approximation (Annoted SPEC) APPROXIMATION
          | Minimization (Annoted SPEC) MINIMIZATION
          | Union [Annoted SPEC] Range
            -- pos: "and"s
          | Extension [Annoted SPEC] Range
            -- pos: "then"s
          | Free_spec (Annoted SPEC) Range
            -- pos: "free"
          | Cofree_spec (Annoted SPEC) Range
            -- pos: "cofree"
          | Minimize_spec (Annoted SPEC) Range
            -- pos: "minimize", "closed-world"
          | Local_spec (Annoted SPEC) (Annoted SPEC) Range
            -- pos: "local", "within"
          | Closed_spec (Annoted SPEC) Range
            -- pos: "closed"
          | Group (Annoted SPEC) Range
            -- pos: "{","}"
          | Spec_inst SPEC_NAME [Annoted FIT_ARG] Range
            -- pos: many of "[","]"; one balanced pair per FIT_ARG
          | Qualified_spec LogicDescr (Annoted SPEC) Range
            -- pos: "logic", Logic_name,":"
          | Data AnyLogic AnyLogic (Annoted SPEC) (Annoted SPEC) Range
            -- pos: "data"
          | Combination [LABELED_ONTO_OR_INTPR_REF] [EXTENSION_REF] Range
            {- pos: combine ONTO_OR_INTPR_REF, ...,  ONTO_OR_INTPR_REF
            excluding EXTENSION_REF, ..., EXTENSION_REF -}
            deriving (Show, Typeable)

{- Renaming and Hiding can be performend with intermediate Logic
   mappings / Logic projections.

-}

data EXTRACTION = ExtractOrRemove Bool [IRI] Range
  deriving (Show, Eq, Typeable)

data RENAMING = Renaming [G_mapping] Range
                -- pos: "with", list of comma pos
                 deriving (Show, Eq, Typeable)

data RESTRICTION = Hidden [G_hiding] Range
                   -- pos: "hide", list of comma pos
                 | Revealed G_symb_map_items_list Range
                   -- pos: "reveal", list of comma pos
                   deriving (Show, Eq, Typeable)

data APPROXIMATION = Named_Approx APPROX_METHOD_REF Range
                   | Qual_Approx APPROX_METHOD_REF LOGIC_REF Range
                     deriving (Show, Eq, Typeable)

data MINIMIZATION = Mini CircMin CircVars Range
                    deriving (Show, Eq, Typeable)


data G_mapping = G_symb_map G_symb_map_items_list
               | G_logic_translation Logic_code
                 deriving (Show, Eq, Typeable)

data G_hiding = G_symb_list G_symb_items_list
               | G_logic_projection Logic_code
                 deriving (Show, Eq, Typeable)

data FIT_ARG = Fit_spec (Annoted SPEC) [G_mapping] Range
               -- pos: opt "fit"
             | Fit_view VIEW_NAME [Annoted FIT_ARG] Range
               -- annotations before the view keyword are stored in Spec_inst
               deriving (Show, Typeable)

type SPEC_NAME = IRI
type VIEW_NAME = IRI
type EQUIV_NAME = IRI
type ALIGN_NAME = IRI
type MODULE_NAME = IRI
type APPROX_METHOD_REF = IRI
type ENTITY = IRI
type RESTRICTION_SIGNATURE = [ENTITY]
type CircMin = [Symb]
type CircVars = [Symb]
type Symb = IRI

-- | a logic with serialization
data LogicDescr = LogicDescr Logic_name (Maybe IRI) Range
  -- pos: "serialization"
  deriving (Show, Typeable)

data Logic_code = Logic_code (Maybe String)
                             (Maybe Logic_name)
                             (Maybe Logic_name) Range
                 {- pos: "logic",<encoding>,":",<src-logic>,"->",<targ-logic>
                 one of <encoding>, <src-logic> or <targ-logic>
                 must be given (by Just)
                 "logic bla"    => <encoding> only
                 "logic bla ->" => <src-logic> only
                 "logic -> bla" => <targ-logic> only
                 "logic bla1 -> bla2" => <src-logic> and <targ-logic>
                 -- "logic bla1:bla2"    => <encoding> and <src-logic>
                 this notation is not very useful and is not maintained
                 "logic bla1:bla2 ->" => <encoding> and <src-logic> (!)
                 "logic bla1: ->bla2" => <encoding> and <targ-logic> -}
                  deriving (Show, Eq, Typeable)

data Logic_name = Logic_name String (Maybe Token) (Maybe SPEC_NAME)
  deriving (Show, Eq, Typeable)

data LABELED_ONTO_OR_INTPR_REF = Labeled (Maybe CombineID) ONTO_OR_INTPR_REF
  deriving (Show, Eq, Typeable)

type ONTO_NAME = IRI
type EXTENSION_NAME = IRI
type IMPORT_NAME = IRI

type ONTO_OR_INTPR_REF = IRI
type ONTO_REF = IRI
type EXTENSION_REF = IRI
type LOGIC_REF = IRI
type CombineID = Token

nameToLogicDescr :: Logic_name -> LogicDescr
nameToLogicDescr n = LogicDescr n Nothing nullRange

setLogicName :: LogicDescr -> LogicGraph -> LogicGraph
setLogicName (LogicDescr (Logic_name lid _ _) s _) =
  setSyntax s . setCurLogic lid

makeSpec :: G_basic_spec -> Annoted SPEC
makeSpec gbs = emptyAnno $ Basic_spec gbs nullRange

makeSpecInst :: SPEC_NAME -> Annoted SPEC
makeSpecInst n = emptyAnno $ Spec_inst n [] nullRange

addImports :: [SPEC_NAME] -> Annoted SPEC -> Annoted SPEC
addImports is bs = case map makeSpecInst is of
  [] -> bs
  js@(i : rs) -> emptyAnno $ Extension
    [ if null rs then i else
          emptyAnno $ Union js nullRange, bs] nullRange

data CORRESPONDENCE = Correspondence_block
                        (Maybe RELATION_REF)
                        (Maybe CONFIDENCE)
                        [CORRESPONDENCE]
                    | Single_correspondence
                        (Maybe CORRESPONDENCE_ID)
                        G_symb_items_list -- was ENTITY_REF
                        G_symb_items_list -- was TERM_OR_ENTITY_REF
                        (Maybe RELATION_REF)
                        (Maybe CONFIDENCE)
                    | Default_correspondence
                      deriving (Show, Eq, Typeable)

type CORRESPONDENCE_ID = Annotation

type ENTITY_REF = IRI

data TERM_OR_ENTITY_REF = Term G_symb_items_list Range
                        | Entity_ref ENTITY_REF
                          deriving (Show, Eq, Typeable)

data RELATION_REF = Subsumes | IsSubsumed | Equivalent | Incompatible
                  | HasInstance | InstanceOf | DefaultRelation
                  | Iri IRI
                    deriving (Show, Eq, Typeable)

refToRel :: RELATION_REF -> REL_REF
refToRel Subsumes = Subs
refToRel IsSubsumed = IsSubs
refToRel Equivalent = Equiv
refToRel Incompatible = Incomp
refToRel HasInstance = HasInst
refToRel InstanceOf = InstOf
refToRel DefaultRelation = DefRel
refToRel (Iri i) = RelName i

type CONFIDENCE = Double -- NOTE: will be revised

instance GetRange Double where
  getRange = const nullRange

getSpecNames :: SPEC -> Set.Set SPEC_NAME
getSpecNames sp = let f = getSpecNames . item in case sp of
  Translation as _ -> f as
  Reduction as _ -> f as
  Approximation as _ -> f as
  Minimization as _ -> f as
  Union as _ -> Set.unions $ map f as
  Extension as _ -> Set.unions $ map f as
  Free_spec as _ -> f as
  Cofree_spec as _ -> f as
  Minimize_spec as _ -> f as
  Local_spec s1 s2 _ -> Set.union (f s1) $ f s2
  Closed_spec as _ -> f as
  Group as _ -> f as
  Spec_inst sn fas _ -> Set.insert sn
    . Set.unions . map f $ concatMap (getSpecs . item) fas
  Qualified_spec _ as _ -> f as
  Data _ _ s1 s2 _ -> Set.union (f s1) $ f s2
  _ -> Set.empty

getSpecs :: FIT_ARG -> [Annoted SPEC]
getSpecs fa = case fa of
  Fit_spec as _ _ -> [as]
  Fit_view _ fas _ -> concatMap (getSpecs . item) fas
