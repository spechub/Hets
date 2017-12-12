{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module PGIP.GraphQL.Schema where

import Data.Char (toLower)
import Data.Text (pack, unpack)
import Protolude hiding (Enum, Symbol, map, show)
import GraphQL.API
  ( GraphQLEnum(..)
  , Enum
  , Object
  , Field
  , Argument
  , Interface
  , Union
  , (:>)
  )
import GraphQL.Resolver (Defaultable(..))
import GraphQL.Value (pattern ValueEnum, makeName, unName)
import GraphQL.Value.ToValue (ToValue(..))

{- The FileVersion type is changed (from Ontohub's) to not show the repository
    and the commit.
    Everything around Repository, Git and OrganizationalUnit has been removed
    from Ontohub's schema. -}

{- Because of https://github.com/jml/graphql-api/issues/93,
    some fields need to be left out of the schema. It is currently not possible
    to use a recursive schema with the graphql-api package. -}

-- # Positional information of a text element in a file
-- type FileRange {
--   # The column of the text element's end
--   endColumn: Int!
--
--   # The line of the text element's end
--   endLine: Int!
--
--   # The file path
--   path: String!
--
--   # The column of the text element's beginning
--   startColumn: Int!
--
--   # The line of the text element's beginning
--   startLine: Int!
-- }
type FileRange = Object "FileRange" '[]
  '[ Field "endColumn" Int
   , Field "endLine" Int
   , Field "path" Text
   , Field "startColumn" Int
   , Field "startLine" Int
   ]

-- # A versioned file
-- type FileVersion {
--   # The state of evaluation
--   evaluationState: EvaluationState!

--   # The path of this file
--   path: String!
-- }
type FileVersion = Object "FileVersion" '[]
  -- '[ Field "evaluationState" EvaluationState
  '[ Field "evaluationState" Text
   , Field "path" Text
   ]

-- # An axiom
-- type Axiom implements LocIdBase, Sentence {
--   # The FileRange of this Sentence's definition
--   fileRange: FileRange

--   # The FileVersion to which this object belongs
--   fileVersion: FileVersion!

--   # The Loc/Id of the document
--   locId: ID!

--   # The name of the Sentence
--   name: String!

--   # The OMS to which this Sentence belongs
--   oms: OMS!

--   # The symbols used in this sentence
--   symbols(
--     # Maximum number of entries to list
--     limit: Int = 20

--     # Skip the first n entries
--     skip: Int = 0
--   ): [Symbol!]!

--   # The definitional text of this Sentence
--   text: String!
-- }
type Axiom = Object "Axiom" '[LocIdBase, Sentence]
  '[ Field "fileRange" (Maybe FileRange)
   , Field "fileVersion" FileVersion
   , Field "locId" Text
   , Field "name" Text
   -- , Field "oms" OMS -- removed due to recursion issue (see the comment at the top of this module).
   , Argument "limit" (Maybe Int) :> Argument "skip" (Maybe Int) :> Field "symbols" [Symbol]
   ]

-- # A conjecture
-- interface Conjecture {
--   # The state of evaluation
--   evaluationState: EvaluationState!

--   # The FileRange of this Sentence's definition
--   fileRange: FileRange

--   # The FileVersion to which this object belongs
--   fileVersion: FileVersion!

--   # The Loc/Id of the document
--   locId: ID!

--   # The name of the Sentence
--   name: String!

--   # The OMS to which this Sentence belongs
--   oms: OMS!

--   # The attempts to prove this Conjecture
--   proofAttempts(
--     # Maximum number of entries to list
--     limit: Int = 20

--     # Skip the first n entries
--     skip: Int = 0
--   ): [ProofAttempt!]!

--   # The reasoning status of this Conjecture
--   reasoningStatus: ReasoningStatus!

--   # The symbols used in this sentence
--   symbols(
--     # Maximum number of entries to list
--     limit: Int = 20

--     # Skip the first n entries
--     skip: Int = 0
--   ): [Symbol!]!

--   # The definitional text of this Sentence
--   text: String!
-- }
type Conjecture = Interface "Conjecture"
  -- '[ Field "evaluationState" EvaluationState
  '[ Field "evaluationState" Text
   , Field "fileRange" (Maybe FileRange)
   , Field "fileVersion" FileVersion
   , Field "locId" Text
   , Field "name" Text
   -- , Field "oms" OMS -- removed due to recursion issue (see the comment at the top of this module).
   , Argument "limit" (Maybe Int) :> Argument "skip" (Maybe Int) :> Field "proofAttempts" [ProofAttempt]
   , Field "reasoningStatus" ReasoningStatus
   , Argument "limit" (Maybe Int) :> Argument "skip" (Maybe Int) :> Field "symbols" [Symbol]
   , Field "text" Text
   ]

-- # A conservativity status
-- type ConservativityStatus {
--   # The proved conservativity value
--   proved: String!

--   # The required conservativity value
--   required: String!
-- }
type ConservativityStatus = Object "ConservativityStatus" '[]
  '[ Field "proved" Text
   , Field "required" Text
   ]

-- # An attempt to check consistency of an OMS
-- type ConsistencyCheckAttempt implements ReasoningAttempt {
--   # The state of evaluation
--   evaluationState: EvaluationState!

--   # Axioms that have been generated during reasoning
--   generatedAxioms: [GeneratedAxiom!]!

--   # The ID of this ReasoningAttempt
--   id: Int!

--   # The number of this ReasoningAttempt
--   number: Int!

--   # The OMS of interest
--   oms: OMS!

--   # The used ReasonerConfiguration
--   reasonerConfiguration: ReasonerConfiguration!

--   # The output of the Reasoner
--   reasonerOutput: ReasonerOutput

--   # The reasoning status of this ReasoningAttempt
--   reasoningStatus: ReasoningStatus!

--   # The time it took to run the reasoner
--   timeTaken: Int

--   # The used Reasoner
--   usedReasoner: Reasoner!
-- }
type ConsistencyCheckAttempt = Object "ConsistencyCheckAttempt" '[ReasoningAttempt]
  -- '[ Field "evaluationState" EvaluationState
  '[ Field "evaluationState" Text
   , Field "generatedAxioms" [GeneratedAxiom]
   , Field "id" Text
   , Field "number" Int
   , Field "oms" OMS
   , Field "reasonerConfiguration" ReasonerConfiguration
   , Field "reasonerOutput" (Maybe ReasonerOutput)
   , Field "reasoningStatus" ReasoningStatus
   , Field "timeTaken" (Maybe Int)
   , Field "usedReasoner" Reasoner
   ]

-- # A counter-theorem (disproved conjecture)
-- type CounterTheorem implements Conjecture, LocIdBase, Sentence {
--   # The state of evaluation
--   evaluationState: EvaluationState!

--   # The FileRange of this Sentence's definition
--   fileRange: FileRange

--   # The FileVersion to which this object belongs
--   fileVersion: FileVersion!

--   # The Loc/Id of the document
--   locId: ID!

--   # The name of the Sentence
--   name: String!

--   # The OMS to which this Sentence belongs
--   oms: OMS!

--   # The attempts to prove this Conjecture
--   proofAttempts(
--     # Maximum number of entries to list
--     limit: Int = 20

--     # Skip the first n entries
--     skip: Int = 0
--   ): [ProofAttempt!]!

--   # The reasoning status of this Conjecture
--   reasoningStatus: ReasoningStatus!

--   # The symbols used in this sentence
--   symbols(
--     # Maximum number of entries to list
--     limit: Int = 20

--     # Skip the first n entries
--     skip: Int = 0
--   ): [Symbol!]!

--   # The definitional text of this Sentence
--   text: String!
-- }
type CounterTheorem = Object "CounterTheorem" '[Conjecture]
  -- '[ Field "evaluationState" EvaluationState
  '[ Field "evaluationState" Text
   , Field "fileRange" (Maybe FileRange)
   , Field "fileVersion" FileVersion
   , Field "locId" Text
   , Field "name" Text
   -- , Field "oms" OMS -- removed due to recursion issue (see the comment at the top of this module).
   , Argument "limit" (Maybe Int) :> Argument "skip" (Maybe Int) :> Field "proofAttempts" [ProofAttempt]
   , Field "reasoningStatus" ReasoningStatus
   , Argument "limit" (Maybe Int) :> Argument "skip" (Maybe Int) :> Field "symbols" [Symbol]
   , Field "text" Text
   ]

-- # A debug message
-- type Debug implements Diagnosis {
--   # The FileRange that this message is about
--   fileRange: FileRange

--   # The FileVersion which this message is about
--   fileVersion: FileVersion!

--   # The number of this message
--   number: Int!

--   # The actual message
--   text: String!
-- }
type Debug = Object "Debug" '[Diagnosis]
  '[ Field "fileRange" (Maybe FileRange)
   , Field "fileVersion" FileVersion
   , Field "number" Int
   , Field "text" Text
   ]

-- # A message about a file's content
-- interface Diagnosis {
--   # The FileRange that this message is about
--   fileRange: FileRange

--   # The FileVersion which this message is about
--   fileVersion: FileVersion!

--   # The number of this message
--   number: Int!

--   # The actual message
--   text: String!
-- }
type Diagnosis = Interface "Diagnosis"
  '[ Field "fileRange" (Maybe FileRange)
   , Field "fileVersion" FileVersion
   , Field "number" Int
   , Field "text" Text
   ]

-- # A Document is a container for OMS
-- interface Document {
--   # All DocumentLinks that this Document is part of
--   documentLinks(
--     # Maximum number of entries to list
--     limit: Int = 20

--     # Specifies which end of the link the current document is. Possible values: 'source', 'target'
--     origin: LinkOrigin = any

--     # Skip the first n entries
--     skip: Int = 0
--   ): [DocumentLink!]!

--   # The FileVersion to which this object belongs
--   fileVersion: FileVersion!

--   # The documents which import this Document
--   importedBy(
--     # Maximum number of entries to list
--     limit: Int = 20

--     # Skip the first n entries
--     skip: Int = 0
--   ): [Document!]!

--   # The documents which are imported by this Document
--   imports(
--     # Maximum number of entries to list
--     limit: Int = 20

--     # Skip the first n entries
--     skip: Int = 0
--   ): [Document!]!

--   # The Loc/Id of the document
--   locId: ID!
-- }
type Document = Interface "Document"
  '[ Field "fileVersion" FileVersion
   -- , Argument "limit" (Maybe Int) :> Argument "skip" (Maybe Int) :> Argument "origin" (Maybe LinkOrigin) :> Field "documentLinks" [DocumentLink] -- removed due to recursion issue (see the comment at the top of this module).
   -- , Argument "limit" (Maybe Int) :> Argument "skip" (Maybe Int) :> Field "importedBy" [Document] -- removed due to recursion issue (see the comment at the top of this module).
   -- , Argument "limit" (Maybe Int) :> Argument "skip" (Maybe Int) :> Field "imports" [Document] -- removed due to recursion issue (see the comment at the top of this module).
   , Field "locId" Text
   ]

-- # A DocumentLink shows a dependency between Documents
-- type DocumentLink {
--   # The source Document
--   source: Document!

--   # The target Document
--   target: Document!
-- }
-- type DocumentLink = Object "DocumentLink" '[] -- removed due to recursion issue (see the comment at the top of this module).
  -- '[ Field "source" Document -- removed due to recursion issue (see the comment at the top of this module).
   -- , Field "target" Document -- removed due to recursion issue (see the comment at the top of this module).
   -- ] -- removed due to recursion issue (see the comment at the top of this module).

-- # An error message
-- type Error implements Diagnosis {
--   # The FileRange that this message is about
--   fileRange: FileRange

--   # The FileVersion which this message is about
--   fileVersion: FileVersion!

--   # The number of this message
--   number: Int!

--   # The actual message
--   text: String!
-- }
type Error = Object "Error" '[Diagnosis]
  '[ Field "fileRange" (Maybe FileRange)
   , Field "fileVersion" FileVersion
   , Field "number" Int
   , Field "text" Text
   ]

-- # Specifies the state of evaluation
-- enum EvaluationState {
--   # The object has been enqueued but is not yet processing
--   enqueued

--   # The object has been evaluated successfully
--   finished_successfully

--   # The evaluation of this object has failed
--   finished_unsuccessfully

--   # The object has not yet been enqueued for evaluation
--   not_yet_enqueued

--   # The object is currently in evaluation
--   processing
-- }
data EvaluationState = Enqueued
                     | Finished_successully
                     | Finished_unsuccessfully
                     | Not_yet_enqueued
                     | Processing
                       deriving (Show, Eq, Ord, Generic)
instance GraphQLEnum EvaluationState
instance ToValue EvaluationState where
  toValue = toValue . pack . Prelude.map Data.Char.toLower . unpack . unName . enumToValue

-- # An that has been generated during reasoning
-- type GeneratedAxiom {
--   # The ID of the GeneratedAxiom
--   id: Int!

--   # The ReasoningAttempt in which this axiom has been generated
--   reasoningAttempt: ReasoningAttempt!

--   # The definitional text
--   text: String!
-- }
type GeneratedAxiom = Object "GeneratedAxiom" '[]
  '[ Field "id" Int
   -- , Field "reasoningAttempt" ReasoningAttempt -- removed due to recursion issue (see the comment at the top of this module).
   , Field "text" Text
   ]

-- # A hint
-- type Hint implements Diagnosis {
--   # The FileRange that this message is about
--   fileRange: FileRange

--   # The FileVersion which this message is about
--   fileVersion: FileVersion!

--   # The number of this message
--   number: Int!

--   # The actual message
--   text: String!
-- }
type Hint = Object "Hint" '[Diagnosis]
  '[ Field "fileRange" (Maybe FileRange)
   , Field "fileVersion" FileVersion
   , Field "number" Int
   , Field "text" Text
   ]

-- # A logical language
-- type Language {
--   # Where this language has been defined
--   definedBy: String!

--   # The description of this language
--   description: String!

--   # The ID of this language
--   id: ID!

--   # A LanguageMapping of which this Language is the source or the target
--   languageMappings(
--     # Maximum number of entries to list
--     limit: Int = 20

--     # Specifies which end of the link the current Language is
--     origin: LinkOrigin = any

--     # Skip the first n entries
--     skip: Int = 0
--   ): [LanguageMapping!]!

--   # The logics of this Language
--   logics(
--     # Maximum number of entries to list
--     limit: Int = 20

--     # Skip the first n entries
--     skip: Int = 0
--   ): [Logic!]!

--   # The name of this language
--   name: String!

--   # The standardization status of this language
--   standardizationStatus: String!
-- }
type Language = Object "Language" '[]
  '[ Field "definedBy" Text
   , Field "description" Text
   , Field "id" Text
   -- , Argument "limit" (Maybe Int) :> Argument "skip" (Maybe Int) :> Argument "origin" (Maybe LinkOrigin) :> Field "languageMappings" [LanguageMapping] -- removed due to recursion issue (see the comment at the top of this module).
   -- , Argument "limit" (Maybe Int) :> Argument "skip" (Maybe Int) :> Field "logics" [Logic] -- removed due to recursion issue (see the comment at the top of this module).
   , Field "name" Text
   , Field "standardizationStatus" Text
   ]

-- # A mapping between two languages
-- type LanguageMapping {
--   # The ID of this LanguageMapping
--   id: ID!

--   # The source language
--   source: Language!

--   # The target language
--   target: Language!
-- }
type LanguageMapping = Object "LanguageMapping" '[]
  '[ Field "id" Text
   -- , Field "source" Language -- removed due to recursion issue (see the comment at the top of this module).
   -- , Field "target" Language -- removed due to recursion issue (see the comment at the top of this module).
   ]

-- # A Library is a container for any number of OMS
-- type Library implements Document, LocIdBase {
--   # All DocumentLinks that this Document is part of
--   documentLinks(
--     # Maximum number of entries to list
--     limit: Int = 20

--     # Specifies which end of the link the current document is. Possible values: 'source', 'target'
--     origin: LinkOrigin = any

--     # Skip the first n entries
--     skip: Int = 0
--   ): [DocumentLink!]!

--   # The FileVersion to which this object belongs
--   fileVersion: FileVersion!

--   # The documents which import this Document
--   importedBy(
--     # Maximum number of entries to list
--     limit: Int = 20

--     # Skip the first n entries
--     skip: Int = 0
--   ): [Document!]!

--   # The documents which are imported by this Document
--   imports(
--     # Maximum number of entries to list
--     limit: Int = 20

--     # Skip the first n entries
--     skip: Int = 0
--   ): [Document!]!

--   # The Loc/Id of the document
--   locId: ID!

--   # A list of OMS in this Library
--   oms(
--     # Maximum number of entries to list
--     limit: Int = 20

--     # Skip the first n entries
--     skip: Int = 0
--   ): [OMS!]!
-- }
type Library = Object "Library" '[Document]
  '[ Field "fileVersion" FileVersion
   -- , Argument "limit" (Maybe Int) :> Argument "skip" (Maybe Int) :> Argument "origin" (Maybe LinkOrigin) :> Field "documentLinks" [DocumentLink] -- removed due to recursion issue (see the comment at the top of this module).
   -- , Argument "limit" (Maybe Int) :> Argument "skip" (Maybe Int) :> Field "importedBy" [Document] -- removed due to recursion issue (see the comment at the top of this module).
   -- , Argument "limit" (Maybe Int) :> Argument "skip" (Maybe Int) :> Field "imports" [Document] -- removed due to recursion issue (see the comment at the top of this module).
   , Field "locId" Text
   -- , Argument "limit" (Maybe Int) :> Argument "skip" (Maybe Int) :> Field "oms" [OMS]
   ]

-- # Specifies which end of the link the current object is
-- enum LinkOrigin {
--   # The current object is any end of the link
--   any

--   # The current object is the source of the link
--   source

--   # The current object is the target of the link
--   target
-- }
data LinkOrigin = Any
                | Source
                | Target
                  deriving (Show, Eq, Ord, Generic)
instance GraphQLEnum LinkOrigin
instance ToValue LinkOrigin where
  toValue = toValue . pack . Prelude.map Data.Char.toLower . unpack . unName . enumToValue

-- # An object with a Loc/Id
-- interface LocIdBase {
--   # The FileVersion to which this object belongs
--   fileVersion: FileVersion!

--   # The Loc/Id of the document
--   locId: ID!
-- }
type LocIdBase = Interface "LocIdBase"
  '[ Field "fileVersion" FileVersion
   , Field "locId" Text
   ]

-- # A logic
-- type Logic {
--   # The ID of this logic
--   id: ID!

--   # The language to which this logic belongs
--   language: Language!

--   # A LogicMapping of which this Logic is the source or the target
--   logicMappings(
--     # Maximum number of entries to list
--     limit: Int = 20

--     # Specifies which end of the link the current Logic is
--     origin: LinkOrigin = any

--     # Skip the first n entries
--     skip: Int = 0
--   ): [LogicMapping!]!

--   # The name of this logic
--   name: String!
-- }
type Logic = Object "Logic" '[]
  '[ Field "id" Text
   , Field "language" Language
   , Argument "limit" (Maybe Int) :> Argument "skip" (Maybe Int) :> Argument "origin" (Maybe LinkOrigin) :> Field "logicMappings" [LogicMapping]
   , Field "name" Text
   ]

-- # A mapping between two logics
-- type LogicMapping {
--   # The ID of this LogicMapping
--   id: ID!

--   # The LanguageMapping to which this LogicMapping belongs
--   languageMapping: LanguageMapping!

--   # The source logic
--   source: Logic!

--   # The target logic
--   target: Logic!
-- }
type LogicMapping = Object "LogicMapping" '[]
  '[ Field "id" Text
   , Field "languageMapping" LanguageMapping
   -- , Field "source" Logic -- removed due to recursion issue (see the comment at the top of this module).
   -- , Field "target" Logic -- removed due to recursion issue (see the comment at the top of this module).
   ]

-- # A PremiseSelection whose premises were selected by hand
-- type ManualPremiseSelection implements PremiseSelection {
--   # The ID of the PremiseSelection
--   id: Int!

--   # The used ReasonerConfiguration
--   reasonerConfiguration: ReasonerConfiguration!

--   # The selected premises
--   selectedPremises(
--     # Maximum number of entries to list
--     limit: Int = 20

--     # Skip the first n entries
--     skip: Int = 0
--   ): [Sentence!]!
-- }
type ManualPremiseSelection = Object "ManualPremiseSelection" '[PremiseSelection]
  '[ Field "id" Int
   -- , Field "reasonerConfiguration" ReasonerConfiguration -- removed due to recursion issue (see the comment at the top of this module).
   , Argument "limit" (Maybe Int) :> Argument "skip" (Maybe Int) :> Field "selectedPremises" [Sentence]
   ]

-- # A mapping between two OMS
-- type Mapping implements LocIdBase {
--   # The ConservativityStatus of this Mapping
--   conservativityStatus: ConservativityStatus!

--   # The human-friendly name of this Mapping
--   displayName: String!

--   # The FileVersion to which this object belongs
--   fileVersion: FileVersion!

--   # The Language of the Mapping's freeness parameter
--   freenessParameterLanguage: Language

--   # The OMS of the Mapping's freeness parameter
--   freenessParameterOMS: OMS

--   # The Loc/Id of the document
--   locId: ID!

--   # The technical name of this Mapping
--   name: String!

--   # The origin of this Mapping
--   origin: MappingOrigin!

--   # True if there are open proofs in this Mapping
--   pending: Boolean!

--   # The SignatureMorphism that this Mapping uses
--   signatureMorphism: SignatureMorphism!

--   # The source of the Mapping
--   source: OMS!

--   # The target of the Mapping
--   target: OMS!

--   # The type of this Mapping
--   type: MappingType!
-- }
type Mapping = Object "Mapping" '[LocIdBase]
  '[ Field "conservativityStatus" ConservativityStatus
   , Field "displayName" Text
   , Field "fileVersion" FileVersion
   , Field "freenessParameterLanguage" Language
   , Field "freenessParameterOMS" OMS
   , Field "locId" Text
   , Field "name" Text
   , Field "origin" MappingOrigin
   , Field "pending" Bool
   , Field "signatureMorphism" SignatureMorphism
   , Field "source" OMS
   , Field "target" OMS
   , Field "type" MappingType
   ]

-- # Specifies the origin (in the DOL document) of the Mapping
-- enum MappingOrigin {
--   # implied extension
--   dg_implies_link

--   # alignment
--   dg_link_align

--   # closure OMS
--   dg_link_closed_lenv

--   # extension OMS
--   dg_link_extension

--   # fitting view on an instantiation of a parameterised OMS (CASL syntax)
--   dg_link_fit_view

--   # implict fitting view on an instantiation of a parameterised OMS (CASL syntax)
--   dg_link_fit_view_imp

--   # flattening of an OMS translation
--   dg_link_flattening_rename

--   # flattening of an OMS union
--   dg_link_flattening_union

--   # CASL imports
--   dg_link_imports

--   # reference to an OMS
--   dg_link_inst

--   # argument of a parameterised OMS (CASL syntax)
--   dg_link_inst_arg

--   # intersection
--   dg_link_intersect

--   # morphism created during an instantiation of a parameterised OMS (CASL syntax)
--   dg_link_morph

--   # proof within the development graph calculus
--   dg_link_proof

--   # refinement of OMS
--   dg_link_refinement

--   # translation OMS
--   dg_link_translation

--   # development graph calculus
--   dg_link_verif

--   # interpretation (view)
--   dg_link_view

--   # that of the target OMS of the mapping
--   see_source

--   # that of the source OMS of the mapping
--   see_target

--   # used for testing purposes
--   test
-- }
data MappingOrigin = Dg_implies_link
                   | Dg_link_align
                   | Dg_link_closed_lenv
                   | Dg_link_extension
                   | Dg_link_fit_view
                   | Dg_link_fit_view_imp
                   | Dg_link_flattening_rename
                   | Dg_link_flattening_union
                   | Dg_link_imports
                   | Dg_link_inst
                   | Dg_link_inst_arg
                   | Dg_link_intersect
                   | Dg_link_morph
                   | Dg_link_proof
                   | Dg_link_refinement
                   | Dg_link_translation
                   | Dg_link_verif
                   | Dg_link_view
                   | See_source
                   | See_target
                   | Test
                     deriving (Show, Eq, Ord, Generic)
instance GraphQLEnum MappingOrigin
instance ToValue MappingOrigin where
  toValue = toValue . pack . Prelude.map Data.Char.toLower . unpack . unName . enumToValue

-- # Specifies the type of the Mapping (=link in the development graph)
-- enum MappingType {
--   # cofree definition link
--   cofree_def

--   # open cofree theorem link
--   cofree_open

--   # proved cofree theorem link
--   cofree_proved

--   # free definition link
--   free_def

--   # open free theorem link
--   free_open

--   # proved free theorem link
--   free_proved

--   # global definition link
--   global_def

--   # open global theorem link
--   global_thm_open

--   # proved global theorem link
--   global_thm_proved

--   # hiding defintion link
--   hiding_def

--   # open hiding theorem link
--   hiding_open

--   # proved hiding theorem link
--   hiding_proved

--   # local definition link
--   local_def

--   # open local theorem link
--   local_thm_open

--   # proved local theorem link
--   local_thm_proved

--   # minimization definition link
--   minimize_def

--   # open minimization theorem link
--   minimize_open

--   # proved minimization theorem link
--   minimize_proved

--   # free definition link generated by Maude
--   np_free_def

--   # open free theorem link generated by Maude
--   np_free_open

--   # proved free theorem link generated by Maude
--   np_free_proved
-- }
data MappingType = Cofree_def
                 | Cofree_open
                 | Cofree_proved
                 | Free_def
                 | Free_open
                 | Free_proved
                 | Global_def
                 | Global_thm_open
                 | Global_thm_proved
                 | Hiding_def
                 | Hiding_open
                 | Hiding_proved
                 | Local_def
                 | Local_thm_open
                 | Local_thm_proved
                 | Minimize_def
                 | Minimize_open
                 | Minimize_proved
                 | Np_free_def
                 | Np_free_open
                 | Np_free_proved
                   deriving (Show, Eq, Ord, Generic)
instance GraphQLEnum MappingType
instance ToValue MappingType where
  toValue = toValue . pack . Prelude.map Data.Char.toLower . unpack . unName . enumToValue

-- # A NativeDocument is a container for exactly one OMS
-- type NativeDocument implements Document, LocIdBase {
--   # All DocumentLinks that this Document is part of
--   documentLinks(
--     # Maximum number of entries to list
--     limit: Int = 20

--     # Specifies which end of the link the current document is. Possible values: 'source', 'target'
--     origin: LinkOrigin = any

--     # Skip the first n entries
--     skip: Int = 0
--   ): [DocumentLink!]!

--   # The FileVersion to which this object belongs
--   fileVersion: FileVersion!

--   # The documents which import this Document
--   importedBy(
--     # Maximum number of entries to list
--     limit: Int = 20

--     # Skip the first n entries
--     skip: Int = 0
--   ): [Document!]!

--   # The documents which are imported by this Document
--   imports(
--     # Maximum number of entries to list
--     limit: Int = 20

--     # Skip the first n entries
--     skip: Int = 0
--   ): [Document!]!

--   # The Loc/Id of the document
--   locId: ID!

--   # The OMS in this NativeDocument
--   oms: OMS!
-- }
type NativeDocument = Object "NativeDocument" '[Document]
  '[ Field "fileVersion" FileVersion
   -- , Argument "limit" (Maybe Int) :> Argument "skip" (Maybe Int) :> Argument "origin" (Maybe LinkOrigin) :> Field "documentLinks" [DocumentLink] -- removed due to recursion issue (see the comment at the top of this module).
   -- , Argument "limit" (Maybe Int) :> Argument "skip" (Maybe Int) :> Field "importedBy" [Document] -- removed due to recursion issue (see the comment at the top of this module).
   -- , Argument "limit" (Maybe Int) :> Argument "skip" (Maybe Int) :> Field "imports" [Document] -- removed due to recursion issue (see the comment at the top of this module).
   , Field "locId" Text
   -- , Field "oms" OMS
   ]

-- # An Ontology, Model or Specification (OMS)
-- type OMS implements LocIdBase {
--   # The conservativity status of this OMS
--   conservativityStatus: ConservativityStatus!

--   # The attempts to check this OMS's consistency
--   consistencyCheckAttempts(
--     # Maximum number of entries to list
--     limit: Int = 20

--     # Skip the first n entries
--     skip: Int = 0
--   ): [ConsistencyCheckAttempt!]!

--   # The description of this OMS
--   description: String

--   # The human-friendly name of this OMS
--   displayName: String!

--   # The Document containing this OMS
--   document: Document!

--   # The FileVersion to which this object belongs
--   fileVersion: FileVersion!

--   # The free normal form of this OMS
--   freeNormalForm: OMS

--   # The signature morphism leading to the free normal form
--   freeNormalFormSignatureMorphism: SignatureMorphism

--   # Flag indicating whether this OMS uses freeness
--   labelHasFree: Boolean!

--   # Flag indicating whether this OMS uses hiding
--   labelHasHiding: Boolean!

--   # The Language of this OMS
--   language: Language!

--   # The Loc/Id of the document
--   locId: ID!

--   # The Logic of this OMS
--   logic: Logic!

--   # Mappings of which this OMS is the the source or the target
--   mappings(
--     # Maximum number of entries to list
--     limit: Int = 20

--     # Specifies which end of the link the current OMS is
--     origin: LinkOrigin = any

--     # Skip the first n entries
--     skip: Int = 0
--   ): [Mapping]!

--   # The technical name of this OMS
--   name: String!

--   # The technical name extension of this OMS
--   nameExtension: String!

--   # The index of this OMS by the name+extension
--   nameExtensionIndex: Int!

--   # The Range of the name of this OMS
--   nameFileRange: FileRange

--   # The normal form of this OMS
--   normalForm: OMS

--   # The signature morphism leading to the normal form
--   normalFormSignatureMorphism: SignatureMorphism

--   # The origin of this OMS
--   origin: OMSOrigin!

--   # All sentneces in this OMS
--   sentences(
--     # Maximum number of entries to list
--     limit: Int = 20

--     # Skip the first n entries
--     skip: Int = 0
--   ): [Sentence!]!

--   # The Serialization of this OMS
--   serialization: Serialization

--   # The Signature of this OMS
--   signature: Signature!
-- }
type OMS = Object "OMS" '[LocIdBase]
  '[ Field "conservativityStatus" ConservativityStatus
   -- , Argument "limit" (Maybe Int) :> Argument "skip" (Maybe Int) :> Field "consistencyCheckAttempts" [ConsistencyCheckAttempt] -- removed due to recursion issue (see the comment at the top of this module).
   , Field "description" Text
   , Field "displayName" Text
   -- , Field "document" Document
   , Field "fileVersion" FileVersion
   -- , Field "freeNormalForm" OMS -- removed due to recursion issue (see the comment at the top of this module).
   -- , Field "freeNormalFormSignatureMorphism" SignatureMorphism -- removed due to recursion issue (see the comment at the top of this module).
   , Field "labelHasFree" Bool
   , Field "labelHasHiding" Bool
   , Field "language" Language
   , Field "logic" Logic
   , Field "locId" Text
   -- , Argument "limit" (Maybe Int) :> Argument "skip" (Maybe Int) :> Argument "origin" (Maybe LinkOrigin) :> Field "mappings" [Mapping] -- removed due to recursion issue (see the comment at the top of this module).
   , Field "name" Text
   , Field "nameExtension" Text
   , Field "nameExtensionIndex" Int
   , Field "nameFileRange" (Maybe FileRange)
   -- , Field "normalForm" OMS -- removed due to recursion issue (see the comment at the top of this module).
   -- , Field "normalFormSignatureMorphism" SignatureMorphism -- removed due to recursion issue (see the comment at the top of this module).
   , Field "origin" OMSOrigin
   , Argument "limit" (Maybe Int) :> Argument "skip" (Maybe Int) :> Field "sentences" [Sentence]
   , Field "serialization" Serialization
   , Field "signature" Signature
   ]

-- # Specifies the origin of the OMS
-- enum OMSOrigin {
--   # cofree OMS
--   cofree

--   # alignment
--   dg_alignment

--   # basic OMS
--   dg_basic

--   # basic OMS
--   dg_basic_spec

--   # closed OMS (CASL syntax)
--   dg_closed

--   # data part of an OMS
--   dg_data

--   # empty OMS
--   dg_empty

--   # extension OMS
--   dg_extension

--   # OMS module extraction
--   dg_extract

--   # fitting argument (CASL syntax)
--   dg_fit_spec

--   # fitting view (CASL syntax)
--   dg_fit_view

--   # flattening of an OMS
--   dg_flattening

--   # formal parameter OMS
--   dg_formal_params

--   # import OMS (CASL syntax)
--   dg_imports

--   # instantiation of a parameterized OMS (CASL syntax)
--   dg_inst

--   # computation of strongly connected component
--   dg_integrated_scc

--   # OMS intersection
--   dg_intersect

--   # local OMS (CASL syntax)
--   dg_local

--   # logic coercion OMS
--   dg_logic_coercion

--   # logic qualification
--   dg_logic_qual

--   # computation of normal form or colimit
--   dg_normal_form

--   # proof in the development graph calculus
--   dg_proof

--   # OMS hiding
--   dg_restriction

--   # OMS translation after hiding
--   dg_reveal_translation

--   # used for testing purposes
--   dg_test

--   # OMS translation
--   dg_translation

--   # OMS union
--   dg_union

--   # free OMS
--   free

--   # minimization OMS
--   minimize

--   # free OMS generated by Maude
--   np_free
-- }
data OMSOrigin = Cofree
               | Dg_alignment
               | Dg_basic
               | Dg_basic_spec
               | Dg_closed
               | Dg_data
               | Dg_empty
               | Dg_extension
               | Dg_extract
               | Dg_fit_spec
               | Dg_fit_view
               | Dg_flattening
               | Dg_formal_params
               | Dg_imports
               | Dg_inst
               | Dg_integrated_scc
               | Dg_intersect
               | Dg_local
               | Dg_logic_coercion
               | Dg_logic_qual
               | Dg_normal_form
               | Dg_proof
               | Dg_restriction
               | Dg_reveal_translation
               | Dg_test
               | Dg_translation
               | Dg_union
               | Free
               | Minimize
               | Np_free
                 deriving (Show, Eq, Ord, Generic)
instance GraphQLEnum OMSOrigin
instance ToValue OMSOrigin where
  toValue = toValue . pack . Prelude.map Data.Char.toLower . unpack . unName . enumToValue

-- # An open (unproved) conjecture
-- type OpenConjecture implements Conjecture, LocIdBase, Sentence {
--   # The state of evaluation
--   evaluationState: EvaluationState!

--   # The FileRange of this Sentence's definition
--   fileRange: FileRange

--   # The FileVersion to which this object belongs
--   fileVersion: FileVersion!

--   # The Loc/Id of the document
--   locId: ID!

--   # The name of the Sentence
--   name: String!

--   # The OMS to which this Sentence belongs
--   oms: OMS!

--   # The attempts to prove this Conjecture
--   proofAttempts(
--     # Maximum number of entries to list
--     limit: Int = 20

--     # Skip the first n entries
--     skip: Int = 0
--   ): [ProofAttempt!]!

--   # The reasoning status of this Conjecture
--   reasoningStatus: ReasoningStatus!

--   # The symbols used in this sentence
--   symbols(
--     # Maximum number of entries to list
--     limit: Int = 20

--     # Skip the first n entries
--     skip: Int = 0
--   ): [Symbol!]!

--   # The definitional text of this Sentence
--   text: String!
-- }
type OpenConjecture = Object "OpenConjecture" '[Conjecture]
  -- '[ Field "evaluationState" EvaluationState
  '[ Field "evaluationState" Text
   , Field "fileRange" (Maybe FileRange)
   , Field "fileVersion" FileVersion
   , Field "locId" Text
   , Field "name" Text
   -- , Field "oms" OMS -- removed due to recursion issue (see the comment at the top of this module).
   , Argument "limit" (Maybe Int) :> Argument "skip" (Maybe Int) :> Field "proofAttempts" [ProofAttempt]
   , Field "reasoningStatus" ReasoningStatus
   , Argument "limit" (Maybe Int) :> Argument "skip" (Maybe Int) :> Field "symbols" [Symbol]
   , Field "text" Text
   ]

-- # A selection of premises for reasoning
-- interface PremiseSelection {
--   # The ID of the PremiseSelection
--   id: Int!

--   # The used ReasonerConfiguration
--   reasonerConfiguration: ReasonerConfiguration!

--   # The selected premises
--   selectedPremises(
--     # Maximum number of entries to list
--     limit: Int = 20

--     # Skip the first n entries
--     skip: Int = 0
--   ): [Sentence!]!
-- }
type PremiseSelection = Interface "PremiseSelection"
  '[ Field "id" Int
   -- , Field "reasonerConfiguration" ReasonerConfiguration -- removed due to recursion issue (see the comment at the top of this module).
   , Argument "limit" (Maybe Int) :> Argument "skip" (Maybe Int) :> Field "selectedPremises" [Sentence]
   ]

-- # An attempt to prove a conjecture
-- type ProofAttempt implements ReasoningAttempt {
--   # The conjecture of interest
--   conjecture: Conjecture!

--   # The state of evaluation
--   evaluationState: EvaluationState!

--   # Axioms that have been generated during reasoning
--   generatedAxioms: [GeneratedAxiom!]!

--   # The ID of this ReasoningAttempt
--   id: Int!

--   # The number of this ReasoningAttempt
--   number: Int!

--   # The used ReasonerConfiguration
--   reasonerConfiguration: ReasonerConfiguration!

--   # The output of the Reasoner
--   reasonerOutput: ReasonerOutput

--   # The reasoning status of this ReasoningAttempt
--   reasoningStatus: ReasoningStatus!

--   # The time it took to run the reasoner
--   timeTaken: Int

--   # The used Reasoner
--   usedReasoner: Reasoner!
-- }
type ProofAttempt = Object "ProofAttempt" '[ReasoningAttempt]
  -- '[ Field "evaluationState" EvaluationState
  '[ Field "evaluationState" Text
   -- , Field "conjecture" Conjecture -- removed due to recursion issue (see the comment at the top of this module).
   , Field "generatedAxioms" [GeneratedAxiom]
   , Field "id" Text
   , Field "number" Int
   , Field "reasonerConfiguration" ReasonerConfiguration
   , Field "reasonerOutput" (Maybe ReasonerOutput)
   , Field "reasoningStatus" ReasoningStatus
   , Field "timeTaken" (Maybe Int)
   , Field "usedReasoner" Reasoner
   ]

-- # Base query type
-- type Query {
--   # A GeneratedAxiom
--   generatedAxiom(
--     # The id of the GeneratedAxiom
--     id: Int!
--   ): GeneratedAxiom

--   # A Language for the given ID
--   language(
--     # The ID of the Langauge
--     id: ID!
--   ): Language

--   # A LanguageMapping for the given ID
--   languageMapping(
--     # The ID of the LangaugeMapping
--     id: ID!
--   ): LanguageMapping

--   # A Logic for the given ID
--   logic(
--     # The ID of the Langauge
--     id: ID!
--   ): Logic

--   # A LogicMapping for the given ID
--   logicMapping(
--     # The ID of the LogicMapping
--     id: ID!
--   ): LogicMapping

--   # A PremiseSelection
--   premiseSelection(
--     # The id of the PremiseSelection
--     id: Int!
--   ): PremiseSelection

--   # A Reasoner
--   reasoner(
--     # The id of the Reasoner
--     id: ID!
--   ): Reasoner

--   # A ReasonerConfiguration
--   reasonerConfiguration(
--     # The id of the ReasonerConfiguration
--     id: Int!
--   ): ReasonerConfiguration

--   # A ReasoningAttempt
--   reasoningAttempt(
--     # The id of the ReasoningAttempt
--     id: Int!
--   ): ReasoningAttempt

--   # A Serialization for the given ID
--   serialization(
--     # The ID of the Serialization
--     id: ID!
--   ): Serialization

--   # A Signature
--   signature(
--     # The id of the Signature
--     id: Int!
--   ): Signature

--   # A SignatureMorphism
--   signatureMorphism(
--     # The id of the SignatureMorphism
--     id: Int!
--   ): SignatureMorphism
-- }
type Query = Object "Query" '[]
  -- '[ Argument "id" (Maybe Int) :> Field "generatedAxiom" GeneratedAxiom
  --  , Argument "id" (Maybe Text) :> Field "language" Language
  --  , Argument "id" (Maybe Text) :> Field "languageMapping" LanguageMapping
  --  , Argument "id" (Maybe Text) :> Field "logic" Logic
  --  , Argument "id" (Maybe Text) :> Field "logicMapping" LogicMapping
  --  , Argument "id" (Maybe Int) :> Field "premiseSelection" PremiseSelection
  --  , Argument "id" (Maybe Text) :> Field "reasoner" Reasoner
  --  , Argument "id" (Maybe Int) :> Field "reasoningAttempt" ReasoningAttempt
  --  , Argument "id" (Maybe Text) :> Field "serialization" Serialization
  --  , Argument "id" (Maybe Int) :> Field "signature" Signature
  --  , Argument "id" (Maybe Int) :> Field "signatureMorphism" SignatureMorphism
  --  -- TODO: Add a query field as a replacement for repository/commit
  '[ Argument "location" Text :> Field "library" Library
   ]

-- # A Reasoning system (prover or consistency checker)
-- type Reasoner {
--   # The human-friendly name of this reasoner
--   displayName: String!

--   # The ID of the reasoner
--   id: ID!
-- }
type Reasoner = Object "Reasoner" '[]
  '[ Field "displayName" Text
   , Field "id" Text
   ]

-- # A configuration of a Reasoner for a ReasoningAttempt
-- type ReasonerConfiguration {
--   # The configured Reasoner
--   configuredReasoner: Reasoner

--   # The ID of the ReasonerConfiguration
--   id: Int!

--   # The PremiseSelections that use this configuration
--   premiseSelections: [PremiseSelection!]!

--   # The reasoningAttempts that use this configuration
--   reasoningAttempts: [ReasoningAttempt!]!
-- }
type ReasonerConfiguration = Object "ReasonerConfiguration" '[]
  '[ Field "configuredReasoner" (Maybe Reasoner)
   , Field "id" Int
   , Field "premiseSelections" [PremiseSelection]
   -- , Field "reasoningAttempts" [ReasoningAttempt] -- removed due to recursion issue (see the comment at the top of this module).
   ]

-- # The output of a Reasoner
-- type ReasonerOutput {
--   # The Reasoner that produced this output
--   reasoner: Reasoner!

--   # The ReasoningAttempt in which this axiom has been generated
--   reasoningAttempt: ReasoningAttempt!

--   # The actual output
--   text: String!
-- }
type ReasonerOutput = Object "ReasonerOutput" '[]
  '[ Field "reasoner" Reasoner
   -- , Field "reasoningAttempt" ReasoningAttempt -- removed due to recursion issue (see the comment at the top of this module).
   , Field "text" Text
   ]

-- # An attempt to prove a conjecture or check consistency of an OMS
-- interface ReasoningAttempt {
--   # The state of evaluation
--   evaluationState: EvaluationState!

--   # Axioms that have been generated during reasoning
--   generatedAxioms: [GeneratedAxiom!]!

--   # The ID of this ReasoningAttempt
--   id: Int!

--   # The number of this ReasoningAttempt
--   number: Int!

--   # The used ReasonerConfiguration
--   reasonerConfiguration: ReasonerConfiguration!

--   # The output of the Reasoner
--   reasonerOutput: ReasonerOutput

--   # The reasoning status of this ReasoningAttempt
--   reasoningStatus: ReasoningStatus!

--   # The time it took to run the reasoner
--   timeTaken: Int

--   # The used Reasoner
--   usedReasoner: Reasoner!
-- }
type ReasoningAttempt = Interface "ReasoningAttempt"
  -- '[ Field "evaluationState" EvaluationState
  '[ Field "evaluationState" Text
   , Field "generatedAxioms" [GeneratedAxiom]
   , Field "id" Text
   , Field "number" Int
   , Field "reasonerConfiguration" ReasonerConfiguration
   , Field "reasonerOutput" (Maybe ReasonerOutput)
   , Field "reasoningStatus" ReasoningStatus
   , Field "timeTaken" (Maybe Int)
   , Field "usedReasoner" Reasoner
   ]

-- # Specifies the reasoning status of a Conjecture
-- enum ReasoningStatus {
--   # Contradictory: There are reasoning attempts that found a proof as well as some
--   # that found a counter example. This indicates a malfunction of the reasoning system.
--   CONTR

--   # CounterSatisfiable: A counter example was found.
--   CSA

--   # CounterSatisfiable on a subset of axioms: A counter example was found but only
--   # a subset of the axioms was used. There is no conclusive result.
--   CSAS

--   # Error: A reasoning attempt has failed.
--   ERR

--   # Open: No reasoning attempt has been finished.
--   OPN

--   # ResourceOut: The reasoner ran out of time/memory.
--   RSO

--   # Theorem: A proof was found.
--   THM

--   # Unknown: There is no solution.
--   UNK
-- }
data ReasoningStatus = CONTR
                     | CSA
                     | CSAS
                     | ERR
                     | OPN
                     | RSO
                     | THM
                     | UNK
                       deriving (Show, Eq, Ord, Generic)
instance GraphQLEnum ReasoningStatus
instance ToValue ReasoningStatus where
  toValue = toValue . pack . Prelude.map Data.Char.toLower . unpack . unName . enumToValue

-- # A logical sentence
-- interface Sentence {
--   # The FileRange of this Sentence's definition
--   fileRange: FileRange

--   # The FileVersion to which this object belongs
--   fileVersion: FileVersion!

--   # The Loc/Id of the document
--   locId: ID!

--   # The name of the Sentence
--   name: String!

--   # The OMS to which this Sentence belongs
--   oms: OMS!

--   # The symbols used in this sentence
--   symbols(
--     # Maximum number of entries to list
--     limit: Int = 20

--     # Skip the first n entries
--     skip: Int = 0
--   ): [Symbol!]!

--   # The definitional text of this Sentence
--   text: String!
-- }
type Sentence = Interface "Sentence"
  '[ Field "fileRange" (Maybe FileRange)
   , Field "fileVersion" FileVersion
   , Field "locId" Text
   , Field "name" Text
   -- , Field "oms" OMS -- removed due to recursion issue (see the comment at the top of this module).
   , Argument "limit" (Maybe Int) :> Argument "skip" (Maybe Int) :> Field "symbols" [Symbol]
   , Field "text" Text
   ]

-- # A serialization of a language
-- type Serialization {
--   # The ID of this serialization
--   id: ID!

--   # The language to which this serialization belongs
--   language: Language!

--   # The name of this serialization
--   name: String!
-- }
type Serialization = Object "Serialization" '[]
  '[ Field "id" Text
   , Field "language" Language
   , Field "name" Text
   ]

-- # A signautre of an OMS is a container for the OMS's symbols
-- type Signature {
--   # The signature's symbols in JSON
--   asJson: String!

--   # The ID of this signature
--   id: Int!

--   # OMS that have this signature
--   oms: [OMS!]!

--   # The SignatureMorphisms of which this Signature is the target
--   signatureMorphisms(
--     # Maximum number of entries to list
--     limit: Int = 20

--     # Specifies which end of the link the current Signature is
--     origin: LinkOrigin = any

--     # Skip the first n entries
--     skip: Int = 0
--   ): [SignatureMorphism!]!

--   # The Symbols of this Signature
--   symbols(
--     # Maximum number of entries to list
--     limit: Int = 20

--     # Whether or not only (non-)imported Symbols should be retrieved
--     origin: SymbolOrigin = either

--     # Skip the first n entries
--     skip: Int = 0
--   ): [Symbol!]!
-- }
type Signature = Object "Signature" '[]
  '[ Field "asJson" Text
   , Field "id" Int
   -- , Field "oms" [OMS] -- removed due to recursion issue (see the comment at the top of this module).
   -- , Argument "limit" (Maybe Int) :> Argument "skip" (Maybe Int) :> Argument "origin" (Maybe LinkOrigin) :> Field "signatureMorphisms" [SignatureMorphism] -- removed due to recursion issue (see the comment at the top of this module).
   , Argument "limit" (Maybe Int) :> Argument "skip" (Maybe Int) :> Argument "origin" (Maybe SymbolOrigin) :> Field "symbols" [Symbol]
   ]

-- # A morphism between two Signatures
-- type SignatureMorphism {
--   # The SignatureMorphism's mappings in JSON
--   asJson: String!

--   # The ID of the SignatureMorphism
--   id: Int!

--   # The LogicMapping which this SignatureMorphism uses
--   logicMapping: LogicMapping!

--   # The Mappings that use this SignatureMorphism
--   mappings: [Mapping!]!

--   # The source Signature
--   source: Signature!

--   # The SymbolMappings of this SignatureMorphism
--   symbolMappings: [SymbolMapping!]!

--   # The target Signature
--   target: Signature!
-- }
type SignatureMorphism = Object "SignatureMorphism" '[]
  '[ Field "asJson" Text
   , Field "id" Int
   , Field "logicMapping" LogicMapping
   , Field "source" Signature
   -- , Field "symbolMappings" [SymbolMapping] -- removed due to recursion issue (see the comment at the top of this module).
   , Field "target" Signature
   ]

-- # The SInE premise selection heuristic
-- type SinePremiseSelection implements PremiseSelection {
--   # The maximum number of iterations to be done by the SInE heuristic. The higher,
--   # the more premises are selected. A null value indicates that this feature is disabled.
--   depthLimit: Int!

--   # The ID of the PremiseSelection
--   id: Int!

--   # The number of premises to be selected at most. A null value indicates that this feature is disabled.
--   premiseNumberLimit: Int

--   # The used ReasonerConfiguration
--   reasonerConfiguration: ReasonerConfiguration!

--   # The selected premises
--   selectedPremises(
--     # Maximum number of entries to list
--     limit: Int = 20

--     # Skip the first n entries
--     skip: Int = 0
--   ): [Sentence!]!

--   # Shows in how many Sentences of the OMS a Symbol occurs
--   sineSymbolCommonnesses(
--     # Maximum number of entries to list
--     limit: Int = 20

--     # Skip the first n entries
--     skip: Int = 0
--   ): [SineSymbolCommonness!]!

--   # Shows the tolerance needed for a Symbol to trigger (select) a premise
--   sineSymbolPremiseTriggers(
--     # Maximum number of entries to list
--     limit: Int = 20

--     # Skip the first n entries
--     skip: Int = 0
--   ): [SineSymbolPremiseTrigger!]!

--   # A higher tolerance value causes more premises to be selected. Minimum value: 1.0.
--   tolerance: Float!
-- }
type SinePremiseSelection = Object "SinePremiseSelection" '[PremiseSelection]
  '[ Field "depthLimit" Int
   , Field "id" Int
   , Field "premiseNumberLimit" Int
   -- , Field "reasonerConfiguration" ReasonerConfiguration -- removed due to recursion issue (see the comment at the top of this module).
   , Argument "limit" (Maybe Int) :> Argument "skip" (Maybe Int) :> Field "selectedPremises" [Sentence]
   , Argument "limit" (Maybe Int) :> Argument "skip" (Maybe Int) :> Field "sineSymbolCommonnesses" [SineSymbolCommonness]
   , Argument "limit" (Maybe Int) :> Argument "skip" (Maybe Int) :> Field "sineSymbolPremiseTriggers" [SineSymbolPremiseTrigger]
   , Field "tolerance" Double
   ]

-- # Shows in how many Sentences of the OMS a Symbol occurs
-- type SineSymbolCommonness {
--   # The commonness of the symbol (number of sentences in which it occurs)
--   commonness: Int!

--   # The SinePremiseSelection
--   sinePremiseSelection: SinePremiseSelection!

--   # The Symbol
--   symbol: Symbol!
-- }
type SineSymbolCommonness = Object "SineSymbolCommonness" '[]
  '[ Field "commonness" Int
   -- , Field "sinePremiseSelection" SinePremiseSelection -- removed due to recursion issue (see the comment at the top of this module).
   , Field "symbol" Symbol
   ]

-- # Shows the tolerance needed for a Symbol to trigger (select) a premise
-- type SineSymbolPremiseTrigger {
--   # The tolerance needed for a Symbol to trigger (select) a premise
--   minTolerance: Float!

--   # The premise
--   premise: Sentence!

--   # The SinePremiseSelection
--   sinePremiseSelection: SinePremiseSelection!

--   # The Symbol
--   symbol: Symbol!
-- }
type SineSymbolPremiseTrigger = Object "SineSymbolPremiseTrigger" '[]
  '[ Field "minTolerance" Double
   -- , Field "premise" Sentence -- removed due to recursion issue (see the comment at the top of this module).
   -- , Field "sinePremiseSelection" SinePremiseSelection -- removed due to recursion issue (see the comment at the top of this module).
   , Field "symbol" Symbol
   ]

-- # A (non-logical) symbol
-- type Symbol implements LocIdBase {
--   # The FileRange of this Symbol's definition
--   fileRange: FileRange

--   # The FileVersion to which this object belongs
--   fileVersion: FileVersion!

--   # The fully qualified name of the Symbol
--   fullName: String!

--   # The kind of the Symbol
--   kind: String!

--   # The Loc/Id of the document
--   locId: ID!

--   # The name of the Symbol
--   name: String!

--   # The OMS to which this Symbol belongs to
--   oms: OMS!

--   # The Sentences in which this Symbol occurs
--   sentences(
--     # Maximum number of entries to list
--     limit: Int = 20

--     # Skip the first n entries
--     skip: Int = 0
--   ): [Sentence!]!

--   # The Signatures in which this Symbol occurs
--   signatures(
--     # Maximum number of entries to list
--     limit: Int = 20

--     # Skip the first n entries
--     skip: Int = 0
--   ): [Signature!]!
-- }
type Symbol = Object "Symbol" '[LocIdBase]
  '[ Field "fileRange" (Maybe FileRange)
   , Field "fileVersion" FileVersion
   , Field "fullName" Text
   , Field "kind" Text
   , Field "locId" Text
   , Field "name" Text
   -- , Field "oms" OMS -- removed due to recursion issue (see the comment at the top of this module).
   -- , Argument "limit" (Maybe Int) :> Argument "skip" (Maybe Int) :> Field "sentences" [Sentence] -- removed due to recursion issue (see the comment at the top of this module).
   -- , Argument "limit" (Maybe Int) :> Argument "skip" (Maybe Int) :> Field "signatures" [Signature] -- removed due to recursion issue (see the comment at the top of this module).
   ]

-- # A mapping between two symbols along a SignatureMorphism
-- type SymbolMapping {
--   # The SignatureMorphism to which this SymbolMapping belongs
--   signatureMorphism: SignatureMorphism!

--   # The source symbol
--   source: Symbol!

--   # The target symbol
--   target: Symbol!
-- }
type SymbolMapping = Object "SymbolMapping" '[]
  -- '[ Field "signatureMorphism" SignatureMorphism -- removed due to recursion issue (see the comment at the top of this module).
  '[ Field "source" Symbol
   , Field "target" Symbol
   ]

-- # Specifies which end of the link the current Symbol is
-- enum SymbolOrigin {
--   # The current Symbol is either imported or or not
--   either

--   # The current Symbol is imported
--   imported

--   # The current Symbol is not imported
--   non_imported
-- }
data SymbolOrigin = Either
                  | Imported
                  | Non_imported
                    deriving (Show, Eq, Ord, Generic)
instance GraphQLEnum SymbolOrigin
instance ToValue SymbolOrigin where
  toValue = toValue . pack . Prelude.map Data.Char.toLower . unpack . unName . enumToValue

-- # A theorem (proved conjecture)
-- type Theorem implements Conjecture, LocIdBase, Sentence {
--   # The state of evaluation
--   evaluationState: EvaluationState!

--   # The FileRange of this Sentence's definition
--   fileRange: FileRange

--   # The FileVersion to which this object belongs
--   fileVersion: FileVersion!

--   # The Loc/Id of the document
--   locId: ID!

--   # The name of the Sentence
--   name: String!

--   # The OMS to which this Sentence belongs
--   oms: OMS!

--   # The attempts to prove this Conjecture
--   proofAttempts(
--     # Maximum number of entries to list
--     limit: Int = 20

--     # Skip the first n entries
--     skip: Int = 0
--   ): [ProofAttempt!]!

--   # The reasoning status of this Conjecture
--   reasoningStatus: ReasoningStatus!

--   # The symbols used in this sentence
--   symbols(
--     # Maximum number of entries to list
--     limit: Int = 20

--     # Skip the first n entries
--     skip: Int = 0
--   ): [Symbol!]!

--   # The definitional text of this Sentence
--   text: String!
-- }
type Theorem = Object "Theorem" '[Conjecture]
  -- '[ Field "evaluationState" EvaluationState
  '[ Field "evaluationState" Text
   , Field "fileRange" (Maybe FileRange)
   , Field "fileVersion" FileVersion
   , Field "locId" Text
   , Field "name" Text
   -- , Field "oms" OMS -- removed due to recursion issue (see the comment at the top of this module).
   , Argument "limit" (Maybe Int) :> Argument "skip" (Maybe Int) :> Field "proofAttempts" [ProofAttempt]
   , Field "reasoningStatus" ReasoningStatus
   , Argument "limit" (Maybe Int) :> Argument "skip" (Maybe Int) :> Field "symbols" [Symbol]
   , Field "text" Text
   ]

-- # A warning
-- type Warn implements Diagnosis {
--   # The FileRange that this message is about
--   fileRange: FileRange

--   # The FileVersion which this message is about
--   fileVersion: FileVersion!

--   # The number of this message
--   number: Int!

--   # The actual message
--   text: String!
-- }
type Warn = Object "Warn" '[Diagnosis]
  '[ Field "fileRange" (Maybe FileRange)
   , Field "fileVersion" FileVersion
   , Field "number" Int
   , Field "text" Text
   ]
