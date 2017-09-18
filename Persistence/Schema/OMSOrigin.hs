module Persistence.Schema.OMSOrigin where

import Data.List (isPrefixOf)
import Database.Persist.TH

data OMSOrigin = DGEmpty
               | DGBasic
               | DGBasicSpec
               | DGExtension
               | DGLogicCoercion
               | DGTranslation
               | DGUnion
               | DGIntersect
               | DGExtract
               | DGRestriction
               | DGRevealTranslation
               | Free -- From DGFreeOrCofree
               | Cofree -- From DGFreeOrCofree
               | NPFree -- From DGFreeOrCofree
               | Minimize -- From DGFreeOrCofree
               | DGLocal
               | DGClosed
               | DGLogicQual
               | DGData
               | DGFormalParams
               | DGImports
               | DGInst
               | DGFitSpec
               | DGFitView
               | DGProof
               | DGNormalForm
               | DGintegratedSCC
               | DGFlattening
               | DGAlignment
               | DGTest
                 deriving Eq

instance Show OMSOrigin where
  show DGEmpty = "dg_empty"
  show DGBasic = "dg_basic"
  show DGBasicSpec = "dg_basic_spec"
  show DGExtension = "dg_extension"
  show DGLogicCoercion = "dg_logic_coercion"
  show DGTranslation = "dg_translation"
  show DGUnion = "dg_union"
  show DGIntersect = "dg_intersect"
  show DGExtract = "dg_extract"
  show DGRestriction = "dg_restriction"
  show DGRevealTranslation = "dg_reveal_translation"
  show Free = "free"
  show Cofree = "cofree"
  show NPFree = "np_free"
  show Minimize = "minimize"
  show DGLocal = "dg_local"
  show DGClosed = "dg_closed"
  show DGLogicQual = "dg_logic_qual"
  show DGData = "dg_data"
  show DGFormalParams = "dg_formal_params"
  show DGImports = "dg_imports"
  show DGInst = "dg_inst"
  show DGFitSpec = "dg_fit_spec"
  show DGFitView = "dg_fit_view"
  show DGProof = "dg_proof"
  show DGNormalForm = "dg_normal_form"
  show DGintegratedSCC = "dg_integrated_scc"
  show DGFlattening = "dg_flattening"
  show DGAlignment = "dg_alignment"
  show DGTest = "dg_test"

instance Read OMSOrigin where
  readsPrec _ input
    | show DGEmpty `isPrefixOf` input = [(DGEmpty, drop (length $ show DGEmpty) input)]
    | show DGBasic `isPrefixOf` input = [(DGBasic, drop (length $ show DGBasic) input)]
    | show DGBasicSpec `isPrefixOf` input = [(DGBasicSpec, drop (length $ show DGBasicSpec) input)]
    | show DGExtension `isPrefixOf` input = [(DGExtension, drop (length $ show DGExtension) input)]
    | show DGLogicCoercion `isPrefixOf` input = [(DGLogicCoercion, drop (length $ show DGLogicCoercion) input)]
    | show DGTranslation `isPrefixOf` input = [(DGTranslation, drop (length $ show DGTranslation) input)]
    | show DGUnion `isPrefixOf` input = [(DGUnion, drop (length $ show DGUnion) input)]
    | show DGIntersect `isPrefixOf` input = [(DGIntersect, drop (length $ show DGIntersect) input)]
    | show DGExtract `isPrefixOf` input = [(DGExtract, drop (length $ show DGExtract) input)]
    | show DGRestriction `isPrefixOf` input = [(DGRestriction, drop (length $ show DGRestriction) input)]
    | show DGRevealTranslation `isPrefixOf` input = [(DGRevealTranslation, drop (length $ show DGRevealTranslation) input)]
    | show Free `isPrefixOf` input = [(Free, drop (length $ show Free) input)]
    | show Cofree `isPrefixOf` input = [(Cofree, drop (length $ show Cofree) input)]
    | show NPFree `isPrefixOf` input = [(NPFree, drop (length $ show NPFree) input)]
    | show Minimize `isPrefixOf` input = [(Minimize, drop (length $ show Minimize) input)]
    | show DGLocal `isPrefixOf` input = [(DGLocal, drop (length $ show DGLocal) input)]
    | show DGClosed `isPrefixOf` input = [(DGClosed, drop (length $ show DGClosed) input)]
    | show DGLogicQual `isPrefixOf` input = [(DGLogicQual, drop (length $ show DGLogicQual) input)]
    | show DGData `isPrefixOf` input = [(DGData, drop (length $ show DGData) input)]
    | show DGFormalParams `isPrefixOf` input = [(DGFormalParams, drop (length $ show DGFormalParams) input)]
    | show DGImports `isPrefixOf` input = [(DGImports, drop (length $ show DGImports) input)]
    | show DGInst `isPrefixOf` input = [(DGInst, drop (length $ show DGInst) input)]
    | show DGFitSpec `isPrefixOf` input = [(DGFitSpec, drop (length $ show DGFitSpec) input)]
    | show DGFitView `isPrefixOf` input = [(DGFitView, drop (length $ show DGFitView) input)]
    | show DGProof `isPrefixOf` input = [(DGProof, drop (length $ show DGProof) input)]
    | show DGNormalForm `isPrefixOf` input = [(DGNormalForm, drop (length $ show DGNormalForm) input)]
    | show DGintegratedSCC `isPrefixOf` input = [(DGintegratedSCC, drop (length $ show DGintegratedSCC) input)]
    | show DGFlattening `isPrefixOf` input = [(DGFlattening, drop (length $ show DGFlattening) input)]
    | show DGAlignment `isPrefixOf` input = [(DGAlignment, drop (length $ show DGAlignment) input)]
    | show DGTest `isPrefixOf` input = [(DGTest, drop (length $ show DGTest) input)]
    | otherwise = []

derivePersistField "OMSOrigin"
