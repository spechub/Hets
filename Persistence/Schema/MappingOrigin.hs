module Persistence.Schema.MappingOrigin where

import Data.List (isPrefixOf)
import Database.Persist.TH

data MappingOrigin = SeeTarget
                   | SeeSource
                   | TEST
                   | DGLinkVerif
                   | DGImpliesLink
                   | DGLinkExtension
                   | DGLinkTranslation
                   | DGLinkClosedLenv
                   | DGLinkImports
                   | DGLinkIntersect
                   | DGLinkMorph
                   | DGLinkInst
                   | DGLinkInstArg
                   | DGLinkView
                   | DGLinkAlign
                   | DGLinkFitView
                   | DGLinkFitViewImp
                   | DGLinkProof
                   | DGLinkFlatteningUnion
                   | DGLinkFlatteningRename
                   | DGLinkRefinement
                     deriving Eq

instance Show MappingOrigin where
  show SeeTarget = "see_target"
  show SeeSource = "see_source"
  show TEST = "test"
  show DGLinkVerif = "dg_link_verif"
  show DGImpliesLink = "dg_implies_link"
  show DGLinkExtension = "dg_link_extension"
  show DGLinkTranslation = "dg_link_translation"
  show DGLinkClosedLenv = "dg_link_closed_lenv"
  show DGLinkImports = "dg_link_imports"
  show DGLinkIntersect = "dg_link_intersect"
  show DGLinkMorph = "dg_link_morph"
  show DGLinkInst = "dg_link_inst"
  show DGLinkInstArg = "dg_link_inst_arg"
  show DGLinkView = "dg_link_view"
  show DGLinkAlign = "dg_link_align"
  show DGLinkFitView = "dg_link_fit_view"
  show DGLinkFitViewImp = "dg_link_fit_view_imp"
  show DGLinkProof = "dg_link_proof"
  show DGLinkFlatteningUnion = "dg_link_flattening_union"
  show DGLinkFlatteningRename = "dg_link_flattening_rename"
  show DGLinkRefinement = "dg_link_refinement"

instance Read MappingOrigin where
  readsPrec _ input
    | show SeeTarget `isPrefixOf` input = [(SeeTarget, drop (length $ show SeeTarget) input)]
    | show SeeSource `isPrefixOf` input = [(SeeSource, drop (length $ show SeeSource) input)]
    | show TEST `isPrefixOf` input = [(TEST, drop (length $ show TEST) input)]
    | show DGLinkVerif `isPrefixOf` input = [(DGLinkVerif, drop (length $ show DGLinkVerif) input)]
    | show DGImpliesLink `isPrefixOf` input = [(DGImpliesLink, drop (length $ show DGImpliesLink) input)]
    | show DGLinkExtension `isPrefixOf` input = [(DGLinkExtension, drop (length $ show DGLinkExtension) input)]
    | show DGLinkTranslation `isPrefixOf` input = [(DGLinkTranslation, drop (length $ show DGLinkTranslation) input)]
    | show DGLinkClosedLenv `isPrefixOf` input = [(DGLinkClosedLenv, drop (length $ show DGLinkClosedLenv) input)]
    | show DGLinkImports `isPrefixOf` input = [(DGLinkImports, drop (length $ show DGLinkImports) input)]
    | show DGLinkIntersect `isPrefixOf` input = [(DGLinkIntersect, drop (length $ show DGLinkIntersect) input)]
    | show DGLinkMorph `isPrefixOf` input = [(DGLinkMorph, drop (length $ show DGLinkMorph) input)]
    | show DGLinkInst `isPrefixOf` input = [(DGLinkInst, drop (length $ show DGLinkInst) input)]
    | show DGLinkInstArg `isPrefixOf` input = [(DGLinkInstArg, drop (length $ show DGLinkInstArg) input)]
    | show DGLinkView `isPrefixOf` input = [(DGLinkView, drop (length $ show DGLinkView) input)]
    | show DGLinkAlign `isPrefixOf` input = [(DGLinkAlign, drop (length $ show DGLinkAlign) input)]
    | show DGLinkFitView `isPrefixOf` input = [(DGLinkFitView, drop (length $ show DGLinkFitView) input)]
    | show DGLinkFitViewImp `isPrefixOf` input = [(DGLinkFitViewImp, drop (length $ show DGLinkFitViewImp) input)]
    | show DGLinkProof `isPrefixOf` input = [(DGLinkProof, drop (length $ show DGLinkProof) input)]
    | show DGLinkFlatteningUnion `isPrefixOf` input = [(DGLinkFlatteningUnion, drop (length $ show DGLinkFlatteningUnion) input)]
    | show DGLinkFlatteningRename `isPrefixOf` input = [(DGLinkFlatteningRename, drop (length $ show DGLinkFlatteningRename) input)]
    | show DGLinkRefinement `isPrefixOf` input = [(DGLinkRefinement, drop (length $ show DGLinkRefinement) input)]
    | otherwise = []

derivePersistField "MappingOrigin"
