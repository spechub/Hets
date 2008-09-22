{- |
Module      :  $Header$
Description :  Hets-to-OMDoc conversion
Copyright   :  (c) Elena Digor, Uni Bremen 2005-2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  e.digor@jacobs-university.de
Stability   :  provisional
Portability :  non-portable(Logic)

methods responsible for sentences analysis
-}
module OMDoc.Sentences
  where

import qualified OMDoc.HetsDefs as Hets
import OMDoc.CASLOutput
import CASL.Sign
import CASL.AS_Basic_CASL as ABC
import qualified Common.Id as Id

import qualified CASL.Induction as Induction
import qualified Common.Result as Result
import qualified Common.DocUtils as Pretty
import Common.LibName

import Static.DevGraph
import qualified Data.Graph.Inductive.Graph as Graph

import qualified Data.Map as Map
import qualified Common.AS_Annotation as Ann

import Debug.Trace (trace)

import OMDoc.Util
import OMDoc.XmlHandling
import OMDoc.OMDocDefs

import qualified OMDoc.OMDocInterface as OMDoc
-- | translate a single named 'CASLFORMULA' to OMDoc.
--
-- This will result in either an /axiom/- or /definition/-element and a
-- corresponding /presentation/-element preserving the internal (Hets) name.
wrapFormulaCMPOM::
  GlobalOptions -- ^ HetscatsOpts + debuggin-information
  ->LibEnv -- ^ library environment
  ->LIB_NAME -- ^ library of formula
  ->Graph.Node -- ^ node of formula
  ->[Hets.IdNameMapping] -- ^ mapping of unique names
  ->Hets.CollectionMap
  ->((Ann.Named CASLFORMULA), Int) -- ^ named formula and integer-tag to
                                   --   disambiguate formula
  ->(Map.Map Id.Pos String) -- ^ map of original formula input to create /CMP/-elements
  ->(Either OMDoc.Axiom OMDoc.Definition, OMDoc.Presentation)
wrapFormulaCMPOM
  go
  lenv
  ln
  nn
  uniqueNames
  collectionMap
  (ansen, sennum)
  poslinemap =
  let
    senxmlid =
      case
        filter
          (\((sidwo, snum), _) ->
            (Hets.getIdId $ Hets.woItem sidwo) == (Id.stringToId $ Ann.senAttr ansen)
            && snum == sennum
          )
          $
          Hets.getSensAt
            collectionMap
            (ln, nn)
      of
        [] -> error $
          "OMDoc.OMDocOutput.wrapFormulaCMPOM: No unique name for Sentence \""
          ++ Ann.senAttr ansen ++ "\""
        (_, uName) : _ -> uName
    sens = Ann.sentence ansen
    sposl = Id.getPosList sens
    omformula = processFormulaOM go lenv ln nn uniqueNames collectionMap [] sens
    omobj = OMDoc.mkOMOBJ omformula
    cmptext =
      foldl
        (\cmpt p ->
          cmpt ++ (Map.findWithDefault "" p poslinemap) ++ "\n"
        )
        ""
        sposl
    cmp = OMDoc.mkCMP (OMDoc.MTextText cmptext)
    cmpl =
      if null $ trimString cmptext
        then
          []
        else
          [cmp]
    fmp = OMDoc.FMP Nothing (Left omobj)
    axiom =
      if Ann.isAxiom ansen
        then
          Left $ OMDoc.mkAxiom (adjustStringForXmlName senxmlid) cmpl [fmp]
        else
          Right $ OMDoc.mkDefinition (adjustStringForXmlName senxmlid) [cmp] [fmp]
    pres = makePresentationForOM (adjustStringForXmlName senxmlid) (Ann.senAttr ansen)
  in
    (axiom, pres)

-- | translate a 'FORMULA' into an OMDoc-structure.
--
-- This function is applied recusively on all encountered formulas inside
-- the given formula. 'TERM'S inside the formula are processed by
-- 'processTermOM'.
processFormulaOM::
  forall f .
  (Pretty.Pretty f)
  =>GlobalOptions -- ^ HetcatsOpts + debugging information
  ->LibEnv  -- ^ library environment
  ->LIB_NAME -- ^ library name of formula
  ->Graph.Node -- ^ node of formula
  ->[Hets.IdNameMapping] -- ^ unique name mapping
  ->Hets.CollectionMap
  ->[(String, String)] -- ^ variable bindings (Name, Type)
  ->FORMULA f  -- ^ formula to translate
  ->OMDoc.OMElement
-- Quantification
processFormulaOM go lenv ln nn uN cM vb
  (Quantification q vl f _) =
    let
      currentVarNames = map snd vb
      varbindings = makeVarDeclList ln nn uN cM vl
      newBindings =
        foldl
          (\nb c@(vtn, vnn) ->
            if elem vnn currentVarNames
              then
                map
                  (\o@(vto, vno) ->
                    if vno == vnn
                      then
                        if vto == vtn
                          then
                            Debug.Trace.trace
                              (
                                "Warning: Variable " ++ vtn ++
                                " has been bound a second time (same type)"
                              )
                              o
                          else
                            Debug.Trace.trace
                              (
                                "Warning: Variable " ++ vtn ++ "::" ++ vtn ++
                                " shadows existing variable of type " ++ vto
                              )
                              c
                      else
                        o
                  )
                  nb
              else
                nb ++ [c]
          )
          vb
          varbindings
    in
      OMDoc.mkOMBINDE
        (OMDoc.mkOMS Nothing caslS (quantName q))
        (processVarDeclOM ln nn uN cM vl)
        (processFormulaOM go lenv ln nn uN cM newBindings f)

-- Conjunction
processFormulaOM go lenv ln nn uN cM vb
  (Conjunction fl _) =
    OMDoc.mkOMAE
      (
        [ OMDoc.mkOMSE Nothing caslS caslConjunctionS ]
        ++
        (
          foldl
            (\fs f ->
              fs ++ [ processFormulaOM go lenv ln nn uN cM vb f ]
            )
            []
            fl
        )
      )

-- Disjunction
processFormulaOM go lenv ln nn uN cM vb
  (Disjunction fl _) =
    OMDoc.mkOMAE
      (
        [ OMDoc.mkOMSE Nothing caslS caslDisjunctionS ]
        ++
        (
          foldl
            (\fs f ->
              fs ++ [ processFormulaOM go lenv ln nn uN cM vb f ]
            )
            []
            fl
        )
      )
-- Implication
processFormulaOM go lenv ln nn uN cM vb
  (Implication f1 f2 b _) =
    OMDoc.mkOMAE
      [
          OMDoc.mkOMSE Nothing caslS caslImplicationS
        , processFormulaOM go lenv ln nn uN cM vb f1
        , processFormulaOM go lenv ln nn uN cM vb f2
        , processFormulaOM go lenv ln nn uN cM vb
            ((if b then True_atom Id.nullRange else False_atom Id.nullRange)::(FORMULA f))
      ]

-- Equivalence
processFormulaOM go lenv ln nn uN cM vb
  (Equivalence f1 f2 _) =
    OMDoc.mkOMAE
      [
          OMDoc.mkOMSE Nothing caslS caslEquivalenceS
        , processFormulaOM go lenv ln nn uN cM vb f1
        , processFormulaOM go lenv ln nn uN cM vb f2
      ]
-- Negation
processFormulaOM go lenv ln nn uN cM vb
  (Negation f _) =
    OMDoc.mkOMAE
      [
          OMDoc.mkOMSE Nothing caslS caslNegationS
        , processFormulaOM go lenv ln nn uN cM vb f
      ]
-- Predication
processFormulaOM go lenv ln nn uN cM vb
  (Predication p tl _) =
    OMDoc.mkOMAE
      (
        [
            OMDoc.mkOMSE Nothing caslS caslPredicationS
          , OMDoc.toElement $ createSymbolForPredicationOM go lenv ln nn uN cM p
        ]
        ++
        (
          foldl
            (\ts t ->
              ts ++ [ processTermOM go lenv ln nn uN cM vb t ]
            )
            []
            tl
        )
      )
-- Definedness
processFormulaOM go lenv ln nn uN cM vb
  (Definedness t _ ) =
    OMDoc.mkOMAE
      [
          OMDoc.mkOMSE Nothing caslS caslDefinednessS
        , processTermOM go lenv ln nn uN cM vb t
      ]
-- Existl_equation
processFormulaOM go lenv ln nn uN cM vb
  (Existl_equation t1 t2 _) =
    OMDoc.mkOMAE
      [
          OMDoc.mkOMSE Nothing caslS caslExistl_equationS
        , processTermOM go lenv ln nn uN cM vb t1
        , processTermOM go lenv ln nn uN cM vb t2
      ]
-- Strong_equation
processFormulaOM go lenv ln nn uN cM vb
  (Strong_equation t1 t2 _) =
    OMDoc.mkOMAE
      [
          OMDoc.mkOMSE Nothing caslS caslStrong_equationS
        , processTermOM go lenv ln nn uN cM vb t1
        , processTermOM go lenv ln nn uN cM vb t2
      ]
-- Membership
processFormulaOM go lenv ln nn uN cM vb
  (Membership t s _) =
    OMDoc.mkOMAE
      [
          OMDoc.mkOMSE Nothing caslS caslMembershipS
        , processTermOM go lenv ln nn uN cM vb t
        , OMDoc.toElement $ createSymbolForSortOM ln nn uN cM s
      ]
-- False_atom
processFormulaOM _ _ _ _ _  _ _
  (False_atom _) =
    OMDoc.mkOMSE Nothing caslS caslSymbolAtomFalseS
-- True_atom
processFormulaOM _ _ _ _ _ _ _
  (True_atom _) =
    OMDoc.mkOMSE Nothing caslS caslSymbolAtomTrueS
-- Sort_gen_ax
processFormulaOM go lenv ln nn uN cM vb
  (Sort_gen_ax constraints freetype) =
  let
    soCon = Induction.inductionScheme constraints
  in
    OMDoc.mkOMAE
      (
      [
        OMDoc.mkOMSE
          Nothing
          caslS
          caslSort_gen_axS
      ]
      ++
      (
        processConstraintsOM
          go
          lenv
          ln
          nn
          uN
          cM
          constraints
      )
      ++
      (
        case Result.resultToMaybe soCon of
          Nothing -> []
          Just cf ->
              [processFormulaOM go lenv ln nn uN cM vb (cf :: FORMULA f)]
      )
      ++
      [
        OMDoc.mkOMSE
          Nothing
          caslS
          (if freetype then caslSymbolAtomTrueS else caslSymbolAtomFalseS)
      ]
      )
-- unsupported formulas
-- Mixfix_formula
processFormulaOM _ _ _ _ _ _ _
  (Mixfix_formula {}) =
    OMDoc.mkOMComment "unsupported : Mixfix_formula"
-- Unparsed_formula
processFormulaOM _ _ _ _ _ _ _
  (Unparsed_formula {}) =
    OMDoc.mkOMComment "unsupported : Unparsed_formula"
-- ExtFORMULA
processFormulaOM _ _ _ _ _ _ _
  (ExtFORMULA {}) =
    OMDoc.mkOMComment "unsupported : ExtFORMULA"

-- | creates a xml structure describing a Hets-presentation for a symbol
makePresentationForOM::
  XmlName -- ^ Xml-Name (xml:id) of symbol to represent
  ->String -- ^ Hets-representation (as 'String')
  ->OMDoc.Presentation -- ^ Wrapped \"/\<presentation>\<use>.../\"-element
makePresentationForOM xname presstring =
  OMDoc.mkPresentation xname [OMDoc.mkUse "Hets" presstring]

-- | transform a list of variable declarations
-- into a list of (Name, Type) (bindings).
makeVarDeclList::
  LIB_NAME
  ->Graph.Node
  ->[Hets.IdNameMapping]
  ->Hets.CollectionMap
  ->[VAR_DECL] -- ^ variable declarations to transform
  ->[(String, String)]
makeVarDeclList ln nn uN cM vdl =
  process vdl
  where
  process::[VAR_DECL]->[(String, String)]
  process [] = []
  process ( (Var_decl vl s _):vdl' ) =
    let
      (_, uName) =
        findOriginId
          cM
          uN
          Hets.findIdIdsForId
          (ln, nn)
          s
          " OMDoc.OMDocOutput.makeVarDeclList#process"
    in
      (
        map
          (\vd ->
            (adjustStringForXmlName uName, adjustStringForXmlName (show vd))
          )
          vl
      )
      ++ process vdl'

--data QUANTIFIER = Universal | Existential | Unique_existential
-- Quantifier as CASL Symbol
quantName :: QUANTIFIER->String
quantName Universal = caslSymbolQuantUniversalS
quantName Existential = caslSymbolQuantExistentialS
quantName Unique_existential = caslSymbolQuantUnique_existentialS

-- first newline needs pulling up because we have a list of lists...
-- | transform Hets variable declarations to OpenMath variable bindings.
--
-- Results in something like this :
--
-- @
--   \<OMBVAR>
--     \<OMATTR>
--       \<OMATP>
--          \<OMS cd=\"casl\" name=\"type\"\/>
--          \<OMS cd=\"/libnameOfType1/\" name=\"/typename1/\"\/>
--       \<\/OMATP>
--       \<OMV name=\"/varname1/\"\/>
--     \<\/OMATTR>
--     \<OMATTR>
--       \<OMATP>
--          \<OMS cd=\"casl\" name=\"type\"\/>
--          \<OMS cd=\"/libnameOfType2/\" name=\"/typename2/\"\/>
--       \<\/OMATP>
--       \<OMV name=\"/varname2/\"\/>
--     \<\/OMATTR>
--     /.../
--   \<\/OMBVAR>
-- @
processVarDeclOM::
  LIB_NAME -- ^ libary of variable declaration
  ->Graph.Node -- ^ node
  ->[Hets.IdNameMapping] -- ^ unique name mapping
  ->Hets.CollectionMap
  ->[VAR_DECL] -- ^ variable declarations
  ->OMDoc.OMBindingVariables
processVarDeclOM ln nn uN cM vdl =
  OMDoc.mkOMBVAR
    (processVarDecls vdl)

  where
  processVarDecls::
    [VAR_DECL]
    ->[OMDoc.OMVariable]
  processVarDecls [] = []
  processVarDecls ( (Var_decl vl s _):vdl' ) =
    -- <ombattr><omatp><oms>+</omatp><omv></ombattr>
    (
      foldl
        (\decls vd ->
          decls
          ++
          [ OMDoc.toVariable $ createTypedVarOM ln nn uN cM s (show vd) ]
        )
        []
        vl
    )
    ++ (processVarDecls vdl')

-- | create an xml-representation for a predication
createSymbolForPredicationOM::
  GlobalOptions -- ^ HetcatsOpts + debuggin information
  ->LibEnv -- ^ library environment
  ->LIB_NAME -- ^ library name of predication
  ->Graph.Node -- ^ node of predication
  ->[Hets.IdNameMapping] -- ^ unique name mapping
  ->Hets.CollectionMap
  -> PRED_SYMB -- ^ the predication to process
  ->OMDoc.OMSymbol
createSymbolForPredicationOM _ lenv ln nn uniqueNames collectionMap ps =
    let
      e_fname = "OMDoc.OMDocOutput.createSymbolForPredicationOM: "
      currentNode =
          flip labDG nn
            $ lookupDGraph ln lenv
      currentSign = Hets.getJustCASLSign $ Hets.getCASLSign (dgn_sign currentNode)
      currentRel = sortRel currentSign
      (predxmlid, (predbase, predorigin)) =
        let
          (pid, ptype) =
            case ps of
              (Qual_pred_name pid' pt _) -> (pid', Hets.cv_Pred_typeToPredType pt)
              _ -> error (e_fname ++ "Unqualified Predicate!")
          (origin, uName) =
            findOriginId
              collectionMap
              uniqueNames
              (Hets.findIdPredsForId currentRel ptype)
              (ln, nn)
              pid
              (e_fname)
        in
          (adjustStringForXmlName uName, getNodeNameBaseForXml ln origin)
    in
      OMDoc.mkOMS predbase predorigin predxmlid

-- | create a xml-representation from a term (in context of a theory).
--
-- This function is applied recursively to all 'TERM'S inside the given term.
-- 'FORMULA'S inside a 'TERM' are processed by 'processFormulaOM'.
processTermOM::
  forall f .
  (Pretty.Pretty f)
  =>GlobalOptions -- ^ HetcatsOpts + debugging information
  ->LibEnv -- ^ library environment
  ->LIB_NAME -- ^ library name of term
  ->Graph.Node -- ^ node of term
  ->[Hets.IdNameMapping] -- ^ unique name mapping
  ->Hets.CollectionMap
  ->[(String, String)] -- ^ variable bindings (Name, Type)
  -> TERM f -- ^ the term to process
  ->OMDoc.OMElement
-- Qual_var
processTermOM _ _ ln nn uniqueNames collectionMap vb
  (Qual_var v s _) =
    if elem (show v) (map snd vb)
      then
        let
          e_fname = "OMDoc.OMDocOutput.processTermOM@Qual_var: "
          matches = map fst $ filter (\(_, sort) -> (==) (show v) sort) vb
          element =
            let
              matchingIds =
                Hets.findIdIdsForId
                  collectionMap
                  (ln, nn)
                  s
              sortxmlid =
                case matchingIds of
                  [] ->
                    error (e_fname ++ "Unknown Sort \"" ++ show s ++ "\"")
                  ((_, (_, uN)):r) ->
                    (\x ->
                      if null r
                        then
                          x
                        else
                          Debug.Trace.trace
                            (
                              e_fname ++ " more than one origin for Sort \""
                              ++ x ++ "\""
                            )
                            x
                    )
                    (adjustStringForXmlName uN)
            in
              if elem sortxmlid matches
                then
                  OMDoc.toElement
                    $
                    OMDoc.mkOMCommented
                      (
                        (show v) ++ " is qualified for "
                        ++ (implode ", " matches)
                      )
                      (OMDoc.mkOMSimpleVar (show v))
                else
                  OMDoc.toElement
                    $
                    (
                      OMDoc.mkOMCommented
                        (
                          "Qualification mismatch: Expected one of \""
                          ++ (implode ", " matches)
                          ++ "\" but \"" ++ sortxmlid ++ "\" found..."

                        )
                        $
                        (OMDoc.mkOMSimpleVar (show v))
                    )
        in
          element
      else
        OMDoc.toElement
          $
          (createTypedVarOM ln nn uniqueNames collectionMap s (show v) )
-- Application
processTermOM go lenv ln nn uniqueNames collectionMap vb
  (Application op termlist _) =
    let
      omterms =
        foldl
          (\ts t ->
            ts ++
              [
                OMDoc.toElement
                  $
                  processTermOM go lenv ln nn uniqueNames collectionMap vb t
              ]
          )
          []
          termlist
    in
      if null omterms
        then
          OMDoc.toElement
            $
            (processOperatorOM go lenv ln nn uniqueNames collectionMap op)
        else
          OMDoc.toElement
            $
            OMDoc.mkOMA
              (
                [
                  OMDoc.toElement
                    $
                    processOperatorOM go lenv ln nn uniqueNames collectionMap op
                ] ++ omterms
              )
-- Cast
processTermOM go lenv ln nn uniqueNames collectionMap vb
  (Cast t _s _) = -- add here a "PROJ" to sort (via show)
    processTermOM go lenv ln nn uniqueNames collectionMap vb t

-- Conditional
processTermOM go lenv ln nn uniqueNames collectionMap vb
  (Conditional t1 f t2 _) =
    OMDoc.toElement
      $
      OMDoc.mkOMA
        [
            OMDoc.toElement $ OMDoc.mkOMS Nothing caslS "IfThenElse"
          , OMDoc.toElement $ processFormulaOM go lenv ln nn uniqueNames collectionMap vb f
          , OMDoc.toElement $ processTermOM go lenv ln nn uniqueNames collectionMap vb t1
          , OMDoc.toElement $ processTermOM go lenv ln nn uniqueNames collectionMap vb t2
        ]
-- Sorted_term is to be ignored in OMDoc (but could be modelled...) (Sample/Simple.casl uses it...)
processTermOM go lenv ln nn uniqueNames collectionMap vb
  (Sorted_term t _ _) =
    processTermOM go lenv ln nn uniqueNames collectionMap vb t
-- Unsupported Terms...
processTermOM _ _ _ _ _ _ _ _ =
  error "OMDoc.OMDocOutput.processTermOM: Unsupported Term encountered..."

-- | create an XML-representation of a 'SORT'.
createSymbolForSortOM::
  LIB_NAME -- ^ library of sort
  ->Graph.Node -- ^ node of sort
  ->[Hets.IdNameMapping] -- ^ unique name mapping
  ->Hets.CollectionMap
  ->SORT -- ^ sort to represent
  ->OMDoc.OMSymbol
createSymbolForSortOM
  ln
  nn
  uniqueNames
  collectionMap
  s
  =
    let
      (sortxmlid, (sortbase, sortorigin)) =
        let
          (origin, uName) =
            findOriginId
              collectionMap
              uniqueNames
              Hets.findIdIdsForId
              (ln, nn)
              s
              " OMDoc.OMDocOutput.createSymbolForSortOM"
        in
          (adjustStringForXmlName uName, getNodeNameBaseForXml ln origin)
    in
      OMDoc.mkOMS sortbase sortorigin sortxmlid

-- | translate constraints to OMDoc by fitting the data into
--   artificial operator applications.
--
--  This is used by 'processFormula' and will be obsolete
--  when the formulas generated by 'Induction.inductionScheme' can
--  be read back to constraints.
processConstraintsOM::
  GlobalOptions -- ^ HetcatsOpts + debugging information
  ->LibEnv -- ^ library environment
  ->LIB_NAME -- ^ library of constraints
  ->Graph.Node -- ^ node of constrains
  ->[Hets.IdNameMapping] -- ^ unique name mapping
  ->Hets.CollectionMap
  ->[ABC.Constraint] -- ^ constraints to process
  ->[OMDoc.OMElement]
processConstraintsOM _ _ _ _ _ _ [] = []
processConstraintsOM go lenv ln nn uN cM constraints
  =
    [
        OMDoc.mkOMAE
          (
            [
              OMDoc.mkOMSE Nothing caslS "constraint-definitions"
            ]
            ++
            (
              foldl
                (\celems (ABC.Constraint news ops' origs) ->
                  let
                    (newOrigin, newuName) =
                      findOriginId
                        cM
                        uN
                        Hets.findIdIdsForId
                        (ln, nn)
                        news
                        " OMDoc.OMDocOutput.processConstrainsOM"
                    (origOrigin, origuName) =
                      findOriginId
                        cM
                        uN
                        Hets.findIdIdsForId
                        (ln, nn)
                        origs
                        " OMDoc.OMDocOutput.processConstrainsOM"
                    (newCDBase, newCD) = getNodeNameBaseForXml ln newOrigin
                    (origCDBase, origCD) = getNodeNameBaseForXml ln origOrigin
                  in
                  celems ++
                  [
                    OMDoc.mkOMAE
                      [
                          OMDoc.mkOMSE Nothing caslS "constraint-context"
                        , OMDoc.mkOMSE newCDBase newCD (adjustStringForXmlName newuName)
                        , OMDoc.mkOMSE origCDBase origCD (adjustStringForXmlName origuName)
                        , OMDoc.mkOMAE
                            (
                              [
                                  OMDoc.mkOMSE Nothing caslS "constraint-list"
                              ]
                              ++
                              (
                                foldl
                                  (\vars (op, il) ->
                                    vars ++
                                    [
                                      OMDoc.mkOMAE
                                        [
                                            OMDoc.mkOMSE Nothing caslS "constraint"
                                          , OMDoc.mkOMAE
                                              (
                                                [
                                                    OMDoc.mkOMSE
                                                      Nothing
                                                      caslS
                                                      "constraint-indices"
                                                ]
                                                ++
                                                (
                                                  map OMDoc.mkOMIE il
                                                )
                                              )
                                          , OMDoc.toElement
                                              (
                                              processOperatorOM
                                                (go { processingConstraint = True } )
                                                lenv
                                                ln
                                                nn
                                                uN
                                                cM
                                                op
                                              )
                                        ]
                                    ]
                                  )
                                  []
                                  ops'
                              )
                            )
                      ]
                  ]
                )
                []
                constraints
            )
          )
    ]

findOriginId
  ::Hets.CollectionMap
  ->[Hets.IdNameMapping]
  ->(
      Hets.CollectionMap
      ->(LIB_NAME, Graph.Node)
      ->Id.Id
      ->[(LIB_NAME, (Hets.IdentifierWON, String))]
    )
  ->(LIB_NAME, Graph.Node)
  ->Id.Id
  ->String
  ->(Hets.IdNameMapping, String)
findOriginId
  collMap
  mappings
  searchFun
  loc
  sId
  debugMsg
  =
    case searchFun collMap loc sId of
      [] ->
        error
          (
            "No Origin for \"" ++ (show sId) ++ "\""
            ++ debugMsg ++ " "
            ++ (show (Map.findWithDefault (Debug.Trace.trace "Empty!" Map.empty) loc collMap))
          )
      resultlist@((iln, (idwo, uN)):r) ->
        (\x ->
          if null r
            then
              x
            else
              Debug.Trace.trace
                (
                  "More than one origin for \"" ++ (show  sId) ++ "\" "
                  ++ (show resultlist)
                  ++ debugMsg
                )
                x
        )
        $
        case Hets.getLNGN mappings iln (Hets.woOrigin idwo) of
          Nothing ->
            error
              (
                "Non-existant origin for \""
                ++ (show sId) ++ "\" " ++ show (iln, Hets.woOrigin idwo)
                ++ debugMsg
              )
          (Just o) -> (o, uN)

-- | create an OMDoc-structure to attach type information to a variable.
--
-- Results in something like this :
--
-- @
--   \<OMATTR>
--     \<OMATP>
--        \<OMS cd=\"casl\" name=\"type\"\/>
--        \<OMS cd=\"/libnameOfType/\" name=\"/typename/\"\/>
--     \<\/OMATP>
--     \<OMV name=\"/varname/\"\/>
--   \<\/OMATTR>
-- @
--
-- See 'createATPOM'
createTypedVarOM::
  LIB_NAME -- ^ library of variable
  ->Graph.Node -- ^ node of variable
  ->[Hets.IdNameMapping] -- ^ unique name mapping
  ->Hets.CollectionMap
  ->SORT -- ^ sort\/type of variable
  ->String -- ^ name of variable
  ->OMDoc.OMAttribution
createTypedVarOM ln nn uniqueNames collectionMap sort varname =
  OMDoc.mkOMATTR
    (createATPOM ln nn uniqueNames collectionMap sort)
    (OMDoc.mkOMSimpleVar (adjustStringForXmlName varname))

processOperatorOM::
  GlobalOptions -- ^ HetscatsOpts + debug information
  ->LibEnv -- ^ library environment
  ->LIB_NAME -- ^ library name of operator
  ->Graph.Node -- ^ node of operator
  ->[Hets.IdNameMapping] -- ^ unique name mapping
  ->Hets.CollectionMap
  ->OP_SYMB -- ^ the operator to process
  ->OMDoc.OMSymbol
      -- ^ the xml-representation of the operator
processOperatorOM _ lenv ln nn uniqueNames collectionMap
    os =
    let
      e_fname = "OMDoc.OMDocOutput.processOperatorOM: "
      currentNode =
          flip labDG nn
            $ lookupDGraph ln lenv
      currentSign =
        Hets.getJustCASLSign $ Hets.getCASLSign (dgn_sign currentNode)
      currentRel = sortRel currentSign
      (opxmlid, (opbase, oporigin)) =
        let
          (opid, optype) =
            case os of
              (Qual_op_name op ot _) -> (op, Hets.cv_Op_typeToOpType ot)
              _ -> error (e_fname ++ "Unqualified Operator!")
          (origin, uName) =
            findOriginId
              collectionMap
              uniqueNames
              (Hets.findIdOpsForId currentRel optype)
              (ln, nn)
              opid
              (" " ++ e_fname ++ " " ++ show os)
        in
          (adjustStringForXmlName uName, getNodeNameBaseForXml ln origin)
    in
      OMDoc.mkOMS opbase oporigin opxmlid

-- | create an OMDoc-structure containing type information.
--
-- Results in something like this :
--
-- @
--   \<OMATP>
--     \<OMS cd=\"casl\" name=\"type\"\/>
--     \<OMS cd=\"/libname/\" name=\"/typename/\"\/>
--   \<\/OMATP>
-- @
--
-- See 'createTypedVarOM'
createATPOM::
  LIB_NAME -- ^ library of sort\/type
  ->Graph.Node -- ^ node
  ->[Hets.IdNameMapping] -- ^ unique name mapping
  ->Hets.CollectionMap
  ->SORT -- ^ sort\/type
  ->OMDoc.OMAttributionPart
createATPOM ln nn uniqueNames collectionMap sort =
  OMDoc.mkOMATP
    [
      (
          OMDoc.mkOMS Nothing caslS typeS
        , createSymbolForSortOM ln nn uniqueNames collectionMap sort
      )
    ]
