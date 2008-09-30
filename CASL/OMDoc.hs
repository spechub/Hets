{- |
Module      :  $Header$
Description :  Hets-to-OMDoc conversion
Copyright   :  (c) Elena Digor, Uni Bremen 2005-2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  hiben@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable(Logic)

Output-methods for writing OMDoc
Toplevel module providing the composition of all translations CASL -> OMDoc
Recurses over imported CASL libraries
-}
module CASL.OMDoc
  where

import qualified OMDoc.CASLDefs as Hets
import OMDoc.CASLOutput()
import CASL.Sign()
import CASL.AS_Basic_CASL as ABC
import qualified Common.Id as Id
---import qualified Syntax.AS_Library as ASL

import qualified CASL.Induction as Induction
import qualified Common.Result as Result
import qualified Common.DocUtils as Pretty

import Driver.Options()

--import Common.Utils (joinWith)

import Static.DevGraph()
import qualified Data.Graph.Inductive.Graph as Graph()

-- Often used symbols from HXT
--import Text.XML.HXT.Parser
--  (
--      {- a_name, k_public, k_system, -} emptyRoot
--    , v_1, a_indent, a_output_file
--  )

--import qualified Text.XML.HXT.Parser as HXT hiding (run, trace, when)
--import qualified Text.XML.HXT.DOM.XmlTreeTypes as HXTT hiding (when)

import qualified Data.Map as Map
import qualified Data.Set as Set()
import qualified Common.Lib.Rel as Rel()

import qualified Common.AS_Annotation as Ann

--import Data.List (find)

import Debug.Trace (trace)

import System.Directory()

import Control.Monad()

import OMDoc.Util
import OMDoc.XmlHandling
import OMDoc.OMDocDefs

import qualified OMDoc.OMDocInterface as OMDoc
import qualified OMDoc.OMDocXml as OMDocXML()
import CASL.Logic_CASL()
import qualified Network.URI as URI

-- | translate a single named 'CASLFORMULA' to OMDoc.
--
-- This will result in either an /axiom/- or /definition/-element and a
-- corresponding /presentation/-element preserving the internal (Hets) name.
wrapFormulaCMPOM_CASL::
  GlobalOptions -- ^ HetscatsOpts + debuggin-information
  ->((Ann.Named CASLFORMULA), Int) -- ^ named formula and integer-tag to
                                   --   disambiguate formula
  ->(Map.Map Id.Pos String) -- ^ map of original formula input to create /CMP/-elements
  ->(Either OMDoc.Axiom OMDoc.Definition, OMDoc.Presentation)
wrapFormulaCMPOM_CASL
  go
  (ansen, _)
  poslinemap =
  let
    senxmlid =
      Ann.senAttr ansen
    sens = Ann.sentence ansen
    sposl = Id.getPosList sens
    omformula = processFormulaOM go [] sens
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


processFormulaOM::
  forall f .
  (Pretty.Pretty f)
  =>
  GlobalOptions -- ^ HetscatsOpts + debuggin-information 
  ->[(String, String)] -- ^ variable bindings (Name, Type)
  ->FORMULA f  -- ^ formula to translate
  ->OMDoc.OMElement
  
  -- Quantification
processFormulaOM go vb
  (Quantification q vl f _) =
    let
      currentVarNames = map snd vb
      varbindings = makeVarDeclList vl
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
        (processVarDeclOM vl)
        (processFormulaOM go newBindings f)

-- Conjunction
processFormulaOM go vb
  (Conjunction fl _) =
    OMDoc.mkOMAE
      (
        [ OMDoc.mkOMSE Nothing caslS caslConjunctionS ]
        ++
        (
          foldl
            (\fs f ->
              fs ++ [ processFormulaOM go vb f ]
            )
            []
            fl
        )
      )

-- Disjunction
processFormulaOM go vb
  (Disjunction fl _) =
    OMDoc.mkOMAE
      (
        [ OMDoc.mkOMSE Nothing caslS caslDisjunctionS ]
        ++
        (
          foldl
            (\fs f ->
              fs ++ [ processFormulaOM go vb f ]
            )
            []
            fl
        )
      )
-- Implication
processFormulaOM go vb
  (Implication f1 f2 b _) =
    OMDoc.mkOMAE
      [
          OMDoc.mkOMSE Nothing caslS caslImplicationS
        , processFormulaOM go vb f1
        , processFormulaOM go vb f2
        , processFormulaOM go vb
            ((if b then True_atom Id.nullRange else False_atom Id.nullRange)::(FORMULA f))
      ]

-- Equivalence
processFormulaOM go vb
  (Equivalence f1 f2 _) =
    OMDoc.mkOMAE
      [
          OMDoc.mkOMSE Nothing caslS caslEquivalenceS
        , processFormulaOM go vb f1
        , processFormulaOM go vb f2
      ]
-- Negation
processFormulaOM go vb
  (Negation f _) =
    OMDoc.mkOMAE
      [
          OMDoc.mkOMSE Nothing caslS caslNegationS
        , processFormulaOM go vb f
      ]
-- Predication
processFormulaOM go vb
  (Predication p tl _) =
    OMDoc.mkOMAE
      (
        [
            OMDoc.mkOMSE Nothing caslS caslPredicationS
          , OMDoc.toElement $ createSymbolForPredicationOM $ predSymbName p
        ]
        ++
        (
          foldl
            (\ts t ->
              ts ++ [ processTermOM go vb t ]
            )
            []
            tl
        )
      )
-- Definedness
processFormulaOM go vb
  (Definedness t _ ) =
    OMDoc.mkOMAE
      [
          OMDoc.mkOMSE Nothing caslS caslDefinednessS
        , processTermOM go vb t
      ]
-- Existl_equation
processFormulaOM go vb
  (Existl_equation t1 t2 _) =
    OMDoc.mkOMAE
      [
          OMDoc.mkOMSE Nothing caslS caslExistl_equationS
        , processTermOM go vb t1
        , processTermOM go vb t2
      ]
-- Strong_equation
processFormulaOM go vb
  (Strong_equation t1 t2 _) =
    OMDoc.mkOMAE
      [
          OMDoc.mkOMSE Nothing caslS caslStrong_equationS
        , processTermOM go vb t1
        , processTermOM go vb t2
      ]
-- Membership
processFormulaOM go vb
  (Membership t s _) =
    OMDoc.mkOMAE
      [
          OMDoc.mkOMSE Nothing caslS caslMembershipS
        , processTermOM go vb t
        , OMDoc.toElement $ createSymbolForSortOM s
      ]
-- False_atom
processFormulaOM _ _
  (False_atom _) =
    OMDoc.mkOMSE Nothing caslS caslSymbolAtomFalseS
-- True_atom
processFormulaOM _ _
  (True_atom _) =
    OMDoc.mkOMSE Nothing caslS caslSymbolAtomTrueS
-- Sort_gen_ax
processFormulaOM go vb
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
          constraints
      )
      ++
      (
        case Result.resultToMaybe soCon of
          Nothing -> []
          Just cf ->
              [processFormulaOM go vb (cf :: FORMULA f)]
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
processFormulaOM _ _
  (Mixfix_formula {}) =
    OMDoc.mkOMComment "unsupported : Mixfix_formula"
-- Unparsed_formula
processFormulaOM _ _
  (Unparsed_formula {}) =
    OMDoc.mkOMComment "unsupported : Unparsed_formula"
-- ExtFORMULA
processFormulaOM _ _
  (ExtFORMULA {}) =
    OMDoc.mkOMComment "unsupported : ExtFORMULA"
    
    
-- | translate constraints to OMDoc by fitting the data into
--   artificial operator applications.
--
--  This is used by 'processFormula' and will be obsolete
--  when the formulas generated by 'Induction.inductionScheme' can
--  be read back to constraints.
processConstraintsOM::
  GlobalOptions  
  ->[ABC.Constraint] -- ^ constraints to process
  ->[OMDoc.OMElement]
processConstraintsOM _ [] = []
processConstraintsOM go constraints
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
                    (newCDBase,newCD, newuName) =
                      findOriginId
                        news
                        --" OMDoc.OMDocOutput.processConstrainsOM"
                    (origCDBase, origCD, origuName) =
                      findOriginId
                        origs
                        --" OMDoc.OMDocOutput.processConstrainsOM"
                  in
                  celems ++
                  [
                    OMDoc.mkOMAE
                      [
                          OMDoc.mkOMSE Nothing caslS "constraint-context"
                        , OMDoc.mkOMSE newCDBase newCD newuName
                        , OMDoc.mkOMSE origCDBase origCD origuName
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
-- | create a xml-representation of an operator
processOperatorOM::
  GlobalOptions -- ^ HetscatsOpts + debug information
  ->OP_SYMB -- ^ the operator to process
  ->OMDoc.OMSymbol
      -- ^ the xml-representation of the operator
processOperatorOM _ 
    os =
    let
      e_fname = "OMDoc.OMDocOutput.processOperatorOM: "
      (opbase,oporigin, opxmlid) =
        let
          (opid, _) =
            case os of
              (Qual_op_name op ot _) -> (op, Hets.cv_Op_typeToOpType ot)
              _ -> error (e_fname ++ "Unqualified Operator!")
              --(" " ++ e_fname ++ " " ++ show os)
        in
          findOriginId opid
    in
      OMDoc.mkOMS opbase oporigin opxmlid

{-
-- | Generic function to search for an element where two predicates
-- signal preferred (/equal/) and sufficient (/compatible/) elements
-- respectively.
--
-- If an /equal/ element exists it is returned, else if a /compatible/
-- element exists, it is returned and else 'Nothing' is returned.
preferEqualFindCompatible::
  [a] -- ^ elements to search in
  ->(a->Bool) -- ^ /equality/-predicate
  ->(a->Bool) -- ^ /compatibility/-predicate
  ->Maybe a
preferEqualFindCompatible l isEqual isCompatible =
  case find isEqual l of
    Nothing ->
      find isCompatible l
    x -> x
-}

-- | create a xml-representation from a term (in context of a theory).
--
-- This function is applied recursively to all 'TERM'S inside the given term.
-- 'FORMULA'S inside a 'TERM' are processed by 'processFormulaOM'.
processTermOM::
  forall f .
  (Pretty.Pretty f)
  =>GlobalOptions -- ^ HetcatsOpts + debugging information
  ->[(String, String)] -- ^ variable bindings (Name, Type)
  -> TERM f -- ^ the term to process
  ->OMDoc.OMElement
-- Simple_id
processTermOM _ _
  (Simple_id id' ) =
  OMDoc.toElement
    $
    (OMDoc.mkOMSimpleVar (show id'))
-- Qual_var
processTermOM _ vb
  (Qual_var v s _) =
    if elem (show v) (map snd vb)
      then
        let
          --e_fname = "OMDoc.OMDocOutput.processTermOM@Qual_var: "
          matches = map fst $ filter (\(_, sort) -> (==) (show v) sort) vb
          element =
            let
             (_, _, sortxmlid) =
                findOriginId s
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
          (createTypedVarOM s (show v) )
-- Application
processTermOM go vb
  (Application op termlist _) =
    let
      omterms =
        foldl
          (\ts t ->
            ts ++
              [
                OMDoc.toElement
                  $
                  processTermOM go vb t
              ]
          )
          []
          termlist
    in
      if null omterms
        then
          OMDoc.toElement
            $
            (processOperatorOM go op)
        else
          OMDoc.toElement
            $
            OMDoc.mkOMA
              (
                [
                  OMDoc.toElement
                    $
                    processOperatorOM go op
                ] ++ omterms
              )
-- Cast
processTermOM go vb
  (Cast t _s _) = -- add here a "PROJ" to sort (via show)
    processTermOM go vb t

-- Conditional
processTermOM go vb
  (Conditional t1 f t2 _) =
    OMDoc.toElement
      $
      OMDoc.mkOMA
        [
            OMDoc.toElement $ OMDoc.mkOMS Nothing caslS "IfThenElse"
          , OMDoc.toElement $ processFormulaOM go vb f
          , OMDoc.toElement $ processTermOM go vb t1
          , OMDoc.toElement $ processTermOM go vb t2
        ]
-- Sorted_term is to be ignored in OMDoc (but could be modelled...) (Sample/Simple.casl uses it...)
processTermOM go vb
  (Sorted_term t _ _) =
    processTermOM go vb t
-- Unsupported Terms...
processTermOM _ _ _ =
  error "OMDoc.OMDocOutput.processTermOM: Unsupported Term encountered..."


-- | creates a xml structure describing a Hets-presentation for a symbol
makePresentationForOM::
  XmlName -- ^ Xml-Name (xml:id) of symbol to represent
  ->String -- ^ Hets-representation (as 'String')
  ->OMDoc.Presentation -- ^ Wrapped \"/\<presentation>\<use>.../\"-element
makePresentationForOM xname presstring =
  OMDoc.mkPresentation xname [OMDoc.mkUse "Hets" presstring]


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
  SORT -- ^ sort\/type of variable
  ->String -- ^ name of variable
  ->OMDoc.OMAttribution
createTypedVarOM sort varname =
  OMDoc.mkOMATTR
    (createATPOM sort)
    (OMDoc.mkOMSimpleVar (adjustStringForXmlName varname))
    
    
    
findOriginId ::SORT ->(Maybe OMDoc.OMDocRef, OMDoc.XmlId, OMDoc.XmlId)
findOriginId   
	(Id.Id ts cs _)
	=
  let 
  	(uName', origin', cdbase') = 
  		case ts of
    		[t] | Id.tokStr t == "gnOMS" ->
      			case cs of
              		[uName, origin, cdbase] ->
                  		((show uName), (show origin), (show cdbase))
              		[uName,  origin] -> ((show uName), (show origin), "")
               		_ -> error "unexptected predicate name"
    		_ -> error ""
  	
  	cdbase''=URI.parseURI cdbase'
    --origin=origin'  
  	xmlid=adjustStringForXmlName uName'		
  in 
  	(cdbase'', origin', xmlid)
          
          
         
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
  SORT -- ^ sort\/type
  ->OMDoc.OMAttributionPart
createATPOM sort =
  OMDoc.mkOMATP
    [
      (
          OMDoc.mkOMS Nothing caslS typeS
        , createSymbolForSortOM sort
      )
    ]


-- | create an XML-representation of a 'SORT'.
createSymbolForSortOM::
	SORT -- ^ sort to represent
  ->OMDoc.OMSymbol
createSymbolForSortOM
  s
  =
  let 
  	(sortbase, sortorigin, sortxmlid) = findOriginId s
  in
  	OMDoc.mkOMS sortbase sortorigin sortxmlid
  	
-- | create an xml-representation for a predication
createSymbolForPredicationOM::
	SORT
	->OMDoc.OMSymbol
createSymbolForPredicationOM
	s
	=
  let 
  	(predbase, predorigin, predxmlid) = 
  		findOriginId s
  in
  	OMDoc.mkOMS predbase predorigin predxmlid	


-- | transform a list of variable declarations
-- into a list of (Name, Type) (bindings).
makeVarDeclList::
  [VAR_DECL] -- ^ variable declarations to transform
  ->[(String, String)]
makeVarDeclList vdl =
  process vdl
  where
  process::[VAR_DECL]->[(String, String)]
  process [] = []
  process ( (Var_decl vl s _):vdl' ) =
    let
      (_, _, xmlid) =
        findOriginId
          s
    in
      (
        map
          (\vd ->
            (xmlid, adjustStringForXmlName (show vd))
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
  [VAR_DECL] -- ^ variable declarations
  ->OMDoc.OMBindingVariables
processVarDeclOM vdl =
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
          [ OMDoc.toVariable $ createTypedVarOM s (show vd) ]
        )
        []
        vl
    )
    ++ (processVarDecls vdl')