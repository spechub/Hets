{- |
Module      :  $Header$
Description :  static analysis of CASL architectural specifications
Copyright   :  (c) Maciek Makowski, Warsaw University, C. Maeder 2004-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (via imports)

Static analysis of CASL architectural specifications
   Follows the extended static semantics sketched in Chap. III:5.6
   of the CASL Reference Manual.
-}

module Static.AnalysisArchitecture
    ( anaArchSpec
    , anaUnitSpec
    , anaUnitRef
    ) where

import Driver.Options

import Logic.Logic
import Logic.ExtSign
import Logic.Coerce
import Logic.Grothendieck

import Static.GTheory
import Static.DevGraph
import Static.ArchDiagram
import Static.AnalysisStructured

import Syntax.Print_AS_Architecture ()
import Syntax.AS_Architecture
import Syntax.AS_Structured

import Common.AS_Annotation
import Common.Id
import Common.Result
import Common.Amalgamate
import Common.DocUtils
import qualified Data.Map as Map

import Data.Graph.Inductive.Graph as Graph (Node)

-- | Analyse an architectural specification
-- @
-- ARCH-SPEC ::= BASIC-ARCH-SPEC | GROUP-ARCH-SPEC | ARCH-SPEC-NAME
-- @
anaArchSpec :: LogicGraph -> DGraph
  -> HetcatsOpts  -- ^ should only the structure be analysed?
  -> ARCH_SPEC -> Result (ArchSig, DGraph, ARCH_SPEC)
{- ^ returns 1. the architectural signature of given ARCH-SPEC
2. development graph resulting from structured specs within the arch
spec and 3. ARCH_SPEC after possible conversions -}
anaArchSpec lgraph dg opts archSp = case archSp of
  Basic_arch_spec udd uexpr pos ->
    do (uctx, dg', udd') <- anaUnitDeclDefns lgraph dg opts udd
       (_, usig, _, dg'', uexpr') <-
           anaUnitExpression lgraph dg' opts uctx (item uexpr)
       return (ArchSig (ctx uctx) usig, dg'', Basic_arch_spec udd'
                           (replaceAnnoted uexpr' uexpr) pos)
  Group_arch_spec asp _ -> anaArchSpec lgraph dg opts (item asp)
  Arch_spec_name asn@(Token astr pos) -> case lookupGlobalEnvDG asn dg of
            Just (ArchEntry asig) -> return (asig, dg, archSp)
            _ -> fatal_error (astr ++
                              " is not an architectural specification") pos

-- | Analyse a list of unit declarations and definitions
anaUnitDeclDefns :: LogicGraph -> DGraph
    -> HetcatsOpts -> [Annoted UNIT_DECL_DEFN]
    -> Result (ExtStUnitCtx, DGraph, [Annoted UNIT_DECL_DEFN])
{- ^ returns 1. extended static unit context 2. possibly modified
development graph 3. possibly modified list of unit declarations and
definitions -}
anaUnitDeclDefns lgraph dg opts =
  anaUnitDeclDefns' lgraph dg opts emptyExtStUnitCtx

anaUnitDeclDefns' :: LogicGraph -> DGraph
    -> HetcatsOpts -> ExtStUnitCtx -> [Annoted UNIT_DECL_DEFN]
    -> Result (ExtStUnitCtx, DGraph, [Annoted UNIT_DECL_DEFN])
anaUnitDeclDefns' lgraph dg opts uctx uds = case uds of
  udd : udds -> do
    (uctx', dg', udd') <-
        anaUnitDeclDefn lgraph dg opts uctx (item udd)
    (uctx'', dg'', udds') <-
        anaUnitDeclDefns' lgraph dg' opts uctx' udds
    return (uctx'', dg'', replaceAnnoted udd' udd : udds')
  [] -> return (uctx, dg, [])

alreadyDefinedUnit :: SIMPLE_ID -> String
alreadyDefinedUnit u = "Unit " ++ tokStr u ++ " already declared/defined"

-- | Create a node that represents a union of signatures
nodeSigUnion :: LogicGraph -> DGraph -> [MaybeNode] -> DGOrigin
             -> Result (NodeSig, DGraph)
nodeSigUnion lgraph dg nodeSigs orig =
  do sigUnion@(G_sign lid sigU ind) <- gsigManyUnion lgraph
                                   $ map getMaybeSig nodeSigs
     let nodeContents = newNodeLab emptyNodeName orig
           $ noSensGTheory lid sigU ind
         node = getNewNodeDG dg
         dg' = insNodeDG (node, nodeContents) dg
         inslink dgres nsig = do
             dgv <- dgres
             case nsig of
                 EmptyNode _ -> dgres
                 JustNode (NodeSig n sig) -> do
                     incl <- ginclusion lgraph sig sigUnion
                     return $ snd $ insLEdgeDG
                       (n, node, globDefLink incl SeeTarget) dgv
     dg'' <- foldl inslink (return dg') nodeSigs
     return (NodeSig node sigUnion, dg'')

-- | Analyse unit refs
anaUnitRef :: LogicGraph -> DGraph
             -> HetcatsOpts -> ExtStUnitCtx -> UNIT_REF
             -> Result (ExtStUnitCtx, DGraph, UNIT_REF)
{- ^ returns 1. extended static unit context 2. possibly modified
development graph 3. possibly modified UNIT_DECL_DEFN -}

-- unit declaration
anaUnitRef lgraph dg opts
                   uctx@(buc, _) (Unit_ref un usp pos) =
    do (dns, diag', dg', _) <-
           anaUnitImported lgraph dg opts uctx pos []
       let impSig = toMaybeNode dns
       (usig, dg'', usp') <-
           anaRefSpec lgraph dg' opts impSig usp
       insertBasedUnit lgraph dg'' usig (buc, diag') dns un
         $ Unit_ref un usp' pos

insertBasedUnit :: LogicGraph -> DGraph -> UnitSig -> ExtStUnitCtx
                -> MaybeDiagNode -> UNIT_NAME -> a
                -> Result (ExtStUnitCtx, DGraph, a)
insertBasedUnit lgraph dg'' usig uctx@(buc, diag') dns un@(Token ustr unpos)
  ud' =
       if Map.member un buc
          then plain_error (uctx, dg'', ud') (alreadyDefinedUnit un) unpos
          else case usig of
               UnitSig argSigs resultSig -> do
                      let impSig = toMaybeNode dns
                      (resultSig', dg''') <- nodeSigUnion lgraph dg''
                          (JustNode resultSig : [impSig]) DGImports
                      (basedParUSig, diag''') <- if null argSigs then do
                          (dn', diag'') <- extendDiagramIncl lgraph diag'
                             (case dns of
                                JustDiagNode dn -> [dn]
                                _ -> []) resultSig' ustr
                          return (Based_unit_sig dn', diag'')
                          else return (Based_par_unit_sig dns $
                                         UnitSig argSigs resultSig', diag')
                      return ((Map.insert un basedParUSig buc, diag'''),
                              dg''', ud')

-- | Analyse unit declaration or definition
anaUnitDeclDefn :: LogicGraph -> DGraph
                   -> HetcatsOpts -> ExtStUnitCtx -> UNIT_DECL_DEFN
                   -> Result (ExtStUnitCtx, DGraph, UNIT_DECL_DEFN)
{- ^ returns 1. extended static unit context 2. possibly modified
development graph 3. possibly modified UNIT_DECL_DEFN -}
anaUnitDeclDefn lgraph dg opts uctx@(buc, _) udd = case udd of
  Unit_decl un usp uts pos -> do
       (dns, diag', dg', uts') <-
           anaUnitImported lgraph dg opts uctx pos uts
       let impSig = toMaybeNode dns
       (usig, dg'', usp') <-
           anaRefSpec lgraph dg' opts impSig usp
       insertBasedUnit lgraph dg'' usig (buc, diag') dns un
         $ Unit_decl un usp' uts' pos
  Unit_defn un uexp poss -> do
       (p, usig, diag, dg', uexp') <-
         anaUnitExpression lgraph dg opts uctx uexp
       let ud' = Unit_defn un uexp' poss
       {- it's sufficient to check that un is not mapped in buc, we
          don't need to convert the ExtStUnitCtx to StUnitCtx as the
          domain will be preserved -}
       if Map.member un buc then
          plain_error (uctx, dg', ud') (alreadyDefinedUnit un) $ tokPos un
          else case usig of
               {- we can use Map.insert as there are no mappings for
                  un in ps and bs (otherwise there would have been a
                  mapping in (ctx uctx)) -}
               UnitSig args _ -> if null args then case p of
                           JustDiagNode dn -> return ((Map.insert un
                               (Based_unit_sig dn) buc, diag), dg', ud')
                           _ -> error "anaUnitDeclDefn"
                  else return ((Map.insert un
                                            (Based_par_unit_sig p usig) buc
                                           , diag), dg', ud')

-- | Analyse unit imports
anaUnitImported :: LogicGraph -> DGraph
    -> HetcatsOpts -> ExtStUnitCtx -> Range -> [Annoted UNIT_TERM]
    -> Result (MaybeDiagNode, Diag, DGraph, [Annoted UNIT_TERM])
anaUnitImported lgraph dg opts uctx@(_, diag) poss terms =
  case terms of
  [] -> do
    curl <- lookupCurrentLogic "UnitImported" lgraph
    return (EmptyDiagNode curl, diag, dg, [])
  _ -> do
       (dnsigs, diag', dg', terms') <-
           anaUnitImported' lgraph dg opts uctx terms
       (sig, dg'') <- nodeSigUnion lgraph dg'
                      (map (JustNode . getSigFromDiag) dnsigs) DGImports
       -- check amalgamability conditions
    {- let incl s = propagateErrors (ginclusion lgraph (getSig
                (getSigFromDiag s)) (getSig sig)) -}
       let pos = getPosUnitImported poss
       sink <- inclusionSink lgraph dnsigs sig
       () <- assertAmalgamability opts pos diag' sink
       (dnsig, diag'') <- extendDiagramIncl lgraph diag' dnsigs
                          sig $ showDoc terms ""
       return (JustDiagNode dnsig, diag'', dg'', terms')

anaUnitImported' :: LogicGraph -> DGraph
    -> HetcatsOpts -> ExtStUnitCtx -> [Annoted UNIT_TERM]
    -> Result ([DiagNodeSig], Diag, DGraph, [Annoted UNIT_TERM])
anaUnitImported' lgraph dg opts uctx@(buc, diag) ts = case ts of
    [] -> return ([], diag, dg, [])
    ut : uts -> do
       (dnsig, diag', dg', ut') <-
           anaUnitTerm lgraph dg opts uctx (item ut)
       (dnsigs, diag'', dg'', uts') <-
           anaUnitImported' lgraph dg' opts (buc, diag') uts
       return (dnsig : dnsigs, diag'', dg'', replaceAnnoted ut' ut : uts')

-- | Analyse an unit expression
anaUnitExpression :: LogicGraph -> DGraph
    -> HetcatsOpts -> ExtStUnitCtx -> UNIT_EXPRESSION
    -> Result (MaybeDiagNode, UnitSig, Diag, DGraph, UNIT_EXPRESSION)
anaUnitExpression lgraph dg opts uctx@(buc, diag)
  uexp@(Unit_expression ubs ut poss) = case ubs of
  [] -> do
       (dnsig@(Diag_node_sig _ ns'), diag', dg', ut') <-
           anaUnitTerm lgraph dg opts uctx (item ut)
       return (JustDiagNode dnsig, UnitSig [] ns', diag', dg',
               Unit_expression [] (replaceAnnoted ut' ut) poss)
  _ -> do
       (args, dg', ubs') <-
           anaUnitBindings lgraph dg opts uctx ubs
       (resnsig, _dg'') <- nodeSigUnion lgraph dg'
                           (map (JustNode . snd) args) DGFormalParams
       -- build the extended diagram and new based unit context
       let dexp = showDoc uexp ""
           insNodes diag0 [] buc0 = return ([], diag0, buc0)
           insNodes diag0 ((un, nsig) : args0) buc0 =
               do (dnsig, diag') <- extendDiagramIncl lgraph diag0 []
                           nsig dexp
                  {- we made sure in anaUnitBindings that there's no
                     mapping for un in buc so we can just use
                     Map.insert -}
                  let buc' = Map.insert un (Based_unit_sig dnsig) buc0
                  (dnsigs, diag'', buc'') <- insNodes diag' args0 buc'
                  return (dnsig : dnsigs, diag'', buc'')
       (pardnsigs, diag', buc') <- insNodes diag args buc
       (_, diag'') <- extendDiagramIncl lgraph diag' pardnsigs
                      resnsig dexp
       -- analyse the unit term
       (p@(Diag_node_sig _ pnsig), diag''', dg''', ut') <-
           anaUnitTerm lgraph dg' opts (buc', diag'') (item ut)
       -- check amalgamability conditions
       let pos = getPosUnitExpression uexp
           checkSubSign dnsigs nsup =
             all (\ dnsub -> isSubGsign lgraph (getSig $ getSigFromDiag dnsub)
                  $ getSig nsup) dnsigs
       -- check that signatures in pardnsigs are subsignatures of pnsig
       if checkSubSign pardnsigs pnsig
          then
            do sink <- inclusionSink lgraph (p : pardnsigs) pnsig
               () <- assertAmalgamability opts pos diag''' sink
               -- add new node to the diagram
               curl <- lookupCurrentLogic "UnitExpression" lgraph
               return (EmptyDiagNode curl, UnitSig (map snd args) pnsig,
                       diag''', dg''',
                       Unit_expression ubs' (replaceAnnoted ut' ut) poss)
          else -- report an error
              fatal_error
          ("The body signature does not extend the parameter signatures in\n"
           ++ dexp) pos

{- | Analyse a list of unit bindings. Ensures that the unit names are
not present in extended static unit context and that there are no
duplicates among them. -}
anaUnitBindings :: LogicGraph -> DGraph
    -> HetcatsOpts -> ExtStUnitCtx -> [UNIT_BINDING]
    -> Result ([(SIMPLE_ID, NodeSig)], DGraph, [UNIT_BINDING])
anaUnitBindings lgraph dg opts uctx@(buc, _) bs = case bs of
  [] -> return ([], dg, [])
  Unit_binding un@(Token ustr unpos) usp poss : ubs -> do
       curl <- lookupCurrentLogic "UnitBindings" lgraph
       (usig, dg', usp') <-
           anaUnitSpec lgraph dg opts (EmptyNode curl) usp
       let ub' = Unit_binding un usp' poss
       case usig of
            UnitSig ups nsig -> if not $ null ups then
              plain_error ([], dg', [])
                     ("An argument unit " ++
                      ustr ++ " must not be parameterized") unpos
              else
                do (args, dg'', ubs') <- anaUnitBindings lgraph
                       dg' opts uctx ubs
                   let args' = (un, nsig) : args
                   if Map.member un buc
                      then plain_error (args', dg'', ub' : ubs')
                           (alreadyDefinedUnit un) unpos
                      else case lookup un args of
                           Just _ -> plain_error (args', dg'', ub' : ubs')
                                     (alreadyDefinedUnit un) unpos
                           Nothing -> return (args', dg'', ub' : ubs')

-- | Analyse a list of unit terms
anaUnitTerms :: LogicGraph -> DGraph
    -> HetcatsOpts -> ExtStUnitCtx -> [Annoted UNIT_TERM]
    -> Result ([DiagNodeSig], Diag, DGraph, [Annoted UNIT_TERM])
anaUnitTerms lgraph dg opts uctx@(buc, diag) ts = case ts of
  [] -> return ([], diag, dg, [])
  ut : uts -> do
       (dnsig, diag', dg', ut') <-
           anaUnitTerm lgraph dg opts uctx (item ut)
       (dnsigs, diag'', dg'', uts') <- anaUnitTerms lgraph
               dg' opts (buc, diag') uts
       return (dnsig : dnsigs, diag'', dg'', replaceAnnoted ut' ut : uts')

-- | Analyse an unit term
anaUnitTerm :: LogicGraph -> DGraph
              -> HetcatsOpts -> ExtStUnitCtx -> UNIT_TERM
              -> Result (DiagNodeSig, Diag, DGraph, UNIT_TERM)
anaUnitTerm lgraph dg opts uctx@(buc, diag) utrm =
  let pos = getPosUnitTerm utrm
      utStr = showDoc utrm ""
  in case utrm of
  Unit_reduction ut restr -> do
       (p, diag1, dg1, ut') <-
           anaUnitTerm lgraph dg opts uctx (item ut)
       curl <- lookupCurrentLogic "UnitTerm" lgraph
       (incl, msigma) <- anaRestriction (emptyG_sign curl)
                         (getSig (getSigFromDiag p)) opts restr
       (q@(Diag_node_sig qn _), diag', dg') <-
           extendDiagramWithMorphismRev pos lgraph diag1 dg1 p incl utStr
            (case restr of
                 Hidden _ _ -> DGHiding
                 Revealed _ _ -> DGRevealing)
       case msigma of
                  Nothing ->
                  {- the renaming morphism is just identity, so
                  there's no need to extend the diagram -}
                      return (q, diag', dg',
                                  Unit_reduction (replaceAnnoted ut' ut) restr)
                  Just sigma ->
                      do
                         -- check amalgamability conditions
                         let sink = [(qn, sigma)]
                         () <- assertAmalgamability opts pos diag' sink
                         (q', diag'', dg'') <- extendDiagramWithMorphism pos
                            lgraph diag' dg' q sigma utStr
                             (case restr of
                                Hidden _ _ -> DGHiding
                                Revealed _ _ -> DGRevealing)
                         return (q', diag'', dg'',
                                   Unit_reduction
                                   (replaceAnnoted ut' ut) restr)
  Unit_translation ut ren -> do
       (dnsig@(Diag_node_sig p _), diag1, dg1, ut') <-
           anaUnitTerm lgraph dg opts uctx (item ut)
       -- EmptyNode $ error ... should be replaced with local env!
       gMorph <- anaRenaming lgraph
                 (EmptyNode $ error "Static.AnalysisArchitecture")
                    (getSig (getSigFromDiag dnsig)) opts ren
       let sink = [(p, gMorph)]
       -- check amalamability conditions
       () <- assertAmalgamability opts pos diag1 sink
       (dnsig', diag', dg') <- extendDiagramWithMorphism pos lgraph
           diag1 dg1 dnsig gMorph utStr
                DGTranslation
       return (dnsig', diag', dg', Unit_translation
                         (replaceAnnoted ut' ut) ren)
  Amalgamation uts poss -> do
       (dnsigs, diag1, dg', uts') <-
           anaUnitTerms lgraph dg opts uctx uts
       -- compute sigma
       (sig, dg'') <- nodeSigUnion lgraph dg'
                      (map (JustNode . getSigFromDiag) dnsigs) DGUnion
       -- check amalgamability conditions
       sink <- inclusionSink lgraph dnsigs sig
       () <- assertAmalgamability opts poss diag1 sink
       (q, diag') <- extendDiagramIncl lgraph diag1 dnsigs
                     sig utStr
       return (q, diag', dg'', Amalgamation uts' poss)
  Local_unit udds ut poss -> do
       (uctx', dg1, udds') <-
           anaUnitDeclDefns' lgraph dg opts uctx udds
       (dnsig, diag', dg', ut') <-
           anaUnitTerm lgraph dg1 opts uctx' (item ut)
       return (dnsig, diag', dg',
               Local_unit udds' (replaceAnnoted ut' ut) poss)
  Unit_appl un fargus _ -> do
       let ustr = tokStr un
           argStr = showDoc fargus ""
       case Map.lookup un buc of
            Just (Based_unit_sig dnsig) -> case fargus of
              [] -> return (dnsig, diag, dg, utrm)
              _ -> -- arguments have been given for a parameterless unit
                plain_error (dnsig, diag, dg, utrm)
                  (ustr ++ " is a parameterless unit, "
                   ++ "but arguments have been given: " ++ argStr) pos
            Just (Based_par_unit_sig pI (UnitSig argSigs resultSig)) ->
                do (sigF, dg') <- nodeSigUnion lgraph dg
                       (toMaybeNode pI : map JustNode argSigs) DGFormalParams
                   (morphSigs, dg'', diagA) <-
                       anaFitArgUnits lgraph dg' opts
                            uctx utrm pos argSigs fargus
                   let first (e, _, _) = e
                       second (_, e, _) = e
                       third (_, _, e) = e
                   (sigA, dg''') <- nodeSigUnion lgraph dg''
                       (toMaybeNode pI : map (JustNode . second) morphSigs)
                              DGFitSpec
                   -- compute morphA (\sigma^A)
                   G_sign lidI sigI _ <- return (getMaybeSig (toMaybeNode pI))
                   let idI = mkG_morphism lidI (ext_ide sigI)
                   morphA <- homogeneousMorManyUnion
                             $ idI : map first morphSigs
                   -- compute sigMorExt (\sigma^A(\Delta))
                   (_, gSigMorExt) <- extendMorphism (getSig sigF)
                                     (getSig resultSig) (getSig sigA) morphA
                   -- check amalgamability conditions
                   let sigMorExt = gEmbed gSigMorExt
                       pIL = case pI of
                           JustDiagNode dn -> [dn]
                           _ -> []
                   sink <- inclusionSink lgraph (pIL ++
                                                 map third morphSigs) sigA
                   () <- assertAmalgamability opts pos diagA sink
                   (qB@(Diag_node_sig nqB _), diag') <-
                       extendDiagramIncl lgraph diagA pIL resultSig ""
                   -- insert nodes p^F_i and appropriate edges to the diagram
                   let ins diag0 dg0 [] = return (diag0, dg0)
                       ins diag0 dg0 ((morph, _, targetNode) : morphNodes) =
                           do (dnsig, diag1, dg1) <-
                                extendDiagramWithMorphismRev pos lgraph diag0
                                dg0 targetNode (gEmbed morph) argStr
                                DGFormalParams
                              diag'' <- insInclusionEdges lgraph diag1 [dnsig]
                                        qB
                              ins diag'' dg1 morphNodes
                   (diag'', dg4) <- ins diag' dg''' morphSigs
                   -- check amalgamability conditions
                   (sigR, dg5) <- extendDGraph dg4 resultSig
                                  sigMorExt DGExtension
                   incSink <- inclusionSink lgraph (map third morphSigs) sigR
                   let sink' = (nqB, sigMorExt) : incSink
                   assertAmalgamability opts pos diag'' sink'
                   (q, diag''') <- extendDiagram diag'' qB
                                   sigMorExt sigR utStr
                   diag4 <- insInclusionEdges lgraph diag'''
                            (map third morphSigs) q
                   return (q, diag4, dg5, utrm)
            _ -> fatal_error ("Undefined unit " ++ ustr) pos
  Group_unit_term ut poss -> do
       (dnsig, diag1, dg1, ut') <-
           anaUnitTerm lgraph dg opts uctx (item ut)
       return (dnsig, diag1, dg1, Group_unit_term (replaceAnnoted ut' ut) poss)

-- | Analyse unit arguments
anaFitArgUnits :: LogicGraph -> DGraph
    -> HetcatsOpts -> ExtStUnitCtx -> UNIT_TERM
    -- ^ the whole application for diagnostic purposes
    -> Range
    -- ^ the position of the application (for diagnostic purposes)
    -> [NodeSig]
    -- ^ the signatures of unit's formal parameters
    -> [FIT_ARG_UNIT] -- ^ the arguments for the unit
    -> Result ([(G_morphism, NodeSig, DiagNodeSig)], DGraph, Diag)
anaFitArgUnits lgraph dg opts uctx@(buc, diag)
                  appl pos nodeSigs fArgs = case (nodeSigs, fArgs) of
  (nsig : nsigs, fau : faus) -> do
       (gmorph, nsig', dnsig, dg1, diag1) <-
           anaFitArgUnit lgraph dg opts uctx nsig fau
       (morphSigs, dg', diag') <- anaFitArgUnits lgraph dg1 opts
           (buc, diag1) appl pos nsigs faus
       return ((gmorph, nsig', dnsig) : morphSigs, dg', diag')
  ([], []) -> return ([], dg, diag)
  _ -> plain_error ([], dg, diag)
       ("non-matching number of arguments given in application\n"
                    ++ showDoc appl "") pos

-- | Analyse unit argument
anaFitArgUnit :: LogicGraph -> DGraph
    -> HetcatsOpts -> ExtStUnitCtx -> NodeSig -> FIT_ARG_UNIT
    -> Result (G_morphism, NodeSig, DiagNodeSig, DGraph, Diag)
-- ^ returns 1. the signature morphism 2. the target signature of the morphism
-- 3. the diagram node 4. the modified DGraph 5. the modified diagram
anaFitArgUnit lgraph dg opts uctx nsig
                     (Fit_arg_unit ut symbMap poss) = do
       (p, diag', dg', _) <-
           anaUnitTerm lgraph dg opts uctx (item ut)
       -- compute gMorph (the morphism r|sigma/D(p))
       let adj = adjustPos poss
           gsigmaS = getSig nsig
           gsigmaT = getSig (getSigFromDiag p)
       G_sign lidS sigmaS _ <- return gsigmaS
       G_sign lidT sigmaT _ <- return gsigmaT
       G_symb_map_items_list lid sis <- adj $ homogenizeGM (Logic lidS) symbMap
       sigmaT' <- adj $ coerceSign lidT lidS "" sigmaT
       mor <- if isStructured opts then return (ext_ide sigmaS)
                 else do rmap <- adj $ stat_symb_map_items lid sis
                         rmap' <- adj $ coerceRawSymbolMap lid lidS "" rmap
                         adj $ ext_induced_from_to_morphism lidS rmap'
                             sigmaS sigmaT'
       let gMorph = mkG_morphism lidS mor
       (nsig', dg'') <- extendDGraph dg' nsig (gEmbed gMorph) DGFitSpec
       return (gMorph, nsig', p, dg'', diag')

-- | Analyse unit specification
anaUnitSpec :: LogicGraph
              -> DGraph
              -> HetcatsOpts   -- ^ should only the structure be analysed?
              -> MaybeNode                   -- ^ the signature of imports
              -> UNIT_SPEC -> Result (UnitSig, DGraph, UNIT_SPEC)
-- ^ returns 1. unit signature 2. the development graph resulting from
-- structred specs inside the unit spec and 3. a UNIT_SPEC after possible
-- conversions.
anaUnitSpec lgraph dg opts impsig usp = case usp of
  Unit_type argSpecs resultSpec poss -> case argSpecs of
    [] -> case resultSpec of
      Annoted (Spec_inst spn [] _) _ _ _
        | case lookupGlobalEnvDG spn dg of
            Just (UnitEntry _) -> True
            _ -> False ->
       {- if argspecs are empty and resultspec is a name of unit spec
          then this should be converted to a Spec_name -}
        anaUnitSpec lgraph dg opts impsig (Spec_name spn)
      _ -> do -- a trivial unit type
       (resultSpec', resultSig, dg') <- anaSpec False lgraph
           dg impsig emptyNodeName opts  (item resultSpec)
       return (UnitSig [] resultSig, dg', Unit_type []
                            (replaceAnnoted resultSpec' resultSpec) poss)
    _ -> do -- a non-trivial unit type
       (argSigs, dg1, argSpecs') <- anaArgSpecs lgraph dg opts argSpecs
       (sigUnion, dg2) <- nodeSigUnion lgraph dg1
                          (impsig : map JustNode argSigs) DGFormalParams
       (resultSpec', resultSig, dg3) <- anaSpec True lgraph
           dg2 (JustNode sigUnion)
                emptyNodeName opts (item resultSpec)
       return (UnitSig argSigs resultSig, dg3, Unit_type argSpecs'
                                (replaceAnnoted resultSpec' resultSpec) poss)

  Spec_name usn@(Token ustr pos) -> case lookupGlobalEnvDG usn dg of
    Just (UnitEntry usig) -> return (usig, dg, usp)
    _ -> fatal_error (ustr ++ " is not an unit specification") pos
  Closed_unit_spec usp' _ -> do
    curl <- lookupCurrentLogic "UnitSpec" lgraph
    anaUnitSpec lgraph dg opts (EmptyNode curl) usp'

-- | Analyse refinement specification
anaRefSpec :: LogicGraph -> DGraph
  -> HetcatsOpts      -- ^ should only the structure be analysed?
  -> MaybeNode        -- ^ the signature of imports
  -> REF_SPEC -> Result (UnitSig, DGraph, REF_SPEC)
anaRefSpec lgraph dg just_struct nsig rsp = case rsp of
  Unit_spec asp -> do
       (usig, dg', asp') <-
           anaUnitSpec lgraph dg just_struct nsig asp
       return (usig, dg', Unit_spec asp')
  Arch_unit_spec asp poss -> do
       (ArchSig _ usig, dg', asp') <-
           anaArchSpec lgraph dg just_struct (item asp)
       return (usig, dg', Arch_unit_spec (replaceAnnoted asp' asp) poss)
  -- dummy implementation for the rest
  _ -> error "anaRefSpec"

-- | Analyse a list of argument specifications
anaArgSpecs :: LogicGraph -> DGraph -> HetcatsOpts
             -> [Annoted SPEC]
             -> Result ([NodeSig], DGraph, [Annoted SPEC])
anaArgSpecs lgraph dg opts args = case args of
  [] -> return ([], dg, [])
  argSpec : argSpecs -> do
       l <- lookupLogic "anaArgSpecs" (currentLogic lgraph) lgraph
       (argSpec', argSig, dg') <-
           anaSpec False lgraph dg (EmptyNode l) emptyNodeName
                                           opts (item argSpec)
       (argSigs, dg'', argSpecs') <-
           anaArgSpecs lgraph dg' opts argSpecs
       return (argSig : argSigs, dg'', replaceAnnoted argSpec' argSpec
                          : argSpecs')

{- | Check that given diagram ensures amalgamability along given set
of morphisms -}
assertAmalgamability :: HetcatsOpts          -- ^ the program options
                     -> Range               -- ^ the position (for diagnostics)
                     -> Diag                -- ^ the diagram to be checked
                     -> [(Node, GMorphism)] -- ^ the sink
                     -> Result ()
assertAmalgamability opts pos diag sink =
    do ensAmalg <- homogeneousEnsuresAmalgamability opts pos diag sink
       case ensAmalg of
                     Amalgamates -> return ()
                     NoAmalgamation msg -> plain_error ()
                             ("Amalgamability is not ensured: " ++ msg) pos
                     DontKnow msg -> warning () msg pos

-- | Check the amalgamability assuming common logic for whole diagram
homogeneousEnsuresAmalgamability :: HetcatsOpts  -- ^ the program options
                                 -> Range  -- ^ the position (for diagnostics)
                                 -> Diag   -- ^ the diagram to be checked
                                 -> [(Node, GMorphism)] -- ^ the sink
                                 -> Result Amalgamates
homogeneousEnsuresAmalgamability opts pos diag sink = case sink of
                 [] -> plain_error defaultDontKnow
                       "homogeneousEnsuresAmalgamability: Empty sink" pos
                 lab:_ -> do let (_, mor) = lab
                                 sig = cod mor
                             G_sign lid _ _<- return sig
                             hDiag <- homogeniseDiagram lid diag
                             hSink <- homogeniseSink lid sink
                             ensures_amalgamability lid (caslAmalg opts,
                                        hDiag, hSink, (diagDesc diag))

-- | Get a position within the source file of a UNIT-TERM
getPosUnitTerm :: UNIT_TERM -> Range
getPosUnitTerm ut = case ut of
  Unit_reduction _ restr -> case restr of
    -- obtain position from RESTRICTION
               Hidden _ poss -> poss
               Revealed _ poss -> poss
  Unit_translation _ (Renaming _ poss) -> poss
  Amalgamation _ poss -> poss
  Local_unit _ _ poss -> poss
  Unit_appl u _ poss -> appRange (tokPos u) poss
  Group_unit_term _ poss -> poss

-- | Get a position within the source file of UNIT-IMPORTED
getPosUnitImported :: Range -> Range
getPosUnitImported (Range ps) = Range $ case ps of
                          [] -> []
                          _ : qs -> if null qs then ps else qs

-- | Get a position within the source file of UNIT-EXPRESSION
getPosUnitExpression :: UNIT_EXPRESSION -> Range
getPosUnitExpression (Unit_expression _ (Annoted ut _ _ _) poss) =
    appRange (getPosUnitTerm ut) poss
