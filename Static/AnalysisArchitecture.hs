{- | 
   Module      :  $Header$
   Author      :  Maciek Makowski
   Year        :  2004
   Copyright   :  (c) Maciek Makowski, Warsaw University 2004
   Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

   Maintainer  :  hets@tzi.de
   Stability   :  provisional
   Portability :  non-portable (via imports)

   Analysis of architectural specifications.

   Follows the extended static semantics sketched in Chap. III:5.6
   of the CASL Reference Manual.
-}

module Static.AnalysisArchitecture (ana_ARCH_SPEC, ana_UNIT_SPEC)
where

import Driver.Options
import Logic.Logic
import Logic.Grothendieck
import Common.Lib.Graph
import Static.DevGraph
import Static.ArchDiagram
import Syntax.AS_Architecture
import Syntax.AS_Structured
import Static.AnalysisStructured
import Common.AS_Annotation
import Common.Id
import Common.Result
import Common.Amalgamate
import Common.Lib.Graph
import Common.PrettyPrint
import qualified Common.Lib.Map as Map
import Syntax.Print_AS_Architecture

-- | Analyse an architectural specification
-- @
-- ARCH-SPEC ::= BASIC-ARCH-SPEC | GROUP-ARCH-SPEC | ARCH-SPEC-NAME
-- @
ana_ARCH_SPEC :: LogicGraph -> AnyLogic    -- ^ the default logic
              -> GlobalContext -> AnyLogic -- ^ current logic
              -> HetcatsOpts                      -- ^ should only the structure be analysed?
              -> ARCH_SPEC -> Result (ArchSig, DGraph, ARCH_SPEC)
-- ^ returns 1. the architectural signature of given ARCH-SPEC 2. development graph resulting from
-- structured specs within the arch spec and 3. ARCH_SPEC after possible conversions

-- BASIC-ARCH-SPEC
ana_ARCH_SPEC lgraph defl gctx@(gannos, genv, _) curl opts (Basic_arch_spec udd uexpr pos) = 
    do (uctx, dg', udd') <- ana_UNIT_DECL_DEFNS lgraph defl gctx curl opts udd 
       (_, usig, _, dg'', uexpr') <- ana_UNIT_EXPRESSION lgraph defl (gannos, genv, dg') curl opts uctx (item uexpr)
       return ((ctx uctx, usig), dg'', Basic_arch_spec udd' (replaceAnnoted uexpr' uexpr) pos)
-- GROUP-ARCH-SPEC
ana_ARCH_SPEC lgraph defl gctx curl opts (Group_arch_spec asp _) = 
    ana_ARCH_SPEC lgraph defl gctx curl opts (item asp)
-- ARCH-SPEC-NAME
ana_ARCH_SPEC _ defl (_, genv, dg) _ _ asp@(Arch_spec_name asn@(Token _ pos)) = 
    do case Map.lookup asn genv of
            Nothing -> plain_error ((emptyStUnitCtx, (emptyUnitSig defl)), dg, asp)
                                   ("Undefined architectural specification " ++ showPretty asn "")
                                   pos
            Just (ArchEntry asig) -> return (asig, dg, asp)
            _ -> plain_error ((emptyStUnitCtx, (emptyUnitSig defl)), dg, asp)
                             ((showPretty asn "") ++ " is not an architectural specification")
                             pos


-- | Analyse a list of unit declarations and definitions
ana_UNIT_DECL_DEFNS :: LogicGraph -> AnyLogic -> GlobalContext -> AnyLogic 
                    -> HetcatsOpts -> [Annoted UNIT_DECL_DEFN] 
                    -> Result (ExtStUnitCtx, DGraph, [Annoted UNIT_DECL_DEFN])
-- ^ returns 1. extended static unit context 2. possibly modified development graph
-- 3. possibly modified list of unit declarations and definitions
ana_UNIT_DECL_DEFNS lgraph defl gctx curl opts udds = 
    ana_UNIT_DECL_DEFNS' lgraph defl gctx curl opts emptyExtStUnitCtx udds

ana_UNIT_DECL_DEFNS' :: LogicGraph -> AnyLogic -> GlobalContext -> AnyLogic -> HetcatsOpts 
                     -> ExtStUnitCtx -> [Annoted UNIT_DECL_DEFN] 
                     -> Result (ExtStUnitCtx, DGraph, [Annoted UNIT_DECL_DEFN])
ana_UNIT_DECL_DEFNS' _ _ (_, _, dg) _ _ uctx [] =
    do return (uctx, dg, [])
ana_UNIT_DECL_DEFNS' lgraph defl gctx@(gannos, genv, _) curl opts uctx (udd : udds) =
    do (uctx', dg', udd') <- ana_UNIT_DECL_DEFN lgraph defl gctx curl opts uctx (item udd) 
       (uctx'', dg'', udds') <- ana_UNIT_DECL_DEFNS' lgraph defl (gannos, genv, dg') curl opts uctx' udds
       return (uctx'', dg'', (replaceAnnoted udd' udd) : udds')


-- | Analyse unit refs
ana_UNIT_REF :: LogicGraph -> AnyLogic -> GlobalContext -> AnyLogic 
              -> HetcatsOpts -> ExtStUnitCtx -> UNIT_REF -> Result (ExtStUnitCtx, DGraph, UNIT_REF)
-- ^ returns 1. extended static unit context 2. possibly modified development graph 
-- 3. possibly modified UNIT_DECL_DEFN

-- unit declaration
ana_UNIT_REF lgraph defl gctx@(gannos, genv, _) curl opts 
                   uctx@(buc, _) (Unit_ref un@(Token _ unpos) usp pos) =
    do (dns, diag', dg', uts') <- ana_UNIT_IMPORTED lgraph defl gctx curl opts uctx pos []
       let impSig = getSigFromDiag dns
       (usig, dg'', usp') <- ana_REF_SPEC lgraph defl (gannos, genv, dg') curl opts impSig usp
       let ud' = Unit_ref un usp' pos
       if Map.member un buc 
          then
          plain_error (uctx, dg'', ud')
                      ("Unit " ++ showPretty un " already declared/defined")
                      unpos
          else
          case usig of
               Par_unit_sig (argSigs, resultSig) -> 
                   do (resultSig', dg''') <- nodeSigUnion lgraph dg'' (resultSig : [impSig]) DGImports
                      let basedParUSig = Based_par_unit_sig (dns, (argSigs, resultSig'))
                      return ((Map.insert un basedParUSig buc, diag'), dg''', ud')
               Unit_sig nsig -> 
                   do (nsig', dg''') <- nodeSigUnion lgraph dg'' (impSig : [nsig]) DGImports
                      (dn', diag'') <- extendDiagramIncl lgraph diag' [dns] nsig' (renderText Nothing (printText un))
                      return ((Map.insert un (Based_unit_sig dn') buc, diag''), dg''', ud')

-- | Analyse unit declaration or definition
ana_UNIT_DECL_DEFN :: LogicGraph -> AnyLogic -> GlobalContext -> AnyLogic 
                   -> HetcatsOpts -> ExtStUnitCtx -> UNIT_DECL_DEFN -> Result (ExtStUnitCtx, DGraph, UNIT_DECL_DEFN)
-- ^ returns 1. extended static unit context 2. possibly modified development graph 
-- 3. possibly modified UNIT_DECL_DEFN

-- unit declaration
ana_UNIT_DECL_DEFN lgraph defl gctx@(gannos, genv, _) curl opts
                   uctx@(buc, _) (Unit_decl un@(Token _ unpos) usp uts pos) =
    do (dns, diag', dg', uts') <- ana_UNIT_IMPORTED lgraph defl gctx curl opts uctx pos uts
       let impSig = getSigFromDiag dns
       (usig, dg'', usp') <- ana_REF_SPEC lgraph defl (gannos, genv, dg') curl opts impSig usp
       let ud' = Unit_decl un usp' uts' pos
       if Map.member un buc
          then
          plain_error (uctx, dg'', ud')
                      ("Unit " ++ showPretty un " already declared/defined")
                      unpos
          else
          case usig of
               Par_unit_sig (argSigs, resultSig) ->
                   do (resultSig', dg''') <- nodeSigUnion lgraph dg'' (resultSig : [impSig]) DGImports
                      let basedParUSig = Based_par_unit_sig (dns, (argSigs, resultSig'))
                      return ((Map.insert un basedParUSig buc, diag'), dg''', ud')
               Unit_sig nsig ->
                   do (nsig', dg''') <- nodeSigUnion lgraph dg'' (impSig : [nsig]) DGImports
                      (dn', diag'') <- extendDiagramIncl lgraph diag' [dns] nsig' (renderText Nothing (printText un))
                      return ((Map.insert un (Based_unit_sig dn') buc, diag''), dg''', ud')
-- unit definition
ana_UNIT_DECL_DEFN lgraph defl gctx curl opts uctx@(buc, _) 
                   (Unit_defn un@(Token _ unpos) uexp poss) =
    do (p, usig, diag, dg', uexp') <- ana_UNIT_EXPRESSION lgraph defl gctx curl opts uctx uexp
       let ud' = Unit_defn un uexp' poss
       {- it's sufficient to check that un is not mapped in buc, we don't need
          to convert the ExtStUnitCtx to StUnitCtx as the domain will be preserved -}
       if Map.member un buc 
          then
          plain_error (uctx, dg', ud')
                      ("Unit " ++ showPretty un " already defined/declared")
                      unpos
          else
          case usig of
               {- we can use Map.insert as there are no mappings for un in ps and bs
                  (otherwise there would have been a mapping in (ctx uctx)) -}
               Unit_sig _ -> return ((Map.insert un (Based_unit_sig p) buc, diag),
                                     dg', ud')
               Par_unit_sig parusig -> return ((Map.insert un (Based_par_unit_sig (p, parusig)) buc, diag),
                                               dg', ud')


-- | Analyse unit imports
ana_UNIT_IMPORTED :: LogicGraph -> AnyLogic -> GlobalContext -> AnyLogic 
                  -> HetcatsOpts -> ExtStUnitCtx -> [Pos] -> [Annoted UNIT_TERM] 
                  -> Result (DiagNodeSig, Diag, DGraph, [Annoted UNIT_TERM])
ana_UNIT_IMPORTED _ _ (_, _, dg) curl _ (_, diag) _ [] =
    do return (Empty_node curl, diag, dg, [])
ana_UNIT_IMPORTED lgraph defl gctx curl opts uctx poss terms =
    do (dnsigs, diag', dg', terms') <- ana_UNIT_IMPORTED' lgraph defl gctx curl opts uctx terms 
       (sig, dg'') <- nodeSigUnion lgraph dg' (map getSigFromDiag dnsigs) DGImports
       -- check amalgamability conditions
       -- let incl s = propagateErrors (ginclusion lgraph (getSig (getSigFromDiag s)) (getSig sig))
       let pos = getPos_UNIT_IMPORTED poss
       sink <- inclusionSink lgraph dnsigs sig
       () <- assertAmalgamability opts pos diag' sink
       (dnsig, diag'') <- extendDiagramIncl lgraph diag' dnsigs sig (renderText Nothing (printText terms))
       return (dnsig, diag'', dg'', terms')

ana_UNIT_IMPORTED' :: LogicGraph -> AnyLogic -> GlobalContext -> AnyLogic 
                   -> HetcatsOpts -> ExtStUnitCtx -> [Annoted UNIT_TERM] 
                   -> Result ([DiagNodeSig], Diag, DGraph, [Annoted UNIT_TERM])
ana_UNIT_IMPORTED' _ _ (_, _, dg) _ _ (_, diag) [] =
    do return ([], diag, dg, [])
ana_UNIT_IMPORTED' lgraph defl gctx@(gannos, genv, _) curl opts uctx@(buc, _) (ut : uts) =
    do (dnsig, diag', dg', ut') <- ana_UNIT_TERM lgraph defl gctx curl opts uctx (item ut)
       (dnsigs, diag'', dg'', uts') <- ana_UNIT_IMPORTED' lgraph defl (gannos, genv, dg') curl opts (buc, diag') uts
       return (dnsig : dnsigs, diag'', dg'', (replaceAnnoted ut' ut) : uts')


-- | Analyse an unit expression
ana_UNIT_EXPRESSION :: LogicGraph -> AnyLogic -> GlobalContext -> AnyLogic 
                    -> HetcatsOpts -> ExtStUnitCtx -> UNIT_EXPRESSION 
                    -> Result (DiagNodeSig, UnitSig, Diag, DGraph, UNIT_EXPRESSION)
ana_UNIT_EXPRESSION lgraph defl gctx curl opts uctx (Unit_expression [] ut poss) =
    do (dnsig, diag', dg', ut') <- ana_UNIT_TERM lgraph defl gctx curl opts uctx (item ut)
       return (dnsig, Unit_sig (getSigFromDiag dnsig), diag', dg', 
               Unit_expression [] (replaceAnnoted ut' ut) poss)
ana_UNIT_EXPRESSION lgraph defl gctx@(gannos, genv, _) curl opts 
                    uctx@(buc, diag) exp@(Unit_expression ubs ut poss) =
    do (args, dg', ubs') <- ana_UNIT_BINDINGS lgraph defl gctx curl opts uctx ubs
       (resnsig, dg'') <- nodeSigUnion lgraph dg' (map snd args) DGFormalParams
       -- build the extended diagram and new based unit context
       let insNodes diag [] buc = do return ([], diag, buc)
           insNodes diag ((un, nsig) : args) buc = 
               do (dnsig, diag') <- extendDiagramIncl lgraph diag [] nsig (renderText Nothing (printText exp))
                  {- we made sure in ana_UNIT_BINDINGS that there's no mapping for un in buc
                     so we can just use Map.insert -}
                  let buc' = Map.insert un (Based_unit_sig dnsig) buc
                  (dnsigs, diag'', buc'') <- insNodes diag' args buc'
                  return (dnsig : dnsigs, diag'', buc'')
       (pardnsigs, diag', buc') <- insNodes diag args buc
       (_, diag'') <- extendDiagramIncl lgraph diag' pardnsigs resnsig (renderText Nothing (printText exp))
       -- analyse the unit term
       (p@(Diag_node_sig _ pnsig), diag''', dg''', ut') <- ana_UNIT_TERM lgraph defl (gannos, genv, dg'') 
                                                                     curl opts (buc', diag'') (item ut)
       -- check amalgamability conditions
       let pos = getPos_UNIT_EXPRESSION exp
           checkSubSign [] _ = True
           checkSubSign (dnsub : dnsigs) nsup =
               if is_subgsign (getSig (getSigFromDiag dnsub)) (getSig nsup) 
                  then checkSubSign dnsigs nsup
                  else False
       -- check that signatures in pardnsigs are subsignatures of pnsig
       if checkSubSign pardnsigs pnsig 
          then 
            do sink <- inclusionSink lgraph (p : pardnsigs) pnsig
               () <- assertAmalgamability opts pos diag''' sink
               -- add new node to the diagram
               (z, diag4) <- extendDiagramIncl lgraph diag''' [] (EmptyNode curl) (renderText Nothing (printText exp))
               return (z, Par_unit_sig (map snd args, getSigFromDiag p), diag4, dg''', 
                       Unit_expression ubs' (replaceAnnoted ut' ut) poss)
          else -- report an error
            do (z, diag4) <- extendDiagramIncl lgraph diag''' [] (EmptyNode curl) (renderText Nothing (printText exp))
               plain_error (z, Par_unit_sig (map snd args, getSigFromDiag p), diag4, dg''', 
                            Unit_expression ubs' (replaceAnnoted ut' ut) poss)
                            ("The body signature does not extend the parameter signatures in\n" ++ (showPretty exp ""))
                            pos



-- | Analyse a list of unit bindings. Ensures that the unit names are not present
-- in extended static unit context and that there are no duplicates among them.
ana_UNIT_BINDINGS :: LogicGraph -> AnyLogic -> GlobalContext -> AnyLogic
                  -> HetcatsOpts -> ExtStUnitCtx -> [UNIT_BINDING]
                  -> Result ([(SIMPLE_ID, NodeSig)], DGraph, [UNIT_BINDING])
ana_UNIT_BINDINGS _ _ (_, _, dg) _ _ _ [] =
    do return ([], dg, [])
ana_UNIT_BINDINGS lgraph defl gctx@(gannos, genv, _) curl opts uctx@(buc, _) 
                  ((Unit_binding un@(Token _ unpos) usp poss) : ubs) =
    do (usig, dg', usp') <- ana_UNIT_SPEC lgraph defl gctx curl opts (EmptyNode curl) usp
       let ub' = Unit_binding un usp' poss
       case usig of 
            Par_unit_sig _ -> plain_error ([], dg', [])
                                          ("An argument unit " ++ showPretty un " must not be parameterized")
                                          unpos
            Unit_sig nsig ->
                do (args, dg'', ubs') <- ana_UNIT_BINDINGS lgraph defl (gannos, genv, dg') curl opts uctx ubs
                   let args' = (un, nsig) : args
                   if Map.member un buc
                      then
                      plain_error (args', dg'', ub' : ubs')
                                  ("Unit " ++ showPretty un " already declared/defined")
                                  unpos
                      else
                      case lookup un args of
                           Just _ -> plain_error (args', dg'', ub' : ubs')
                                                 ("Unit " ++ showPretty un " already declared/defined")
                                                 unpos
                           Nothing -> return (args', dg'', ub' : ubs')


-- | Analyse a list of unit terms
ana_UNIT_TERMS :: LogicGraph -> AnyLogic -> GlobalContext -> AnyLogic 
               -> HetcatsOpts -> ExtStUnitCtx -> [Annoted UNIT_TERM]
               -> Result ([DiagNodeSig], Diag, DGraph, [Annoted UNIT_TERM])
ana_UNIT_TERMS _ _ (_, _, dg) _ _ (_, diag) [] =
    do return ([], diag, dg, [])
ana_UNIT_TERMS lgraph defl gctx@(gannos, genv, _) curl opts uctx@(buc, _) (ut : uts) =
    do (dnsig, diag', dg', ut') <- ana_UNIT_TERM lgraph defl gctx curl opts uctx (item ut)
       (dnsigs, diag'', dg'', uts') <- ana_UNIT_TERMS lgraph defl (gannos, genv, dg') curl opts (buc, diag') uts
       return (dnsig : dnsigs, diag'', dg'', (replaceAnnoted ut' ut) : uts')


-- | Analyse an unit term
ana_UNIT_TERM :: LogicGraph -> AnyLogic -> GlobalContext -> AnyLogic 
              -> HetcatsOpts -> ExtStUnitCtx -> UNIT_TERM 
              -> Result (DiagNodeSig, Diag, DGraph, UNIT_TERM)

-- UNIT-REDUCTION
ana_UNIT_TERM lgraph defl gctx curl opts uctx red@(Unit_reduction ut restr) =
    do (p, diag, dg, ut') <- ana_UNIT_TERM lgraph defl gctx curl opts uctx (item ut)
       (incl, msigma) <- ana_RESTRICTION dg (emptyG_sign curl) (getSig (getSigFromDiag p)) opts restr
       let pos = getPos_UNIT_TERM red
       (q@(Diag_node_sig qn _), diag', dg') <- extendDiagramWithMorphismRev pos lgraph diag dg p incl 
                                                                            (renderText Nothing (printText red)) 
                                                                            (case restr of 
                                                                                  (Hidden _ _) -> DGHiding
                                                                                  (Revealed _ _) -> DGRevealing)
       case msigma of 
                  Nothing -> 
                      -- the renaming morphism is just identity, so there's no need
                      -- to extend the diagram
                      do return (q, diag', dg', Unit_reduction (replaceAnnoted ut' ut) restr)
                  Just sigma -> 
                      do 
                         -- check amalgamability conditions
                         let sink = [(qn, sigma)]
                         () <- assertAmalgamability opts pos diag' sink
                         (q', diag'', dg'') <- extendDiagramWithMorphism pos lgraph diag' dg' q sigma 
                                                                       (renderText Nothing (printText red))
                                                                       (case restr of 
                                                                                   (Hidden _ _) -> DGHiding
                                                                                   (Revealed _ _) -> DGRevealing)
                         return (q', diag'', dg'', Unit_reduction (replaceAnnoted ut' ut) restr)
-- UNIT-TRANSLATION
ana_UNIT_TERM lgraph defl gctx curl opts uctx tr@(Unit_translation ut ren) =
    do (dnsig@(Diag_node_sig p _), diag, dg, ut') <- ana_UNIT_TERM lgraph defl gctx curl opts uctx (item ut)
       gMorph <- ana_RENAMING lgraph (getSig (getSigFromDiag dnsig)) opts ren
       let pos = getPos_UNIT_TERM tr
           sink = [(p, gMorph)]
       -- check amalamability conditions
       () <- assertAmalgamability opts pos diag sink
       (dnsig', diag', dg') <- extendDiagramWithMorphism pos lgraph diag dg dnsig gMorph 
                                                         (renderText Nothing (printText tr))
                                                         DGTranslation
       return (dnsig', diag', dg', Unit_translation (replaceAnnoted ut' ut) ren)
-- AMALGAMATION
ana_UNIT_TERM lgraph defl gctx curl opts uctx am@(Amalgamation uts poss) =
    do (dnsigs, diag, dg', uts') <- ana_UNIT_TERMS lgraph defl gctx curl opts uctx uts
       -- compute sigma
       (sig, dg'') <- nodeSigUnion lgraph dg' (map getSigFromDiag dnsigs) DGUnion
       -- check amalgamability conditions
       sink <- inclusionSink lgraph dnsigs sig
       () <- assertAmalgamability opts (headPos poss) diag sink
       (q, diag') <- extendDiagramIncl lgraph diag dnsigs sig (renderText Nothing (printText am))
       return (q, diag', dg'', Amalgamation uts' poss)
-- LOCAL-UNIT
ana_UNIT_TERM lgraph defl gctx@(gannos, genv, _) curl opts uctx (Local_unit udds ut poss) =
    do (uctx', dg, udds') <- ana_UNIT_DECL_DEFNS' lgraph defl gctx curl opts uctx udds
       (dnsig, diag, dg', ut') <- ana_UNIT_TERM lgraph defl (gannos, genv, dg) curl opts uctx' (item ut)
       return (dnsig, diag, dg', Local_unit udds' (replaceAnnoted ut' ut) poss)
-- UNIT-APPL
ana_UNIT_TERM lgraph defl (gannos, genv, dg) curl opts uctx@(buc, diag) 
              uappl@(Unit_appl un fargus _) =
    do let pos = getPos_UNIT_TERM uappl
       case Map.lookup un buc of
            Just (Based_unit_sig dnsig) -> 
                do case fargus of 
                        [] -> return (dnsig, diag, dg, uappl)
                        _ -> -- arguments have been given for a parameterless unit
                             do plain_error (dnsig, diag, dg, uappl)
                                            (showPretty un " is a parameterless unit, but arguments have been given: " ++ 
                                             showPretty fargus "")
                                            pos
            Just (Based_par_unit_sig (pI, (argSigs, resultSig))) ->
                do (sigF, dg') <- nodeSigUnion lgraph dg ((getSigFromDiag pI) : argSigs) DGFormalParams
                   (morphSigs, dg'', diagA) <- ana_FIT_ARG_UNITS lgraph defl (gannos, genv, dg') curl opts uctx
                                                                 uappl pos argSigs fargus
                   let first (e, _, _) = e
                       second (_, e, _) = e
                       third (_, _, e) = e
                   (sigA, dg''') <- nodeSigUnion lgraph dg'' 
                                                 ((getSigFromDiag pI) : (map second morphSigs))
                                                 DGFitSpec
                   -- compute morphA (\sigma^A)
                   G_sign lidI sigI <- return (getSig (getSigFromDiag pI))
                   let idI = G_morphism lidI (ide lidI sigI)
                   morphA <- homogeneousMorManyUnion (idI : (map first morphSigs))
                   -- compute sigMorExt (\sigma^A(\Delta))
                   (_, sigMorExt) <- extendMorphism (getSig sigF) (getSig resultSig) (getSig sigA) morphA
                   -- check amalgamability conditions
                   sink <- inclusionSink lgraph (pI : (map third morphSigs)) sigA
                   () <- assertAmalgamability opts pos diagA sink
                   (qB@(Diag_node_sig nqB _), diag') <- extendDiagramIncl lgraph diagA [pI] resultSig ""
                   -- insert nodes p^F_i and appropriate edges to the diagram
                   let ins diag dg [] = do return (diag, dg)
                       ins diag dg ((morph, _, targetNode) : morphNodes) = 
                           do (dnsig, diag', dg') <- extendDiagramWithMorphismRev pos lgraph diag 
                                                                                  dg targetNode (gEmbed morph) 
                                                                                  (renderText Nothing (printText fargus))
                                                                                  DGFormalParams
                              diag'' <- insInclusionEdges lgraph diag' [dnsig] qB
                              ins diag'' dg' morphNodes
                   (diag'', dg4) <- ins diag' dg''' morphSigs
                   -- check amalgamability conditions
                   (sigR, dg5) <- extendDGraph dg4 resultSig (gEmbed sigMorExt) DGExtension
                   sink <-  inclusionSink lgraph (map third morphSigs) sigR
                   let sink' = (nqB, gEmbed sigMorExt) : sink
                   () <- assertAmalgamability opts pos diag'' sink'
                   (q, diag''') <- extendDiagram diag'' qB (gEmbed sigMorExt) sigR
                                                 (renderText Nothing (printText uappl))
                   diag4 <- insInclusionEdges lgraph diag''' (map third morphSigs) q
                   return (q, diag4, dg5, uappl)
            Nothing -> plain_error (emptyDiagNodeSig defl, diag, dg, uappl) 
                                   ("Undefined unit " ++ showPretty un "")
                                   pos
-- group unit term
ana_UNIT_TERM lgraph defl gctx curl opts uctx (Group_unit_term ut poss) =
    do (dnsig, diag, dg, ut') <- ana_UNIT_TERM lgraph defl gctx curl opts uctx (item ut)
       return (dnsig, diag, dg, Group_unit_term (replaceAnnoted ut' ut) poss)


-- | Analyse unit arguments
ana_FIT_ARG_UNITS :: LogicGraph -> AnyLogic -> GlobalContext -> AnyLogic 
                  -> HetcatsOpts -> ExtStUnitCtx 
                  -> UNIT_TERM      -- ^ the whole application for diagnostic purposes
                  -> Pos            -- ^ the position of the application (for diagnostic purposes)
                  -> [NodeSig]      -- ^ the signatures of unit's formal parameters
                  -> [FIT_ARG_UNIT] -- ^ the arguments for the unit
                  -> Result ([(G_morphism, NodeSig, DiagNodeSig)], DGraph, Diag)
ana_FIT_ARG_UNITS _ _ (_, _, dg) _ _ (_, diag) _ _ [] [] =
    do return ([], dg, diag)
ana_FIT_ARG_UNITS lgraph defl gctx@(gannos, genv, _) curl opts uctx@(buc, _) 
                  appl pos (nsig : nsigs) (fau : faus) =
    do (gmorph, nsig', dnsig, dg, diag) <- ana_FIT_ARG_UNIT lgraph defl gctx curl opts 
                                                           uctx nsig fau
       (morphSigs, dg', diag') <- ana_FIT_ARG_UNITS lgraph defl (gannos, genv, dg) curl opts 
                                                    (buc, diag) appl pos nsigs faus
       return ((gmorph, nsig', dnsig) : morphSigs, dg', diag')
ana_FIT_ARG_UNITS _ _ (_, _, dg) _ _ (_, diag) appl pos [] _ =
    do plain_error ([], dg, diag)
                   ("Too many arguments given in application\n" ++ showPretty appl "")
                   pos
ana_FIT_ARG_UNITS _ _ (_, _, dg) _ _ (_, diag) appl pos _ [] =
    do plain_error ([], dg, diag)
                   ("Too few arguments given in application\n" ++ showPretty appl "")
                   pos


-- | Analyse unit argument
ana_FIT_ARG_UNIT :: LogicGraph -> AnyLogic -> GlobalContext -> AnyLogic 
                 -> HetcatsOpts -> ExtStUnitCtx -> NodeSig -> FIT_ARG_UNIT 
                 -> Result (G_morphism, NodeSig, DiagNodeSig, DGraph, Diag) 
-- ^ returns 1. the signature morphism 2. the target signature of the morphism
-- 3. the diagram node 4. the modified DGraph 5. the modified diagram
ana_FIT_ARG_UNIT lgraph defl gctx curl opts uctx nsig (Fit_arg_unit ut symbMap poss) =
    do (p, diag', dg', _) <- ana_UNIT_TERM lgraph defl gctx curl opts uctx (item ut)
       -- compute gMorph (the morphism r|sigma/D(p))
       let adj = adjustPos (headPos poss)
           gsigmaS = getSig nsig
           gsigmaT = getSig (getSigFromDiag p)
       G_sign lidS sigmaS <- return gsigmaS
       G_sign lidT sigmaT <- return gsigmaT
       G_symb_map_items_list lid sis <- adj $ homogenizeGM (Logic lidS) symbMap
       sigmaT' <- rcoerce lidT lidS (headPos poss) sigmaT
       mor <- if isStructured opts then return (ide lidS sigmaS)
                 else do rmap <- adj $ stat_symb_map_items lid sis
                         rmap' <- rcoerce lid lidS (headPos poss) rmap
                         adj $ induced_from_to_morphism lidS rmap' sigmaS sigmaT'
       let gMorph = G_morphism lidS mor
       (nsig', dg'') <- extendDGraph dg' nsig (gEmbed gMorph) DGFitSpec
       return (gMorph, nsig', p, dg'', diag')


-- | Analyse unit specification
ana_UNIT_SPEC :: LogicGraph -> AnyLogic    -- ^ the default logic
              -> GlobalContext -> AnyLogic -- ^ current logic
              -> HetcatsOpts                      -- ^ should only the structure be analysed?
              -> NodeSig                   -- ^ the signature of imports
              -> UNIT_SPEC -> Result (UnitSig, DGraph, UNIT_SPEC)
-- ^ returns 1. unit signature 2. the development graph resulting from 
-- structred specs inside the unit spec and 3. a UNIT_SPEC after possible
-- conversions.

-- UNIT-TYPE
{- if argspecs are empty and resultspec is a name of unit spec then this
   should be converted to a Spec_name -}
ana_UNIT_SPEC lgraph defl gctx@(_, genv, _) curl just_struct 
              impsig (Unit_type [] (Annoted (Spec_inst spn [] _) _ _ _) _)
    | case Map.lookup spn genv of Just (UnitEntry _) -> True
                                  _ -> False =
        ana_UNIT_SPEC lgraph defl gctx curl just_struct impsig (Spec_name spn)
-- a trivial unit type
ana_UNIT_SPEC lgraph _ gctx _ just_struct impsig (Unit_type [] resultSpec poss) =
    do (resultSpec', resultSig, dg') <- ana_SPEC lgraph gctx impsig Nothing 
                                                 just_struct (item resultSpec)
       return (Unit_sig resultSig, dg', Unit_type [] (replaceAnnoted resultSpec' resultSpec) poss)
-- a non-trivial unit type
ana_UNIT_SPEC lgraph defl gctx@(gannos, genv, _) _ opts impSig (Unit_type argSpecs resultSpec poss) =
    do (argSigs, dg1, argSpecs') <- ana_argSpecs lgraph defl gctx opts argSpecs
       (sigUnion, dg2) <- nodeSigUnion lgraph dg1 (impSig : argSigs) DGFormalParams
       (resultSpec', resultSig, dg3) <- ana_SPEC lgraph (gannos, genv, dg2) sigUnion
                                                 Nothing opts (item resultSpec)
       return (Par_unit_sig (argSigs, resultSig), dg3, 
               Unit_type argSpecs' (replaceAnnoted resultSpec' resultSpec) poss) 
-- SPEC-NAME (an alias)
ana_UNIT_SPEC _ _ (_, genv, dg) _ _ impsig usp@(Spec_name usn@(Token _ pos)) =
    do case Map.lookup usn genv of
            Nothing -> plain_error (Unit_sig impsig, dg, usp)
                                   ("Undefined unit specification " ++ showPretty usn "")
                                   pos
            Just (UnitEntry usig) -> return (usig, dg, usp)
            _ -> plain_error (Unit_sig impsig, dg, usp)
                             ((showPretty usn "") ++ " is not an unit specification")
                             pos
-- CLOSED-UNIT-SPEC
ana_UNIT_SPEC lgraph defl gctx curl just_struct _ (Closed_unit_spec usp' _) =
    ana_UNIT_SPEC lgraph defl gctx curl just_struct (EmptyNode curl) usp'



-- | Analyse refinement specification
ana_REF_SPEC :: LogicGraph -> AnyLogic    -- ^ the default logic
              -> GlobalContext -> AnyLogic -- ^ current logic
              -> HetcatsOpts                      -- ^ should only the structure be analysed?
              -> NodeSig                   -- ^ the signature of imports
              -> REF_SPEC -> Result (UnitSig, DGraph, REF_SPEC)
-- UNIT-SPEC
ana_REF_SPEC lgraph defl gctx curl just_struct nsig (Unit_spec asp) =
    do (usig, dg', asp') <- ana_UNIT_SPEC lgraph defl gctx curl just_struct nsig asp
       return (usig, dg', Unit_spec asp')
-- ARCH-UNIT-SPEC
ana_REF_SPEC lgraph defl gctx curl just_struct _ (Arch_unit_spec asp poss) =
    do ((_, usig), dg', asp') <- ana_ARCH_SPEC lgraph defl gctx curl just_struct (item asp)
       return (usig, dg', Arch_unit_spec (replaceAnnoted asp' asp) poss)
-- dummy implementation for the rest
ana_REF_SPEC lgraph defl gctx@(_,_,dg) curl just_struct nsig rsp =
  return (Unit_sig nsig,dg,rsp)


-- | Analyse a list of argument specifications
ana_argSpecs :: LogicGraph -> AnyLogic -> GlobalContext -> HetcatsOpts -> [Annoted SPEC] 
                -> Result ([NodeSig], DGraph, [Annoted SPEC])
ana_argSpecs _ _ (_, _, dg) _ [] =
    do return ([], dg, [])
ana_argSpecs lgraph defl gctx@(gannos, genv, _) opts (argSpec : argSpecs) =
    do (argSpec', argSig, dg') <- ana_SPEC lgraph gctx (EmptyNode defl) Nothing
                                           opts (item argSpec)
       (argSigs, dg'', argSpecs') <- ana_argSpecs lgraph defl (gannos, genv, dg') opts argSpecs
       return (argSig : argSigs, dg'', (replaceAnnoted argSpec' argSpec) : argSpecs')


-- | Check that given diagram ensures amalgamability along given set of morphisms
assertAmalgamability :: HetcatsOpts          -- ^ the program options
                     -> Pos                  -- ^ the position (for diagnostics)
                     -> Diag                 -- ^ the diagram to be checked
                     -> [(Node, GMorphism)]  -- ^ the sink
                     -> Result ()
assertAmalgamability opts pos diag sink =
    do ensAmalg <- homogeneousEnsuresAmalgamability opts pos diag sink
       case ensAmalg of
                     Amalgamates -> return ()
                     NoAmalgamation msg -> plain_error () 
                             ("Amalgamability is not ensured: " ++ msg) pos
                     DontKnow msg -> warning () msg pos


-- | Check the amalgamability assuming common logic for whole diagram
homogeneousEnsuresAmalgamability :: HetcatsOpts         -- ^ the program options
                                 -> Pos                 -- ^ the position (for diagnostics)
                                 -> Diag                -- ^ the diagram to be checked
                                 -> [(Node, GMorphism)] -- ^ the sink
                                 -> Result Amalgamates
homogeneousEnsuresAmalgamability opts pos diag sink =
    do case sink of  
                 [] -> plain_error defaultDontKnow 
                       "homogeneousEnsuresAmalgamability: Empty sink" pos
                 lab:_ -> do let (_, mor) = lab
                                 sig = cod Grothendieck mor
                             G_sign lid _ <- return sig
                             hDiag <- homogeniseDiagram lid diag
                             hSink <- homogeniseSink lid sink
                             ensures_amalgamability lid (caslAmalg opts, 
                                        hDiag, hSink, (diagDesc diag))


-- | Get a position within the source file of a UNIT-TERM
getPos_UNIT_TERM :: UNIT_TERM
                 -> Pos
-- UNIT-REDUCTION
getPos_UNIT_TERM (Unit_reduction _ restr) =
    -- obtain position from RESTRICTION
    case restr of 
               (Hidden _ poss) -> headPos poss
               (Revealed _ poss) -> headPos poss
-- UNIT-TRANSLATION
getPos_UNIT_TERM (Unit_translation _ (Renaming _ poss)) =
    headPos poss
-- AMALGAMATION
getPos_UNIT_TERM (Amalgamation _ poss) = 
    headPos poss
-- LOCAL-UNIT
getPos_UNIT_TERM (Local_unit _ _ poss) = 
    headPos poss
-- UNIT-APPLICATION
getPos_UNIT_TERM (Unit_appl (Token _ unpos) _ _) = 
    unpos
-- GROUP-UNIT-TERM
getPos_UNIT_TERM (Group_unit_term _ poss) = 
    headPos poss


-- | Get a position within the source file of UNIT-IMPORTED
getPos_UNIT_IMPORTED :: [Pos]
                     -> Pos
getPos_UNIT_IMPORTED (_ : (pos : _)) = pos
getPos_UNIT_IMPORTED _ = nullPos


-- | Get a position within the source file of UNIT-EXPRESSION
getPos_UNIT_EXPRESSION :: UNIT_EXPRESSION
                       -> Pos
getPos_UNIT_EXPRESSION (Unit_expression _ (Annoted ut _ _ _) []) =
    getPos_UNIT_TERM ut
getPos_UNIT_EXPRESSION (Unit_expression _ _ poss) = 
    headPos poss
