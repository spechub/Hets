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

   TODO:
   - assertAmalgamability
   - replace IOResult with Result in the return types
   - pass proper positions instead of nullPos to message functions
   - see specific TODOs in functions
-}

module Static.AnalysisArchitecture (ana_ARCH_SPEC, ana_UNIT_SPEC)
where

import Maybe 
import Logic.Logic
import Logic.Grothendieck
import Common.Lib.Graph
import Static.DevGraph
-- import Syntax.AS_Library
import Syntax.AS_Architecture
import Syntax.AS_Structured
import Static.AnalysisStructured
import Common.AS_Annotation
import Common.Id (Token)
-- import Common.GlobalAnnotations
-- import Common.ConvertGlobalAnnos
-- import Common.AnalyseAnnos
import Common.Result
import Common.Id
import qualified Common.Lib.Map as Map
import Syntax.Print_AS_Architecture
-- import Common.PrettyPrint
-- import Common.AnnoState
-- import Options
-- import System
-- import List
-- import Directory
-- import ReadFn
-- import WriteFn (writeFileInfo)



-- | Analyse an architectural specification
-- @
-- ARCH-SPEC ::= BASIC-ARCH-SPEC | GROUP-ARCH-SPEC | ARCH-SPEC-NAME
-- @
ana_ARCH_SPEC :: LogicGraph -> AnyLogic    -- ^ the default logic
	      -> GlobalContext -> AnyLogic -- ^ current logic
	      -> Bool                      -- ^ should only the structure be analysed?
	      -> ARCH_SPEC -> IOResult (ArchSig, DGraph, ARCH_SPEC)
-- ^ returns 1. the architectural signature of given ARCH-SPEC 2. development graph resulting from
-- structured specs within the arch spec and 3. ARCH_SPEC after possible conversions

-- BASIC-ARCH-SPEC
ana_ARCH_SPEC lgraph defl gctx@(gannos, genv, _) curl justStruct (Basic_arch_spec udd uexpr pos) = 
    do (uctx, dg', udd') <- ana_UNIT_DECL_DEFNS lgraph defl gctx curl justStruct udd 
       (_, usig, _, dg'', uexpr') <- ana_UNIT_EXPRESSION lgraph defl (gannos, genv, dg') curl justStruct uctx (item uexpr)
       return ((ctx uctx, usig), dg'', Basic_arch_spec udd' (replaceAnnoted uexpr' uexpr) pos)
-- GROUP-ARCH-SPEC
ana_ARCH_SPEC lgraph defl gctx curl justStruct (Group_arch_spec asp _) = 
    ana_ARCH_SPEC lgraph defl gctx curl justStruct (item asp)
-- ARCH-SPEC-NAME
ana_ARCH_SPEC _ defl (_, genv, dg) _ _ asp@(Arch_spec_name asn@(Token _ pos)) = 
    do case Map.lookup asn genv of
	    Nothing -> resToIORes (plain_error ((emptyStUnitCtx, (emptyUnitSig defl)), dg, asp)
				   ("Undefined architectural specification " ++ showPretty asn "")
				   pos)
	    Just (ArchEntry asig) -> return (asig, dg, asp)
	    _ -> resToIORes (plain_error ((emptyStUnitCtx, (emptyUnitSig defl)), dg, asp)
			     ((showPretty asn "") ++ " is not an architectural specification")
			     pos)


-- | Analyse a list of unit declarations and definitions
ana_UNIT_DECL_DEFNS :: LogicGraph -> AnyLogic -> GlobalContext -> AnyLogic 
		    -> Bool -> [Annoted UNIT_DECL_DEFN] 
		    -> IOResult (ExtStUnitCtx, DGraph, [Annoted UNIT_DECL_DEFN])
-- ^ returns 1. extended static unit context 2. possibly modified development graph
-- 3. possibly modified list of unit declarations and definitions
ana_UNIT_DECL_DEFNS lgraph defl gctx curl justStruct udds = 
    ana_UNIT_DECL_DEFNS' lgraph defl gctx curl justStruct emptyExtStUnitCtx udds

ana_UNIT_DECL_DEFNS' :: LogicGraph -> AnyLogic -> GlobalContext -> AnyLogic -> Bool 
		     -> ExtStUnitCtx -> [Annoted UNIT_DECL_DEFN] 
		     -> IOResult (ExtStUnitCtx, DGraph, [Annoted UNIT_DECL_DEFN])
ana_UNIT_DECL_DEFNS' _ _ (_, _, dg) _ _ uctx [] =
    do return (uctx, dg, [])
ana_UNIT_DECL_DEFNS' lgraph defl gctx@(gannos, genv, _) curl justStruct uctx (udd : udds) =
    do (uctx', dg', udd') <- ana_UNIT_DECL_DEFN lgraph defl gctx curl justStruct uctx (item udd) 
       (uctx'', dg'', udds') <- ana_UNIT_DECL_DEFNS' lgraph defl (gannos, genv, dg') curl justStruct uctx' udds
       return (uctx'', dg'', (replaceAnnoted udd' udd) : udds')


-- | Analyse unit declaration or definition
ana_UNIT_DECL_DEFN :: LogicGraph -> AnyLogic -> GlobalContext -> AnyLogic 
		   -> Bool -> ExtStUnitCtx -> UNIT_DECL_DEFN -> IOResult (ExtStUnitCtx, DGraph, UNIT_DECL_DEFN)
-- ^ returns 1. extended static unit context 2. possibly modified development graph 
-- 3. possibly modified UNIT_DECL_DEFN

-- unit declaration
ana_UNIT_DECL_DEFN lgraph defl gctx@(gannos, genv, _) curl justStruct 
		   uctx@(buc, _) (Unit_decl un@(Token _ unpos) usp uts pos) =
    do (dns, diag', dg', uts') <- ana_UNIT_IMPORTED lgraph defl gctx curl justStruct uctx uts
       let impSig = getSigFromDiag dns
       (usig, dg'', usp') <- ana_UNIT_SPEC lgraph defl (gannos, genv, dg') curl justStruct impSig usp
       let ud' = Unit_decl un usp' uts' pos
       if Map.member un buc 
	  then
	  resToIORes (plain_error (uctx, dg'', ud')
		                  ("Unit " ++ showPretty un " already declared/defined")
		                  unpos)
	  else
	  case usig of
    	       Par_unit_sig (argSigs, resultSig) -> 
		   do (resultSig', dg''') <- resToIORes (nodeSigUnion lgraph dg'' (resultSig : [impSig]) DGImports)
		      let basedParUSig = Based_par_unit_sig (dns, (argSigs, resultSig'))
   		      return ((Map.insert un basedParUSig buc, diag'), dg''', ud')
	       Unit_sig nsig -> 
		   do (nsig', dg''') <- resToIORes (nodeSigUnion lgraph dg'' (impSig : [nsig]) DGImports)
		      (dn', diag'') <- extendDiagram lgraph diag' [dns] nsig'
		      return ((Map.insert un (Based_unit_sig dn') buc, diag''), dg''', ud')

-- unit definition
ana_UNIT_DECL_DEFN lgraph defl gctx curl justStruct uctx@(buc, _) 
		   (Unit_defn un@(Token _ unpos) uexp poss) =
    do (p, usig, diag, dg', uexp') <- ana_UNIT_EXPRESSION lgraph defl gctx curl justStruct uctx uexp
       let ud' = Unit_defn un uexp' poss
       {- it's sufficient to check that un is not mapped in buc, we don't need
          to convert the ExtStUnitCtx to StUnitCtx as the domain will be preserved -}
       if Map.member un buc 
	  then
	  resToIORes (plain_error (uctx, dg', ud')
		                  ("Unit " ++ showPretty un " already defined/declared")
		                  unpos)
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
		  -> Bool -> ExtStUnitCtx -> [Annoted UNIT_TERM] 
		  -> IOResult (DiagNodeSig, Diag, DGraph, [Annoted UNIT_TERM])
ana_UNIT_IMPORTED _ _ (_, _, dg) curl _ (_, diag) [] =
    do return (Empty_node curl, diag, dg, [])
ana_UNIT_IMPORTED lgraph defl gctx curl justStruct uctx terms =
    do (dnsigs, diag', dg', terms') <- ana_UNIT_IMPORTED' lgraph defl gctx curl justStruct uctx terms 
       (sig, dg'') <- resToIORes (nodeSigUnion lgraph dg' (map getSigFromDiag dnsigs) DGImports)
       -- check amalgamability conditions
       let incl s = propagateErrors (ginclusion lgraph (getSig (getSigFromDiag s)) (getSig sig))
       () <- assertAmalgamability nullPos diag' (map incl dnsigs)
       (dnsig, diag'') <- extendDiagram lgraph diag' dnsigs sig
       return (dnsig, diag'', dg'', terms')

ana_UNIT_IMPORTED' :: LogicGraph -> AnyLogic -> GlobalContext -> AnyLogic 
		   -> Bool -> ExtStUnitCtx -> [Annoted UNIT_TERM] 
		   -> IOResult ([DiagNodeSig], Diag, DGraph, [Annoted UNIT_TERM])
ana_UNIT_IMPORTED' _ _ (_, _, dg) _ _ (_, diag) [] =
    do return ([], diag, dg, [])
ana_UNIT_IMPORTED' lgraph defl gctx@(gannos, genv, _) curl justStruct uctx@(buc, _) (ut : uts) =
    do (dnsig, diag', dg', ut') <- ana_UNIT_TERM lgraph defl gctx curl justStruct uctx (item ut)
       (dnsigs, diag'', dg'', uts') <- ana_UNIT_IMPORTED' lgraph defl (gannos, genv, dg') curl justStruct (buc, diag') uts
       return (dnsig : dnsigs, diag'', dg'', (replaceAnnoted ut' ut) : uts')


-- | Analyse an unit expression
ana_UNIT_EXPRESSION :: LogicGraph -> AnyLogic -> GlobalContext -> AnyLogic 
		    -> Bool -> ExtStUnitCtx -> UNIT_EXPRESSION 
		    -> IOResult (DiagNodeSig, UnitSig, Diag, DGraph, UNIT_EXPRESSION)
ana_UNIT_EXPRESSION lgraph defl gctx curl justStruct uctx (Unit_expression [] ut poss) =
    do (dnsig, diag', dg', ut') <- ana_UNIT_TERM lgraph defl gctx curl justStruct uctx (item ut)
       return (dnsig, Unit_sig (getSigFromDiag dnsig), diag', dg', 
	       Unit_expression [] (replaceAnnoted ut' ut) poss)
ana_UNIT_EXPRESSION lgraph defl gctx@(gannos, genv, _) curl justStruct 
		    uctx@(buc, diag) (Unit_expression ubs ut poss) =
    do (args, dg', ubs') <- ana_UNIT_BINDINGS lgraph defl gctx curl justStruct uctx ubs
       (resnsig, dg'') <- resToIORes (nodeSigUnion lgraph dg' (map snd args) DGFormalParams)
       -- build the extended diagram and new based unit context
       let insNodes diag [] buc = do return ([], diag, buc)
	   insNodes diag ((un, nsig) : args) buc = 
	       do (dnsig, diag') <- extendDiagram lgraph diag [] nsig
		  {- we made sure in ana_UNIT_BINDINGS that there's no mapping for un in buc
		     so we can just use Map.insert -}
		  let buc' = Map.insert un (Based_unit_sig dnsig) buc
		  (dnsigs, diag'', buc'') <- insNodes diag' args buc'
		  return (dnsig : dnsigs, diag'', buc'')
       (pardnsigs, diag', buc') <- insNodes diag args buc
       (resdnsig, diag'') <- extendDiagram lgraph diag' pardnsigs resnsig
       -- analyse the unit term
       (p, diag''', dg''', ut') <- ana_UNIT_TERM lgraph defl (gannos, genv, dg'') 
				                 curl justStruct (buc', diag'') (item ut)
       -- add new node to the diagram
       (z, diag4) <- extendDiagram lgraph diag''' [] (EmptyNode curl)
       -- check amalgamability conditions
       -- TODO: create a list of morphisms
       () <- assertAmalgamability nullPos diag []
       return (z, Par_unit_sig (map snd args, getSigFromDiag p), diag4, dg''', 
	       Unit_expression ubs' (replaceAnnoted ut' ut) poss)


-- | Analyse a list of unit bindings. Ensures that the unit names are not present
-- in extended static unit context and that there are no duplicates among them.
ana_UNIT_BINDINGS :: LogicGraph -> AnyLogic -> GlobalContext -> AnyLogic
		  -> Bool -> ExtStUnitCtx -> [UNIT_BINDING]
		  -> IOResult ([(SIMPLE_ID, NodeSig)], DGraph, [UNIT_BINDING])
ana_UNIT_BINDINGS _ _ (_, _, dg) _ _ _ [] =
    do return ([], dg, [])
ana_UNIT_BINDINGS lgraph defl gctx@(gannos, genv, _) curl justStruct uctx@(buc, _) 
		  ((Unit_binding un@(Token _ unpos) usp poss) : ubs) =
    do (usig, dg', usp') <- ana_UNIT_SPEC lgraph defl gctx curl justStruct (EmptyNode curl) usp
       let ub' = Unit_binding un usp' poss
       case usig of 
	    Par_unit_sig _ -> resToIORes (plain_error ([], dg', [])
					              ("An argument unit " ++ showPretty un " must not be parameterized")
					              unpos)
	    Unit_sig nsig ->
		do (args, dg'', ubs') <- ana_UNIT_BINDINGS lgraph defl (gannos, genv, dg') curl justStruct uctx ubs
		   let args' = (un, nsig) : args
	           if Map.member un buc
		      then
		      resToIORes (plain_error (args', dg'', ub' : ubs')
		                              ("Unit " ++ showPretty un " already declared/defined")
                     	                      unpos)
		      else
		      case lookup un args of
		           Just _ -> resToIORes (plain_error (args', dg'', ub' : ubs')
		                                             ("Unit " ++ showPretty un " already declared/defined")
		                                             unpos)
			   Nothing -> return (args', dg'', ub' : ubs')


-- | Analyse a list of unit terms
ana_UNIT_TERMS :: LogicGraph -> AnyLogic -> GlobalContext -> AnyLogic 
	       -> Bool -> ExtStUnitCtx -> [Annoted UNIT_TERM]
	       -> IOResult ([DiagNodeSig], Diag, DGraph, [Annoted UNIT_TERM])
ana_UNIT_TERMS _ _ (_, _, dg) _ _ (_, diag) [] =
    do return ([], diag, dg, [])
ana_UNIT_TERMS lgraph defl gctx@(gannos, genv, _) curl justStruct uctx@(buc, _) (ut : uts) =
    do (dnsig, diag', dg', ut') <- ana_UNIT_TERM lgraph defl gctx curl justStruct uctx (item ut)
       (dnsigs, diag'', dg'', uts') <- ana_UNIT_TERMS lgraph defl (gannos, genv, dg') curl justStruct (buc, diag') uts
       return (dnsig : dnsigs, diag'', dg'', (replaceAnnoted ut' ut) : uts')


-- | Analyse an unit term
ana_UNIT_TERM :: LogicGraph -> AnyLogic -> GlobalContext -> AnyLogic 
	      -> Bool -> ExtStUnitCtx -> UNIT_TERM 
	      -> IOResult (DiagNodeSig, Diag, DGraph, UNIT_TERM)

-- UNIT-REDUCTION
ana_UNIT_TERM lgraph defl gctx curl@(Logic lid) justStruct uctx (Unit_reduction ut restr) =
    do (p, diag, dg, ut') <- ana_UNIT_TERM lgraph defl gctx curl justStruct uctx (item ut)
       -- TODO: what with the second morphism returned by ana_RESTRICTION?
       (morph, _) <- resToIORes (ana_RESTRICTION dg (emptyG_sign curl) (getSig (getSigFromDiag p)) justStruct restr)
       -- TODO: the domain of morph should already be in the dev graph -- find it there
       -- temporary solution: create new node representing the domain of morph
       let rsig' = dom Grothendieck morph
           nodeContents = DGNode {dgn_name = Nothing,
				  dgn_sign = rsig',
				  dgn_sens = G_l_sentence_list lid [],
				  dgn_origin = DGHiding }
	   [node] = newNodes 0 dg
	   dg' = insNode (node, nodeContents) dg
       sig' <- return (NodeSig (node, rsig'))
       (q, diag') <- extendDiagramRev lgraph diag [p] sig'
       -- check amalgamability conditions
       () <- assertAmalgamability nullPos diag [morph]
       (q', diag'', dg'') <- extendDiagramWithMorphism nullPos lgraph diag' dg' q morph
       return (q', diag'', dg'', Unit_reduction (replaceAnnoted ut' ut) restr)
-- UNIT-TRANSLATION
ana_UNIT_TERM lgraph defl gctx curl justStruct uctx (Unit_translation ut ren) =
    do (dnsig, diag, dg, ut') <- ana_UNIT_TERM lgraph defl gctx curl justStruct uctx (item ut)
       gMorph <- resToIORes (ana_RENAMING dg (getSig (getSigFromDiag dnsig)) justStruct ren)
       -- check amalamability conditions
       () <- assertAmalgamability nullPos diag [gMorph]
       -- create an edge in the diagram that represents gMorph
       -- TODO: pass a meaningful position
       (dnsig', diag', dg') <- extendDiagramWithMorphism nullPos lgraph diag dg dnsig gMorph
       return (dnsig', diag', dg', Unit_translation (replaceAnnoted ut' ut) ren)
-- AMALGAMATION
ana_UNIT_TERM lgraph defl gctx curl justStruct uctx (Amalgamation uts poss) =
    do (dnsigs, diag, dg', uts') <- ana_UNIT_TERMS lgraph defl gctx curl justStruct uctx uts
       -- compute sigma
       (sig, dg'') <- resToIORes (nodeSigUnion lgraph dg' (map getSigFromDiag dnsigs) DGUnion)
       -- check amalgamability conditions
       let incl s = propagateErrors (ginclusion lgraph (getSig (getSigFromDiag s)) (getSig sig))
       () <- assertAmalgamability nullPos diag (map incl dnsigs)
       (q, diag') <- extendDiagram lgraph diag dnsigs sig
       return (q, diag', dg'', Amalgamation uts' poss)
-- LOCAL-UNIT
ana_UNIT_TERM lgraph defl gctx@(gannos, genv, _) curl justStruct uctx (Local_unit udds ut poss) =
    do (uctx', dg, udds') <- ana_UNIT_DECL_DEFNS' lgraph defl gctx curl justStruct uctx udds
       (dnsig, diag, dg', ut') <- ana_UNIT_TERM lgraph defl (gannos, genv, dg) curl justStruct uctx' (item ut)
       return (dnsig, diag, dg', Local_unit udds' (replaceAnnoted ut' ut) poss)
-- UNIT-APPL
ana_UNIT_TERM lgraph defl (gannos, genv, dg) curl justStruct uctx@(buc, diag) 
	      uappl@(Unit_appl un@(Token _ unpos) fargus poss) =
    do case Map.lookup un buc of
            Just (Based_unit_sig dnsig) -> 
		do case fargus of 
			[] -> return (dnsig, diag, dg, uappl)
			_ -> -- arguments have been given for a parameterless unit
			     do resToIORes (plain_error (dnsig, diag, dg, uappl)
				   	                (showPretty un " is a parameterless unit, but arguments have been given: " ++ 
   						         showPretty fargus "")
					                unpos)
	    Just (Based_par_unit_sig (pI, (argSigs, resultSig))) ->
		do (sigF, dg') <- resToIORes (nodeSigUnion lgraph dg ((getSigFromDiag pI) : argSigs) DGFormalParams)
		   (morphSigs, dg'', diagA) <- ana_FIT_ARG_UNITS lgraph defl (gannos, genv, dg') curl justStruct uctx
					                         uappl unpos argSigs fargus
		   let first (e, _, _) = e
		       second (_, e, _) = e
		       third (_, _, e) = e
		   (sigA, dg''') <- resToIORes (nodeSigUnion lgraph dg'' 
				 	                     ((getSigFromDiag pI) : (map second morphSigs))
					                     DGFitSpec)
		   -- compute morphA (\sigma^A)
		   G_sign lidI sigI <- return (getSig (getSigFromDiag pI))
		   let idI = G_morphism lidI (ide lidI sigI)
		   morphA <- resToIORes (homogeneousMorManyUnion (headPos poss) (idI : (map first morphSigs)))
		   -- compute sigMorExt (\sigma^A(\Delta))
		   (sigR, sigMorExt) <- resToIORes (extendMorphism (headPos poss) (getSig sigF) (getSig resultSig) (getSig sigA) morphA)
		   (qB, diag') <- extendDiagram lgraph diagA [pI] resultSig
		   -- insert nodes p^F_i and appropriate edges to the diagram
		   let ins diag dg [] = do return (diag, dg)
		       ins diag dg ((morph, _, targetNode) : morphNodes) = 
			   do (dnsig, diag', dg') <- extendDiagramWithMorphismRev unpos lgraph diag 
						                                  dg targetNode (gEmbed morph)
			      diag'' <- insInclusionEdges lgraph diag' [dnsig] qB
			      ins diag'' dg' morphNodes
		   (diag'', dg4) <- ins diag' dg''' morphSigs
		   -- check amalgamability conditions
		   -- TODO: create a list of morphisms
		   () <- assertAmalgamability nullPos diag []
		   (q, diag''', dg5) <- extendDiagramWithMorphism unpos lgraph diag'' dg4 qB (gEmbed sigMorExt)
		   diag4 <- insInclusionEdges lgraph diag''' (map third morphSigs) q
		   return (q, diag4, dg5, uappl)
	    Nothing -> resToIORes (plain_error (emptyDiagNodeSig defl, diag, dg, uappl) 
				               ("Undefined unit " ++ showPretty un "")
				               unpos)
-- group unit term
ana_UNIT_TERM lgraph defl gctx curl justStruct uctx (Group_unit_term ut poss) =
    do (dnsig, diag, dg, ut') <- ana_UNIT_TERM lgraph defl gctx curl justStruct uctx (item ut)
       return (dnsig, diag, dg, Group_unit_term (replaceAnnoted ut' ut) poss)


-- | Analyse unit arguments
ana_FIT_ARG_UNITS :: LogicGraph -> AnyLogic -> GlobalContext -> AnyLogic 
		  -> Bool -> ExtStUnitCtx 
		  -> UNIT_TERM      -- ^ the whole application for diagnostic purposes
		  -> Pos            -- ^ the position of the application (for diagnostic purposes)
		  -> [NodeSig]      -- ^ the signatures of unit's formal parameters
		  -> [FIT_ARG_UNIT] -- ^ the arguments for the unit
		  -> IOResult ([(G_morphism, NodeSig, DiagNodeSig)], DGraph, Diag)
ana_FIT_ARG_UNITS _ _ (_, _, dg) _ _ (_, diag) _ _ [] [] =
    do return ([], dg, diag)
ana_FIT_ARG_UNITS lgraph defl gctx@(gannos, genv, _) curl justStruct uctx@(buc, _) 
		  appl pos (nsig : nsigs) (fau : faus) =
    do (gmorph, nsig', dnsig, dg, diag) <- ana_FIT_ARG_UNIT lgraph defl gctx curl justStruct 
				                           uctx nsig fau
       (morphSigs, dg', diag') <- ana_FIT_ARG_UNITS lgraph defl (gannos, genv, dg) curl justStruct 
			                            (buc, diag) appl pos nsigs faus
       return ((gmorph, nsig', dnsig) : morphSigs, dg', diag')
ana_FIT_ARG_UNITS _ _ (_, _, dg) _ _ (_, diag) appl pos [] _ =
    do resToIORes (plain_error ([], dg, diag)
		               ("Too many arguments given in application\n" ++ showPretty appl "")
		               pos)
ana_FIT_ARG_UNITS _ _ (_, _, dg) _ _ (_, diag) appl pos _ [] =
    do resToIORes (plain_error ([], dg, diag)
		               ("Too few arguments given in application\n" ++ showPretty appl "")
		               pos)


-- | Analyse unit argument
ana_FIT_ARG_UNIT :: LogicGraph -> AnyLogic -> GlobalContext -> AnyLogic 
		 -> Bool -> ExtStUnitCtx -> NodeSig -> FIT_ARG_UNIT 
		 -> IOResult (G_morphism, NodeSig, DiagNodeSig, DGraph, Diag) 
-- ^ returns 1. the signature morphism 2. the target signature of the morphism
-- 3. the diagram node 4. the modified DGraph 5. the modified diagram
ana_FIT_ARG_UNIT lgraph defl gctx curl justStruct uctx nsig (Fit_arg_unit ut symbMap poss) =
    do (p, diag', dg', _) <- ana_UNIT_TERM lgraph defl gctx curl justStruct uctx (item ut)
       -- compute gMorph (the morphism r|sigma/D(p))
       let adj = adjustPos (headPos poss)
	   gsigmaS = getSig nsig
	   gsigmaT = getSig (getSigFromDiag p)
       G_sign lidS sigmaS <- return gsigmaS
       G_sign lidT sigmaT <- return gsigmaT
       G_symb_map_items_list lid sis <- return symbMap
       sigmaT' <- resToIORes (rcoerce lidT lidS (headPos poss) sigmaT)
       mor <- if justStruct then return (ide lidS sigmaS)
	         else do rmap <- resToIORes (adj $ stat_symb_map_items lid sis)
			 rmap' <- resToIORes (rcoerce lid lidS (headPos poss) rmap)
			 resToIORes (adj $ induced_from_to_morphism lidS rmap' sigmaS sigmaT')
       let gMorph = G_morphism lidS mor
       (nsig', dg'') <- resToIORes (extendDGraph dg' nsig (gEmbed gMorph) DGFitSpec)
       return (gMorph, nsig', p, dg'', diag')


-- | Analyse unit specification
ana_UNIT_SPEC :: LogicGraph -> AnyLogic    -- ^ the default logic
	      -> GlobalContext -> AnyLogic -- ^ current logic
	      -> Bool                      -- ^ should only the structure be analysed?
	      -> NodeSig                   -- ^ the signature of imports
	      -> UNIT_SPEC -> IOResult (UnitSig, DGraph, UNIT_SPEC)
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
    do (resultSpec', resultSig, dg') <- resToIORes (ana_SPEC lgraph gctx impsig Nothing 
						             just_struct (item resultSpec))
       return (Unit_sig resultSig, dg', Unit_type [] (replaceAnnoted resultSpec' resultSpec) poss)
-- a non-trivial unit type
ana_UNIT_SPEC lgraph defl gctx@(gannos, genv, _) _ justStruct impSig (Unit_type argSpecs resultSpec poss) =
    do (argSigs, dg1, argSpecs') <- ana_argSpecs lgraph defl gctx justStruct argSpecs
       (sigUnion, dg2) <- resToIORes (nodeSigUnion lgraph dg1 (impSig : argSigs) DGFormalParams)
       (resultSpec', resultSig, dg3) <- resToIORes (ana_SPEC lgraph (gannos, genv, dg2) sigUnion
					                     Nothing justStruct (item resultSpec))
       return (Par_unit_sig (argSigs, resultSig), dg3, 
	       Unit_type argSpecs' (replaceAnnoted resultSpec' resultSpec) poss) 
-- SPEC-NAME (an alias)
ana_UNIT_SPEC _ _ (_, genv, dg) _ _ impsig usp@(Spec_name usn@(Token _ pos)) =
    do case Map.lookup usn genv of
	    Nothing -> resToIORes (plain_error (Unit_sig impsig, dg, usp)
				   ("Undefined unit specification " ++ showPretty usn "")
				   pos)
	    Just (UnitEntry usig) -> return (usig, dg, usp)
	    _ -> resToIORes (plain_error (Unit_sig impsig, dg, usp)
			     ((showPretty usn "") ++ " is not an unit specification")
			     pos)
-- ARCH-UNIT-SPEC
ana_UNIT_SPEC lgraph defl gctx curl just_struct _ (Arch_unit_spec asp poss) =
    do ((_, usig), dg', asp') <- ana_ARCH_SPEC lgraph defl gctx curl just_struct (item asp)
       return (usig, dg', Arch_unit_spec (replaceAnnoted asp' asp) poss)
-- CLOSED-UNIT-SPEC
ana_UNIT_SPEC lgraph defl gctx curl just_struct _ (Closed_unit_spec usp' _) =
    ana_UNIT_SPEC lgraph defl gctx curl just_struct (EmptyNode curl) usp'


-- | Analyse a list of argument specifications
ana_argSpecs :: LogicGraph -> AnyLogic -> GlobalContext -> Bool -> [Annoted SPEC] 
		-> IOResult ([NodeSig], DGraph, [Annoted SPEC])
ana_argSpecs _ _ (_, _, dg) _ [] =
    do return ([], dg, [])
ana_argSpecs lgraph defl gctx@(gannos, genv, _) justStruct (argSpec : argSpecs) =
    do (argSpec', argSig, dg') <- resToIORes (ana_SPEC lgraph gctx (EmptyNode defl) Nothing
					               justStruct (item argSpec))
       (argSigs, dg'', argSpecs') <- ana_argSpecs lgraph defl (gannos, genv, dg') justStruct argSpecs
       return (argSig : argSigs, dg'', (replaceAnnoted argSpec' argSpec) : argSpecs')


-- | Insert the edges from given source nodes to given target node
-- into the given diagram. The edges are labelled with inclusions.
insInclusionEdges :: LogicGraph
		  -> Diag          -- ^ the diagram to which the edges should be inserted
		  -> [DiagNodeSig] -- ^ the source nodes
		  -> DiagNodeSig   -- ^ the target node
		  -> IOResult Diag
-- ^ returns the diagram with edges inserted
insInclusionEdges lgraph diag srcNodes (Diag_node_sig tn tnsig) =
    do let inslink diag dns = do d <- diag
				 case dns of
			            Empty_node _ -> return d
				    Diag_node_sig n nsig -> 
					do incl <- resToIORes (ginclusion lgraph (getSig nsig) (getSig tnsig))
					   return (insEdge (n, tn, DiagLink { dl_morphism = incl }) d)
       diag' <- foldl inslink (return diag) srcNodes
       return diag'


-- | Insert the edges from given source node to given target nodes
-- into the given diagram. The edges are labelled with inclusions.
insInclusionEdgesRev :: LogicGraph
		     -> Diag          -- ^ the diagram to which the edges should be inserted
		     -> DiagNodeSig   -- ^ the source node
		     -> [DiagNodeSig] -- ^ the target nodes
		     -> IOResult Diag
-- ^ returns the diagram with edges inserted
insInclusionEdgesRev lgraph diag (Diag_node_sig sn snsig) targetNodes =
    do let inslink diag dns = do d <- diag
				 case dns of
			            Empty_node _ -> return d
				    Diag_node_sig n nsig -> 
					do incl <- resToIORes (ginclusion lgraph (getSig snsig) (getSig nsig))
					   return (insEdge (sn, n, DiagLink { dl_morphism = incl }) d)
       diag' <- foldl inslink (return diag) targetNodes
       return diag'


-- | Build a diagram that extends given diagram with a node containing
-- given signature and with edges from given set of nodes to the new node.
-- The new edges are labelled with sigature inclusions.
extendDiagram :: LogicGraph
	      -> Diag          -- ^ the diagram to be extended
	      -> [DiagNodeSig] -- ^ the nodes which should be linked to the new node
	      -> NodeSig       -- ^ the signature with which the new node should be labelled
	      -> IOResult (DiagNodeSig, Diag)
-- ^ returns the new node and the extended diagram
extendDiagram lgraph diag srcNodes newNodeSig = 
  do let nodeContents = DiagNode {dn_sig = newNodeSig}
	 [node] = newNodes 0 diag
	 diag' = insNode (node, nodeContents) diag
	 newDiagNode = Diag_node_sig node newNodeSig
     diag'' <- insInclusionEdges lgraph diag' srcNodes newDiagNode
     return (newDiagNode, diag'') 


-- | Build a diagram that extends given diagram with a node containing
-- given signature and with edges from the new node to given set of nodes.
-- The new edges are labelled with sigature inclusions.
extendDiagramRev :: LogicGraph
		 -> Diag          -- ^ the diagram to be extended
		 -> [DiagNodeSig] -- ^ the nodes which should be linked to the new node
		 -> NodeSig       -- ^ the signature with which the new node should be labelled
		 -> IOResult (DiagNodeSig, Diag)
-- ^ returns the new node and the extended diagram
extendDiagramRev lgraph diag targetNodes newNodeSig = 
  do let nodeContents = DiagNode {dn_sig = newNodeSig}
	 [node] = newNodes 0 diag
	 diag' = insNode (node, nodeContents) diag
	 newDiagNode = Diag_node_sig node newNodeSig
     diag'' <- insInclusionEdgesRev lgraph diag' newDiagNode targetNodes
     return (newDiagNode, diag'') 


-- | Build a diagram that extends given diagram with a node and an
-- edge to that node. The edge is labelled with given signature morphism and
-- the node contains the target of this morphism. Extends the development graph 
-- with given morphis as well.
extendDiagramWithMorphism :: Pos           -- ^ the position (for diagnostics)
			  -> LogicGraph
			  -> Diag          -- ^ the diagram to be extended
			  -> DGraph        -- ^ the development graph
			  -> DiagNodeSig   -- ^ the node from which the edge should originate
			  -> GMorphism     -- ^ the morphism with which the new edge should be labelled
			  -> IOResult (DiagNodeSig, Diag, DGraph)
-- ^ returns the new node, the extended diagram and extended development graph
extendDiagramWithMorphism pos _ diag dg (Diag_node_sig n nsig) morph =
  if (getSig nsig) == (dom Grothendieck morph) then
     do (targetSig, dg') <- resToIORes (extendDGraph dg nsig morph DGTranslation) -- TODO: parameterised origin
	let nodeContents = DiagNode {dn_sig = targetSig}
	    [node] = newNodes 0 diag
 	    diag' = insNode (node, nodeContents) diag
	    diag'' = insEdge (n, node, DiagLink { dl_morphism = morph }) diag'
        return (Diag_node_sig node targetSig, diag'', dg') 
     else do resToIORes (fatal_error ("Internal error: Static.AnalysisArchitecture.extendDiagramWithMorphism: the morphism domain differs from the signature in given source node")
				     pos)


-- | Build a diagram that extends given diagram with a node and an
-- edge from that node. The edge is labelled with given signature morphism and
-- the node contains the source of this morphism. Extends the development graph 
-- with given morphis as well.
extendDiagramWithMorphismRev :: Pos           -- ^ the position (for diagnostics)
			     -> LogicGraph
			     -> Diag          -- ^ the diagram to be extended
			     -> DGraph        -- ^ the development graph
			     -> DiagNodeSig   -- ^ the node to which the edge should point
			     -> GMorphism     -- ^ the morphism with which the new edge should be labelled
			     -> IOResult (DiagNodeSig, Diag, DGraph)
-- ^ returns the new node, the extended diagram and extended development graph
extendDiagramWithMorphismRev pos _ diag dg (Diag_node_sig n nsig) morph =
  if (getSig nsig) == (cod Grothendieck morph) then
     do (sourceSig, dg') <- resToIORes (extendDGraphRev dg nsig morph DGTranslation) -- TODO: parameterised origin
	let nodeContents = DiagNode {dn_sig = sourceSig}
	    [node] = newNodes 0 diag
 	    diag' = insNode (node, nodeContents) diag
	    diag'' = insEdge (node, n, DiagLink { dl_morphism = morph }) diag'
        return (Diag_node_sig node sourceSig, diag'', dg') 
     else do resToIORes (fatal_error ("Internal error: Static.AnalysisArchitecture.extendDiagramWithMorphismRev: the morphism codomain differs from the signature in given target node")
				     pos)


-- | Check that given diagram ensures amalgamability along given set of morphisms
assertAmalgamability :: Pos          -- ^ the position (for diagnostics)
		     -> Diag         -- ^ the diagram to be checked
		     -> [GMorphism]  -- ^ the set of morphisms
		     -> IOResult ()
-- TODO
assertAmalgamability pos _ _ =
    do resToIORes (warning () "Ignoring amalgamability requirement" pos)