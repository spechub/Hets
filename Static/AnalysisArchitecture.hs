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

import Maybe 
import Logic.Logic
import Logic.Grothendieck
import Common.Lib.Graph
import Static.DevGraph
import Syntax.AS_Library
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
ana_ARCH_SPEC lgraph defl gctx@(gannos, genv, dg) curl justStruct (Basic_arch_spec udd uexpr pos) = 
    do (uctx, dg', udd') <- ana_UNIT_DECL_DEFNS lgraph defl gctx curl justStruct udd 
       (_, usig, _, dg'', uexpr') <- ana_UNIT_EXPRESSION lgraph defl (gannos, genv, dg') curl justStruct uctx (item uexpr)
       -- TODO: use dg and uexpr returned by ana_UNIT_EXPRESSION
       return ((ctx uctx, usig), dg'', Basic_arch_spec udd' (replaceAnnoted uexpr' uexpr) pos)
-- GROUP-ARCH-SPEC
ana_ARCH_SPEC lgraph defl gctx@(gannos, genv, dg) curl justStruct gsp@(Group_arch_spec asp pos) = 
    ana_ARCH_SPEC lgraph defl gctx curl justStruct (item asp)
-- ARCH-SPEC-NAME
ana_ARCH_SPEC lgraph defl gctx@(gannos, genv, dg) l just_struct asp@(Arch_spec_name asn@(Token _ pos)) = 
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
ana_UNIT_DECL_DEFNS' lgraph defl gctx@(gannos, genv, dg) curl justStruct uctx (udd : udds) =
    do (uctx', dg', udd') <- ana_UNIT_DECL_DEFN lgraph defl gctx curl justStruct uctx (item udd) 
       (uctx'', dg'', udds') <- ana_UNIT_DECL_DEFNS' lgraph defl (gannos, genv, dg') curl justStruct uctx' udds
       return (uctx'', dg'', (replaceAnnoted udd' udd) : udds)


-- | Analyse unit declaration or definition
ana_UNIT_DECL_DEFN :: LogicGraph -> AnyLogic -> GlobalContext -> AnyLogic 
		   -> Bool -> ExtStUnitCtx -> UNIT_DECL_DEFN -> IOResult (ExtStUnitCtx, DGraph, UNIT_DECL_DEFN)
-- ^ returns 1. extended static unit context 2. possibly modified development graph 
-- 3. possibly modified UNIT_DECL_DEFN

-- unit declaration
ana_UNIT_DECL_DEFN lgraph defl gctx@(gannos, genv, dg) curl justStruct 
		   uctx@(buc, diag) ud@(Unit_decl un@(Token _ unpos) usp uts pos) =
    do (dns, diag', dg') <- ana_UNIT_IMPORTED lgraph defl gctx curl justStruct uctx uts
       let impSig = getSigFromDiag dns
       (usig, dg'', usp') <- ana_UNIT_SPEC lgraph defl (gannos, genv, dg') curl justStruct impSig usp
       let ud' = Unit_decl un usp' uts pos
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
		      (dn', diag'') <- extendDiagram diag' [dns] nsig'
		      return ((Map.insert un (Based_unit_sig dn') buc, diag''), dg''', ud')

-- unit definition
ana_UNIT_DECL_DEFN lgraph defl gctx curl justStruct uctx@(buc, d) 
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
		  -> IOResult (DiagNodeSig, Diag, DGraph)
ana_UNIT_IMPORTED lgraph defl (_, _, dg) curl justStruct uctx@(_, diag) [] =
    do return (Empty_node curl, diag, dg)
ana_UNIT_IMPORTED lgraph defl gctx curl justStruct uctx@(buc, diag) terms =
    do (nodes, diag', dg') <- ana_UNIT_IMPORTED' lgraph defl gctx curl justStruct uctx terms 
       (sig, dg'') <- resToIORes (nodeSigUnion lgraph dg' (map getSigFromDiag nodes) DGImports)
       -- TODO: check amalgamability conditions
       (dnsig, diag'') <- extendDiagram diag' nodes sig
       return (dnsig, diag'', dg'')

-- TODO: return updated UNIT_TERMs
ana_UNIT_IMPORTED' :: LogicGraph -> AnyLogic -> GlobalContext -> AnyLogic 
		   -> Bool -> ExtStUnitCtx -> [Annoted UNIT_TERM] 
		   -> IOResult ([DiagNodeSig], Diag, DGraph)
ana_UNIT_IMPORTED' lgraph defl (_, _, dg) curl justStruct uctx@(buc, diag) [] =
    do return ([], diag, dg)
ana_UNIT_IMPORTED' lgraph defl gctx@(gannos, genv, _) curl justStruct uctx@(buc, diag) (ut : uts) =
    do (dnsig, diag', dg', ut') <- ana_UNIT_TERM lgraph defl gctx curl justStruct uctx (item ut)
       (dnsigs, diag'', dg'') <- ana_UNIT_IMPORTED' lgraph defl (gannos, genv, dg') curl justStruct (buc, diag') uts
       return (dnsig : dnsigs, diag'', dg'')


-- | Analyse an unit expression
ana_UNIT_EXPRESSION :: LogicGraph -> AnyLogic -> GlobalContext -> AnyLogic 
		    -> Bool -> ExtStUnitCtx -> UNIT_EXPRESSION 
		    -> IOResult (DiagNodeSig, UnitSig, Diag, DGraph, UNIT_EXPRESSION)
ana_UNIT_EXPRESSION lgraph defl gctx@(gannos, genv, dg) curl justStruct 
		    uctx (Unit_expression [] ut poss) =
    do (dnsig, diag', dg', ut') <- ana_UNIT_TERM lgraph defl gctx curl justStruct uctx (item ut)
       return (dnsig, Unit_sig (getSigFromDiag dnsig), diag', dg', 
	       Unit_expression [] (replaceAnnoted ut' ut) poss)
ana_UNIT_EXPRESSION lgraph defl gctx@(gannos, genv, dg) curl justStruct 
		    uctx@(buc, diag) uexp@(Unit_expression ubs ut poss) =
    do (args, dg', ubs') <- ana_UNIT_BINDINGS lgraph defl gctx curl justStruct uctx ubs
       (resnsig, dg'') <- resToIORes (nodeSigUnion lgraph dg' (map snd args) DGFormalParams)
       -- build the extended diagram and new based unit context
       let insNodes diag [] buc = do return ([], diag, buc)
	   insNodes diag ((un, nsig) : args) buc = 
	       do (dnsig, diag') <- extendDiagram diag [] nsig
		  {- we made sure in ana_UNIT_BINDINGS that there's no mapping for un in buc
		     so we can just use Map.insert -}
		  let buc' = Map.insert un (Based_unit_sig dnsig) buc
		  (dnsigs, diag'', buc'') <- insNodes diag' args buc'
		  return (dnsig : dnsigs, diag'', buc'')
       (pardnsigs, diag', buc') <- insNodes diag args buc
       (resdnsig, diag'') <- extendDiagram diag' pardnsigs resnsig
       -- analyse the unit term
       (p, diag''', dg''', ut') <- ana_UNIT_TERM lgraph defl (gannos, genv, dg'') 
				                 curl justStruct (buc', diag'') (item ut)
       -- add new node to the diagram
       (z, diag4) <- extendDiagram diag''' [] (EmptyNode curl)
       -- TODO: check amalgamability conditions
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


-- | Analyse an unit term
ana_UNIT_TERM :: LogicGraph -> AnyLogic -> GlobalContext -> AnyLogic 
	      -> Bool -> ExtStUnitCtx -> UNIT_TERM 
	      -> IOResult (DiagNodeSig, Diag, DGraph, UNIT_TERM)
-- TODO

-- UNIT-REDUCTION
ana_UNIT_TERM lgraph defl gctx@(_, _, dg) curl justStruct uctx@(buc, diag) 
	      ured@(Unit_reduction ut restr) =
    do resToIORes (warning (emptyDiagNodeSig defl, diag, ured) "Ignoring unit reduction" nullPos)
       return (emptyDiagNodeSig defl, diag, dg, ured)
-- UNIT-TRANSLATION
ana_UNIT_TERM lgraph defl gctx curl justStruct uctx@(buc, diag0) (Unit_translation ut ren) =
    do (dnsig, diag, dg, ut') <- ana_UNIT_TERM lgraph defl gctx curl justStruct uctx (item ut)
       --resToIORes (warning () ("buc: " ++ show buc) nullPos)
       --resToIORes (warning () ("diag: " ++ show diag) nullPos)
       --resToIORes (warning () (show (getSigFromDiag dnsig)) nullPos)
       --resToIORes (warning () (show (getSig (getSigFromDiag dnsig))) nullPos)
       gMorph <- resToIORes (ana_RENAMING dg (getSig (getSigFromDiag dnsig)) justStruct ren)
       -- TODO: check amalamability conditions
       -- insert the target signature to the DGraph
       (targetSig, dg') <- resToIORes (extendDGraph dg (getSigFromDiag dnsig) gMorph DGTranslation)
       -- TODO: label the new edge in diagram with gMorph
       (dnsig', diag') <- extendDiagram diag [dnsig] targetSig
       return (dnsig', diag', dg', Unit_translation (replaceAnnoted ut' ut) ren)
-- AMALGAMATION
ana_UNIT_TERM lgraph defl gctx@(_, _, dg) curl justStruct uctx@(buc, diag) 
	      ut@(Amalgamation uts poss) =
    do resToIORes (warning (emptyDiagNodeSig defl, diag, ut) "Ignoring unit amalgamation" nullPos)
       return (emptyDiagNodeSig defl, diag, dg, ut)
-- LOCAL-UNIT
ana_UNIT_TERM lgraph defl gctx curl justStruct uctx
	      lu@(Local_unit udds ut poss) =
    do (uctx', dg, udds') <- ana_UNIT_DECL_DEFNS' lgraph defl gctx curl justStruct uctx udds
       (dnsig, diag, dg', ut') <- ana_UNIT_TERM lgraph defl gctx curl justStruct uctx' (item ut)
       return (dnsig, diag, dg', Local_unit udds' (replaceAnnoted ut' ut) poss)
-- UNIT-APPL
ana_UNIT_TERM lgraph defl gctx@(gannos, genv, dg) curl justStruct uctx@(buc, diag) 
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
		   let second (_, e, _) = e
		   (sigA, dg''') <- resToIORes (nodeSigUnion lgraph dg'' 
				 	                     ((getSigFromDiag pI) : (map second morphSigs))
					                     DGFitSpec)
		   -- TODO: compute delta
		   -- TODO: compute sigR
		   (qB, diag') <- extendDiagram diagA [pI] resultSig
		   -- TODO: insert nodes p^F_i and appropriate edges to the diagram
		   -- TODO: check amalgamability conditions
		   let third (_, _, e) = e
		   (q, diag'') <- extendDiagram diag' (qB : (map third morphSigs)) resultSig -- TODO: use sigR here
		   return (q, diag'', dg, uappl)
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
		  -> IOResult ([(GMorphism, NodeSig, DiagNodeSig)], DGraph, Diag)
ana_FIT_ARG_UNITS _ _ (_, _, dg) _ _ (_, diag) _ _ [] [] =
    do return ([], dg, diag)
ana_FIT_ARG_UNITS lgraph defl gctx@(gannos, genv, _) curl justStruct uctx@(buc, _) 
		  appl pos (nsig : nsigs) (fau : faus) =
    do (gmorph, nsig, dnsig, dg, diag) <- ana_FIT_ARG_UNIT lgraph defl gctx curl justStruct 
				                           uctx nsig fau
       (morphSigs, dg', diag') <- ana_FIT_ARG_UNITS lgraph defl (gannos, genv, dg) curl justStruct 
			                            (buc, diag) appl pos nsigs faus
       return ((gmorph, nsig, dnsig) : morphSigs, dg', diag')
ana_FIT_ARG_UNITS _ _ (_, _, dg) _ _ (_, diag) appl pos [] _ =
    do resToIORes (plain_error ([], dg, diag)
		               ("Too many arguments given in application\n" ++ showPretty appl "")
		               pos)
ana_FIT_ARG_UNITS _ _ (_, _, dg) _ _ (_, diag) appl pos _ [] =
    do resToIORes (plain_error ([], dg, diag)
		               ("Too few arguments given in application\n" ++ showPretty appl "")
		               pos)


-- | Analyse unit argument
-- TODO
ana_FIT_ARG_UNIT :: LogicGraph -> AnyLogic -> GlobalContext -> AnyLogic 
		 -> Bool -> ExtStUnitCtx -> NodeSig -> FIT_ARG_UNIT 
		 -> IOResult (GMorphism, NodeSig, DiagNodeSig, DGraph, Diag)
-- ^ returns 1. the signature morphism 2. the target signature of the morphism
-- 3. the diagram node 4. the modified DGraph 5. the modified diagram
ana_FIT_ARG_UNIT lgraph defl gctx@(_, _, dg) curl justStruct uctx@(_, diag) 
		 nsig@(NodeSig (_, G_sign lid sig)) fau@(Fit_arg_unit ut symbMap poss) =
    do resToIORes (warning () 
		           ("Ignoring unit argument " ++ showPretty fau "")
		           nullPos)
       let gMorph = gEmbed (G_morphism lid (ide lid sig))
       (nsig, dg') <- resToIORes (extendDGraph dg nsig gMorph DGFitSpec)
       return (gMorph, nsig, emptyDiagNodeSig curl, dg', diag)


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
ana_UNIT_SPEC lgraph defl gctx@(gannos, genv, dg) curl just_struct impsig usp@(Unit_type [] resultSpec poss) =
    do (resultSpec', resultSig, dg') <- resToIORes (ana_SPEC lgraph gctx impsig Nothing 
						             just_struct (item resultSpec))
       return (Unit_sig resultSig, dg', Unit_type [] (replaceAnnoted resultSpec' resultSpec) poss)
-- a non-trivial unit type
ana_UNIT_SPEC lgraph defl gctx@(gannos, genv, _) _ justStruct impSig usp@(Unit_type argSpecs resultSpec poss) =
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
ana_UNIT_SPEC lgraph defl gctx curl just_struct _ (Closed_unit_spec usp' poss) =
    ana_UNIT_SPEC lgraph defl gctx curl just_struct (EmptyNode curl) usp'


-- | Analyse a list of argument specifications
ana_argSpecs :: LogicGraph -> AnyLogic -> GlobalContext -> Bool -> [Annoted SPEC] 
		-> IOResult ([NodeSig], DGraph, [Annoted SPEC])
ana_argSpecs _ _ (_, _, dg) _ [] =
    do return ([], dg, [])
ana_argSpecs lgraph defl gctx@(gannos, genv, dg) justStruct (argSpec : argSpecs) =
    do (argSpec', argSig, dg') <- resToIORes (ana_SPEC lgraph gctx (EmptyNode defl) Nothing
					               justStruct (item argSpec))
       (argSigs, dg'', argSpecs') <- ana_argSpecs lgraph defl (gannos, genv, dg') justStruct argSpecs
       return (argSig : argSigs, dg'', (replaceAnnoted argSpec' argSpec) : argSpecs')


-- | Build a diagram that extends given diagram with a node containing
-- given signature and with edges from given set of nodes to the new node.
extendDiagram :: Diag          -- ^ the diagram to be extended
	      -> [DiagNodeSig] -- ^ the nodes which should be linked to the new node
	      -> NodeSig       -- ^ the signature with which the new node should be labelled
	      -> IOResult (DiagNodeSig, Diag)
-- ^ returns the new node and the extended diagram
extendDiagram diag srcNodes newNodeSig = 
  do let nodeContents = DiagNode {dn_sig = newNodeSig}
	 [node] = newNodes 0 diag
	 diag' = insNode (node, nodeContents) diag
	 inslink diag dns = do d <- diag
			       case dns of
			            Empty_node _ -> return d
				    Diag_node_sig n _ -> return (insEdge (n, node, DiagLink) d)
     diag'' <- foldl inslink (return diag') srcNodes
     return (Diag_node_sig node newNodeSig, diag'') 

