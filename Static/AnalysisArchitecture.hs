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
-- import Syntax.Parse_AS_Structured (lookupLogicName)
-- import Syntax.Parse_AS_Library(library)
-- import Common.Lib.Parsec
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
	      -> ARCH_SPEC -> IOResult ArchSig 
-- ^ returns the architectural signature of given ARCH-SPEC

-- BASIC-ARCH-SPEC
ana_ARCH_SPEC lgraph defl gctx@(gannos, genv, dg) curl justStruct asp@(Basic_arch_spec udd uexpr pos) = 
    do uctx <- ana_UNIT_DECL_DEFNS lgraph defl gctx curl justStruct udd
       (_, usig, _) <- ana_UNIT_EXPRESSION defl gctx uctx (item uexpr)
       return (ctx uctx, usig)
-- GROUP-ARCH-SPEC
ana_ARCH_SPEC lgraph defl gctx@(gannos, genv, dg) curl justStruct gsp@(Group_arch_spec asp pos) = 
    ana_ARCH_SPEC lgraph defl gctx curl justStruct (item asp)
-- ARCH-SPEC-NAME
ana_ARCH_SPEC lgraph defl gctx@(gannos, genv, dg) l just_struct asp@(Arch_spec_name asn@(Token _ pos)) = 
    do case Map.lookup asn genv of
	    Nothing -> resToIORes (plain_error (emptyStUnitCtx, (emptyUnitSig defl))
				   ("Undefined architectural specification " ++ showPretty asn "")
				   pos)
	    Just (ArchEntry asig) -> return asig
	    _ -> resToIORes (plain_error (emptyStUnitCtx, (emptyUnitSig defl))
			     ((showPretty asn "") ++ " is not an architectural specification")
			     pos)


-- | Analyse a list of unit declarations and definitions
ana_UNIT_DECL_DEFNS :: LogicGraph -> AnyLogic -> GlobalContext -> AnyLogic 
		    -> Bool -> [Annoted UNIT_DECL_DEFN] -> IOResult ExtStUnitCtx
ana_UNIT_DECL_DEFNS lgraph defl gctx curl justStruct udds = 
    ana_UNIT_DECL_DEFNS' lgraph defl gctx curl justStruct emptyExtStUnitCtx udds

ana_UNIT_DECL_DEFNS' :: LogicGraph -> AnyLogic -> GlobalContext -> AnyLogic -> Bool 
		     -> ExtStUnitCtx -> [Annoted UNIT_DECL_DEFN] -> IOResult ExtStUnitCtx
-- TODO: pass the dg' and udd' further
ana_UNIT_DECL_DEFNS' _ _ _ _ _ uctx [] =
    do return uctx
ana_UNIT_DECL_DEFNS' lgraph defl gctx@(gannos, genv, dg) curl justStruct uctx (udd : udds) =
    do (uctx', dg', udd') <- ana_UNIT_DECL_DEFN lgraph defl gctx curl justStruct uctx (item udd) 
       uctx'' <- ana_UNIT_DECL_DEFNS' lgraph defl (gannos, genv, dg') curl justStruct uctx' udds
       return uctx''


-- | Analyse unit declaration or definition
ana_UNIT_DECL_DEFN :: LogicGraph -> AnyLogic -> GlobalContext -> AnyLogic 
		   -> Bool -> ExtStUnitCtx -> UNIT_DECL_DEFN -> IOResult (ExtStUnitCtx, DGraph, UNIT_DECL_DEFN)
-- ^ returns 1. extended static unit context 2. possibly modified development graph 
-- 3. possibly modified UNIT_DECL_DEFN

-- unit declaration
ana_UNIT_DECL_DEFN lgraph defl gctx@(gannos, genv, dg) curl justStruct 
		   uctx@(buc, diag) ud@(Unit_decl un@(Token _ unpos) usp uts pos) =
    do (dns@(Diag_node_sig n impSig), diag') <- ana_UNIT_IMPORTED defl uctx uts
       (usig, dg', usp') <- ana_UNIT_SPEC lgraph defl gctx curl justStruct impSig usp
       let ud' = Unit_decl un usp' uts pos
       if Map.member un buc 
	  then
	  resToIORes (plain_error (uctx, dg', ud')
		                  ("Unit " ++ showPretty un " already declared/defined")
		                  unpos)
	  else
	  case usig of
    	       Par_unit_sig (argSigs, resultSig) -> 
		   do (resultSig', dg'') <- resToIORes (nodeSigUnion lgraph dg' (resultSig : [impSig]) DGImports)
		      let basedParUSig = Based_par_unit_sig (dns, (argSigs, resultSig'))
   		      return ((Map.insert un basedParUSig buc, diag'), dg'', ud')
	       Unit_sig nsig -> 
		   do (nsig', dg'') <- resToIORes (nodeSigUnion lgraph dg' (impSig : [nsig]) DGImports)
		      (dn', diag'') <- extendDiagram diag' [dns] nsig'
		      return ((Map.insert un (Based_unit_sig dn') buc, diag''), dg'', ud')

-- unit definition
ana_UNIT_DECL_DEFN lgraph defl gctx@(_, _, dg) curl justStruct uctx@(buc, d) 
		   ud@(Unit_defn un@(Token _ unpos) uexp pos) =
    do (p, usig, diag) <- ana_UNIT_EXPRESSION defl gctx uctx uexp
       {- it's sufficient to check that un is not mapped in buc, we don't need
          to convert the ExtStUnitCtx to StUnitCtx as the domain will be preserved -}
       if Map.member un buc 
	  then
	  resToIORes (plain_error (uctx, dg, ud)
		                  ("Unit " ++ showPretty un " already defined/declared")
		                  unpos)
	  else
	  case usig of
	       -- we can use Map.insert as there are no mappings for un in ps and bs
	       -- (otherwise there would have been a mapping in (ctx uctx))
	       Unit_sig _ -> return ((Map.insert un (Based_unit_sig p) buc, diag),
				     dg, ud)
	       Par_unit_sig parusig -> return ((Map.insert un (Based_par_unit_sig (p, parusig)) buc, diag),
					       dg, ud)


-- | Analyse unit imports
-- TODO
ana_UNIT_IMPORTED :: AnyLogic -> ExtStUnitCtx -> [Annoted UNIT_TERM] -> IOResult (DiagNodeSig, Diag)
ana_UNIT_IMPORTED defl uctx uts =
    do resToIORes (warning (emptyDiagNodeLab defl, emptyDiag) "Ignoring unit imports" nullPos)
       extendDiagram emptyDiag [] (EmptyNode defl)
       -- return (emptyDiagNodeSig defl, emptyDiag)


-- | Analyse an unit expression
-- TODO
ana_UNIT_EXPRESSION :: AnyLogic -> GlobalContext -> ExtStUnitCtx 
		    -> UNIT_EXPRESSION -> IOResult (DiagNodeSig, UnitSig, Diag)
ana_UNIT_EXPRESSION defl gctx@(gannos, genv, dg) uctx uexp@(Unit_expression ubs ut pos) =
    do resToIORes (warning ((), emptyUnitSig defl, emptyDiag) "Ignoring unit expression" (headPos pos))
       return (emptyDiagNodeSig defl, emptyUnitSig defl, emptyDiag)


-- | Analyse an unit term
ana_UNIT_TERM :: LogicGraph -> AnyLogic -> GlobalContext -> AnyLogic 
	      -> Bool -> ExtStUnitCtx -> UNIT_TERM 
	      -> IOResult (DiagNodeSig, Diag, UNIT_TERM)
-- TODO
ana_UNIT_TERM lgraph defl gctx curl justStruct uctx@(buc, diag) ut =
    do resToIORes (warning (emptyDiagNodeSig defl, diag, ut) "Ignoring unit term" nullPos)
       return (emptyDiagNodeSig defl, diag, ut)


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
ana_UNIT_SPEC lgraph defl gctx@(_, _, dg) curl just_struct _ usp@(Arch_unit_spec asp poss) =
    do (_, usig) <- ana_ARCH_SPEC lgraph defl gctx curl just_struct (item asp)
       return (usig, dg, usp)
-- CLOSED-UNIT-SPEC
ana_UNIT_SPEC lgraph defl gctx curl just_struct _ usp@(Closed_unit_spec usp' poss) =
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
