{-| 
Module      :  $Header$
Author      :  Maciek Makowski
Copyright   :  (c) Maciek Makowski, Warsaw University 2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt
Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  non-portable (Logic)

   Analysis of architectural specifications
   Follows the extended static semantics sketched in Chap. III:5.6
   of the CASL Reference Manual.
-}

module Static.AnalysisArchitecture (ana_ARCH_SPEC, ana_UNIT_SPEC)
where

import Maybe 
import Logic.Logic
import Logic.Grothendieck
-- import Common.Lib.Graph
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
ana_ARCH_SPEC :: LogicGraph -> AnyLogic -> GlobalContext 
	      -> AnyLogic -> Bool -> ARCH_SPEC
              -> IOResult ArchSig
-- BASIC-ARCH-SPEC
ana_ARCH_SPEC lgraph defl gctx@(gannos, genv, dg) l just_struct asp@(Basic_arch_spec udd uexpr pos) = 
    do uctx <- ana_UNIT_DECL_DEFNS defl gctx udd
       (_, usig, _) <- ana_UNIT_EXPRESSION defl gctx uctx (item uexpr)
       return (ctx uctx, usig)
-- GROUP-ARCH-SPEC
ana_ARCH_SPEC lgraph defl gctx@(gannos, genv, dg) l just_struct gsp@(Group_arch_spec asp pos) = 
    ana_ARCH_SPEC lgraph defl gctx l just_struct (item asp)
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


-- | Analyse a list of unit declarations/definitions
ana_UNIT_DECL_DEFNS :: AnyLogic -> GlobalContext -> [Annoted UNIT_DECL_DEFN] -> IOResult ExtStUnitCtx
ana_UNIT_DECL_DEFNS defl gctx udds = ana_UNIT_DECL_DEFNS' defl gctx emptyExtStUnitCtx udds

ana_UNIT_DECL_DEFNS' :: AnyLogic -> GlobalContext -> ExtStUnitCtx 
		     -> [Annoted UNIT_DECL_DEFN] -> IOResult ExtStUnitCtx
ana_UNIT_DECL_DEFNS' _ _ uctx [] =
    do return uctx
ana_UNIT_DECL_DEFNS' defl gctx uctx (udd : udds) =
    do uctx' <- ana_UNIT_DECL_DEFN defl gctx uctx (item udd)
       uctx'' <- ana_UNIT_DECL_DEFNS' defl gctx uctx' udds
       return uctx''


-- | Analyse unit declaration/definition
ana_UNIT_DECL_DEFN :: AnyLogic -> GlobalContext -> ExtStUnitCtx -> UNIT_DECL_DEFN -> IOResult ExtStUnitCtx
ana_UNIT_DECL_DEFN defl gctx@(gannos, genv, dg) uctx ud@(Unit_decl un usp uts pos) =
    -- TODO
    do resToIORes (warning emptyExtStUnitCtx "Ignoring unit declaration" (head (fromJust (get_pos_l ud))))
       return uctx
ana_UNIT_DECL_DEFN defl gctx uctx@(ps, bs, d) 
		   ud@(Unit_defn un@(Token _ unpos) uexp pos) =
    do (p, usig, diag) <- ana_UNIT_EXPRESSION defl gctx uctx uexp
       if Map.member un (ctx uctx)
	  then
	  resToIORes (plain_error uctx
		                  ("Unit " ++ showPretty un " already defined")
		                  unpos)
	  else
	  case usig of
	       -- we can use Map.insert as there are no mappings for un in ps and bs
	       -- (otherwise there would have been a mapping in (ctx uctx))
	       Unit_sig _ -> return (ps, Map.insert un p bs, d)
	       Par_unit_sig parusig -> return (Map.insert un (p, parusig) ps, bs, d)


-- | Analyse unit imports
-- TODO
ana_UNIT_IMPORTED :: ExtStUnitCtx -> [Annoted UNIT_TERM] -> IOResult (Item, Diag)
ana_UNIT_IMPORTED uctx uts =
    do resToIORes (warning ((), emptyDiag) "Ignoring unit imports" nullPos)
       return (0, emptyDiag)


-- | Analyse an unit expression
-- TODO
ana_UNIT_EXPRESSION :: AnyLogic -> GlobalContext -> ExtStUnitCtx 
		    -> UNIT_EXPRESSION -> IOResult (Item, UnitSig, Diag)
ana_UNIT_EXPRESSION defl gctx@(gannos, genv, dg) uctx uexp@(Unit_expression ubs ut pos) =
    do resToIORes (warning ((), emptyUnitSig defl, emptyDiag) "Ignoring unit expression" (headPos pos))
       return (0, emptyUnitSig defl, emptyDiag)


-- | Analyse unit specification
ana_UNIT_SPEC :: LogicGraph -> AnyLogic -> GlobalContext -> AnyLogic 
	      -> Bool -> NodeSig -> UNIT_SPEC -> IOResult (UnitSig, DGraph, UNIT_SPEC)
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