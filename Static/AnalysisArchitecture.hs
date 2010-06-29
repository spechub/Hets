{- |
Module      :  $Header$
Description :  static analysis of CASL architectural specifications
Copyright   :  (c) Maciek Makowski, Warsaw University, C. Maeder 2004-2006
               Mihai Codescu, DFKI GmbH Bremen 2010
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
    , anaRefSpec
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

import Data.Graph.Inductive.Graph as Graph (Node, nodes)
import Control.Monad(foldM)

--import Debug.Trace

-- | Analyse an architectural specification
-- @
-- ARCH-SPEC ::= BASIC-ARCH-SPEC | GROUP-ARCH-SPEC | ARCH-SPEC-NAME
-- @
anaArchSpec :: LogicGraph -> DGraph
  -> HetcatsOpts  -- ^ should only the structure be analysed?
  -> ExtStUnitCtx -- ^ for visibility levels
  -> Maybe Node
  -> ARCH_SPEC -> Result ([DiagNodeSig],Maybe DiagNodeSig,
                          Diag,RefSig, DGraph, ARCH_SPEC)
{- ^ returns 1. the architectural signature of given ARCH-SPEC
2. development graph resulting from structured specs within the arch
spec and 3. ARCH_SPEC after possible conversions -}
anaArchSpec lgraph dg opts sharedCtx nP archSp = case archSp of
  Basic_arch_spec udd uexpr pos ->
    do (branchMap, uctx, dg', udd') <-
         anaUnitDeclDefns lgraph dg opts sharedCtx udd
       (nodes, usig, diag'', dg'', uexpr') <- -- trace "exp" $
           anaUnitExpression lgraph dg' opts uctx $ item uexpr
       let (nodes', maybeRes) = case nodes of
                [] -> ([], Nothing) -- don't think its possible
                x:[] -> ([], Just x)
                _ -> (nodes, Nothing)
           rNodes = -- trace (show $ Map.elems branchMap)$
                    map refSource $ Map.elems branchMap
           (rN, dg3) =
              case nP of
               Nothing -> let
                   (n, dgI) = addNodeRT dg'' usig "ArchSpec"
                          in (n, addEdgesToNodeRT dgI rNodes n)
               Just x -> (x, addEdgesToNodeRT dg' rNodes x)
           rP = NPBranch rN branchMap
       return (nodes', maybeRes,
                diag'',
                BranchRefSig rP (usig, Just $ BranchStaticContext (ctx uctx)),

                dg3, Basic_arch_spec udd'
                           (replaceAnnoted uexpr' uexpr) pos)
  Group_arch_spec asp _ -> anaArchSpec lgraph dg opts sharedCtx nP (item asp)
  Arch_spec_name asn@(Token astr pos) -> case lookupGlobalEnvDG asn dg of
            Just (ArchEntry asig@(BranchRefSig
                        (NPBranch n f) (UnitSig nsList resNs, _))) -> do
              let (rN, dg', asig') =
                        case nP of
                         Nothing -> let
                           (dg0, g) = copySubTree dg n Nothing
                           n0 = Map.findWithDefault (error "copy") n g
                           (r1, d1) = addNodeRefRT dg0 n0 $ show asn
                           a1 = setPointerInRef asig (NPBranch r1 $
                                 Map.map (mapRTNodes g) f)
                          in (r1, d1, a1)
                         Just x  -> let
                           (dg0, g) = copySubTree dg n Nothing
                           n0 = Map.findWithDefault (error "copy") n g
                           d1 = addRefEdgeRT dg0 x n0
                           a1 = setPointerInRef asig (NPBranch rN  $
                                 Map.map (mapRTNodes g) f)
                          in (x, d1, a1)
              case nsList of
               [] -> do
                 return ([], Nothing, snd sharedCtx, asig', dg', archSp)
               _ -> do
                (dnsigs, diag')<- foldM (\(l,d) ns -> do
                        (dns, d')<- extendDiagramIncl lgraph d [] ns "Arch Sig"
                        return (dns:l, d'))
                      ([], snd sharedCtx) $ reverse nsList
                (dns, diag'') <-
                   extendDiagramIncl lgraph diag' dnsigs resNs "arch sig"
                return (dns:dnsigs, Nothing, diag'', asig', dg', archSp)
            _ -> fatal_error (astr ++
                              " is not an architectural specification") pos

-- | Analyse a list of unit declarations and definitions
anaUnitDeclDefns :: LogicGraph -> DGraph
    -> HetcatsOpts -> ExtStUnitCtx -> [Annoted UNIT_DECL_DEFN]
    -> Result (Map.Map SIMPLE_ID RTPointer, ExtStUnitCtx,
               DGraph, [Annoted UNIT_DECL_DEFN])
{- ^ returns 1. extended static unit context 2. possibly modified
development graph 3. possibly modified list of unit declarations and
definitions -}
anaUnitDeclDefns lgraph dg opts sharedCtx =
  anaUnitDeclDefns' lgraph dg opts sharedCtx Map.empty

anaUnitDeclDefns' :: LogicGraph -> DGraph
    -> HetcatsOpts -> ExtStUnitCtx -> Map.Map SIMPLE_ID RTPointer
    -> [Annoted UNIT_DECL_DEFN]
    -> Result (Map.Map SIMPLE_ID RTPointer, ExtStUnitCtx,
               DGraph, [Annoted UNIT_DECL_DEFN])
anaUnitDeclDefns' lgraph dg opts uctx rNodes uds = case uds of
  udd : udds -> do
    (rNodes1, uctx', dg', udd') <- -- trace (show $ item udd)$
        anaUnitDeclDefn lgraph dg opts uctx (item udd)
    (rNodes2, uctx'', dg'', udds') <- --trace (show $ edges $ dgBody dg') $
        anaUnitDeclDefns' lgraph dg' opts uctx' (Map.union rNodes1 rNodes) udds
    return (rNodes2, uctx'', dg'', replaceAnnoted udd' udd : udds')
  [] -> return (rNodes, uctx, dg, [])

alreadyDefinedUnit :: SIMPLE_ID -> String
alreadyDefinedUnit u = "Unit " ++ tokStr u ++ " already declared/defined"

-- | Create a node that represents a union of signatures
nodeSigUnion :: LogicGraph -> DGraph -> [MaybeNode] -> DGOrigin
             -> Result (NodeSig, DGraph)
nodeSigUnion lgraph dg nodeSigs orig = --trace (show $ length nodeSigs) $
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
                     return $ insLEdgeNubDG
                       (n, node, globDefLink incl SeeTarget) dgv
     dg'' <- foldl inslink (return dg') nodeSigs
     return (NodeSig node sigUnion, dg'')

-- | Analyse unit declaration or definition
anaUnitDeclDefn :: LogicGraph -> DGraph
                   -> HetcatsOpts -> ExtStUnitCtx -> UNIT_DECL_DEFN
                   -> Result (Map.Map SIMPLE_ID RTPointer,
                              ExtStUnitCtx, DGraph, UNIT_DECL_DEFN)
{- ^ returns 1. extended static unit context 2. possibly modified
development graph 3. possibly modified UNIT_DECL_DEFN -}
anaUnitDeclDefn lgraph dg opts uctx@(buc, _) udd = case udd of
  Unit_decl un@(Token ustr unpos) usp uts pos -> do
       (dns, diag', dg', uts') <-
           anaUnitImported lgraph dg opts uctx pos uts
       let impSig = toMaybeNode dns
       (nodes, maybeRes, mDiag, rsig', dg0, usp') <-
           anaRefSpec lgraph dg' opts impSig un (buc, diag') Nothing usp
       usig <- getUnitSigFromRef rsig'
       let (n, dg1, rsig) =
              case getPointerFromRef rsig' of
               RTNone -> let (n',d') = addNodeRT dg0 usig $ show un
                             r' = setPointerInRef rsig' (NPUnit n')
                         in (n',d',r')
               _ -> --trace "RT" $
                    (refSource $ getPointerFromRef rsig', dg0, rsig')
           dg'' = --trace ("aUDD:" ++ show un)$
                  updateNodeNameRT dg1 n $ show un
       let diag = case mDiag of
                    Just d -> d
                    Nothing -> diag' -- check!
       let ud' = Unit_decl un usp' uts' pos
       case rsig of
        ComponentRefSig _ _ -> error $
                    "component refinement forbidden in arch spec: unit"
                    ++ show un
        _ -> do
         _usig@(UnitSig argSigs resultSig) <- getUnitSigFromRef rsig
         if Map.member un buc
          then plain_error (Map.empty,uctx, dg'', ud')
               (alreadyDefinedUnit un) unpos
          else  do -- !!!!! handle maybeRes here!!!
                      (resultSig', dg''') <- nodeSigUnion lgraph dg''
                          (JustNode resultSig:[impSig]) DGImports
                      (basedParUSig, diag''') <-  if null argSigs then do
                          (dn', diag'') <- extendDiagramIncl lgraph diag
                             ((case dns of
                                JustDiagNode dn -> [dn]
                                _ -> []) ++
                              (case maybeRes of
                                 Just x ->[x]
                                 _ -> [])) resultSig' ustr
                          return (Based_unit_sig dn' rsig, diag'')
-- here compare resultSig' and rsig
                          else if length nodes < 2 then
                                 return (Based_par_unit_sig dns $
                                         mkRefSigFromUnit $
                                         UnitSig argSigs resultSig', diag)
                                else
                                 return (Based_lambda_unit_sig nodes $
                                           mkRefSigFromUnit $
                                          UnitSig argSigs resultSig, diag)
-- here i need to return a different refinement signature
-- unitsig argsigs resultsig before refinement
-- and after refinement i introduce an unnamed component
-- this happens in all cases
                      return (Map.fromList [(un, getPointerFromRef rsig)],
                       (Map.insert un basedParUSig buc, diag'''),
                                  dg''', ud')
  Unit_defn un uexp poss -> do
       (nodes, usig, diag, dg'', uexp') <-
         anaUnitExpression lgraph dg opts uctx uexp
       let ud' = Unit_defn un uexp' poss
           --(n, dg'') = addNodeRT dg' usig $ show un
       {- it's sufficient to check that un is not mapped in buc, we
          don't need to convert the ExtStUnitCtx to StUnitCtx as the
          domain will be preserved -}
       if Map.member un buc then
          plain_error (Map.empty, uctx, dg'', ud')
                      (alreadyDefinedUnit un) $ tokPos un
          else -- trace "aU_d" $
               case usig of
               {- we can use Map.insert as there are no mappings for
                  un in ps and bs (otherwise there would have been a
                  mapping in (ctx uctx)) -}
               UnitSig args _ -> --trace ("defn:"++show nodes)$
                 if null args then
                   case nodes of
                     [dn] -> do
                              let bsig = Based_unit_sig dn $
                                           mkBotSigFromUnit usig
                              return (Map.empty,
                                      (Map.insert un bsig buc, diag),
                                        dg'', ud')
                     _ -> error "anaUnitDeclDefn"
                  else
                   if length nodes < 2 then
                     error "anaUnitDeclDefn:lambda expression"
                   else
                   return (Map.empty , (Map.insert un
                             (Based_lambda_unit_sig nodes $
                              mkBotSigFromUnit usig)
                             buc, diag), dg'', ud')

-- | Analyse unit refs
anaUnitRef :: LogicGraph -> DGraph
             -> HetcatsOpts -> ExtStUnitCtx -> Maybe RTLeaves -> UNIT_REF
             -> Result ((UNIT_NAME, RefSig), DGraph, UNIT_REF)
{- ^ returns 1. extended static unit context 2. possibly modified
development graph 3. possibly modified UNIT_DECL_DEFN -}
-- this was definitely wrong in the original function!
-- %%%%%%%%%%%%
-- no need for ExtStUnitCtx, just pair (un, rsig)
-- %%%%%%%%%%%
anaUnitRef lgraph dg opts
             _uctx@(_ggbuc, _diag') rN
             (Unit_ref un@(Token _ustr _unpos) usp pos) = do
-- %%%%%%%%%%%%%%%%%%%%
-- here: check if impSig is needed
--       check if ComponentRefSig is handled correctly.
-- %%%%%%%%%%%%%%%%%%%%
  let n = case rN of
           Nothing -> Nothing
           Just (RTLeaves f) -> Just $ Map.findWithDefault
                  (error "component not in map!") un f
           _ -> error "components!"
  curl <- lookupCurrentLogic "UNIT_REF" lgraph
  --let dns = EmptyDiagNode curl
  let impSig = EmptyNode curl
  ( _,_,_,rsig, dg'', usp') <- anaRefSpec lgraph dg opts impSig un
                        emptyExtStUnitCtx n usp
  -- check if this is enough !!!!!!
  -- no sharing
  let ud' = Unit_ref un usp' pos
  return ((un, rsig), dg'', ud')

-- -- | Analyse unit refs
-- anaUnitRef :: LogicGraph -> DGraph
--              -> HetcatsOpts -> ExtStUnitCtx -> UNIT_REF
--              -> Result (ExtStUnitCtx, DGraph, UNIT_REF)
-- {- ^ returns 1. extended static unit context 2. possibly modified
-- development graph 3. possibly modified UNIT_DECL_DEFN -}
-- -- unit declaration
-- anaUnitRef lgraph dg opts
--                    uctx@(buc, _) (Unit_ref un usp pos) =
--     do (dns, diag', dg', _) <-
--            anaUnitImported lgraph dg opts uctx pos []
--        let impSig = toMaybeNode dns
--        (nodes, diag'', usig, dg'', usp') <-
--            anaRefSpec lgraph dg' opts impSig (emptyStBasedUnitCtx, diag') usp
--        let diag = case diag'' of
--                    Just d -> d
--                    Nothing -> emptyDiag
--        -- aici trebuie sa reunesc diag si diag'!!!
--        insertBasedUnit lgraph dg'' nodes diag usig (buc, diag') dns un
--          $ Unit_ref un usp' pos


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
       (sig, dg'') <- --trace (show $ map (JustNode . getSigFromDiag) dnsigs)$
                      nodeSigUnion lgraph dg'
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
       (dnsig, diag', dg', ut') <- --trace (show ut)$
           anaUnitTerm lgraph dg opts uctx (item ut)
       (dnsigs, diag'', dg'', uts') <- --trace (show dnsig)$
           anaUnitImported' lgraph dg' opts (buc, diag') uts
       return (dnsig : dnsigs, diag'', dg'', replaceAnnoted ut' ut : uts')

-- | Analyse an unit expression
anaUnitExpression :: LogicGraph -> DGraph
    -> HetcatsOpts -> ExtStUnitCtx -> UNIT_EXPRESSION
    -> Result ([DiagNodeSig], UnitSig, Diag, DGraph, UNIT_EXPRESSION)
anaUnitExpression lgraph dg opts uctx@(buc, diag)
  uexp@(Unit_expression ubs ut poss) = case ubs of
  [] -> do
       (dnsig@(Diag_node_sig _ ns'), diag', dg', ut') <-
           anaUnitTerm lgraph dg opts uctx (item ut)
       --trace ("in exp: "++ show dnsig) $
       return ([dnsig], UnitSig [] ns', diag', dg',
               Unit_expression [] (replaceAnnoted ut' ut) poss)
  _ -> do
       (args, dg', ubs') <-
           anaUnitBindings lgraph dg opts uctx ubs
       -- (resnsig, _dg'') <- nodeSigUnion lgraph dg'
       --                     (map (JustNode . snd) args) DGFormalParams
       -- build the extended diagram and new based unit context
       let dexp = showDoc uexp ""
           insNodes diag0 [] buc0 = return ([], diag0, buc0)
           insNodes diag0 ((un, nsig) : args0) buc0 =
               do (dnsig, diag') <- extendDiagramIncl lgraph diag0 []
                           nsig $ show un
                  {- we made sure in anaUnitBindings that there's no
                     mapping for un in buc so we can just use
                     Map.insert -}
                  let rsig = BranchRefSig RTNone (UnitSig [] nsig) Nothing
                      buc' = Map.insert un (Based_unit_sig dnsig rsig) buc0
                  (dnsigs, diag'', buc'') <- insNodes diag' args0 buc'
                  return (dnsig : dnsigs, diag'', buc'')
       (pardnsigs, diag'', buc') <- insNodes diag args buc
       (resnsig,_) <- nodeSigUnion lgraph dg'
                              (map (JustNode . snd) args) DGFormalParams
       (Diag_node_sig nU _, diagI) <- --trace ("diag3:" ++ show diag'')$
                             extendDiagramIncl lgraph diag''
                             pardnsigs resnsig dexp
               -- only add the union to ensure compatibility of
               -- formal parameters
               -- but remove afterwards to be able to check
               -- compatibility of actual parameters: matchDiagram below
       (p@(Diag_node_sig _ pnsig), diag''', dg''', ut') <-
           --trace ("before:"++show diagI)$
           anaUnitTerm lgraph dg' opts (buc', diagI) (item ut)
       -- check amalgamability conditions
       let pos = getPosUnitExpression uexp
           checkSubSign dnsigs nsup =
             all (\ dnsub -> isSubGsign lgraph (getSig $ getSigFromDiag dnsub)
                  $ getSig nsup) dnsigs
       -- check that signatures in pardnsigs are subsignatures of pnsig
       if checkSubSign pardnsigs pnsig
          then
            do
               sink <- inclusionSink lgraph (p : pardnsigs) pnsig
               () <- --trace ("diag4:" ++ (show diag'''))$
                     assertAmalgamability opts pos diag''' sink
               -- add new node to the diagram
               --curl <- lookupCurrentLogic "UnitExpression" lgraph
               let (_, diag4) =  matchDiagram nU diag'''
               return (p:pardnsigs,
                        UnitSig (map snd args) pnsig,
                        diag4, dg''',
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
 	       curl <- lookupCurrentLogic "UNIT_BINDINGS" lgraph
 	       (BranchRefSig _ (_usig@(UnitSig argSigs nsig),_), dg', usp') <-
 	           anaUnitSpec lgraph dg opts (EmptyNode curl) Nothing usp
 	       let ub' = Unit_binding un usp' poss
 	       case null argSigs of
 	            False -> plain_error ([], dg', [])
 	                     ("An argument unit " ++
 	                      ustr ++ " must not be parameterized") unpos
 	            _ ->
 	                do (args, dg'', ubs') <- anaUnitBindings lgraph
 	                       dg' opts uctx ubs
 	                   let args' = (un, nsig) : args
 	                   if Map.member un buc
 	                      then plain_error (args', dg'', ub' : ubs')
 	                           (alreadyDefinedUnit un) unpos
 	                      else case lookup un args of
                                    Just _ ->
                                          plain_error (args', dg'', ub' : ubs')
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
anaUnitTerm :: LogicGraph -> DGraph -> HetcatsOpts -> ExtStUnitCtx
  -> UNIT_TERM -> Result (DiagNodeSig, Diag, DGraph, UNIT_TERM)
anaUnitTerm lgraph dg opts uctx@(buc, diag) utrm =
  let pos = getPosUnitTerm utrm
      utStr = showDoc utrm ""
  in case utrm of
  Unit_reduction ut restr -> do
       let orig = DGRestriction $ Restricted restr
       (p, diag1, dg1, ut') <- --trace ("before:"++(show $ edges $ dgBody dg)) $
           anaUnitTerm lgraph dg opts uctx (item ut)
       curl <- lookupCurrentLogic "UnitTerm" lgraph
       (incl, msigma) <- --trace ("p:" ++ show p) $
                         anaRestriction lgraph (emptyG_sign curl)
                         (getSig (getSigFromDiag p)) opts restr
       (q@(Diag_node_sig qn _), diag', dg') <-
           extendDiagramWithMorphismRev pos lgraph diag1 dg1 p incl utStr
            orig
       case msigma of
                  Nothing ->
                  {- the renaming morphism is just identity, so
                  there's no need to extend the diagram -}
                   --trace (show $ edges $ dgBody dg') $
                      return (q, diag', dg',
                                  Unit_reduction (replaceAnnoted ut' ut) restr)
                  Just sigma ->
                      do
                         -- check amalgamability conditions
                         let sink = [(qn, sigma)]
                         () <- assertAmalgamability opts pos diag' sink
                         (q', diag'', dg'') <- extendDiagramWithMorphism pos
                            lgraph diag' dg' q sigma utStr orig
                         --trace (show $ edges $ dgBody dg'') $
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
                (DGTranslation $ Renamed ren)
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
       (_, uctx', dg1, udds')<-
           anaUnitDeclDefns' lgraph dg opts uctx Map.empty udds
       (dnsig, diag', dg', ut') <-
           anaUnitTerm lgraph dg1 opts uctx' (item ut)
       return (dnsig, diag', dg',
               Local_unit udds' (replaceAnnoted ut' ut) poss)
  Unit_appl un fargus _ -> do
       let ustr = tokStr un
           argStr = showDoc fargus ""
       case --trace ("lookup:" ++ show un)$ trace (show  $ buc Map.! un) $
            Map.lookup un buc of
            Just (Based_unit_sig dnsig _rsig) -> case fargus of
              [] -> --trace ("in appl:" ++ show dnsig) $
                    return (dnsig, diag, dg, utrm)
              _ -> -- arguments have been given for a parameterless unit
                plain_error (dnsig, diag, dg, utrm)
                  (ustr ++ " is a parameterless unit, "
                   ++ "but arguments have been given: " ++ argStr) pos
            Just (Based_par_unit_sig pI
                     (BranchRefSig _ (UnitSig argSigs resultSig, _))) ->
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
                   () <- --trace ("diagA:" ++ show diagA) $
                         assertAmalgamability opts pos diagA sink
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
                   -- for lambda applications below
                   -- the node qB is not added, but only the edge from r
                   (q, diag''') <- extendDiagram diag'' qB
                                   sigMorExt sigR utStr
                   diag4 <- insInclusionEdges lgraph diag'''
                            (map third morphSigs) q
                   return (q, diag4, dg5, utrm)
            Just (Based_lambda_unit_sig nodes
              (BranchRefSig _ (UnitSig argSigs resultSig, _))) ->
              case nodes of
               [] -> error "error in lambda expression"
               r:fs ->
                do (sigF, dg') <- nodeSigUnion lgraph dg
                       (map JustNode argSigs) DGFormalParams
                   (morphSigs, dg'', diagA) <-
                       anaFitArgUnits lgraph dg' opts
                            uctx utrm pos argSigs fargus
                   let first (e, _, _) = e
                       second (_, e, _) = e
                       third (_, _, e) = e
                   (sigA, dg''') <- nodeSigUnion lgraph dg''
                       (map (JustNode . second) morphSigs)
                              DGFitSpec
                   -- compute morphA (\sigma^A)
                   morphA <- homogeneousMorManyUnion
                             $ map first morphSigs
                   -- compute sigMorExt (\sigma^A(\Delta))
                   (_, gSigMorExt) <- extendMorphism (getSig sigF)
                                     (getSig resultSig) (getSig sigA) morphA
                   -- check amalgamability conditions
                   let sigMorExt = gEmbed gSigMorExt
                   sink <- inclusionSink lgraph (map third morphSigs) sigA
                   () <- --trace ("in lambda:" ++ show diagA)$
                         assertAmalgamability opts pos diagA sink
                   let eI = zip fs $ map (\x->(first x, third x)) morphSigs
                   --  insert an edge from f_i to targetNode_i
                   -- extendDiagramWithEdge does it
                   -- and then call it for pairs (f_i, targetNode_i)
                   let ins diag0 dg0 [] = return (diag0, dg0)
                       ins diag0 dg0 ((fI,(morph, pIA)) : eIS) =
                           do (diag1, dg1) <-
                                extendDiagramWithEdge pos lgraph diag0
                                dg0 fI pIA (gEmbed morph) TEST
                              ins diag1 dg1 eIS
                   (diag', dg4) <- ins diagA dg''' eI
                   -- check amalgamability conditions
                   (sigR, dg5) <- extendDGraph dg4 resultSig
                                   sigMorExt DGExtension
                   incSink <- inclusionSink lgraph (map third morphSigs) sigR
                   assertAmalgamability opts pos diag' incSink
                   -- -- for lambda applications
                   -- -- the node qB is not added, but only the edge from r
                   (q, diag'') <- extendDiagram diag' r
                                    sigMorExt sigR utStr
                   diag3 <- insInclusionEdges lgraph diag''
                             (map third morphSigs) q
                   return (q, diag3, dg5, utrm)
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
              -> Maybe RTLeaves -- for building refinement trees
              -> UNIT_SPEC -> Result (RefSig, DGraph, UNIT_SPEC)
-- ^ returns 1. unit signature 2. the development graph resulting from
-- structred specs inside the unit spec and 3. a UNIT_SPEC after possible
-- conversions.
anaUnitSpec lgraph dg opts impsig rN usp = case usp of
  Unit_type argSpecs resultSpec poss ->  case argSpecs of
    [] -> case resultSpec of
      Annoted (Spec_inst spn [] _) _ _ _
        | case lookupGlobalEnvDG spn dg of
            Just (UnitEntry _) -> True
            Just (SpecEntry _) -> True
              -- without this i get signatures dont compose
            Just (RefEntry _) -> True
            _ -> False ->
       {- if argspecs are empty and resultspec is a name of unit spec
          then this should be converted to a Spec_name -}
        anaUnitSpec lgraph dg opts impsig rN (Spec_name spn)
      _ ->  do -- a trivial unit type
       (resultSpec', resultSig, dg') <- anaSpec False lgraph
           dg impsig emptyNodeName opts  (item resultSpec)
       let usig= UnitSig [] resultSig
       return (mkRefSigFromUnit usig , dg', Unit_type []
                            (replaceAnnoted resultSpec' resultSpec) poss)
    _ -> do -- a non-trivial unit type
       (argSigs, dg1, argSpecs') <- anaArgSpecs lgraph dg opts argSpecs
       (sigUnion, dg2) <- nodeSigUnion lgraph dg1
                          (impsig : map JustNode argSigs) DGFormalParams
        -- if i have no imports, i can optimize?
        -- in that case, an identity morphism is introduced
       (resultSpec', resultSig, dg3) <- anaSpec True lgraph
           dg2 (JustNode sigUnion)
                emptyNodeName opts (item resultSpec)
       let usig = UnitSig argSigs resultSig
           rsig = mkRefSigFromUnit usig
       return (rsig, dg3, Unit_type argSpecs'
                                (replaceAnnoted resultSpec' resultSpec) poss)
  Spec_name usn@(Token ustr pos) -> case lookupGlobalEnvDG usn dg of
    Just (UnitEntry usig) -> return (mkRefSigFromUnit usig, dg, usp)
    Just (SpecEntry (ExtGenSig _gsig@(GenSig _ args _) nsig) ) ->
     --trace (show usn)$
      return (mkRefSigFromUnit $ UnitSig args nsig, dg, usp)
    Just (RefEntry rsig) -> --trace ("rsig of: " ++ show usn) $
          case rN of
           Nothing -> let
             p = getPointerFromRef rsig
             s = refSource p
             (dg', f) = copySubTree dg s Nothing
             newP = mapRTNodes f p
            in return (setPointerInRef rsig newP , dg', usp)
           Just (RTLeaf x) -> let
                       p = getPointerFromRef rsig
                       s = refSource p
                       (dg', f) = copySubTree dg s $ Just x
                       --dg' = addTypingEdgeRT dg x $ refSource $
                       --       getPointerFromRef rsig
                       p'=  mapRTNodes f p
                       np' =
                             compPointer (NPUnit x) p'
                     in return (setPointerInRef rsig np', dg', usp)
           Just (RTLeaves leaves) -> let
               p = getPointerFromRef rsig
             in case p of
                  NPComp f2 -> error "nyi arch sig as ref"
                  _ -> error "can't compose signatures!"
    _ -> fatal_error (ustr ++ " is not an unit specification") pos
  Closed_unit_spec usp' _ -> do
    curl <- lookupCurrentLogic "UnitSpec" lgraph
    anaUnitSpec lgraph dg opts (EmptyNode curl) rN usp'

-- | Analyse refinement specification
anaRefSpec :: LogicGraph
              -> DGraph
              -> HetcatsOpts      -- ^ should only the structure be analysed?
              -> MaybeNode                   -- ^ the signature of imports
              -> SPEC_NAME -- for origin
              -> ExtStUnitCtx
              -> Maybe RTLeaves
              -> REF_SPEC
              -> Result ([DiagNodeSig], -- for lambda expressions
                         Maybe DiagNodeSig, -- for tracing between levels
                         Maybe Diag,
                         RefSig, DGraph, REF_SPEC)
anaRefSpec lgraph dg opts nsig rn sharedCtx nP rsp =
 case rsp of
  Unit_spec asp ->
    do
       (rsig, dg', asp') <-
           anaUnitSpec lgraph dg opts nsig nP asp
       usig <- getUnitSigFromRef rsig
       let rP = getPointerFromRef rsig
           (rsig', dg3) = case rP of
                           RTNone -> let
                             (n,dg'') = addNodeRT dg' usig $ name asp
                             r' = setPointerInRef rsig (NPUnit n)
                            in (r', dg'')
                           _ -> (rsig, dg')
       return $ ([], Nothing, Just (snd sharedCtx), rsig', dg3, Unit_spec asp')
  Arch_unit_spec asp poss ->
     do
       let x = case nP of
                Nothing -> Nothing
                Just (RTLeaf y) -> Just y
                _ -> error "nyi"
       (nodes,maybeRes, diag, rsig, dg', asp') <-
           anaArchSpec lgraph dg opts sharedCtx x $ item asp
       return (nodes, maybeRes, Just diag, rsig, dg',
               Arch_unit_spec (replaceAnnoted asp' asp) poss)
-- check whether it is indeed correct
-- to ignore the nodes of the
-- lambda expressions, like you do in the following
  Compose_ref rslist range ->
    do
       (dg', anaSpecs, _) <- foldM (\(dgr, rList, rN') rsp0 ->do
          (_,_,_,rsig', dgr',rsp')<-
                               anaRefSpec lgraph dgr opts nsig
                               (mkSimpleId $ (show  rn) ++ "gen_ref_name" ++
                                             (show $ length rList) )
                               sharedCtx rN' rsp0
 -- here Nothing will change
          --trace ("comp:" ++(show $ refTarget $ getPointerFromRef rsig'))$
          return (dgr', rList ++ [(rsig',rsp')],
                        Just $ refTarget $ getPointerFromRef rsig')
                           ) (dg, [], nP) rslist
       -- compose signatures in csig
       let refSigs = map fst anaSpecs
       csig <- foldM refSigComposition (head refSigs) $ tail refSigs
       let compRef = Compose_ref (map snd anaSpecs) range
-- here i would have to keep track of the first node inserted
-- and return it as root
-- and in the loop i would have to insert a refinement link
       --trace ("Compose - \n"++ show csig) $
       usig <- getUnitSigFromRef csig
       --let (n, dg'') = addNodeRT dg' usig "Composed refinements here"
       return ([], Nothing, Nothing, csig, dg', compRef)
  Component_ref urlist range ->  do
       (dg', anaRefs, resultMap, pMap) <-
         foldM (\(dgr, rList, cx, ps) uref0 -> do
          ((n,rs), dgr',uref')<-
                    anaUnitRef lgraph dgr opts emptyExtStUnitCtx nP uref0
          return (dgr', uref':rList , Map.insert n rs cx,
                  Map.insert n (getPointerFromRef rs) ps)
                           ) (dg, [], Map.empty, Map.empty) urlist
       -- here:
        -- insert a dummy node labeled with the name of the component
        -- insert a refinement link from the dummy node to the
        -- source of refinement
       return ([], Nothing, Nothing,
               ComponentRefSig (NPComp pMap) resultMap, dg',
               Component_ref (reverse anaRefs) range)
  Refinement beh uspec gMapList rspec range ->
   do
     -- beh will be ignored for now
     (_rsig@(BranchRefSig _ (usig,_)), dg', asp') <-
           anaUnitSpec lgraph dg opts nsig nP uspec
     (_, _, _, _rsig'@(BranchRefSig n2 (usig',bsig)), dgr',rsp') <-
           anaRefSpec lgraph dg' opts nsig rn emptyExtStUnitCtx Nothing rspec
             -- here Nothing is fine
     case (usig, usig') of
       (UnitSig _ls ns, UnitSig _ls' ns') -> do
               dg'' <- anaSymbMapRef dgr' ns ns' gMapList rn
               let (s, dg3) = case nP of
                               Nothing -> addNodeRT dg'' usig  $ name uspec
                               Just (RTLeaf x) -> (x, dg'')
                               _ -> error "can't refine to component!"
                   dg4 = -- trace ("ref link:"++show n2++ " " ++ show s)$
                         addRefEdgeRT dg3 s (refSource n2)
               --trace ("Refinement - \n " ++ show usig ++ " " ++ show bsig) $
               return ([], Nothing, Nothing,
                       BranchRefSig (compPointer (NPUnit s) n2)
                                    (usig, bsig) ,dg4,
                    Refinement beh asp' gMapList rsp' range)

 where
  name usp = case usp of
              Spec_name x -> show x
              Unit_type argSpecs resultSpec _ ->
                case argSpecs of
                 [] -> case resultSpec of
                        Annoted (Spec_inst spn [] _) _ _ _ -> show spn
                        _ -> ""
                 _ -> ""
              _ -> ""


anaSymbMapRef :: DGraph -> NodeSig -> NodeSig -> [G_mapping] -> SPEC_NAME ->
                    Result DGraph
anaSymbMapRef dg' ns ns' symbMap rn = do
   let gSigS = getSig ns
       nodeS = getNode ns
       gSigT = getSig ns'
       nodeT = getNode ns'
   G_sign lidS sigS _ <- return gSigS
   G_sign lidT sigT _ <- return gSigT
   G_symb_map_items_list lid sis <- homogenizeGM (Logic lidS) symbMap
   sigT' <- coerceSign lidT lidS "" sigT
   mor <- do
           rmap <- stat_symb_map_items lid sis
           rmap' <- coerceRawSymbolMap lid lidS "" rmap
           ext_induced_from_to_morphism lidS rmap' sigS sigT'
   let g_mor = mkG_morphism lidS mor
   -- for now we stay in the homogeneous case
   let gm = gEmbed g_mor
       linkLabel = DGLink{
                     dgl_morphism = gm,
                     dgl_type = globalThm,
                     dgl_origin = DGLinkRefinement rn,
                     dglPending = False,
                     dglName = emptyNodeName,
                     dgl_id = getNewEdgeId dg'
                   }
       (_, dg'') =  insLEdgeDG (nodeS, nodeT, linkLabel) dg'
   return dg''

------------------

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
