{- |
Module      :  $Header$
Description :  static analysis of CASL architectural specifications
Copyright   :  (c) Maciek Makowski, Warsaw University, C. Maeder 2004-2006
               Mihai Codescu, DFKI GmbH Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt
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
import Common.ExtSign
import Common.Id
import Common.LibName
import Common.Result
import Common.Amalgamate
import Common.DocUtils
import qualified Data.Map as Map

import Data.Maybe
import Data.Graph.Inductive.Graph as Graph (Node, edges)
import Control.Monad (foldM)

import Debug.Trace

{- | Analyse an architectural specification
@
ARCH-SPEC ::= BASIC-ARCH-SPEC | GROUP-ARCH-SPEC | ARCH-SPEC-NAME
@ -}
anaArchSpec :: LogicGraph -> LibName -> DGraph
  -> HetcatsOpts  -- ^ should only the structure be analysed?
  -> ExtStUnitCtx -- ^ for visibility levels
  -> Maybe Node
  -> ARCH_SPEC -> Result ([DiagNodeSig], Maybe DiagNodeSig,
                          Diag, RefSig, DGraph, ARCH_SPEC)
{- ^ returns 1. the architectural signature of given ARCH-SPEC
2. development graph resulting from structured specs within the arch
spec and 3. ARCH_SPEC after possible conversions -}
anaArchSpec lgraph ln dg opts sharedCtx nP archSp = case archSp of
  Basic_arch_spec udd uexpr pos ->
    do (branchMap, uctx, dg', udd') <-
         anaUnitDeclDefns lgraph ln dg opts sharedCtx udd
       (nodes, usig, diag'', dg'', uexpr') <-
           anaUnitExpression lgraph ln dg' opts uctx $ item uexpr
       let (nodes', maybeRes) = case nodes of
                [] -> ([], Nothing) -- don't think its possible
                x : [] -> ([], Just x)
                _ -> (nodes, Nothing)
           rNodes = map refSource $ Map.elems branchMap
           (rN, dg3) =
              case nP of
               Nothing -> let
                   (n, dgI) = addNodeRT dg'' usig "ArchSpec"
                          in (n, addEdgesToNodeRT dgI rNodes n)
               Just x -> (x, addEdgesToNodeRT dg' rNodes x)
           rP = NPBranch rN branchMap
       return (nodes', maybeRes, diag'',
                BranchRefSig rP (usig, Just $ BranchStaticContext (ctx uctx)),
                dg3, Basic_arch_spec udd'
                           (replaceAnnoted uexpr' uexpr) pos)
  Group_arch_spec asp _ -> anaArchSpec lgraph ln dg opts sharedCtx nP (item asp)
  Arch_spec_name asn@(Token astr pos) -> case lookupGlobalEnvDG asn dg of
            Just (ArchEntry asig@(BranchRefSig
                        (NPBranch n f) (UnitSig nsList resNs _, _))) -> do
              let (rN, dg', asig') =
                        case nP of
                         Nothing -> let
                           (dg0, g) = copySubTree dg n Nothing
                           n0 = Map.findWithDefault (error "copy") n g
                           (r1, d1) = (n0, dg0) -- TODO: this is not needed
                           a1 = setPointerInRef asig (NPBranch r1 $
                                 Map.map (mapRTNodes g) f)
                          in (r1, d1, a1)
                         Just x -> let
                           (dg0, g) = copySubTree dg n Nothing
                           n0 = Map.findWithDefault (error "copy") n g
                           d1 = addRefEdgeRT dg0 x n0
                           a1 = setPointerInRef asig (NPBranch rN $
                                 Map.map (mapRTNodes g) f)
                          in (x, d1, a1)
              case nsList of
               [] ->
                 return ([], Nothing, snd sharedCtx, asig', dg', archSp)
               _ -> do
                (dnsigs, diag') <- foldM (\ (l, d) ns -> do
                        (dns, d') <- extendDiagramIncl lgraph d [] ns "Arch Sig"
                        return (dns : l, d'))
                      ([], snd sharedCtx) $ reverse nsList
                (dns, diag'') <-
                   extendDiagramIncl lgraph diag' dnsigs resNs "arch sig"
                return (dns : dnsigs, Nothing, diag'', asig', dg', archSp)
            _ -> fatal_error (astr ++
                              " is not an architectural specification") pos

-- | Analyse a list of unit declarations and definitions
anaUnitDeclDefns :: LogicGraph -> LibName -> DGraph
    -> HetcatsOpts -> ExtStUnitCtx -> [Annoted UNIT_DECL_DEFN]
    -> Result (Map.Map SIMPLE_ID RTPointer, ExtStUnitCtx,
               DGraph, [Annoted UNIT_DECL_DEFN])
{- ^ returns 1. extended static unit context 2. possibly modified
development graph 3. possibly modified list of unit declarations and
definitions -}
anaUnitDeclDefns lgraph ln dg opts sharedCtx =
  anaUnitDeclDefns' lgraph ln dg opts sharedCtx Map.empty

anaUnitDeclDefns' :: LogicGraph -> LibName -> DGraph
    -> HetcatsOpts -> ExtStUnitCtx -> Map.Map SIMPLE_ID RTPointer
    -> [Annoted UNIT_DECL_DEFN]
    -> Result (Map.Map SIMPLE_ID RTPointer, ExtStUnitCtx,
               DGraph, [Annoted UNIT_DECL_DEFN])
anaUnitDeclDefns' lgraph ln dg opts uctx rNodes uds = case uds of
  udd : udds -> do
    (rNodes1, uctx', dg', udd') <-
        anaUnitDeclDefn lgraph ln dg opts uctx (item udd)
    (rNodes2, uctx'', dg'', udds') <- anaUnitDeclDefns' lgraph ln dg' opts
      uctx' (Map.union rNodes1 rNodes) udds
    return (rNodes2, uctx'', dg'', replaceAnnoted udd' udd : udds')
  [] -> return (rNodes, uctx, dg, [])

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
                     return $ insLEdgeNubDG
                       (n, node, globDefLink incl SeeTarget) dgv
     dg'' <- foldl inslink (return dg') nodeSigs
     return (NodeSig node sigUnion, dg'')

-- | Analyse unit declaration or definition
anaUnitDeclDefn :: LogicGraph -> LibName -> DGraph -> HetcatsOpts
  -> ExtStUnitCtx -> UNIT_DECL_DEFN
  -> Result (Map.Map SIMPLE_ID RTPointer, ExtStUnitCtx, DGraph, UNIT_DECL_DEFN)
{- ^ returns 1. extended static unit context 2. possibly modified
development graph 3. possibly modified UNIT_DECL_DEFN -}
anaUnitDeclDefn lgraph ln dg opts uctx@(buc, _) udd = case udd of
  Unit_decl un@(Token ustr unpos) usp uts pos -> do
       (dns, diag', dg', uts') <-
           anaUnitImported lgraph ln dg opts uctx pos uts
       let impSig = toMaybeNode dns
       (nodes, maybeRes, mDiag, rsig', dg0, usp') <-
           anaRefSpec lgraph ln dg' opts impSig un (buc, diag') Nothing usp
       usig@(UnitSig argSigs resultSig unionSig) <- getUnitSigFromRef rsig'
       let (n, dg1, rsig0) =
              case getPointerFromRef rsig' of
               RTNone -> let
                             (n', d') = addNodeRT dg0 usig $ show un
                             r' = setPointerInRef rsig' (NPUnit n')
                         in (n', d', r')
               _ -> (refSource $ getPointerFromRef rsig', dg0, rsig')
{- is this above needed? when can rsig' have no pointer?
TO DO -}
       (dg'', rsig) <- case impSig of
         EmptyNode _ -> do
          (resultSig', dg2) <- case unionSig of
              Just x -> nodeSigUnion lgraph dg1
                          [JustNode x, JustNode resultSig] DGImports
              _ -> return (resultSig, dg1)
          return (updateNodeNameRT dg2 n $ show un,
                  setUnitSigInRef rsig0 $ UnitSig argSigs resultSig' unionSig)
              -- S -> T becomes S -> S \cup T
         JustNode ns -> do
           let dg2 = updateNodeNameRT dg1 n $ show un
                -- this changes the name of the node in the RT
           (argUnion, dg3) <- nodeSigUnion lgraph dg2
                              (map JustNode argSigs ++ [impSig])
                              DGImports
                -- union of the arguments with the imports
           (resultSig', dg4) <- nodeSigUnion lgraph dg3
                          [JustNode resultSig, JustNode argUnion] DGImports
                {- union of the arguments with the result
                   F : S -> T given M
                   becomes F : M * S -> S_M \cup S \cup T -}
           let dgU = updateSigRT dg4 n $ UnitSig [] resultSig' Nothing
                -- now stores S \cup T
               usig' = UnitSig (ns : argSigs) resultSig' $ Just argUnion
               (newN, dgU') = addNodeRT dgU usig' ""
               newP = NPBranch n $ Map.fromList [(mkSimpleId "a", NPUnit newN)]
               rUnit = UnitSig argSigs resultSig' $ Just argUnion
               rSig = BranchRefSig newP (rUnit, Just $ BranchStaticContext $
                         Map.insert (mkSimpleId "a") (mkRefSigFromUnit usig')
                            Map.empty)
           return (addEdgesToNodeRT dgU' [newN] n, rSig)
             -- check the pointer
       let diag = fromMaybe diag' mDiag
           ud' = Unit_decl un usp' uts' pos
       case rsig of
          ComponentRefSig _ _ -> error $
                     "component refinement forbidden in arch spec: unit"
                     ++ show un
          _ ->
           if Map.member un buc
            then plain_error (Map.empty, uctx, dg'', ud')
               (alreadyDefinedUnit un) unpos
            else do
                      _usigN@(UnitSig argSigsN resultSig' unionSigN) <-
                          getUnitSigFromRef rsig
                      (basedParUSig, diag''') <- if null argSigsN then do
                          (dn', diag'') <- extendDiagramIncl lgraph diag
                             ((case dns of
                                JustDiagNode dn -> [dn]
                                _ -> []) ++
                              (case maybeRes of
                                 Just x -> [x]
                                 _ -> [])) resultSig' ustr
                          return (Based_unit_sig dn' rsig, diag'')
                          else if length nodes < 2 then do
                                -- clarify the pointers here
                                 let rsig'' =
                                      setPointerInRef
                                       (setUnitSigInRef rsig $
                                         UnitSig argSigsN resultSig' unionSigN)
                                       (NPUnit n)
                                 return (Based_par_unit_sig dns rsig''
                                         , diag)
                                else do
             -- here we handle U : arch spec ASP with ASP parametric
                                 let rsig'' = setPointerInRef
                                              (setUnitSigInRef rsig usig)
                                              (NPUnit n)
                                 return (Based_lambda_unit_sig nodes rsig'',
                                         diag)
                      return (Map.fromList [(un, getPointerFromRef rsig)],
                       (Map.insert un basedParUSig buc, diag'''),
                                  dg'', ud')
  Unit_defn un uexp poss -> do
       (nodes, usig, diag, dg'', uexp') <-
         anaUnitExpression lgraph ln dg opts uctx uexp
       let ud' = Unit_defn un uexp' poss
       if Map.member un buc then
          plain_error (Map.empty, uctx, dg'', ud')
                      (alreadyDefinedUnit un) $ tokPos un
          else case usig of
               {- we can use Map.insert as there are no mappings for
                  un in ps and bs (otherwise there would have been a
                  mapping in (ctx uctx)) -}
               UnitSig args _ _ -> case args of
                 [] -> case nodes of
                     [dn] -> do
                              let bsig = Based_unit_sig dn $
                                           mkBotSigFromUnit usig
                              return (Map.empty,
                                      (Map.insert un bsig buc, diag),
                                        dg'', ud')
                     _ -> error "anaUnitDeclDefn"
                 _ -> case nodes of
                   _ : _ : _ ->
                     return (Map.empty , (Map.insert un
                             (Based_lambda_unit_sig nodes $
                              mkBotSigFromUnit usig)
                             buc, diag), dg'', ud')
                   _ -> error "anaUnitDeclDefn:lambda expression"

-- | Analyse unit refs
anaUnitRef :: LogicGraph -> LibName -> DGraph
             -> HetcatsOpts -> ExtStUnitCtx -> Maybe RTPointer -> UNIT_REF
             -> Result ((UNIT_NAME, RefSig), DGraph, UNIT_REF)
{- ^ returns 1. extended static unit context 2. possibly modified
development graph 3. possibly modified UNIT_DECL_DEFN -}
anaUnitRef lgraph ln dg opts
             _uctx@(_ggbuc, _diag') rN
             (Unit_ref un@(Token _ustr _unpos) usp pos) = do
  let n = case rN of
           Nothing -> Nothing
           Just (NPComp f) -> Just $ Map.findWithDefault
                  (error "component not in map!") un f
           Just (NPBranch _ f) -> Just $ Map.findWithDefault
                  (error "component not in map!") un f
           _ -> error "components!"
  curl <- lookupCurrentLogic "UNIT_REF" lgraph
  let impSig = EmptyNode curl
  ( _, _, _, rsig, dg'', usp') <- anaRefSpec lgraph ln dg opts impSig un
                        emptyExtStUnitCtx n usp
  let ud' = Unit_ref un usp' pos
  return ((un, rsig), dg'', ud')


-- | Analyse unit imports
anaUnitImported :: LogicGraph -> LibName -> DGraph
    -> HetcatsOpts -> ExtStUnitCtx -> Range -> [Annoted UNIT_TERM]
    -> Result (MaybeDiagNode, Diag, DGraph, [Annoted UNIT_TERM])
anaUnitImported lgraph ln dg opts uctx@(_, diag) poss terms =
  case terms of
  [] -> do
    curl <- lookupCurrentLogic "UnitImported" lgraph
    return (EmptyDiagNode curl, diag, dg, [])
  _ -> do
       (dnsigs, diag', dg', terms') <-
           anaUnitImported' lgraph ln dg opts uctx terms
       (sig, dg'') <- nodeSigUnion lgraph dg'
                      (map (JustNode . getSigFromDiag) dnsigs) DGImports
       let pos = getPosUnitImported poss
       sink <- inclusionSink lgraph dnsigs sig
       () <- assertAmalgamability opts pos diag' sink
       (dnsig, diag'') <- extendDiagramIncl lgraph diag' dnsigs
                          sig $ showDoc terms ""
       return (JustDiagNode dnsig, diag'', dg'', terms')

anaUnitImported' :: LogicGraph -> LibName -> DGraph
    -> HetcatsOpts -> ExtStUnitCtx -> [Annoted UNIT_TERM]
    -> Result ([DiagNodeSig], Diag, DGraph, [Annoted UNIT_TERM])
anaUnitImported' lgraph ln dg opts uctx@(buc, diag) ts = case ts of
    [] -> return ([], diag, dg, [])
    ut : uts -> do
       (dnsig, diag', dg', ut') <-
           anaUnitTerm lgraph ln dg opts uctx (item ut)
       (dnsigs, diag'', dg'', uts') <-
           anaUnitImported' lgraph ln dg' opts (buc, diag') uts
       return (dnsig : dnsigs, diag'', dg'', replaceAnnoted ut' ut : uts')

-- | Analyse an unit expression
anaUnitExpression :: LogicGraph -> LibName -> DGraph
    -> HetcatsOpts -> ExtStUnitCtx -> UNIT_EXPRESSION
    -> Result ([DiagNodeSig], UnitSig, Diag, DGraph, UNIT_EXPRESSION)
anaUnitExpression lgraph ln dg opts uctx@(buc, diag)
  uexp@(Unit_expression ubs ut poss) = case ubs of
  [] -> do
       (dnsig@(Diag_node_sig _ ns'), diag', dg', ut') <-
           anaUnitTerm lgraph ln dg opts uctx (item ut)
       return ([dnsig], UnitSig [] ns' Nothing, diag', dg',
               Unit_expression [] (replaceAnnoted ut' ut) poss)
  _ -> do
       (args, dg', ubs') <-
           anaUnitBindings lgraph ln dg opts uctx ubs
       let dexp = showDoc uexp ""
           insNodes diag0 [] buc0 = return ([], diag0, buc0)
           insNodes diag0 ((un, nsig) : args0) buc0 =
               do (dnsig, diag') <- extendDiagramIncl lgraph diag0 []
                           nsig $ show un
                  {- we made sure in anaUnitBindings that there's no
                     mapping for un in buc so we can just use
                     Map.insert;
                   here RTNone actually makes sense -}
                  let rsig = BranchRefSig RTNone
                               (UnitSig [] nsig Nothing, Nothing)
                      buc' = Map.insert un (Based_unit_sig dnsig rsig) buc0
                  (dnsigs, diag'', buc'') <- insNodes diag' args0 buc'
                  return (dnsig : dnsigs, diag'', buc'')
       (pardnsigs, diag'', buc') <- insNodes diag args buc
       (resnsig, _) <- nodeSigUnion lgraph dg'
                              (map (JustNode . snd) args) DGFormalParams
       (Diag_node_sig nU _, diagI) <-
                             extendDiagramIncl lgraph diag''
                             pardnsigs resnsig dexp
               {- only add the union to ensure compatibility of
               formal parameters
               but remove afterwards to be able to check
               compatibility of actual parameters: matchDiagram below -}
       (p@(Diag_node_sig _ pnsig), diag''', dg''', ut') <-
           anaUnitTerm lgraph ln dg' opts (buc', diagI) (item ut)
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
               () <-
                     assertAmalgamability opts pos diag''' sink
               -- add new node to the diagram
               let (_, diag4) = matchDiagram nU diag'''
               return (p : pardnsigs,
                        UnitSig (map snd args) pnsig $ Just resnsig,
                          -- check!
                        diag4, dg''',
                       Unit_expression ubs' (replaceAnnoted ut' ut) poss)
          else -- report an error
              fatal_error
          ("The body signature does not extend the parameter signatures in\n"
           ++ dexp) pos

{- | Analyse a list of unit bindings. Ensures that the unit names are
not present in extended static unit context and that there are no
duplicates among them. -}
anaUnitBindings :: LogicGraph -> LibName -> DGraph
    -> HetcatsOpts -> ExtStUnitCtx -> [UNIT_BINDING]
    -> Result ([(SIMPLE_ID, NodeSig)], DGraph, [UNIT_BINDING])
anaUnitBindings lgraph ln dg opts uctx@(buc, _) bs = case bs of
          [] -> return ([], dg, [])
          Unit_binding un@(Token ustr unpos) usp poss : ubs -> do
               curl <- lookupCurrentLogic "UNIT_BINDINGS" lgraph
               (BranchRefSig _ (UnitSig argSigs nsig _, _), dg', usp') <-
                   anaUnitSpec lgraph ln dg opts (EmptyNode curl) Nothing usp
               let ub' = Unit_binding un usp' poss
               case argSigs of
                    _ : _ -> plain_error ([], dg', [])
                             ("An argument unit " ++
                              ustr ++ " must not be parameterized") unpos
                    [] ->
                        do (args, dg'', ubs') <- anaUnitBindings lgraph ln
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
anaUnitTerms :: LogicGraph -> LibName -> DGraph
    -> HetcatsOpts -> ExtStUnitCtx -> [Annoted UNIT_TERM]
    -> Result ([DiagNodeSig], Diag, DGraph, [Annoted UNIT_TERM])
anaUnitTerms lgraph ln dg opts uctx@(buc, diag) ts = case ts of
  [] -> return ([], diag, dg, [])
  ut : uts -> do
       (dnsig, diag', dg', ut') <-
           anaUnitTerm lgraph ln dg opts uctx (item ut)
       (dnsigs, diag'', dg'', uts') <- anaUnitTerms lgraph ln
               dg' opts (buc, diag') uts
       return (dnsig : dnsigs, diag'', dg'', replaceAnnoted ut' ut : uts')

-- | Analyse an unit term
anaUnitTerm :: LogicGraph -> LibName -> DGraph -> HetcatsOpts -> ExtStUnitCtx
  -> UNIT_TERM -> Result (DiagNodeSig, Diag, DGraph, UNIT_TERM)
anaUnitTerm lgraph ln dg opts uctx@(buc, diag) utrm =
  let pos = getPosUnitTerm utrm
      utStr = showDoc utrm ""
  in case utrm of
  Unit_reduction ut restr -> do
       let orig = DGRestriction $ Restricted restr
       (p, diag1, dg1, ut') <-
           anaUnitTerm lgraph ln dg opts uctx (item ut)
       curl <- lookupCurrentLogic "UnitTerm" lgraph
       (incl, msigma) <- anaRestriction lgraph (emptyG_sign curl)
                         (getSig (getSigFromDiag p)) opts restr
       (q@(Diag_node_sig qn _), diag', dg') <-
           extendDiagramWithMorphismRev pos lgraph diag1 dg1 p incl utStr
            orig
       case msigma of
                  Nothing ->
                  {- the renaming morphism is just identity, so
                  there's no need to extend the diagram
                   -}
                      return (q, diag', dg',
                                  Unit_reduction (replaceAnnoted ut' ut) restr)
                  Just sigma ->
                      do
                         -- check amalgamability conditions
                         let sink = [(qn, sigma)]
                         () <- assertAmalgamability opts pos diag' sink
                         (q', diag'', dg'') <- extendDiagramWithMorphism pos
                            lgraph diag' dg' q sigma utStr orig
                         return (q', diag'', dg'',
                                   Unit_reduction
                                   (replaceAnnoted ut' ut) restr)
  Unit_translation ut ren -> do
       (dnsig@(Diag_node_sig p _), diag1, dg1, ut') <-
           anaUnitTerm lgraph ln dg opts uctx (item ut)
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
           anaUnitTerms lgraph ln dg opts uctx uts
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
       (_, uctx', dg1, udds') <-
           anaUnitDeclDefns' lgraph ln dg opts uctx Map.empty udds
       (dnsig, diag', dg', ut') <-
           anaUnitTerm lgraph ln dg1 opts uctx' (item ut)
       return (dnsig, diag', dg',
               Local_unit udds' (replaceAnnoted ut' ut) poss)
  Unit_appl un fargus _ -> do
       let ustr = tokStr un
           argStr = showDoc fargus ""
       case Map.lookup un buc of
            Just (Based_unit_sig dnsig _rsig) -> case fargus of
              [] -> return (dnsig, diag, dg, utrm)
              _ -> plain_error (dnsig, diag, dg, utrm)
                  (ustr ++ " is a parameterless unit, "
                   ++ "but arguments have been given: " ++ argStr) pos
            Just (Based_par_unit_sig pI
                     (BranchRefSig _ (UnitSig argSigs resultSig _, _))) ->
                do (sigF, dg') <- nodeSigUnion lgraph dg
                       (toMaybeNode pI : map JustNode argSigs) DGFormalParams
                   (morphSigs, dg'', diagA) <-
                       anaFitArgUnits lgraph ln dg' opts
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
                   {- for lambda applications below
                   the node qB is not added, but only the edge from r -}
                   (q, diag''') <- extendDiagram diag'' qB
                                   sigMorExt sigR utStr
                   diag4 <- insInclusionEdges lgraph diag'''
                            (map third morphSigs) q
                   return (q, diag4, dg5, utrm)
            Just (Based_lambda_unit_sig nodes
              (BranchRefSig _ (UnitSig argSigs resultSig _, _))) ->
              case nodes of
               [] -> error "error in lambda expression"
               r : fs ->
                do (sigF, dg') <- nodeSigUnion lgraph dg
                       (map JustNode argSigs) DGFormalParams
                   (morphSigs, dg'', diagA) <-
                       anaFitArgUnits lgraph ln dg' opts
                            uctx utrm pos argSigs fargus
                   let first (e, _, _) = e
                       second (_, e, _) = e
                       third (_, _, e) = e
                   (sigA, dg''') <- trace (show $ edges $ diagGraph diagA)
                                    $ nodeSigUnion lgraph dg''
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
                   () <- assertAmalgamability opts pos diagA sink
                   let eI = zip fs $ map (\ (x, _, z) -> (x, z)) morphSigs
                   {- insert an edge from f_i to targetNode_i
                   extendDiagramWithEdge does it
                   and then call it for pairs (f_i, targetNode_i) -}
                   let ins diag0 dg0 [] = return (diag0, dg0)
                       ins diag0 dg0 ((fI, (morph, pIA)) : eIS) =
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
                   {- -- for lambda applications
                   -- the node qB is not added, but only the edge from r -}
                   (q, diag'') <- extendDiagram diag' r
                                    sigMorExt sigR utStr
                   diag3 <- insInclusionEdges lgraph diag''
                             (map third morphSigs) q
                   return (q, diag3, dg5, utrm)
            _ -> fatal_error ("Undefined unit " ++ ustr) pos
  Group_unit_term ut poss -> do
       (dnsig, diag1, dg1, ut') <-
           anaUnitTerm lgraph ln dg opts uctx (item ut)
       return (dnsig, diag1, dg1, Group_unit_term (replaceAnnoted ut' ut) poss)

-- | Analyse unit arguments
anaFitArgUnits :: LogicGraph -> LibName -> DGraph
    -> HetcatsOpts -> ExtStUnitCtx -> UNIT_TERM
    -- ^ the whole application for diagnostic purposes
    -> Range
    -- ^ the position of the application (for diagnostic purposes)
    -> [NodeSig]
    -- ^ the signatures of unit's formal parameters
    -> [FIT_ARG_UNIT] -- ^ the arguments for the unit
    -> Result ([(G_morphism, NodeSig, DiagNodeSig)], DGraph, Diag)
anaFitArgUnits lgraph ln dg opts uctx@(buc, diag)
                  appl pos nodeSigs fArgs = case (nodeSigs, fArgs) of
  (nsig : nsigs, fau : faus) -> do
       (gmorph, nsig', dnsig, dg1, diag1) <-
           anaFitArgUnit lgraph ln dg opts uctx nsig fau
       (morphSigs, dg', diag') <- anaFitArgUnits lgraph ln dg1 opts
           (buc, diag1) appl pos nsigs faus
       return ((gmorph, nsig', dnsig) : morphSigs, dg', diag')
  ([], []) -> return ([], dg, diag)
  _ -> plain_error ([], dg, diag)
       ("non-matching number of arguments given in application\n"
                    ++ showDoc appl "") pos

-- | Analyse unit argument
anaFitArgUnit :: LogicGraph -> LibName -> DGraph
    -> HetcatsOpts -> ExtStUnitCtx -> NodeSig -> FIT_ARG_UNIT
    -> Result (G_morphism, NodeSig, DiagNodeSig, DGraph, Diag)
{- ^ returns 1. the signature morphism 2. the target signature of the morphism
3. the diagram node 4. the modified DGraph 5. the modified diagram -}
anaFitArgUnit lgraph ln dg opts uctx nsig
                     (Fit_arg_unit ut symbMap poss) = adjustPos poss $ do
       (p, diag', dg', _) <-
           anaUnitTerm lgraph ln dg opts uctx (item ut)
       let gsigmaS = getSig nsig
           gsigmaT = getSig (getSigFromDiag p)
       G_sign lidS sigmaS _ <- return gsigmaS
       G_sign lidT sigmaT _ <- return gsigmaT
       G_symb_map_items_list lid sis <- homogenizeGM (Logic lidS) symbMap
       sigmaT' <- coerceSign lidT lidS "anaFitArgUnit1" sigmaT
       mor <- if isStructured opts then return (ext_ide sigmaS) else do
         ExtSign sigS' _ <- coerceSign lidS lid "anaFitArgUnit2" sigmaS
         rmap <- stat_symb_map_items lid sigS' sis
         rmap' <- coerceRawSymbolMap lid lidS "" rmap
         ext_induced_from_to_morphism lidS rmap' sigmaS sigmaT'
       let gMorph = mkG_morphism lidS mor
       (nsig', dg'') <- extendDGraph dg' nsig (gEmbed gMorph) DGFitSpec
       return (gMorph, nsig', p, dg'', diag')

-- | Analyse unit specification
anaUnitSpec :: LogicGraph -> LibName -> DGraph
  -> HetcatsOpts    -- ^ should only the structure be analysed?
  -> MaybeNode      -- ^ the signature of imports
  -> Maybe RTPointer -- for building refinement trees
  -> UNIT_SPEC -> Result (RefSig, DGraph, UNIT_SPEC)
{- ^ returns 1. unit signature 2. the development graph resulting from
structred specs inside the unit spec and 3. a UNIT_SPEC after possible
conversions. -}
anaUnitSpec lgraph ln dg opts impsig rN usp = case usp of
  Unit_type argSpecs resultSpec poss ->
   case argSpecs of
    [] -> case resultSpec of
      Annoted (Spec_inst spn [] _) _ _ _
        | case lookupGlobalEnvDG spn dg of
            Just (UnitEntry _) -> True
            Just (SpecEntry _) -> True
              -- this is needed because there are no REF_NAME in REF_SPEC
            Just (RefEntry _) -> True
            _ -> False ->
       {- if argspecs are empty and resultspec is a name of unit spec
          then this should be converted to a Spec_name -}
        anaUnitSpec lgraph ln dg opts impsig rN (Spec_name spn)
      _ -> do -- a trivial unit type
       (resultSpec', resultSig, dg') <- anaSpec False lgraph ln
           dg impsig emptyNodeName opts (item resultSpec)
       let usig = UnitSig [] resultSig Nothing
       return (mkRefSigFromUnit usig , dg', Unit_type []
                            (replaceAnnoted resultSpec' resultSpec) poss)
    _ -> do -- a non-trivial unit type
       (argSigs, dg1, argSpecs') <- anaArgSpecs lgraph ln dg opts argSpecs
       (sigUnion, dg2) <- nodeSigUnion lgraph dg1
                          (impsig : map JustNode argSigs) DGFormalParams
        {- if i have no imports, i can optimize?
        in that case, an identity morphism is introduced -}
       (resultSpec', resultSig, dg3) <- anaSpec True lgraph ln
           dg2 (JustNode sigUnion)
                emptyNodeName opts (item resultSpec)
       let usig = UnitSig argSigs resultSig $ Just sigUnion
           rsig = mkRefSigFromUnit usig
       return (rsig, dg3, Unit_type argSpecs'
                                (replaceAnnoted resultSpec' resultSpec) poss)
  Spec_name usn@(Token ustr pos) -> case lookupGlobalEnvDG usn dg of
    Just (UnitEntry usig) -> return (mkRefSigFromUnit usig, dg, usp)
    Just (SpecEntry (ExtGenSig _gsig@(GenSig _ args unSig) nsig) ) -> do
      let uSig = case unSig of
                  JustNode n -> Just n
                  _ -> Nothing
      return (mkRefSigFromUnit $ UnitSig args nsig uSig, dg, usp)
    Just (RefEntry rsig) ->
      case rN of
       Nothing -> let
             p = getPointerFromRef rsig
             (dg', newP) = addSubTree dg Nothing p
            in return (setPointerInRef rsig newP , dg', usp)
       Just p0 -> let l = refTarget p0 in
          case l of
           RTLeaf x -> let
                       p = getPointerFromRef rsig
                       (dg', p') = addSubTree dg (Just l) p
                       np' = compPointer (NPUnit x) p'
                     in return (setPointerInRef rsig np', dg', usp)
           RTLeaves leaves -> let
               p = getPointerFromRef rsig
             in case p of
                  NPComp _ -> let
                    (dg', p') = addSubTree dg (Just l) p
                    np' = compPointer p0 p'
                    in return (setPointerInRef rsig np', dg', usp)
                  _ ->
                     case Map.size leaves of
                       1 ->
                             let (_, h@(RTLeaf x)) = head $ Map.toList leaves
                                 (dg', p') = addSubTree dg (Just h) p
                                 np' = compPointer (NPUnit x) p'
                             in return (setPointerInRef rsig np', dg', usp)
                       _ -> error "can't compose signatures!"
    _ -> fatal_error (ustr ++ " is not an unit specification") pos
  Closed_unit_spec usp' _ -> do
    curl <- lookupCurrentLogic "UnitSpec" lgraph
    anaUnitSpec lgraph ln dg opts (EmptyNode curl) rN usp'

-- | Analyse refinement specification
anaRefSpec :: LogicGraph -> LibName -> DGraph
   -> HetcatsOpts      -- ^ should only the structure be analysed?
   -> MaybeNode        -- ^ the signature of imports
   -> SPEC_NAME        -- for origin
   -> ExtStUnitCtx
   -> Maybe RTPointer
   -> REF_SPEC
   -> Result ([DiagNodeSig], -- for lambda expressions
              Maybe DiagNodeSig, -- for tracing between levels
              Maybe Diag, RefSig, DGraph, REF_SPEC)
anaRefSpec lgraph ln dg opts nsig rn sharedCtx nP rsp =
 case rsp of
  Unit_spec asp ->
     do
       (rsig, dg', asp') <-
           anaUnitSpec lgraph ln dg opts nsig nP asp
       case rsig of
         BranchRefSig _ _ -> do
          usig <- getUnitSigFromRef rsig
          let rP = getPointerFromRef rsig
              (rsig', dg3) = case rP of
                           RTNone ->
                             let
                             (n, dg'') = addNodeRT dg' usig $ name asp
                             r' = setPointerInRef rsig (NPUnit n)
                            in (r', dg'')
                           _ -> (rsig, dg')
          return ([], Nothing, Just (snd sharedCtx), rsig', dg3, Unit_spec asp')
         _ ->
          return ([], Nothing, Just (snd sharedCtx), rsig, dg', Unit_spec asp')
  Arch_unit_spec asp poss ->
     do
       let x = case nP of
                Nothing -> Nothing
                Just p ->
                 case refTarget p of
                  RTLeaf y -> Just y
                  _ -> error "nyi"
       (nodes, maybeRes, diag, rsig, dg', asp') <-
           anaArchSpec lgraph ln dg opts sharedCtx x $ item asp
       return (nodes, maybeRes, Just diag, rsig, dg',
               Arch_unit_spec (replaceAnnoted asp' asp) poss)
{- check whether it is indeed correct
to ignore the nodes of the
lambda expressions, like you do in the following -}
  Compose_ref rslist range ->
    do
       (dg', anaSpecs, _) <- foldM (\ (dgr, rList, rN') rsp0 ->
                                        trace (show rN') $ do
          (_, _, _, rsig', dgr', rsp') <-
                               anaRefSpec lgraph ln dgr opts nsig
                               (mkSimpleId $ show rn ++ "gen_ref_name" ++
                                             show (length rList) )
                               sharedCtx rN' rsp0
          return (dgr', rList ++ [(rsig', rsp')],
                        Just $ getPointerFromRef rsig')
                           ) (dg, [], nP) rslist
       -- compose signatures in csig
       let refSigs = map fst anaSpecs
       csig <- foldM refSigComposition (head refSigs) $ tail refSigs
       let compRef = Compose_ref (map snd anaSpecs) range
       return ([], Nothing, Nothing, csig, dg', compRef)
  Component_ref urlist range -> do
       (dg', anaRefs, resultMap, pMap) <-
         foldM (\ (dgr, rList, cx, ps) uref0 -> do
          ((n, rs), dgr', uref') <-
                    anaUnitRef lgraph ln dgr opts emptyExtStUnitCtx nP uref0
          return (dgr', uref' : rList , Map.insert n rs cx,
                  Map.insert n (getPointerFromRef rs) ps)
                           ) (dg, [], Map.empty, Map.empty) urlist
       {- here:
        insert a dummy node labeled with the name of the component
        insert a refinement link from the dummy node to the
        source of refinement -}
       return ([], Nothing, Nothing,
               ComponentRefSig (NPComp pMap) resultMap, dg',
               Component_ref (reverse anaRefs) range)
  Refinement beh uspec gMapList rspec range ->
   do
     -- beh will be ignored for now
     (_rsig@(BranchRefSig _ (usig, _)), dg', asp') <-
           anaUnitSpec lgraph ln dg opts nsig nP uspec
     (_, _, _, _rsig'@(BranchRefSig n2 (usig', bsig)), dgr', rsp') <-
           anaRefSpec lgraph ln dg' opts nsig rn emptyExtStUnitCtx Nothing rspec
             -- here Nothing is fine
     case (usig, usig') of
       (UnitSig _ls ns _, UnitSig _ls' ns' _) -> do
               dg'' <- anaSymbMapRef dgr' ns ns' gMapList rn
               let (s, dg3) = case nP of
                               Nothing -> addNodeRT dg'' usig $ name uspec
                               Just p ->
                                 case refTarget p of
                                  RTLeaf x -> (x, dg'')
                                  _ -> error "can't refine to component!"
                   dg4 = addRefEdgeRT dg3 s (refSource n2)
               return ([], Nothing, Nothing,
                       BranchRefSig (compPointer (NPUnit s) n2)
                                    (usig, bsig) , dg4,
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
   sigT' <- coerceSign lidT lidS "anaSymbMapRef1" sigT
   mor <- do
           ExtSign sigS' _ <- coerceSign lidS lid "anaSymbMapRef2" sigS
           rmap <- stat_symb_map_items lid sigS' sis
           rmap' <- coerceRawSymbolMap lid lidS "" rmap
           ext_induced_from_to_morphism lidS rmap' sigS sigT'
   let g_mor = mkG_morphism lidS mor
   -- for now we stay in the homogeneous case
   let gm = gEmbed g_mor
       linkLabel = DGLink {
                     dgl_morphism = gm,
                     dgl_type = globalThm,
                     dgl_origin = DGLinkRefinement rn,
                     dglPending = False,
                     dglName = emptyNodeName,
                     dgl_id = getNewEdgeId dg'
                   }
       (_, dg'') = insLEdgeDG (nodeS, nodeT, linkLabel) dg'
   return dg''

-- | Analyse a list of argument specifications
anaArgSpecs :: LogicGraph -> LibName -> DGraph -> HetcatsOpts -> [Annoted SPEC]
  -> Result ([NodeSig], DGraph, [Annoted SPEC])
anaArgSpecs lgraph ln dg opts args = case args of
  [] -> return ([], dg, [])
  argSpec : argSpecs -> do
       l <- lookupLogic "anaArgSpecs" (currentLogic lgraph) lgraph
       (argSpec', argSig, dg') <-
           anaSpec False lgraph ln dg (EmptyNode l) emptyNodeName
                                           opts (item argSpec)
       (argSigs, dg'', argSpecs') <-
           anaArgSpecs lgraph ln dg' opts argSpecs
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
                 lab : _ -> do
                             let (_, mor) = lab
                                 sig = cod mor
                             G_sign lid _ _ <- return sig
                             hDiag <- homogeniseDiagram lid diag
                             hSink <- homogeniseSink lid sink
                             ensures_amalgamability lid (caslAmalg opts,
                                        hDiag, hSink, diagDesc diag)

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
