{- |
Module      :  ./Maude/Maude2DG.hs
Description :  Maude Development Graphs
Copyright   :  (c) Adrian Riesco, Facultad de Informatica UCM 2009
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  ariesco@fdi.ucm.es
Stability   :  experimental
Portability :  portable

Conversion of Maude to Development Graphs.
-}

module Maude.Maude2DG (anaMaudeFile) where

import System.Exit
import System.IO
import System.Process

import Static.GTheory
import Static.DevGraph
import Static.DgUtils
import Static.ComputeTheory
import Static.AnalysisStructured

import Logic.Logic
import Logic.Prover
import Logic.ExtSign
import Logic.Comorphism
import Logic.Grothendieck

import Maude.Sign
import Maude.Symbol
import Maude.AS_Maude
import Maude.Sentence
import Maude.Morphism
import Maude.Language
import Maude.Shellout
import Maude.Logic_Maude
import qualified Maude.Meta.HasName as HasName

import Data.Char
import Data.Maybe
import Data.List (intersect)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Graph.Inductive.Graph

import Common.Consistency
import Common.ExtSign
import Common.Id
import Common.IRI (simpleIdToIRI)
import Common.Result
import Common.LibName
import Common.AS_Annotation
import Common.Utils

import Driver.Options

-- | Maude importation types: Protecting, Extending and Including
data ImportType = Pr | Ex | Inc

{- | Pair of tokens and parameters contained by the token.
For example, (List{X,Y}, [X,Y]) -}
type ParamSort = (Symbol, [Token])

{- | Tuple with information about a module expression:
The corresponding node in the development graph.
The signature in this node.
The sorts not bound yet, defined in theories.
The data from parameters: the parameter id, its module expression and
the list of sorts imported.
The list of sorts "parameterized" (of the form List{X}). -}
type ProcInfo = (Node, Sign, Symbols, [(Token, Token, Symbols)], [ParamSort])

-- | map from module expression identifiers to ProcInfo
type TokenInfoMap = Map.Map Token ProcInfo

getProcInfo :: Token -> TokenInfoMap -> ProcInfo
getProcInfo t m = Map.findWithDefault
  (error $ "Maude2DG.TokenInfo: " ++ show t ++ " not found in "
   ++ show (Map.keys m)) t m

tokenNode :: Token -> TokenInfoMap -> Node
tokenNode t m = n where
  (n, _, _, _, _) = getProcInfo t m

{- | Data structure used to parse module expressions, it keeps:
The identifier of the module expression.
The map with the information associated with each module expression.
The morphism associated to the module expression.
The list of sorts parameterized in this module expression.
The development graph thus far. -}
type ModExpProc = (Token, TokenInfoMap, Morphism, [ParamSort], DGraph)

{- | Information related to an importation:
The type of importation.
The module expression imported.
The map with the information associated with each module expression.
The morphism associated to the module expression.
The list of sorts parameterized in this module expression.
The development graph thus far. -}
type ImportProc =
  (ImportType, Token, TokenInfoMap, Morphism, [ParamSort], DGraph)

{- | Information related to the parameters:
The list of parameters information:
 (parameter name, theory name, not instantiated sorts)
The updated TokenInfoMap map.
The list of morphisms associated with each parameter.
The updated development graph. -}
type ParamInfo = ([(Token, Token, Symbols)], TokenInfoMap, [Morphism], DGraph)

{- | Map from view identifiers to tuples containing the target node of the
view, the morphism, and a Boolean value indicating if the view instantiates
all the values -}
type ViewMap = Map.Map Token (Node, Token, Morphism, [Renaming], Bool)

{- | Tuple of data structures updated when a specification is introduced into
a development graph -}
type InsSpecRes = (TokenInfoMap, TokenInfoMap, ViewMap, [Token], DGraph)

{- | Tuple of data structures to introduce in the current DG the predefined
modules used -}
type UpdtPredefs = (TokenInfoMap, TokenInfoMap, DGraph)

{- | inserts the list of specifications in the development graph, updating
the data structures -}
insertSpecs :: [Spec] -> DGraph -> TokenInfoMap -> TokenInfoMap -> ViewMap
  -> [Token] -> DGraph -> InsSpecRes
insertSpecs [] _ ptim tim vm tks dg = (ptim, tim, vm, tks, dg)
insertSpecs (s : ss) pdg ptim tim vm ths dg =
  insertSpecs ss pdg ptim' tim' vm' ths' dg'
  where (ptim', tim', vm', ths', dg') = insertSpec s pdg ptim tim vm ths dg

maudeTheory :: ExtSign Sign Symbol -> SigId
  -> ThSens Sentence (AnyComorphism, BasicProof) -> ThId -> G_theory
maudeTheory = G_theory Maude Nothing

{- | inserts the given specification in the development graph, updating
the data structures -}
insertSpec :: Spec -> DGraph -> TokenInfoMap -> TokenInfoMap -> ViewMap
  -> [Token] -> DGraph -> InsSpecRes
insertSpec (SpecMod sp_mod) pdg ptim tim vm ths dg =
  (ptimUp, tim5, vm, ths, dg6) where
    ps = getParams sp_mod
    (il, _) = getImportsSorts sp_mod
    up = incPredImps il pdg (ptim, tim, dg)
    (ptimUp, timUp, dgUp) = incPredParams ps pdg up
    (pl, tim1, morphs, dg1) = processParameters ps timUp dgUp
    top_sg = Maude.Sign.fromSpec sp_mod
    paramSorts = getSortsParameterizedBy (paramNames ps)
      $ Set.toList $ sorts top_sg
    ips = processImports tim1 vm dg1 il
    (tim2, dg2) = last_da ips (tim1, dg1)
    sg = sign_union_morphs morphs $ sign_union top_sg ips
    ext_sg = makeExtSign Maude sg
    nm_sns = map (makeNamed "") $ Maude.Sentence.fromSpec sp_mod
    sens = toThSens nm_sns
    gt = maudeTheory ext_sg startSigId sens startThId
    tok = HasName.getName sp_mod
    name = makeName $ simpleIdToIRI tok
    (ns, dg3) = insGTheory dg2 name DGBasic gt
    tim3 = Map.insert tok (getNode ns, sg, [], pl, paramSorts) tim2
    (tim4, dg4) = createEdgesImports tok ips sg tim3 dg3
    dg5 = createEdgesParams tok pl morphs sg tim4 dg4
    (_, tim5, dg6) = insertFreeNode tok tim4 morphs dg5
insertSpec (SpecTh sp_th) pdg ptim tim vm ths dg =
  (ptimUp, tim3, vm, tok : ths, dg3) where
    (il, ss1) = getImportsSorts sp_th
    (ptimUp, timUp, dgUp) = incPredImps il pdg (ptim, tim, dg)
    ips = processImports timUp vm dgUp il
    ss2 = getThSorts ips
    (tim1, dg1) = last_da ips (tim, dg)
    sg = sign_union (Maude.Sign.fromSpec sp_th) ips
    ext_sg = makeExtSign Maude sg
    nm_sns = map (makeNamed "") $ Maude.Sentence.fromSpec sp_th
    sens = toThSens nm_sns
    gt = maudeTheory ext_sg startSigId sens startThId
    tok = HasName.getName sp_th
    name = makeName $ simpleIdToIRI tok
    (ns, dg2) = insGTheory dg1 name DGBasic gt
    tim2 = Map.insert tok (getNode ns, sg, ss1 ++ ss2, [], []) tim1
    (tim3, dg3) = createEdgesImports tok ips sg tim2 dg2
    -- (_, tim4, dg4) = insertFreeNode tok tim3 [] dg3
insertSpec (SpecView sp_v) pdg ptim tim vm ths dg =
  (ptimUp, tim3, vm', ths, dg4) where
    View name from to rnms = sp_v
    (ptimUp, timUp, dgUp) = incPredView from to pdg (ptim, tim, dg)
    inst = isInstantiated ths to
    tok_name = HasName.getName name
    (tok1, tim1, morph1, _, dg1) = processModExp timUp vm dgUp from
    (tok2, tim2, morph2, _, dg2) = processModExp tim1 vm dg1 to
    n1 = tokenNode tok1 tim2
    n2 = tokenNode tok2 tim2
    morph = fromSignsRenamings (target morph1) (target morph2) rnms
    Just morph' = maybeResult $ compose morph1 morph
    (new_sign, new_sens) = sign4renamings (target morph1) (sortMap morph) rnms
    (n3, tim3, dg3) = insertInnerNode n2 tim2 tok2 morph2 new_sign new_sens dg2
    vm' = Map.insert (HasName.getName name) (n3, tok2, morph', rnms, inst) vm
    dg4 = insertThmEdgeMorphism tok_name n3 n1 morph' dg3

{- | Includes the references used in importations to modules in the maude
prelude in the current DG -}
incPredImps :: [Import] -> DGraph -> UpdtPredefs -> UpdtPredefs
incPredImps [] _ up = up
incPredImps (i : is) pdg up = incPredImps is pdg up'
          where up' = incPredImp i pdg up

{- | Includes the references used in parameterizations to modules in the maude
prelude in the current DG -}
incPredParams :: [Parameter] -> DGraph -> UpdtPredefs -> UpdtPredefs
incPredParams [] _ up = up
incPredParams (i : is) pdg up = incPredParams is pdg up'
          where up' = incPredParam i pdg up

{- | Includes the references used in views to modules in the maude prelude
in the current DG -}
incPredView :: ModExp -> ModExp -> DGraph -> UpdtPredefs -> UpdtPredefs
incPredView from to pdg up = up''
          where up' = incPredImpME from pdg up
                up'' = incPredImpME to pdg up'

{- | Includes the references used in a parameter to modules in the maude prelude
in the current DG -}
incPredParam :: Parameter -> DGraph -> UpdtPredefs -> UpdtPredefs
incPredParam (Parameter _ me) = incPredImpME me

{- | Includes the references used in an importation to modules in the maude
prelude in the current DG -}
incPredImp :: Import -> DGraph -> UpdtPredefs -> UpdtPredefs
incPredImp i up = up'
          where me = getModExp i
                up' = incPredImpME me up

{- | Includes the references used in a module expression to modules in the
maude prelude in the current DG -}
incPredImpME :: ModExp -> DGraph -> UpdtPredefs -> UpdtPredefs
incPredImpME (ModExp m_id) pdg (ptim, tim, dg) = up where
  ModId q = m_id
  q' = mkFreeName q
  up = if Map.member q ptim then let
         (n, sg1, sys1, tts1, ps1) = ptim Map.! q
         (n', sg2, sys2, tts2, ps2) = ptim Map.! q'
         refInfo = newRefInfo preludeLib n
         refInfo' = newRefInfo preludeLib n'
         ptim1 = Map.delete q ptim
         ptim2 = Map.delete q' ptim1
         ext_sg1 = makeExtSign Maude sg1
         gt1 = maudeTheory ext_sg1 startSigId noSens startThId
         name1 = makeName $ simpleIdToIRI q
         new = newInfoNodeLab name1 refInfo gt1
         newNode = getNewNodeDG dg
         refLab = labDG pdg n
         nodeCont = new { globalTheory = globalTheory refLab }
         -- (ns1, dg1) = insGTheory dg name1 DGBasic gt1
         dg1 = insNodeDG (newNode, nodeCont) dg
         ext_sg2 = makeExtSign Maude sg2
         gt2 = maudeTheory ext_sg2 startSigId noSens startThId
         name2 = makeName $ simpleIdToIRI q'
         new' = newInfoNodeLab name2 refInfo' gt2
         newNode' = getNewNodeDG dg1
         refLab' = labDG pdg n'
         nodeCont' = new' { globalTheory = globalTheory refLab' }
         -- (ns2, dg2) = insGTheory dg1 name2 DGBasic gt2
         dg2 = insNodeDG (newNode', nodeCont') dg1
         tim1 = Map.insert q (newNode, sg1, sys1, tts1, ps1) tim
         tim2 = Map.insert q' (newNode', sg2, sys2, tts2, ps2) tim1
         in (ptim2, tim2, dg2)
       else (ptim, tim, dg)
incPredImpME (SummationModExp me me') pdg up = up''
          where up' = incPredImpME me pdg up
                up'' = incPredImpME me' pdg up'
incPredImpME (RenamingModExp me _) pdg up = incPredImpME me pdg up
incPredImpME (InstantiationModExp me _) pdg up = incPredImpME me pdg up

-- | extracts the module expression from an importation statement
getModExp :: Import -> ModExp
getModExp (Including me) = me
getModExp (Extending me) = me
getModExp (Protecting me) = me

-- | computes the union of the signatures obtained from the importation list
sign_union :: Sign -> [ImportProc] -> Sign
sign_union = foldr (Maude.Sign.union . get_sign)

-- | extracts the target signature from the morphism in an importation tuple
get_sign :: ImportProc -> Sign
get_sign (_, _, _, morph, _, _) = target morph

-- | computes the union of the target signatures of a list of morphisms
sign_union_morphs :: [Morphism] -> Sign -> Sign
sign_union_morphs morphs sg = foldr (Maude.Sign.union . target) sg morphs

{- | extracts the last (newest) data structures from a list of importation
tuples, using the second argument as default value if the list is empty -}
last_da :: [ImportProc] -> (TokenInfoMap, DGraph) -> (TokenInfoMap, DGraph)
last_da [(_, _, tim, _, _, dg)] _ = (tim, dg)
last_da (_ : ips) p = last_da ips p
last_da _ p = p

-- | generates the edges required by a parameter list in a module instantiation
createEdgesParams :: Token -> [(Token, Token, Symbols)] -> [Morphism] -> Sign
                     -> TokenInfoMap -> DGraph -> DGraph
createEdgesParams tok1 ((_, tok2, _) : toks) (morph : morphs) sg tim dg =
    createEdgesParams tok1 toks morphs sg tim
      $ createEdgeMorphism tok1 tok2 globalDef morph sg tim dg
createEdgesParams _ _ _ _ _ dg = dg

createEdgeMorphism :: Token -> Token -> DGLinkType -> Morphism -> Sign
  -> TokenInfoMap -> DGraph -> DGraph
createEdgeMorphism tok1 tok2 lt morph sg tim =
  insertEdgeMorphism n1 n2 lt morph' where
  morph' = setTarget sg morph
  n1 = tokenNode tok1 tim
  n2 = tokenNode tok2 tim

-- | generates the edges required by the importations
createEdgesImports :: Token -> [ImportProc] -> Sign -> TokenInfoMap -> DGraph
                      -> (TokenInfoMap, DGraph)
createEdgesImports _ [] _ tim dg = (tim, dg)
createEdgesImports tok (ip : ips) sg tim dg =
    createEdgesImports tok ips sg tim' dg'
               where (tim', dg') = createEdgeImport tok ip sg tim dg

-- | generates the edge for a concrete importation
createEdgeImport :: Token -> ImportProc -> Sign -> TokenInfoMap -> DGraph
                    -> (TokenInfoMap, DGraph)
createEdgeImport tok1 (ip, tok2, _, morph, _, _) sg tim dg =
  let (tok2', tim', dg') = case ip of
        Pr -> insertFreeNode tok2 tim [] dg
        _ -> (tok2, tim, dg)
  in (tim', createEdgeMorphism tok1 tok2'
      (case ip of
         Ex -> globalConsThm PCons -- a PCons link
         _ -> globalDef) morph sg tim' dg')

-- | extracts the sorts provided by the theories
getThSorts :: [ImportProc] -> Symbols
getThSorts = concatMap getThSortsAux

-- | extracts the not-bounded-yet sorts related to the given identifier
getThSortsAux :: ImportProc -> Symbols
getThSortsAux (_, tok, tim, _, _, _) = srts
         where (_, _, srts, _, _) = getProcInfo tok tim

{- | generates the extra signature needed when using term to term renaming in
views -}
sign4renamings :: Sign -> SymbolMap -> [Renaming] -> (Sign, [Sentence])
sign4renamings sg sm (TermMap t1 t2 : rnms) = (new_sg, Equation eq : sens)
         where (op_top, ss) = getOpSorts t1
               sg' = newOp sg op_top ss sm
               (sg'', sens) = sign4renamings sg sm rnms
               eq = Eq (applyRenamingTerm sm t1) t2 [] []
               new_sg = Maude.Sign.union sg' sg''
sign4renamings sg sm (_ : rnms) = sign4renamings sg sm rnms
sign4renamings sg _ [] = (sg, [])

{- | given the identifier of an operator in the given signature, the function
generates a new signature with this operator and a renamed profile computed
from the renaming given in the mapping -}
newOp :: Sign -> Token -> Symbols -> SymbolMap -> Sign
newOp sg op ss sm = Maude.Sign.empty {ops = Map.singleton op ods'}
         where om = ops sg
               Just ods = Map.lookup op om
               ods' = getOpDeclSet ods ss sm

-- | renames the profile with the given map
getOpDeclSet :: OpDeclSet -> Symbols -> SymbolMap -> OpDeclSet
getOpDeclSet ods ss sm = Set.singleton (op_sym', ats)
         where f ~(Operator _ x _) b = x == ss || b
               g = Set.fold f False . fst
               (ods', ats) : _ = Set.toList $ Set.filter g ods
               h ~(Operator _ y _) = y == ss
               ods'' = Set.filter h ods'
               op_sym : _ = Set.toList ods''
               op_sym' = applyRenamingOpSymbol op_sym sm

-- | applies the renaming in the map to the operator declaration
applyRenamingOpSymbol :: Symbol -> SymbolMap -> SymbolSet
applyRenamingOpSymbol (Operator q ar co) sm = Set.singleton $ Operator q ar' co'
         where f x = Map.findWithDefault x x sm
               ar' = map f ar
               co' = f co
applyRenamingOpSymbol _ _ = Set.empty

-- | renames the sorts in a term
applyRenamingTerm :: SymbolMap -> Term -> Term
applyRenamingTerm sm (Apply q ts ty) = Apply q (map (applyRenamingTerm sm) ts)
                                               (applyRenamingType sm ty)
applyRenamingTerm sm (Const q s) = Const q s'
         where s' = applyRenamingType sm s
applyRenamingTerm sm (Var q s) = Var q s'
         where s' = applyRenamingType sm s

-- | renames a type
applyRenamingType :: SymbolMap -> Type -> Type
applyRenamingType sm (TypeSort s) = TypeSort $ SortId $ HasName.getName q'
         where SortId q = s
               q' = Map.findWithDefault (Sort q) (Sort q) sm
applyRenamingType sm (TypeKind k) = TypeKind $ KindId $ HasName.getName q'
         where KindId q = k
               q' = Map.findWithDefault (Kind q) (Kind q) sm

{- | extracts the top operator of a term and the names of its sorts
if it is applicated to some arguments -}
getOpSorts :: Term -> (Token, Symbols)
getOpSorts (Const q _) = (q, [])
getOpSorts (Var q _) = (q, [])
getOpSorts (Apply q ls _) = (q, getTypes ls)

-- | extracts the types of the terms while they are variables
getTypes :: [Term] -> Symbols
getTypes (Var _ (TypeSort s) : ts) = Sort (HasName.getName s) : getTypes ts
getTypes (Var _ (TypeKind s) : ts) = Kind (HasName.getName s) : getTypes ts
getTypes _ = []

-- | process the information of the given list of imports
processImports :: TokenInfoMap -> ViewMap -> DGraph -> [Import] -> [ImportProc]
processImports _ _ _ [] = []
processImports tim vm dg (i : il) = ip : processImports tim' vm dg' il
         where ip@(_, _, tim', _, _, dg') = processImport tim vm dg i

{- | process the module expression and then adds the information about
the type of import -}
processImport :: TokenInfoMap -> ViewMap -> DGraph -> Import -> ImportProc
processImport tim vm dg (Protecting modExp) = (Pr, tok, tim', morph, ps, dg')
         where (tok, tim', morph, ps, dg') = processModExp tim vm dg modExp
processImport tim vm dg (Extending modExp) = (Ex, tok, tim', morph, ps, dg')
         where (tok, tim', morph, ps, dg') = processModExp tim vm dg modExp
processImport tim vm dg (Including modExp) = (Inc, tok, tim', morph, ps, dg')
         where (tok, tim', morph, ps, dg') = processModExp tim vm dg modExp

-- | traverses the list of parameters and generates the required data structures
processParameters :: [Parameter] -> TokenInfoMap -> DGraph -> ParamInfo
processParameters ps tim dg = foldr processParameter ([], tim, [], dg) ps

{- | given a parameter, the function processes the module expression associated
to it, qualifies the not-bound-yet sorts and creates the morphism -}
processParameter :: Parameter -> ParamInfo -> ParamInfo
processParameter (Parameter sort modExp) (toks, tim, morphs, dg) =
    (toks', tim', morphs', dg')
         where (tok, tim', morph, _, dg') =
                   processModExp tim Map.empty dg modExp
               (_, _, fs, _, _) = getProcInfo tok tim'
               fs' = translateSorts morph fs
               morph' = qualifySorts morph (HasName.getName sort) fs'
               toks' = (HasName.getName sort, tok, fs') : toks
               morphs' = morph' : morphs

{- | distinguishes between the different module expressions to compute
the morphisms and update the development graph -}
processModExp :: TokenInfoMap -> ViewMap -> DGraph -> ModExp -> ModExpProc
processModExp tim _ dg (ModExp modId) = (tok, tim, morph, ps, dg)
                     where tok = HasName.getName modId
                           (_, sg, _, _, ps) = getProcInfo tok tim
                           morph = Maude.Morphism.inclusion sg sg
processModExp tim vm dg (SummationModExp modExp1 modExp2) =
  (tok, tim3, morph, ps', dg5) where
    (tok1, tim1, morph1, ps1, dg1) = processModExp tim vm dg modExp1
    (tok2, tim2, morph2, ps2, dg2) = processModExp tim1 vm dg1 modExp2
    ps' = nubOrd $ ps1 ++ ps2
    tok = mkSimpleId $ concat ["{", show tok1, " + ", show tok2, "}"]
    (n1, _, ss1, _, _) = getProcInfo tok1 tim2
    (n2, _, ss2, _, _) = getProcInfo tok2 tim2
    ss1' = translateSorts morph1 ss1
    ss2' = translateSorts morph1 ss2
    sg1 = target morph1
    sg2 = target morph2
    sg = Maude.Sign.union sg1 sg2
    morph = Maude.Morphism.inclusion sg sg
    morph1' = setTarget sg morph1
    morph2' = setTarget sg morph2
    (tim3, dg3) = insertNode tok sg tim2 (ss1' ++ ss2') [] dg2
    n3 = tokenNode tok tim3
    dg4 = insertDefEdgeMorphism n3 n1 morph1' dg3
    dg5 = insertDefEdgeMorphism n3 n2 morph2' dg4
processModExp tim vm dg (RenamingModExp modExp rnms) =
  (tok, tim', comp_morph, ps', dg') where
    (tok, tim', morph, ps, dg') = processModExp tim vm dg modExp
    morph' = fromSignRenamings (target morph) rnms
    ps' = applyRenamingParamSorts (sortMap morph') ps
    Just comp_morph = maybeResult $ compose morph morph'
processModExp tim vm dg (InstantiationModExp modExp views) =
  (tok'', tim'', final_morph, new_param_sorts, dg'') where
    (tok, tim', morph, paramSorts, dg') = processModExp tim vm dg modExp
    (_, _, _, ps, _) = getProcInfo tok tim'
    param_names = map fstTpl ps
    view_names = map HasName.getName views
    (new_param_sorts, ps_morph) = instantiateSorts param_names view_names vm
      morph paramSorts
    (tok', morph1, ns, deps) = processViews views (mkSimpleId "") tim' vm ps
      (ps_morph, [], [])
    tok'' = mkSimpleId $ concat [show tok, "{", show tok', "}"]
    sg2 = target morph1
    final_morph = Maude.Morphism.inclusion sg2 sg2
    (tim'', dg'') = if Map.member tok'' tim then (tim', dg') else
      updateGraphViews tok tok'' sg2 morph1 ns tim' deps dg'

{- | generates a edge between the source and the target of a view, inserting
a new node if the view contained a term to term renaming, and thus updating
the map from module expression to its info and the development graph -}
updateGraphViews :: Token -> Token -> Sign -> Morphism -> [(Node, Morphism)]
  -> TokenInfoMap -> [(Token, Token, Symbols)] -> DGraph
  -> (TokenInfoMap, DGraph)
updateGraphViews tok1 tok2 sg morph views tim deps dg = (tim', dg''')
                     where n1 = tokenNode tok1 tim
                           morph' = setTarget sg morph
                           (tim', dg') = insertNode tok2 sg tim [] deps dg
                           n2 = tokenNode tok2 tim'
                           dg'' = insertDefEdgeMorphism n2 n1 morph' dg'
                           dg''' = insertDefEdgesMorphism n2 views sg dg''

{- | traverses a list of views obtained in an instantiation module expression
and return a tuple with:
The accumulated identifier of the module expression.
The accumulated morphism thus far.
A list of nodes and morphisms to create the appropriate edges in the
development graph.
The not-bound-yet sorts. -}
processViews :: [ViewId] -> Token -> TokenInfoMap -> ViewMap
  -> [(Token, Token, Symbols)]
  -> (Morphism, [(Node, Morphism)], [(Token, Token, Symbols)])
  -> (Token, Morphism, [(Node, Morphism)], [(Token, Token, Symbols)])
processViews (vi : vis) tok tim vm (p : ps) (morph, lp, dep) =
  processViews vis tok'' tim vm ps (morph', lp ++ [(n, vmorph)], dep ++ new_dep)
      where (tok', morph', vmorph, n, new_dep) = processView vi tim vm p morph
            tok'' = mkSimpleId $ show tok ++ "," ++ show tok'
processViews _ tok _ _ _ (morph, nds, deps) = (tok', morph, nds, deps)
      where tok' = mkSimpleId $ drop 1 $ show tok

{- | this function distinguishes whether the view is an instantiation (and thus)
the view is in the map of views and the function morphismView is used
or it is just a parameter binding and paramBinding is used -}
processView :: ViewId -> TokenInfoMap -> ViewMap -> (Token, Token, Symbols)
  -> Morphism -> (Token, Morphism, Morphism, Node, [(Token, Token, Symbols)])
processView vi tim vm (p, theory, ss) morph =
  if Map.member name vm
  then morphismView name p ss (Map.findWithDefault
         (error "Maude2DG.processView") name vm) morph
  else paramBinding theory name p ss morph tim
    where name = HasName.getName vi

{- | the function distinguishes if the instantiation is from a module, and thus
all the symbols are instantiated, or it is a theory and the symbols are not
completely instantiated. -}
morphismView :: Token -> Token -> Symbols
  -> (Node, Token, Morphism, [Renaming], Bool) -> Morphism
  -> (Token, Morphism, Morphism, Node, [(Token, Token, Symbols)])
morphismView name p _ (n, _, vmorph, rnms, True) morph =
  (name, morph'', vmorph', n, [])
        where rnms' = qualifyRenamings p rnms
              morph' = applyRenamings morph rnms'
              tgt = target vmorph
              vmorph' = Maude.Morphism.inclusion tgt tgt
              ctgt = target morph'
              usg = Maude.Sign.union ctgt tgt
              morph'' = setTarget usg morph'
morphismView name p ss (n, th, morph, rnms, False) morph1 =
  (name, morph4, vmorph', n, [(p, th, translateSorts morph ss)])
        where rnms' = qualifyRenamings2 p rnms
              morph2 = applyRenamings morph1 rnms'
              rnms'' = createQualificationTh2Mod p ss
              morph3 = applyRenamings morph2 rnms''
              tgt = target morph
              vmorph = Maude.Morphism.inclusion tgt tgt
              vmorph' = applyRenamings vmorph rnms''
              vtgt = target vmorph'
              ctgt = target morph3
              usg = Maude.Sign.union vtgt ctgt
              morph4 = setTarget usg morph3


{- this function is applied when two parameters are linked, it updates the
qualifications of the sorts. The parameters are:
theory -> parameter instantiated -> parameter binding -> sorts bound ->
current morph map token info -}
paramBinding :: Token -> Token -> Token -> Symbols -> Morphism -> TokenInfoMap
  -> (Token, Morphism, Morphism, Node, [(Token, Token, Symbols)])
paramBinding th view p ss morph tim = (view, morph', vmorph', n, [])
        where rnms = createQualifiedSortRenaming p view ss
              morph' = applyRenamings morph rnms
              (n, sg, _, _, _) = getProcInfo th tim
              vmorph = Maude.Morphism.inclusion sg sg
              rnms' = createQualificationTh2Mod p ss
              vmorph' = applyRenamings vmorph rnms'

-- | inserts the node into the development graph if it does not already exist
insertNode :: Token -> Sign -> TokenInfoMap -> Symbols
  -> [(Token, Token, Symbols)] -> DGraph -> (TokenInfoMap, DGraph)
insertNode tok sg tim ss deps dg =
  if Map.member tok tim then (tim, dg) else let
    ext_sg = makeExtSign Maude sg
    gt = maudeTheory ext_sg startSigId noSens startThId
    name = makeName $ simpleIdToIRI tok
    (ns, dg') = insGTheory dg name DGBasic gt
    tim' = Map.insert tok (getNode ns, sg, ss, deps, []) tim
  in (tim', dg')

{- | inserts an inner node. This function is used when a view defines a map
between terms, so it is neccesary to extend the signature of the target
module in order to have the appropriate map. -}
insertInnerNode :: Node -> TokenInfoMap -> Token -> Morphism -> Sign
  -> [Sentence] -> DGraph -> (Node, TokenInfoMap, DGraph)
insertInnerNode nod tim tok morph sg sens dg =
  if isIdentity morph && null sens
  then let
    (fn, tim', dg') = insertFreeNode tok tim [] dg
    n2 = tokenNode fn tim'
    in (n2, tim', dg')
  else let
    nm = makeName $ simpleIdToIRI tok
    th_sens = toThSens $ map (makeNamed "") sens
    sg' = Maude.Sign.union sg $ target morph
    ext_sg = makeExtSign Maude sg'
    gt = maudeTheory ext_sg startSigId th_sens startThId
    nm' = inc nm
    (ns, dg1) = insGTheory dg nm' DGBasic gt
    nod2 = getNode ns
    morph' = setTarget sg' morph
    dg2 = insertDefEdgeMorphism nod2 nod morph' dg1
    -- inserting the free node
    gt2 = maudeTheory ext_sg startSigId noSens startThId
    (ns2, dg3) = insGTheory dg2 (inc nm') DGBasic gt2
    nod3 = getNode ns2
    -- inserting the free link
    inc_sg = Maude.Morphism.inclusion Maude.Sign.empty sg'
    mor = G_morphism Maude inc_sg startMorId
    dgt = FreeOrCofreeDefLink NPFree $ EmptyNode (Logic Maude)
    edg = defDGLink (gEmbed mor) dgt SeeTarget
    dg4 = snd $ insLEdgeDG (nod2, nod3, edg) dg3
    in (nod3, tim, dg4)

{- | inserts the list of definition edges, building for each node the inclusion
morphism between the signatures -}
insertDefEdgesMorphism :: Node -> [(Node, Morphism)] -> Sign -> DGraph -> DGraph
insertDefEdgesMorphism _ [] _ dg = dg
insertDefEdgesMorphism n1 ((n2, morph) : views) sg2 dg =
  insertDefEdgesMorphism n1 views sg2 dg'
                  where morph' = setTarget sg2 morph
                        dg' = insertDefEdgeMorphism n1 n2 morph' dg

-- | inserts a definition link between the nodes with the given morphism
insertDefEdgeMorphism :: Node -> Node -> Morphism -> DGraph -> DGraph
insertDefEdgeMorphism n1 n2 = insertEdgeMorphism n1 n2 globalDef

{- | inserts a theorem link, labeled with the name of the view, between the
nodes with the given morphism in the development graph -}
insertThmEdgeMorphism :: Token -> Node -> Node -> Morphism -> DGraph -> DGraph
insertThmEdgeMorphism name n1 n2 morph dg = snd $ insLEdgeDG (n2, n1, edg) dg
                     where mor = G_morphism Maude morph startMorId
                           edg = defDGLink (gEmbed mor) globalThm
                                 (DGLinkView (simpleIdToIRI name) $ Fitted [])

-- | inserts a link between the nodes with the given morphism
insertEdgeMorphism :: Node -> Node -> DGLinkType -> Morphism -> DGraph -> DGraph
insertEdgeMorphism n1 n2 lt morph dg = snd $ insLEdgeDG (n2, n1, edg) dg
    where mor = G_morphism Maude morph startMorId
          edg = defDGLink (gEmbed mor) lt SeeTarget

-- | inserts a free definition link between the nodes with the given name
insertFreeEdge :: Token -> Token -> TokenInfoMap -> DGraph -> DGraph
insertFreeEdge tok1 tok2 tim = insertEdgeMorphism n1 n2
  (FreeOrCofreeDefLink NPFree $ EmptyNode $ Logic Maude)
  (Maude.Morphism.inclusion Maude.Sign.empty sg2)
    -- currently, the empty sign is used in the inclusion instead of sg1
    where n1 = tokenNode tok1 tim
          (n2, sg2, _, _, _) = getProcInfo tok2 tim

{- | inserts a free definition link between the nodes with the given
name. This function is used to create free links when a module is
parameterized, so the morphism is more complicated: It also receives a
morphism, obtained from the parameters. -}
insertFreeEdgeMor :: Token -> Token -> TokenInfoMap -> Morphism -> DGraph
  -> DGraph
insertFreeEdgeMor tok1 tok2 tim mor dg = snd $ insLEdgeDG (n2, n1, edg) dg
    where n1 = tokenNode tok1 tim
          n2 = tokenNode tok2 tim
          mor' = G_morphism Maude mor startMorId
          dgt = FreeOrCofreeDefLink NPFree $ EmptyNode (Logic Maude)
          edg = defDGLink (gEmbed mor') dgt SeeTarget

{- | the importation mode "protecting M" generates a new node M' and a free link
between M and M'. This function is in charge of creating such M' if it does not
exist -}
insertFreeNode :: Token -> TokenInfoMap -> [Morphism] -> DGraph
  -> (Token, TokenInfoMap, DGraph)
insertFreeNode t tim morphs dg = (t', tim', dg'') where
    t' = mkFreeName t
    b = Map.member t' tim
    (tim', dg') = if b then (tim, dg) else
      insertFreeNode2 t' tim (getProcInfo t tim) dg
    dg'' | b = dg'
         | null morphs = insertFreeEdge t' t tim' dg'
         | otherwise = insertFreeEdgeMor t' t tim' (morphismUnion morphs) dg'

morphismUnion :: [Morphism] -> Morphism
morphismUnion = foldr Maude.Morphism.union Maude.Morphism.empty

-- | auxiliary function in charge of creating M' when it does not exist
insertFreeNode2 :: Token -> TokenInfoMap -> ProcInfo -> DGraph
  -> (TokenInfoMap, DGraph)
insertFreeNode2 t tim (_, sg, _, _, _) dg = (tim', dg')
              where ext_sg = makeExtSign Maude sg
                    gt = maudeTheory ext_sg startSigId noSens startThId
                    name = makeName $ simpleIdToIRI t
                    (ns, dg') = insGTheory dg name DGBasic gt
                    tim' = Map.insert t (getNode ns, sg, [], [], []) tim

{- | Given the identifier of a module, generates the identifier for the module
with the ``freeness'' constraint -}
mkFreeName :: Token -> Token
mkFreeName = mkSimpleId . (++ "'") . show

-- | extracts the parameters of a Maude module
getParams :: Module -> [Parameter]
getParams (Module _ params _) = params

-- | extracts the importation statements and the sorts from a module definition
getImportsSorts :: Module -> ([Import], Symbols)
getImportsSorts (Module _ _ stmts) = getImportsSortsStmnts stmts ([], [])

-- | traverses the statements accumulating the importations and the sorts
getImportsSortsStmnts :: [Statement] -> ([Import], Symbols)
  -> ([Import], Symbols)
getImportsSortsStmnts [] p = p
getImportsSortsStmnts (ImportStmnt imp : stmts) (is, ss) =
    getImportsSortsStmnts stmts (imp : is, ss)
getImportsSortsStmnts (SortStmnt s : stmts) (is, ss) =
    getImportsSortsStmnts stmts (is, Sort (HasName.getName s) : ss)
getImportsSortsStmnts (_ : stmts) p = getImportsSortsStmnts stmts p

-- | builds the development graph of the specified Maude file
directMaudeParsing :: HetcatsOpts -> FilePath -> IO (DGraph, DGraph)
directMaudeParsing opts fp = do
    putIfVerbose opts 2 $ "Reading file " ++ fp
    ns <- parse fp
    let ns' = either (const []) id ns
    (inString, hIn, hOut, hErr, procH) <- runMaude
    exitCode <- getProcessExitCode procH
    case exitCode of
      Nothing -> do
              maudePutStrLn hIn $ "load " ++ fp
              maudePutStrLn hIn inString
              psps <- predefinedSpecs opts hIn hOut
              sps <- traverseSpecs opts hIn hOut ns'
              (ok, errs) <- getErrors hErr
              terminateProcess procH
              if ok
                  then return $ maude2DG psps sps
                  else error errs
      Just ExitSuccess -> error "maude terminated immediately"
      Just (ExitFailure i) ->
          error $ "calling maude failed with exitCode: " ++ show i

maude2DG :: [Spec] -> [Spec] -> (DGraph, DGraph)
maude2DG psps sps = (dg1, dg2) where
  (_, tim, vm, tks, dg1) =
    insertSpecs psps emptyDG Map.empty Map.empty Map.empty [] emptyDG
  (_, _, _, _, dg2) = insertSpecs sps dg1 tim Map.empty vm tks emptyDG

-- | list of names of the predefined modules
predefined :: [NamedSpec]
predefined =
  [ ModName "TRUTH-VALUE"
  , ModName "BOOL-OPS"
  , ModName "TRUTH"
  , ModName "BOOL"
  , ModName "EXT-BOOL"
  , ModName "NAT"
  , ModName "INT"
  , ModName "RAT"
  , ModName "FLOAT"
  , ModName "STRING"
  , ModName "CONVERSION"
  , ModName "RANDOM"
  , ModName "QID"
  , ModName "TRIV"
  , ViewName "TRIV"
  , ViewName "Bool"
  , ViewName "Nat"
  , ViewName "Int"
  , ViewName "Rat"
  , ViewName "Float"
  , ViewName "String"
  , ViewName "Qid"
  , ModName "STRICT-WEAK-ORDER"
  , ViewName "STRICT-WEAK-ORDER"
  , ModName "STRICT-TOTAL-ORDER"
  , ViewName "STRICT-TOTAL-ORDER"
  , ViewName "Nat<"
  , ViewName "Int<"
  , ViewName "Rat<"
  , ViewName "Float<"
  , ViewName "String<"
  , ModName "TOTAL-PREORDER"
  , ViewName "TOTAL-PREORDER"
  , ModName "TOTAL-ORDER"
  , ViewName "TOTAL-ORDER"
  , ViewName "Nat<="
  , ViewName "Int<="
  , ViewName "Rat<="
  , ViewName "Float<="
  , ViewName "String<="
  , ModName "DEFAULT"
  , ViewName "DEFAULT"
  , ViewName "Nat0"
  , ViewName "Int0"
  , ViewName "Rat0"
  , ViewName "Float0"
  , ViewName "String0"
  , ViewName "Qid0"
  , ModName "LIST"
  , ModName "WEAKLY-SORTABLE-LIST"
  , ModName "SORTABLE-LIST"
  , ModName "WEAKLY-SORTABLE-LIST'"
  , ModName "SORTABLE-LIST'"
  , ModName "SET"
  , ModName "LIST-AND-SET"
  , ModName "SORTABLE-LIST-AND-SET"
  , ModName "SORTABLE-LIST-AND-SET'"
  , ModName "LIST*"
  , ModName "SET*"
  , ModName "MAP"
  , ModName "ARRAY"
  , ModName "NAT-LIST"
  , ModName "QID-LIST"
  , ModName "QID-SET"
  , ModName "META-TERM"
  , ModName "META-MODULE"
  , ModName "META-VIEW"
  , ModName "META-LEVEL"
  , ModName "COUNTER"
  , ModName "LOOP-MODE"
  , ModName "CONFIGURATION" ]

{- | returns the specifications of the predefined modules by passing as
parameter the list of names -}
predefinedSpecs :: HetcatsOpts -> Handle -> Handle -> IO [Spec]
predefinedSpecs opts hIn hOut = traverseSpecs opts hIn hOut predefined

traverseSpecs :: HetcatsOpts -> Handle -> Handle -> [NamedSpec] -> IO [Spec]
traverseSpecs opts hIn hOut = fmap catMaybes . mapM (traverseSpec opts hIn hOut)

-- | returns the specifications of the predefined modules
traverseSpec :: HetcatsOpts -> Handle -> Handle -> NamedSpec -> IO (Maybe Spec)
traverseSpec opts hIn hOut ns = do
  let args = case ns of
          ModName n -> "(hets " ++ n
          ViewName n -> "(hetsView " ++ n
        ++ " .)"
  putIfVerbose opts 4 $ "maude input: " ++ args
  maudePutStrLn hIn args
  sOutput <- getAllSpec hOut "" False
  let stringSpec = findSpec sOutput
  case readMaybe stringSpec of
    Nothing -> do
      putStrLn $ "failed to read " ++ args ++ ":\n"
        ++ if all isSpace stringSpec then sOutput else stringSpec
      return Nothing
    ms -> return ms

-- | returns the parameter names
paramNames :: [Parameter] -> [Token]
paramNames = map $ \ (Parameter s _) -> HasName.getName s

{- | returns the sorts (second argument of the pair) that contain any of the
parameters given as first argument -}
getSortsParameterizedBy :: [Token] -> Symbols -> [ParamSort]
getSortsParameterizedBy ps = filter f . map (g ps)
           where f = not . null . snd
                 g pss x = let
                         params = getSortParams $ HasName.getName x
                         in (x, intersect params pss)

{- | extracts the parameters of the given sort
For example, getSortParams List{X} = [X]
List{X}{Y, Y} = [Y,Z] -}
getSortParams :: Token -> [Token]
getSortParams t = getSortParamsString $ show t

-- | traverses a String looking for the last curly braces
getSortParamsString :: String -> [Token]
getSortParamsString [] = []
getSortParamsString ('{' : cs) = if null sps
                                 then getSortParamsStringAux cs ""
                                 else sps
            where sps = getSortParamsString cs
getSortParamsString (_ : cs) = getSortParamsString cs

-- | traverses a String keeping the token separated by commas
getSortParamsStringAux :: String -> String -> [Token]
getSortParamsStringAux ('`' : ',' : cs) st =
  mkSimpleId st : getSortParamsStringAux cs ""
getSortParamsStringAux ('`' : '}' : []) st = [mkSimpleId st]
getSortParamsStringAux (' ' : cs) st = getSortParamsStringAux cs st
getSortParamsStringAux (c : cs) st = getSortParamsStringAux cs (st ++ [c])
getSortParamsStringAux [] st = [mkSimpleId st]

-- | checks if the target of the view is completely instantiated (to modules)
isInstantiated :: [Token] -> ModExp -> Bool
isInstantiated ths (ModExp modExp) = notElem (HasName.getName modExp) ths
isInstantiated ths (SummationModExp me1 me2) = isInstantiated ths me1 &&
                                               isInstantiated ths me2
isInstantiated ths (RenamingModExp modExp _) = isInstantiated ths modExp
isInstantiated _ (InstantiationModExp _ _) = True

-- | rename the parameterized sorts and computes if they are still parameterized
applyRenamingParamSorts :: SymbolMap -> [ParamSort] -> [ParamSort]
applyRenamingParamSorts sm = foldr (applyRenamingParamSort sm) []

applyRenamingParamSort :: SymbolMap -> ParamSort -> [ParamSort] -> [ParamSort]
applyRenamingParamSort sm (tok, params) acc = case Map.lookup tok sm of
    Nothing -> (tok, params) : acc
    Just tok' -> getSortsParameterizedBy params [tok'] ++ acc

-- | returns the first element from the triple
fstTpl :: (a, b, c) -> a
fstTpl (a, _, _) = a

{- | instantiate the parametric sorts
ParamNames -> ViewName -> Map of views -> Parametricsorts -}
instantiateSorts :: [Token] -> [Token] -> ViewMap -> Morphism -> [ParamSort]
                    -> ([ParamSort], Morphism)
instantiateSorts _ _ _ morph [] = ([], morph)
instantiateSorts params views vm morph (ps : pss) = (nps'' ++ res_ps, res_morph)
        where np4s = newParamers4sorts params views vm
              nps = instantiateSort ps params views
              nps' = addNewParams2sort nps np4s
              nps'' = if null (snd nps') then [] else [nps']
              morph' = extendWithSortRenaming (fst ps) (fst nps') morph
              (res_ps, res_morph) = instantiateSorts params views vm morph' pss

-- | computes the theories that have to be further instantiated
newParamers4sorts :: [Token] -> [Token] -> ViewMap -> [Token]
newParamers4sorts (param : ps) (view : vs) vm = case Map.lookup view vm of
    Nothing -> newParamers4sorts ps vs vm
    Just (_, _, _, _, inst) -> let
                 param' = if inst
                          then []
                          else [param]
                in param' ++ newParamers4sorts ps vs vm
newParamers4sorts _ _ _ = []

-- | creates a new parameterized sort
addNewParams2sort :: ParamSort -> [Token] -> ParamSort
addNewParams2sort (Sort tok, _) lps@(_ : _) = (Sort tok', lps) where
    tok' = mkSimpleId $ concat [show tok, "`{", printNewParams4sort lps, "`}"]
addNewParams2sort (Kind tok, _) lps@(_ : _) = (Kind tok', lps) where
    tok' = mkSimpleId $ concat [show tok, "`{", printNewParams4sort lps, "`}"]
addNewParams2sort (ps, _) _ = (ps, [])

-- | introduces commas between the tokens
printNewParams4sort :: [Token] -> String
printNewParams4sort [] = ""
printNewParams4sort [p] = show p
printNewParams4sort (p : ps) = concat [show p, "`,", printNewParams4sort ps]

{- | instantiate a sort
Params: Parameterized sort -> Parameter to be replaced -> New name of the
parameter -}
instantiateSort :: ParamSort -> [Token] -> [Token] -> ParamSort
instantiateSort sp@(Sort tok, tok_params) (p : ps) (v : vs) =
  if notElem p tok_params then instantiateSort sp ps vs else
    let tok' = mkSimpleId $ instantiateSortString (show tok) (show p) (show v)
    in instantiateSort (Sort tok', tok_params) ps vs
instantiateSort sp@(Kind tok, tok_params) (p : ps) (v : vs) =
  if notElem p tok_params then instantiateSort sp ps vs else
    let tok' = mkSimpleId $ instantiateSortString (show tok) (show p) (show v)
    in instantiateSort (Kind tok', tok_params) ps vs
instantiateSort ps _ _ = ps

{- | replaces one param by one view in a sort identifier
sort id -> param id -> view id -}
instantiateSortString :: String -> String -> String -> String
instantiateSortString ('{' : cs) param view = '{' : if notElem '{' cs
    then instantiateSortStringAux cs param view ""
    else instantiateSortString cs param view
instantiateSortString (c : cs) param view =
     c : instantiateSortString cs param view
instantiateSortString [] _ _ = ""

{- | replaces one param by one view in the list of parameters
parameters list -> param id -> view id -}
instantiateSortStringAux :: String -> String -> String -> String -> String
instantiateSortStringAux ('`' : ',' : ps) param view acc =
    value ++ "`," ++ instantiateSortStringAux ps param view ""
             where value = if acc == param
                           then view
                           else acc
instantiateSortStringAux ('`' : '}' : _) param view acc = value ++ "`}"
             where value = if acc == param
                           then view
                           else acc
instantiateSortStringAux (p : ps) param view acc =
    instantiateSortStringAux ps param view (acc ++ [p])
instantiateSortStringAux _ _ _ acc = acc

-- | qualifies the source sorts in the renamigs
qualifyRenamings :: Token -> [Renaming] -> [Renaming]
qualifyRenamings t = map (qualifyRenaming t)

{- | qualifies the source sort in the renaming. Sorts only appear in operator
mappings with profile and sort mappings -}
qualifyRenaming :: Token -> Renaming -> Renaming
qualifyRenaming p rnm = case rnm of
    OpRenaming2 from ar co to -> OpRenaming2 from (map (qualifyType p) ar)
      (qualifyType p co) to
    SortRenaming from to -> SortRenaming (qualifySort p from) to
    _ -> rnm

-- | qualifies both the source and target sorts in the renamings
qualifyRenamings2 :: Token -> [Renaming] -> [Renaming]
qualifyRenamings2 t = map (qualifyRenaming2 t)

{- | qualifies both the source and target sorts in the renaming.
Sorts only appear in operator mappings with profile and sort mappings -}
qualifyRenaming2 :: Token -> Renaming -> Renaming
qualifyRenaming2 p rnm = case rnm of
    OpRenaming2 from ar co to -> OpRenaming2 from (map (qualifyType p) ar)
      (qualifyType p co) to
    SortRenaming from to -> SortRenaming
      (qualifySort p from) (qualifySort p to)
    _ -> rnm

{- | creates a renaming to substitute the sorts qualified by a parameter name
with a new parameter name due to a parameter binding -}
createQualifiedSortRenaming :: Token -> Token -> Symbols -> [Renaming]
createQualifiedSortRenaming _ _ [] = []
createQualifiedSortRenaming old new (s : ss) = case old == new of
                True -> []
                False -> rnm : createQualifiedSortRenaming old new ss
                             where rnm = SortRenaming (qualifiedSort old' s')
                                                      (qualifiedSort new' s')
        where old' = HasName.getName old
              new' = HasName.getName new
              s' = HasName.getName s

-- | qualifies with the given parameter the token
qualifiedSort :: Token -> Token -> Sort
qualifiedSort param sort =
    SortId $ mkSimpleId $ concat [show param, "$", show sort]

-- | qualifies with the given parameter the sort
qualifySort :: Token -> Sort -> Sort
qualifySort p (SortId s) = qualifiedSort p s

-- | qualifies with the given parameter the type
qualifyType :: Token -> Type -> Type
qualifyType p (TypeSort (SortId s)) = TypeSort $ qualifiedSort p s
qualifyType _ ty = ty

{- | qualifies the symbols in the theory imported with the parameter name
given as first parameter -}
createQualificationTh2Mod :: Token -> Symbols -> [Renaming]
createQualificationTh2Mod _ [] = []
createQualificationTh2Mod par (s : ss) =
                rnm : createQualificationTh2Mod par ss
        where par' = HasName.getName par
              s' = HasName.getName s
              rnm = SortRenaming (SortId s') (qualifiedSort par' s')

-- | Library name for Maude prelude
preludeLib :: LibName
preludeLib = emptyLibName "Maude_Prelude"

{- | generates the library and the development graph from the path of the
maude file -}
anaMaudeFile :: HetcatsOpts -> FilePath -> IO (Maybe (LibName, LibEnv))
anaMaudeFile opts file = do
    (dg1, dg2) <- directMaudeParsing opts file
    let ln = emptyLibName file
        lib1 = Map.singleton preludeLib $
                 computeDGraphTheories Map.empty ln $ markFree Map.empty $
                 markHiding Map.empty dg1
        lib2 = Map.insert ln
                 (computeDGraphTheories lib1 ln $ markFree lib1 $
                 markHiding lib1 dg2) lib1
    return $ Just (ln, lib2)
