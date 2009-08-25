
module Maude.Maude2DG where

import System.IO
import System.Process

import Static.DevGraph
import Static.GTheory
import Static.AnalysisStructured

import Logic.Prover
import Logic.Grothendieck
import Logic.ExtSign
import Logic.Logic

import Maude.AS_Maude
import Maude.Sign
import Maude.Sentence
import Maude.Morphism
import Maude.Logic_Maude
import Maude.Language
import Maude.Shellout
import Maude.Symbol
import qualified Maude.Meta.HasName as HasName

import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Graph.Inductive.Graph

import Common.AS_Annotation
import Common.Result
import Common.Id

-- Borrar despues de las pruebas
import GUI.ShowGraph
import Driver.Options
import Common.LibName

maude_cmd :: String
maude_cmd = "/Applications/maude-darwin/maude.intelDarwin -interactive -no-banner"

data ImportType = Pr | Ex | Inc
type ModExpProc = (Token, TokenInfoMap, Morphism, [ParamSort], DGraph)
type ImportProc = (ImportType, Token, TokenInfoMap, Morphism, [ParamSort], DGraph)
type TokenInfoMap = Map.Map Token ProcInfo
type ProcInfo = (Node, Sign, Symbols, [(Token, Token, Symbols)], [ParamSort])
type ParamInfo = ([(Token, Token, Symbols)], TokenInfoMap, [Morphism], DGraph)

-- | Map from view identifiers to tuples containing the target node of the
-- view, the morphism, and a Boolean value indicating if the view instantiates
-- all the values
type ViewMap = Map.Map Token (Node, Token, Morphism, [Renaming], Bool)

type InsSpecRes = (TokenInfoMap, ViewMap, [Token], DGraph)

-- | Pair of tokens and parameters contained by the token
type ParamSort = (Symbol, [Token])

insertSpecs :: [Spec] -> TokenInfoMap -> ViewMap -> [Token] -> DGraph -> DGraph
insertSpecs [] _ _ _ dg = dg
insertSpecs (s : ss) tim vm ths dg = insertSpecs ss tim' vm' ths' dg'
              where (tim', vm', ths', dg') = insertSpec s tim vm ths dg

insertSpec :: Spec -> TokenInfoMap -> ViewMap -> [Token] -> DGraph -> InsSpecRes
insertSpec (SpecMod sp_mod) tim vm ths dg = (tim4, vm, ths, dg5)
              where ps = getParams sp_mod
                    (pl, tim1, morphs, dg1) = processParameters ps tim dg
                    top_sg = Maude.Sign.fromSpec sp_mod
                    paramSorts = getSortsParameterizedBy (paramNames ps) (Set.toList $ sorts top_sg)
                    (il, _) = getImportsSorts sp_mod
                    ips = processImports tim1 vm dg1 il
                    (tim2, dg2) = last_da ips (tim1, dg1)
                    sg = sign_union_morphs morphs $ sign_union top_sg ips
                    ext_sg = makeExtSign Maude sg
                    nm_sns = map (makeNamed "") $ Maude.Sentence.fromSpec sp_mod
                    sens = toThSens nm_sns
                    gt = G_theory Maude ext_sg startSigId sens startThId
                    tok = HasName.getName sp_mod
                    name = makeName tok
                    (ns, dg3) = insGTheory dg2 name DGBasic gt
                    tim3 = Map.insert tok (getNode ns, sg, [], pl, paramSorts) tim2
                    (tim4, dg4) = createEdgesImports tok ips sg tim3 dg3
                    dg5 = createEdgesParams tok pl morphs sg tim4 dg4
insertSpec (SpecTh sp_th) tim vm ths dg = (tim3, vm, tok : ths, dg3)
              where (il, ss1) = getImportsSorts sp_th
                    ips = processImports tim vm dg il
                    ss2 = getThSorts ips
                    (tim1, dg1) = last_da ips (tim, dg)
                    sg = sign_union (Maude.Sign.fromSpec sp_th) ips
                    ext_sg = makeExtSign Maude sg
                    nm_sns = map (makeNamed "") $ Maude.Sentence.fromSpec sp_th
                    sens = toThSens nm_sns
                    gt = G_theory Maude ext_sg startSigId sens startThId
                    tok = HasName.getName sp_th
                    name = makeName tok
                    (ns, dg2) = insGTheory dg1 name DGBasic gt
                    tim2 = Map.insert tok (getNode ns, sg, ss1 ++ ss2, [], []) tim1
                    (tim3, dg3) = createEdgesImports tok ips sg tim2 dg2
insertSpec (SpecView sp_v) tim vm ths dg = (tim2, vm', ths, dg4)
              where View name from to rnms = sp_v
                    inst = isInstantiated ths to
                    tok_name = HasName.getName name
                    (tok1, tim1, morph1, _, dg1) = processModExp tim vm dg from
                    (tok2, tim2, morph2, _, dg2) = processModExp tim1 vm dg1 to
                    (n1, _, _, _, _) = fromJust $ Map.lookup tok1 tim2
                    (n2, _, _, _, _) = fromJust $ Map.lookup tok2 tim2
                    morph = fromSignsRenamings (target morph1) (target morph2) rnms
                    morph' = fromJust $ maybeResult $ compose morph1 morph
                    (new_sign, new_sens) = sign4renamings (target morph1) (sortMap morph) rnms
                    (n3, dg3) = insertInnerNode n2 (makeName tok2) morph2 new_sign new_sens dg2
                    vm' = Map.insert (HasName.getName name) (n3, tok2, morph', rnms, inst) vm
                    dg4 = insertThmEdgeMorphism tok_name n3 n1 morph' dg3

-- | compute the union of the signatures obtained from the importation list
sign_union :: Sign -> [ImportProc] -> Sign
sign_union sign = foldr (Maude.Sign.union . get_sign) sign

-- | extract the target signature from the morphism in an importation tuple
get_sign :: ImportProc -> Sign
get_sign (_, _, _, morph, _, _) = target morph

-- | compute the union of the target signatures of a list of morphisms
sign_union_morphs :: [Morphism] -> Sign -> Sign
sign_union_morphs morphs sg =  foldr (Maude.Sign.union . target) sg morphs

-- | extracts the last (newest) data structures from a list of importation
-- tuples, using the second argument as default value if the list is empty
last_da :: [ImportProc] -> (TokenInfoMap, DGraph) -> (TokenInfoMap, DGraph)
last_da [(_, _, tim, _, _, dg)] _ = (tim, dg)
last_da (_ : ips) p = last_da ips p
last_da _ p = p

-- | generate the edges required by a parameter list in a module instantiation
createEdgesParams :: Token -> [(Token, Token, Symbols)] -> [Morphism] -> Sign
                     -> TokenInfoMap -> DGraph -> DGraph
createEdgesParams tok1 ((_, tok2, _) : toks) (morph : morphs) sg tim dg =
                                       createEdgesParams tok1 toks morphs sg tim dg'
               where morph' = setTarget sg morph
                     (n1, _, _, _, _) = fromJust $ Map.lookup tok1 tim
                     (n2, _, _, _, _) = fromJust $ Map.lookup tok2 tim
                     dg' = insertDefEdgeMorphism n1 n2 morph' dg
createEdgesParams _ _ _ _ _ dg = dg

-- | generate the edges required by the importations
createEdgesImports :: Token -> [ImportProc] -> Sign -> TokenInfoMap -> DGraph
                      -> (TokenInfoMap, DGraph)
createEdgesImports _ [] _ tim dg = (tim, dg)
createEdgesImports tok (ip : ips) sg tim dg = createEdgesImports tok ips sg tim' dg'
               where (tim', dg') = createEdgeImport tok ip sg tim dg

-- | generate the edge for a concrete importation
createEdgeImport :: Token -> ImportProc -> Sign -> TokenInfoMap -> DGraph
                    -> (TokenInfoMap, DGraph)
createEdgeImport tok1 (Pr, tok2, _, morph, _, _) sg tim dg = (tim', dg'')
               where morph' = setTarget sg morph
                     (tok2', tim', dg') = insertFreeNode tok2 tim dg
                     (n1, _, _, _, _) = fromJust $ Map.lookup tok1 tim'
                     (n2, _, _, _, _) = fromJust $ Map.lookup tok2' tim'
                     dg'' = insertDefEdgeMorphism n1 n2 morph' dg'
createEdgeImport tok1 (Ex, tok2, _, morph, _, _) sg tim dg = (tim, dg')
               where morph' = setTarget sg morph
                     (n1, _, _, _, _) = fromJust $ Map.lookup tok1 tim
                     (n2, _, _, _, _) = fromJust $ Map.lookup tok2 tim
                     dg' = insertConsEdgeMorphism n1 n2 morph' dg
createEdgeImport tok1 (Inc, tok2, _, morph, _, _) sg tim dg = (tim, dg')
               where morph' = setTarget sg morph
                     (n1, _, _, _, _) = fromJust $ Map.lookup tok1 tim
                     (n2, _, _, _, _) = fromJust $ Map.lookup tok2 tim
                     dg' = insertDefEdgeMorphism n1 n2 morph' dg

-- | extract the sorts provided by the theories
getThSorts :: [ImportProc] -> Symbols
getThSorts [] = []
getThSorts (ip : ips) = getThSortsAux ip ++ getThSorts ips

getThSortsAux :: ImportProc -> Symbols
getThSortsAux (_, tok, tim, _, _, _) = srts
         where (_, _, srts, _, _) = fromJust $ Map.lookup tok tim

-- | generate the extra signature needed when using term to term renaming in views
sign4renamings :: Sign -> SymbolMap -> [Renaming] -> (Sign, [Sentence])
sign4renamings sg sm ((TermMap t1 t2) : rnms) = (new_sg, (Equation eq) : sens)
         where (op_top, ss) = getOpSorts t1
               sg' = newOp sg op_top ss sm
               (sg'', sens) = sign4renamings sg sm rnms
               eq = Eq (applyRenamingTerm sm t1) t2 [] []
               new_sg = Maude.Sign.union sg' sg''
sign4renamings sg sm (_ : rnms) = sign4renamings sg sm rnms
sign4renamings sg _ [] = (sg, [])

-- | given the identifier of an operator in the given signature, the function
-- generates a new signature with this operator and a renamed profile computed
-- from the renaming given in the mapping
newOp :: Sign -> Token -> Symbols -> SymbolMap -> Sign
newOp sg op ss sm = Maude.Sign.empty {ops = Map.singleton op ods'}
         where om = ops sg
               ods = fromJust $ Map.lookup op om
               ods' = getOpDeclSet ods ss sm

-- | rename the profile with the given map
getOpDeclSet :: OpDeclSet -> Symbols -> SymbolMap -> OpDeclSet
getOpDeclSet ods ss sm = Set.singleton (op_sym', ats)
         where f = \ (Operator _ x _) b -> x == ss || b
               g = \ (x, _) -> Set.fold f False x
               (ods', ats) = head $ Set.toList $ Set.filter g ods
               h = \ (Operator _ y _) -> y == ss
               ods'' = Set.filter h ods'
               op_sym = head $ Set.toList ods''
               op_sym' = applyRenamingOpSymbol op_sym sm

-- | apply the renaming in the map to the operator declaration
applyRenamingOpSymbol :: Symbol -> SymbolMap -> SymbolSet
applyRenamingOpSymbol (Operator q ar co) sm = Set.singleton $ Operator q ar' co'
         where f = \ x -> if Map.member x sm
                          then fromJust $ Map.lookup co sm
                          else x
               ar' = map f ar
               co' = f co
applyRenamingOpSymbol _ _ = Set.empty

-- | rename the sorts in a term
applyRenamingTerm :: SymbolMap -> Term -> Term
applyRenamingTerm sm (Apply q ts ty) = Apply q (map (applyRenamingTerm sm) ts)
                                               (applyRenamingType sm ty)
applyRenamingTerm sm (Const q s) = Const q s'
         where s' = applyRenamingType sm s
applyRenamingTerm sm (Var q s) = Var q s'
         where s' = applyRenamingType sm s

-- | rename a type
applyRenamingType :: SymbolMap -> Type -> Type
applyRenamingType sm (TypeSort s) = TypeSort $ SortId $ HasName.getName q'
         where SortId q = s
               q' = if Map.member (Sort q) sm
                    then fromJust $ Map.lookup (Sort q) sm
                    else (Sort q)
applyRenamingType sm (TypeKind k) = TypeKind $ KindId $ HasName.getName q'
         where KindId q = k
               q' = if Map.member (Kind q) sm
                    then fromJust $ Map.lookup (Kind q) sm
                    else (Kind q)

-- | extract the top operator of a term and the names of its sorts
-- if it is applicated to some arguments
getOpSorts :: Term -> (Token, Symbols)
getOpSorts (Const q _) = (q, [])
getOpSorts (Var q _) = (q, [])
getOpSorts (Apply q ls _) = (q, getTypes ls)

getTypes :: [Term] -> Symbols
getTypes ((Var _ (TypeSort s)) : ts) = Sort (HasName.getName s) : getTypes ts
getTypes ((Var _ (TypeKind s)) : ts) = Kind (HasName.getName s) : getTypes ts
getTypes _ = []

processImports :: TokenInfoMap -> ViewMap -> DGraph -> [Import] -> [ImportProc]
processImports _ _ _ [] = []
processImports tim vm dg (i : il) = ip : processImports tim' vm dg' il
         where ip@(_, _, tim', _, _, dg') = processImport tim vm dg i

processImport :: TokenInfoMap -> ViewMap -> DGraph -> Import -> ImportProc
processImport tim vm dg (Protecting modExp) = (Pr, tok, tim', morph, ps, dg')
         where (tok, tim', morph, ps, dg') = processModExp tim vm dg modExp
processImport tim vm dg (Extending modExp) = (Ex, tok, tim', morph, ps, dg')
         where (tok, tim', morph, ps, dg') = processModExp tim vm dg modExp
processImport tim vm dg (Including modExp) = (Inc, tok, tim', morph, ps, dg')
         where (tok, tim', morph, ps, dg') = processModExp tim vm dg modExp

processParameters :: [Parameter] -> TokenInfoMap -> DGraph -> ParamInfo
processParameters ps tim dg = foldr processParameter ([], tim, [], dg) ps

processParameter :: Parameter -> ParamInfo -> ParamInfo
processParameter (Parameter sort modExp) (toks, tim, morphs, dg) = (toks', tim', morphs', dg')
         where (tok, tim', morph, _, dg') = processModExp tim Map.empty dg modExp
               (_, _, fs, _, _) = fromJust $ Map.lookup tok tim'
               fs' = renameSorts morph fs
               morph' = qualifySorts morph (HasName.getName sort) fs'
               toks' = (HasName.getName sort, tok, fs') : toks
               morphs' =  morph' : morphs

processModExp :: TokenInfoMap -> ViewMap -> DGraph -> ModExp -> ModExpProc
processModExp tim _ dg (ModExp modId) = (tok, tim, morph, ps, dg)
                     where tok = HasName.getName modId
                           (_, sg, _, _, ps) = fromJust $ Map.lookup tok tim
                           morph = Maude.Morphism.inclusion sg sg
processModExp tim vm dg (SummationModExp modExp1 modExp2) = (tok, tim3, morph, ps', dg5)
                     where (tok1, tim1, morph1, ps1, dg1) = processModExp tim vm dg modExp1
                           (tok2, tim2, morph2, ps2, dg2) = processModExp tim1 vm dg1 modExp2
                           ps' = deleteRepeated $ ps1 ++ ps2
                           tok = mkSimpleId $ "{" ++ show tok1 ++ " + " ++ show tok2 ++ "}"
                           (n1, _, ss1, _, _) = fromJust $ Map.lookup tok1 tim2
                           (n2, _, ss2, _, _) = fromJust $ Map.lookup tok2 tim2
                           ss1' = renameSorts morph1 ss1
                           ss2' = renameSorts morph1 ss2
                           sg1 = target morph1
                           sg2 = target morph2
                           sg = Maude.Sign.union sg1 sg2
                           morph = Maude.Morphism.inclusion sg sg
                           morph1' = setTarget sg morph1
                           morph2' = setTarget sg morph2
                           (tim3, dg3) = insertNode tok sg tim2 (ss1' ++ ss2') [] dg2
                           (n3, _, _, _, _) = fromJust $ Map.lookup tok tim3
                           dg4 = insertDefEdgeMorphism n3 n1 morph1' dg3
                           dg5 = insertDefEdgeMorphism n3 n2 morph2' dg4
processModExp tim vm dg (RenamingModExp modExp rnms) = (tok, tim', comp_morph, ps', dg')
                     where (tok, tim', morph, ps, dg') = processModExp tim vm dg modExp
                           morph' = fromSignRenamings (target morph) rnms
                           ps' = applyRenamingParamSorts (sortMap morph') ps
                           comp_morph = fromJust $ maybeResult $ compose morph morph'
processModExp tim vm dg (InstantiationModExp modExp views) = (tok'', tim'', final_morph, new_param_sorts, dg'')
                     where (tok, tim', morph, paramSorts, dg') = processModExp tim vm dg modExp
                           (_, _, _, ps, _) = fromJust $ Map.lookup tok tim'
                           param_names = map (fstTern) ps
                           view_names = map HasName.getName views
                           (new_param_sorts, ps_morph) = instantiateSorts param_names view_names vm morph paramSorts
                           (tok', morph1, ns, deps) = processViews views (mkSimpleId "") tim' vm ps (ps_morph, [], [])
                           tok'' = mkSimpleId $ show tok ++ "{" ++ show tok' ++ "}"
                           sg2 = target morph1
                           final_morph = Maude.Morphism.inclusion sg2 sg2
                           (tim'', dg'') = if Map.member tok'' tim
                                           then (tim', dg')
                                           else updateGraphViews tok tok'' sg2 morph1 ns tim' deps dg'

updateGraphViews :: Token -> Token -> Sign -> Morphism -> [(Node, Sign)] -> TokenInfoMap
                    -> [(Token, Token, Symbols)] -> DGraph -> (TokenInfoMap, DGraph)
updateGraphViews tok1 tok2 sg morph views tim deps dg = (tim', dg''')
                     where (n1, _, _, _, _) = fromJust $ Map.lookup tok1 tim
                           morph' = setTarget sg morph
                           (tim', dg') = insertNode tok2 sg tim [] deps dg
                           (n2, _, _, _, _) = fromJust $ Map.lookup tok2 tim'
                           dg'' = insertDefEdgeMorphism n2 n1 morph' dg'
                           dg''' = insertDefEdgesMorphism n2 views sg dg''

processViews :: [ViewId] -> Token -> TokenInfoMap -> ViewMap -> [(Token, Token, Symbols)]
                -> (Morphism, [(Node, Sign)], [(Token, Token, Symbols)]) 
                -> (Token, Morphism, [(Node, Sign)], [(Token, Token, Symbols)])
processViews (vi : vis) tok tim vm (p : ps) (morph, lp, dep) =
                             case mn of
                                   Just n -> processViews vis tok'' tim vm ps (morph', lp ++ [(n, target morph')], dep ++ new_dep)
                                   Nothing -> processViews vis tok'' tim vm ps (morph', lp, dep)
                     where (tok', morph', mn, new_dep) = processView vi tim vm p morph
                           tok'' = mkSimpleId $ show tok ++ "," ++ show tok'
processViews _ tok _ _ _ (morph, nds, deps) = (tok', morph, nds, deps)
                     where tok' = mkSimpleId $ drop 1 $ show tok

processView :: ViewId -> TokenInfoMap -> ViewMap -> (Token, Token, Symbols) ->
               Morphism -> (Token, Morphism, Maybe Node, [(Token, Token, Symbols)])
processView vi tim vm (p, theory, ss) morph =
                       if Map.member name vm
                       then morphismView name p ss (fromJust $ Map.lookup name vm) morph
                       else paramBinding theory name p ss morph tim
        where name = HasName.getName vi

morphismView :: Token -> Token -> Symbols -> (Node, Token, Morphism, [Renaming], Bool)
                -> Morphism -> (Token, Morphism, Maybe Node, [(Token, Token, Symbols)])
morphismView name p _ (n, _, _, rnms, True) morph = (name, morph', Just n, [])
        where rnms' = qualifyRenamings p rnms
              morph' = applyRenamings morph rnms'

morphismView name p ss (n, th, morph, rnms, False) morph1 = 
                         (name, morph2, Just n, [(p, th, getNewSorts ss morph)])
        where rnms' = qualifyRenamings2 p rnms
              morph2 = applyRenamings morph1 rnms'

-- theory, parameter instantiated -> parameter binding -> sorts bound -> current morph
-- map token info
paramBinding :: Token -> Token -> Token -> Symbols -> Morphism -> TokenInfoMap
                -> (Token, Morphism, Maybe Node, [(Token, Token, Symbols)])
paramBinding th view p ss morph tim = (view, morph', Just n, [])
        where rnms = createQualifiedSortRenaming p view ss
              morph' = applyRenamings morph rnms
              (n, _, _, _, _) = fromJust $ Map.lookup th tim 

insertNode :: Token -> Sign -> TokenInfoMap -> Symbols -> [(Token, Token, Symbols)] 
              -> DGraph -> (TokenInfoMap, DGraph)
insertNode tok sg tim ss deps dg = if Map.member tok tim
                         then (tim, dg)
                         else let
                                ext_sg = makeExtSign Maude sg
                                gt = G_theory Maude ext_sg startSigId noSens startThId
                                name = makeName tok
                                (ns, dg') = insGTheory dg name DGBasic gt
                                tim' = Map.insert tok (getNode ns, sg, ss, deps, []) tim
                              in (tim', dg')

insertInnerNode :: Node -> NodeName -> Morphism -> Sign -> [Sentence] -> DGraph
                   -> (Node, DGraph)
insertInnerNode nod nm morph sg sens dg =
                         if (isIdentity morph) && null sens
                         then (nod, dg)
                         else let
                                th_sens = toThSens $ map (makeNamed "") sens
                                sg' = Maude.Sign.union sg $ target morph
                                ext_sg = makeExtSign Maude sg'
                                gt = G_theory Maude ext_sg startSigId th_sens startThId
                                (ns, dg') = insGTheory dg (inc nm) DGBasic gt
                                nod2 = getNode ns
                                morph' = setTarget sg' morph
                                dg'' = insertDefEdgeMorphism nod2 nod morph' dg'
                              in (nod2, dg'')

-- | insert the list of definition edges, building for each node the inclusion morphism
-- between the signatures
insertDefEdgesMorphism :: Node -> [(Node, Sign)] -> Sign -> DGraph -> DGraph
insertDefEdgesMorphism _ [] _ dg = dg
insertDefEdgesMorphism n1 ((n2, sg1) : views) sg2 dg = insertDefEdgesMorphism n1 views sg2 dg'
                  where morph = Maude.Morphism.inclusion sg1 sg2
                        dg' = insertDefEdgeMorphism n1 n2 morph dg

-- | insert a definition link between the nodes with the given morphism
insertDefEdgeMorphism :: Node -> Node -> Morphism -> DGraph -> DGraph
insertDefEdgeMorphism n1 n2 morph dg = insEdgeDG (n2, n1, edg) dg
                     where mor = G_morphism Maude morph startMorId
                           edg = DGLink (gEmbed mor) globalDef SeeTarget $ getNewEdgeId dg

insertThmEdgeMorphism :: Token -> Node -> Node -> Morphism -> DGraph -> DGraph
insertThmEdgeMorphism name n1 n2 morph dg = insEdgeDG (n2, n1, edg) dg
                     where mor = G_morphism Maude morph startMorId
                           edg = DGLink (gEmbed mor) globalThm (DGLinkView name) $ getNewEdgeId dg

insertConsEdgeMorphism :: Node -> Node -> Morphism -> DGraph -> DGraph
insertConsEdgeMorphism n1 n2 morph dg = insEdgeDG (n2, n1, edg) dg
                     where mor = G_morphism Maude morph startMorId
                           edg = DGLink (gEmbed mor) (globalConsThm PCons) SeeTarget $ getNewEdgeId dg

insertFreeEdge :: Token -> Token -> TokenInfoMap -> DGraph -> DGraph
insertFreeEdge tok1 tok2 tim dg = insEdgeDG (n2, n1, edg) dg
                     where (n1, sg1, _, _, _) = fromJust $ Map.lookup tok1 tim
                           (n2, sg2, _, _, _) = fromJust $ Map.lookup tok2 tim
                           mor = G_morphism Maude (Maude.Morphism.inclusion sg1 sg2) startMorId
                           dgt = FreeOrCofreeDefLink Free $ EmptyNode (Logic Maude)
                           edg = DGLink (gEmbed mor) dgt SeeTarget $ getNewEdgeId dg

insertFreeNode :: Token -> TokenInfoMap -> DGraph -> (Token, TokenInfoMap, DGraph)
insertFreeNode t tim dg = (t', tim', dg'')
               where t' = mkFreeName t
                     b = Map.member t' tim
                     (tim', dg') = if b
                                   then (tim, dg)
                                   else insertFreeNode2 t' tim (fromJust $ Map.lookup t tim) dg
                     dg'' = if b
                            then dg'
                            else insertFreeEdge t' t tim' dg'

insertFreeNode2 :: Token -> TokenInfoMap -> ProcInfo -> DGraph -> (TokenInfoMap, DGraph)
insertFreeNode2 t tim (_, sg, _, _, _) dg = (tim', dg')
              where ext_sg = makeExtSign Maude sg
                    gt = G_theory Maude ext_sg startSigId noSens startThId
                    name = makeName t
                    (ns, dg') = insGTheory dg name DGBasic gt
                    tim' = Map.insert t (getNode ns, sg, [], [], []) tim

-- | Given the identifier of a module, generates the identifier for the module
-- with the ``freeness'' constraint
mkFreeName :: Token -> Token
mkFreeName = mkSimpleId . (\ x -> x ++ "'") . show

getParams :: Module -> [Parameter]
getParams (Module _ params _) = params

getImportsSorts :: Module -> ([Import], Symbols)
getImportsSorts (Module _ _ stmts) = getImportsSortsStmnts stmts ([],[])

getImportsSortsStmnts :: [Statement] -> ([Import], Symbols) -> ([Import], Symbols)
getImportsSortsStmnts [] p = p
getImportsSortsStmnts ((ImportStmnt imp) : stmts) (is, ss) =
                                  getImportsSortsStmnts stmts (imp : is, ss)
getImportsSortsStmnts ((SortStmnt s) : stmts) (is, ss) =
            getImportsSortsStmnts stmts (is, (Sort $ HasName.getName s) : ss)
getImportsSortsStmnts (_ : stmts) p = getImportsSortsStmnts stmts p

directMaudeParsing :: FilePath -> IO DGraph
directMaudeParsing fp = do
              (hIn, hOut, _, _) <- runInteractiveCommand maude_cmd
              hPutStrLn hIn $ "load " ++ fp
              ns <- parse fp
              let ns' = either (\ _ -> []) id ns
              ms <- traverseNames hIn hOut ns'
              hPutStrLn hIn "in Maude/hets.prj"
              psps <- predefinedSpecs hIn hOut
              sps <- traverseSpecs hIn hOut ms
              hClose hIn
              hClose hOut
              return $ insertSpecs (psps ++ sps) Map.empty Map.empty [] emptyDG

traverseSpecs :: Handle -> Handle -> [String] -> IO [Spec]
traverseSpecs _ _ [] = return []
traverseSpecs hIn hOut (m : ms) = do
                 hPutStrLn hIn m
                 hFlush hIn
                 sOutput <- getAllSpec hOut "" False
                 ss <- traverseSpecs hIn hOut ms
                 let stringSpec = findSpec sOutput
                 let spec = read stringSpec :: Spec
                 return $ spec : ss

traverseNames :: Handle -> Handle -> [NamedSpec] -> IO [String]
traverseNames _ _ [] = return []
traverseNames hIn hOut (ModName q : ns) = do
                 hPutStrLn hIn $ "show module " ++ q ++ " ."
                 hFlush hIn
                 sOutput <- getAllOutput hOut "" False
                 rs <- traverseNames hIn hOut ns
                 return $ sOutput : rs
traverseNames hIn hOut (ViewName q : ns) = do
                 hPutStrLn hIn $ "show view " ++ q ++ " ."
                 hFlush hIn
                 sOutput <- getAllOutput hOut "" False
                 rs <- traverseNames hIn hOut ns
                 return $ sOutput : rs

getAllOutput :: Handle -> String -> Bool -> IO String
getAllOutput hOut s False = do
                 ss <- hGetLine hOut
                 getAllOutput hOut (s ++ "\n" ++ ss) (final ss)
getAllOutput _ s True = return $ prepare s

getAllSpec :: Handle -> String -> Bool -> IO String
getAllSpec hOut s False = do
                 ss <- hGetLine hOut
                 getAllSpec hOut (s ++ "\n" ++ ss) (finalSpec ss)
getAllSpec _ s True = return s

final :: String -> Bool
final "endfm" = True
final "endm" = True
final "endth" = True
final "endfth" = True
final "endv" = True
final _ = False

prepare :: String -> String
prepare s = "(" ++ (drop 8 s) ++ ")"

finalSpec :: String -> Bool
finalSpec "@#$endHetsSpec$#@" = True
finalSpec _ = False

predefined :: [NamedSpec]
predefined = [ModName "TRUTH-VALUE", ModName "TRUTH", ModName "BOOL", ModName "EXT-BOOL",
              ModName "NAT",
              ModName "INT", ModName "RAT", ModName "FLOAT", ModName "STRING", ModName "CONVERSION",
              ModName "RANDOM", ModName "QID", ModName "TRIV", ViewName "TRIV", ViewName "Bool",
              ViewName "Nat", ViewName "Int", ViewName "Rat", ViewName "Float", ViewName "String",
              ViewName "Qid", ModName "STRICT-WEAK-ORDER", ViewName "STRICT-WEAK-ORDER",
              ModName "STRICT-TOTAL-ORDER", ViewName "STRICT-TOTAL-ORDER", ViewName "Nat<",
              ViewName "Int<", ViewName "Rat<", ViewName "Float<", ViewName "String<",
              ModName "TOTAL-PREORDER", ViewName "TOTAL-PREORDER", ModName "TOTAL-ORDER", 
              ViewName "TOTAL-ORDER", ViewName "Nat<=", ViewName "Int<=", ViewName "Rat<=",
              ViewName "Float<=", ViewName "String<=", ModName "DEFAULT", ViewName "DEFAULT",
              ViewName "Nat0", ViewName "Int0", ViewName "Rat0", ViewName "Float0",
              ViewName "String0", ViewName "Qid0", ModName "LIST", ModName "WEAKLY-SORTABLE-LIST",
              ModName "SORTABLE-LIST", ModName "WEAKLY-SORTABLE-LIST'",
              ModName "SORTABLE-LIST'", ModName "SET", ModName "LIST-AND-SET",
              ModName "SORTABLE-LIST-AND-SET", ModName "SORTABLE-LIST-AND-SET'",
              ModName "LIST*", ModName "SET*", ModName "MAP", ModName "ARRAY",
              ModName "NAT-LIST", ModName "QID-LIST", ModName "QID-SET", ModName "META-TERM",
              ModName "META-MODULE", ModName "META-LEVEL", ModName "COUNTER", ModName "LOOP-MODE",
              ModName "CONFIGURATION"]

predefinedSpecs :: Handle -> Handle -> IO [Spec]
predefinedSpecs hIn hOut = traversePredefined hIn hOut predefined

traversePredefined :: Handle -> Handle -> [NamedSpec] -> IO [Spec]
traversePredefined _ _ [] = return []
traversePredefined hIn hOut (ModName n : ns) = do
                 hPutStrLn hIn $ "(hets " ++ n ++ " .)"
                 hFlush hIn
                 sOutput <- getAllSpec hOut "" False
                 ss <- traversePredefined hIn hOut ns
                 let stringSpec = findSpec sOutput
                 let spec = read stringSpec :: Spec
                 return $ spec : ss
traversePredefined hIn hOut (ViewName n : ns) = do
                 hPutStrLn hIn $ "(hetsView " ++ n ++ " .)"
                 hFlush hIn
                 sOutput <- getAllSpec hOut "" False
                 ss <- traversePredefined hIn hOut ns
                 let stringSpec = findSpec sOutput
                 let spec = read stringSpec :: Spec
                 return $ spec : ss

-- | return the parameter names
paramNames :: [Parameter] -> [Token]
paramNames = map f
         where f = \ (Parameter s _) -> HasName.getName s

-- | return the sorts (second argument of the pair) that contain any of the parameters
-- given as first argument
getSortsParameterizedBy :: [Token] -> Symbols -> [ParamSort]
getSortsParameterizedBy ps = filter f . map (g ps)
           where f = \ (_, l) -> l /= []
                 g = \ pss x -> let 
                         params = getSortParams $ HasName.getName x
                         in (x, intersec params pss)

intersec :: [Token] -> [Token] -> [Token]
intersec [] _ = []
intersec (e : es) l = case elem e l of
        False -> intersec es l
        True -> e : intersec es l

-- | extracts the parameters of the given sort
-- For example, getSortParams List{X} = [X]
-- List{X}{Y, Y} = [Y,Z]
getSortParams :: Token -> [Token]
getSortParams t = getSortParamsString $ show t

getSortParamsString :: String -> [Token]
getSortParamsString [] = []
getSortParamsString ('{' : cs) = if null sps
                                 then getSortParamsStringAux cs ""
                                 else sps
            where sps = getSortParamsString cs
getSortParamsString (_ : cs) = getSortParamsString cs

getSortParamsStringAux :: String -> String -> [Token]
getSortParamsStringAux ('`' : ',' : cs) st = mkSimpleId st : getSortParamsStringAux cs ""
getSortParamsStringAux ('`' : '}' : []) st = [mkSimpleId st]
getSortParamsStringAux (' ' : cs) st = getSortParamsStringAux cs st
getSortParamsStringAux (c : cs) st = getSortParamsStringAux cs (st ++ [c])
getSortParamsStringAux [] st = [mkSimpleId st]

-- | check if the target of the view is completely instantiated (to modules)
isInstantiated :: [Token] -> ModExp -> Bool
isInstantiated ths (ModExp modExp) = notElem (HasName.getName modExp) ths
isInstantiated ths (SummationModExp me1 me2) = isInstantiated ths me1 && 
                                               isInstantiated ths me2
isInstantiated ths (RenamingModExp modExp _) = isInstantiated ths modExp
isInstantiated _ (InstantiationModExp _ _) = True

-- | rename the parameterized sorts and computes if they are still parameterized
applyRenamingParamSorts :: SymbolMap -> [ParamSort] -> [ParamSort]
applyRenamingParamSorts sm = foldr (applyRenamingParamSort sm) []

applyRenamingParamSort :: SymbolMap -> ParamSort -> [ParamSort]
                          -> [ParamSort]
applyRenamingParamSort sm (tok, params) acc = case Map.member tok sm of
              False -> (tok, params) : acc
              True -> let
                   tok' = fromJust $ Map.lookup tok sm
                   ps = getSortsParameterizedBy params [tok']
                   in ps ++ acc

-- | removes the repetitions from a list
deleteRepeated :: [ParamSort] -> [ParamSort]
deleteRepeated [] = []
deleteRepeated (p : ps) = if elem p ps
                          then deleteRepeated ps
                          else p : deleteRepeated ps

fstTern :: (a, b, c) -> a
fstTern (a, _, _) = a

-- | instantiate the parametric sorts
-- ParamNames -> ViewName -> Map of views -> Parametricsorts
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

-- | compute the theories that have to be further instantiated
newParamers4sorts :: [Token] -> [Token] -> ViewMap -> [Token]
newParamers4sorts (param : ps) (view : vs) vm = case Map.member view vm of
        False -> newParamers4sorts ps vs vm
        True -> let
                 (_, _, _, _, inst) = fromJust $ Map.lookup view vm
                 param' = if inst
                          then []
                          else [param]
                in param' ++ newParamers4sorts ps vs vm
newParamers4sorts _ _ _ = []

addNewParams2sort :: ParamSort -> [Token] -> ParamSort
addNewParams2sort (Sort tok, _) lps@(_:_) = (Sort tok', lps)
         where tok' = mkSimpleId $ show tok ++ "`{" ++ printNewParams4sort lps ++ "`}"
addNewParams2sort (Kind tok, _) lps@(_:_) = (Kind tok', lps)
         where tok' = mkSimpleId $ show tok ++ "`{" ++ printNewParams4sort lps ++ "`}"
addNewParams2sort (ps, _) _ = (ps, [])

printNewParams4sort :: [Token] -> String
printNewParams4sort [] = ""
printNewParams4sort [p] = show p
printNewParams4sort (p : ps) = show p ++ "`," ++ printNewParams4sort ps

-- | instantiate a sort
-- Params: Parameterized sort -> Parameter to be replaced -> New name of the parameter
instantiateSort :: ParamSort -> [Token] -> [Token] -> ParamSort
instantiateSort sp@(Sort tok, tok_params) (p : ps) (v : vs) = case elem p tok_params of
                        False -> instantiateSort sp ps vs
                        True -> let 
                                 tok' = mkSimpleId $ instantiateSortString (show tok) (show p) (show v)
                                in instantiateSort (Sort tok', tok_params) ps vs
instantiateSort sp@(Kind tok, tok_params) (p : ps) (v : vs) = case elem p tok_params of
                        False -> instantiateSort sp ps vs
                        True -> let 
                                 tok' = mkSimpleId $ instantiateSortString (show tok) (show p) (show v)
                                in instantiateSort (Kind tok', tok_params) ps vs
instantiateSort ps _ _ = ps

-- | replace one param by one view in a sort identifier
-- sort id -> param id -> view id
instantiateSortString :: String -> String -> String -> String
instantiateSortString ('{' : cs) param view = case elem '{' cs of
                  False -> '{' : instantiateSortStringAux cs param view ""
                  True -> '{' : instantiateSortString cs param view
instantiateSortString (c : cs) param view = c : instantiateSortString cs param view
instantiateSortString [] _ _ = ""

-- | replace one param by one view in the list of parameters
-- parameters list -> param id -> view id
instantiateSortStringAux :: String -> String -> String -> String -> String
instantiateSortStringAux ('`' : ',' : ps) param view acc = value ++ "`," ++
                                                     instantiateSortStringAux ps param view ""
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

qualifyRenamings :: Token -> [Renaming] -> [Renaming]
qualifyRenamings t = map (qualifyRenaming t)

qualifyRenaming :: Token -> Renaming -> Renaming
qualifyRenaming p rnm = case rnm of
           OpRenaming2 from ar co to -> OpRenaming2 from (map (qualifyType p) ar) 
                                                         ((qualifyType p) co) to
           SortRenaming from to -> SortRenaming ((qualifySort p) from) to
           _ -> rnm

qualifyRenamings2 :: Token -> [Renaming] -> [Renaming]
qualifyRenamings2 t = map (qualifyRenaming2 t)

qualifyRenaming2 :: Token -> Renaming -> Renaming
qualifyRenaming2 p rnm = case rnm of
           OpRenaming2 from ar co to -> OpRenaming2 from (map (qualifyType p) ar) 
                                                         ((qualifyType p) co) to
           SortRenaming from to -> SortRenaming ((qualifySort p) from) ((qualifySort p) to)
           _ -> rnm

qualifyType :: Token -> Type -> Type
qualifyType p (TypeSort (SortId s)) = TypeSort (SortId $ mkSimpleId $ show p ++ "$" ++ show s)
qualifyType _ ty = ty

qualifySort :: Token -> Sort -> Sort
qualifySort p (SortId s) = SortId $ mkSimpleId $ show p ++ "$" ++ show s

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

qualifiedSort :: Token -> Token -> Sort
qualifiedSort param sort = SortId $ mkSimpleId $ show param ++ "$" ++ show sort


-- insertNode tiene que recibir tambien la lista de sorts parametrizados que se
-- calculen para la module expression


anaMaudeFile :: HetcatsOpts -> FilePath -> IO (Maybe (LIB_NAME, LibEnv))
anaMaudeFile _ file = do
    dg <- directMaudeParsing file
    let name = Lib_id $ Direct_link "Maude Module" nullRange
    return $ Just (name, Map.singleton name dg)
