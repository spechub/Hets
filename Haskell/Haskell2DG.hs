{- HetCATS/Haskell/Haskell2DG.hs
   Authors: S. Groening
   Year:    2003
-}

module Haskell.Haskell2DG (anaHaskellFile) where

import Options
import Haskell.Hatchet.MultiModule  (readModuleInfo)
import Haskell.Hatchet.HsParseMonad (ParseResult (..))
import Haskell.Hatchet.SynConvert   (toAHsModule)
import Haskell.Hatchet.HsParsePostProcess (fixFunBindsInModule)
import Haskell.Hatchet.HaskellPrelude
                                (tyconsMembersHaskellPrelude, 
                                 preludeDefs, 
                                 preludeSynonyms,
                                 preludeTyconAndClassKinds,
                                 preludeClasses,
                                 preludeInfixDecls,
                                 preludeDataCons)
import Haskell.Hatchet.Type     (assumpToPair)
import Haskell.Hatchet.HsParser (parse)
import Haskell.Hatchet.AnnotatedHsSyn (AHsDecl, AModule (..), AHsModule)
import Haskell.Hatchet.Rename   (IdentTable)
import Haskell.Hatchet.KindInference (KindEnv)
import Haskell.Hatchet.Representation (Scheme)
import Haskell.Hatchet.Class    (ClassHierarchy)
import Haskell.Hatchet.Env      (Env, listToEnv)
import Haskell.Hatchet.MultiModuleBasics (ModuleInfo (..),
                                          joinModuleInfo)
import Haskell.Hatchet.TIModule (tiModule, Timing)
import Haskell.Hatchet.HsSyn    (SrcLoc (..), HsModule (..))
    
import Static.DevGraph          (DGNodeLab (..),
                                 DGLinkLab (..),
                                 DGLinkType (..),
                                 DGOrigin (..),
                                 DGraph,
                                 LibEnv,
                                 GlobalEntry(..),
                                 NodeSig(..),
                                 getNode,
                                 emptyLibEnv)
import Syntax.AS_Library        (LIB_NAME (..),
                                 LIB_ID (..))
import Haskell.Hatchet.AnnotatedHsSyn
import Logic.Grothendieck        (G_sign (..),
                                  G_l_sentence_list (..),
                                  G_morphism (..),
                                  gEmbed)
import Logic.Logic               
import Common.Lib.Graph          (Node,
                                  empty,
                                  insNode,
                                  insEdge,
                                  newNodes,
                                  match)

import Common.Id                 (Token (..),
                                  SIMPLE_ID,
                                  nullPos)
import Haskell.Logic_Haskell     (Haskell (..))
import Haskell.HaskellUtils      (extractSentences)
import qualified Common.Lib.Map as Map
import Common.GlobalAnnotations  (emptyGlobalAnnos)


data HaskellEnv = HasEnv Timing              -- timing values for each stage
                         (Env Scheme)        -- output variable assumptions (may be 
                                             --        local, and pattern variables) 
                         (Env Scheme)        -- output data cons assumptions 
                         ClassHierarchy      -- output class Hierarchy 
                         KindEnv             -- output kinds 
                         IdentTable          -- info about identifiers in the module
                         AHsModule           -- renamed module 
                         [AHsDecl]           -- synonyms defined in this module

-- toplevel function: Creates DevGraph and LibEnv from a .hs file (including all imported modules)
anaHaskellFile :: HetcatsOpts -> String -> IO (Maybe (LIB_NAME, -- filename
                                                      HsModule, -- as tree
                                                      DGraph,   -- development graph
                                                      LibEnv    -- DGraphs for imported modules 
                                                                --  incl. main module
                                                      ))
anaHaskellFile _ srcFile = 
   do
     src <- readFile srcFile
     let moduleSyntax = parseHsSource src

-- re-group matches into their associated funbinds (patch up the output from the parser)

     let moduleSyntaxFixedFunBinds = fixFunBindsInModule moduleSyntax

-- map the abstract syntax into the annotated abstract syntax

     let annotatedSyntax = toAHsModule moduleSyntaxFixedFunBinds 

     -- this is the ModuleInfo that we were passing into tiModule
     -- earlier (just the Prelude stuff)
     let preludeModInfo = ModuleInfo {
                                moduleName = AModule "Prelude",
                                varAssumps = (listToEnv $ map assumpToPair preludeDefs),
                                tyconsMembers = tyconsMembersHaskellPrelude, 
                                dconsAssumps = (listToEnv $ map assumpToPair preludeDataCons),
                                classHierarchy = listToEnv preludeClasses,
                                kinds = (listToEnv preludeTyconAndClassKinds),
                                infixDecls = preludeInfixDecls,
                                synonyms = preludeSynonyms
                           }

     -- now we read in the .ti files from the imported
     -- modules to pass in to tiModule
     importedModInfo <- readModuleInfo annotatedSyntax

     let initialModInfo = joinModuleInfo preludeModInfo importedModInfo

-- call the type inference code for this module 
     (timings, 
      moduleEnv, 
      dataConEnv,
      newClassHierarchy, 
      newKindInfoTable,
      moduleIds,
      moduleRenamed,
      moduleSynonyms) <- tiModule [] annotatedSyntax initialModInfo
     let hasEnv = HasEnv timings 
                         moduleEnv
                         dataConEnv
                         newClassHierarchy
                         newKindInfoTable
                         moduleIds
                         moduleRenamed
                         moduleSynonyms
     let libName = Lib_id(Indirect_link srcFile [])
     (dg,le) <- hasEnv2DG libName hasEnv
     return (Just(libName, moduleSyntax, dg, le))

hasEnv2DG :: LIB_NAME -> HaskellEnv -> IO (DGraph, LibEnv)
hasEnv2DG ln (HasEnv 
               _
               moduleEnv
               dataConEnv
               classHier
               kindInfoTable
               _
               (AHsModule name exps imps decls)
               moduleSynonyms) =

               let modInfo = ModuleInfo {
                     moduleName = name,
                     varAssumps = moduleEnv,
                     dconsAssumps = dataConEnv,
                     classHierarchy = classHier,
                     kinds = kindInfoTable,
                     synonyms = moduleSynonyms,
                     infixDecls = [],
                     tyconsMembers = [] }
                   aMod = AHsModule name exps imps decls
                in
                   dGraphAndLibEnv ln aMod modInfo
                   

-- input: main module's abstract syntax and its ModuleInfo
-- generates a DGraph and 'first node' of this DGraph
-- checks whether there are imported modules or not
dGraphAndLibEnv :: LIB_NAME -> AHsModule -> ModuleInfo -> IO(DGraph, LibEnv)
dGraphAndLibEnv ln (AHsModule name exps imps decls) modInfo = 
           -- create the first node, representing the main Module
       let node_contents  | imps == [] =       -- no imports
                             DGNode {
                               dgn_name = aHsMod2SimpleId name,
                               dgn_sign = G_sign Haskell modInfo,
                               dgn_sens = G_l_sentence Haskell (extractSentences 
                                           (AHsModule name exps imps decls)),
                               dgn_origin = DGBasic }
                          | otherwise =       -- imports
                             DGNode {
                               dgn_name = aHsMod2SimpleId name,
                               dgn_sign = G_sign Haskell modInfo,
                               dgn_sens = G_l_sentence Haskell (extractSentences
                                           (AHsModule name exps imps decls)),
                               dgn_origin = DGExtension }
           dg = empty
           [node] = newNodes 0 dg
           dg' = insNode(node, node_contents) dg
        in
           case imps of
             -- no imports, no other nodes and edges
             [] -> return (dg', (addLibEnv emptyLibEnv ln node dg'))
             -- imports -> add imported Modules
             _  -> insImports ln dg' node emptyLibEnv imps

-- input: LibName of 'main module', growing DGraph, node of 'main module'
--        growing LibEnv, List of importDecls (from 'main module')
insImports :: LIB_NAME -> DGraph ->  Node -> LibEnv -> [AHsImportDecl] -> IO (DGraph,LibEnv)
insImports ln dg n le [] = return (dg, (addLibEnv le ln n dg))
insImports ln dg n le ((AHsImportDecl src name b mbm mayBeHiding):idecls) = 
        do -- analyse imported module just like the main module
           Just(libName, _, dg', libEnv) <- anaHaskellFile defaultHetcatsOpts (fileName name)

           let idecl = AHsImportDecl src name b mbm mayBeHiding
           -- unite the old 'big' LibEnv le with the one for the imported module
           let le' = le `Map.union` libEnv
           -- unite the main DGraph with the one for the imported module
           let dg'' = joinDG dg dg'
           -- lookup node for imported module
           let node = lookupNode libName libEnv
           -- create LinkLabel
           let link = createDGLinkLabel idecl
           -- insert new edge with LinkLabel
           let linkedDG = insEdge (node,n,link) dg''

           insImports ln linkedDG n le' idecls


-- --------------- utilities --------------- --

createDGLinkLabel :: AHsImportDecl -> DGLinkLab
createDGLinkLabel idecl = 
        case idecl of
          AHsImportDecl _ _ _ _ Nothing ->              -- no hiding
                     DGLink  {
                       dgl_morphism = gEmbed (G_morphism Haskell ()),
                       dgl_type = GlobalDef,
                       dgl_origin = DGExtension }
          AHsImportDecl _ _ _ _ (Just(False,_)) ->      -- no hiding
                     DGLink  {
                       dgl_morphism = gEmbed (G_morphism Haskell ()),
                       dgl_type = GlobalDef,
                       dgl_origin = DGExtension }
          AHsImportDecl _ _ _ _ (Just(True,_)) ->       -- hiding 
                     DGLink  {
                       dgl_morphism = gEmbed (G_morphism Haskell ()),
                       dgl_type = HidingDef,
                       dgl_origin = DGExtension }
                              
-- GlobalContext:
-- GlobalAnnos können erstmal leer sein, weil es in Haskell da nichts
-- vergleichbares gibt. (Evtl. könnten später die Deklarationen von
-- Infix-Operatoren und Prioritäten da rein kommen).
-- Das GlobalEnv ordnet in CASL jeder Spezifikation einen Knoten
-- im DGraph zu. Allerdings haben wir bei Haskell pro File nur eine
-- "Spezifikation" (nämlich das Programm-Modul). Also muss das GlobalEnv
-- hier einfach nur einen Eintrag haben, der dem Namen des Programm-Moduls
-- den Knoten des Programm-Moduls im DGraph zuordnet. Das kannst du
-- erzeugen mit

-- Map.insert name (SpecEntry (imp,params,parsig,body)) Map.empty

-- wobei name der Namen des Programm-Moduls ist, und
-- imp = EmptyNode und parsig als empty_signature Haskell gewählt werden können,
-- und params = []. body = NodeSig(n,sig), wobei n der Knoten im Entwicklungsgraph
-- und sig die Signatur ist (beides jeweils die für das Programm-Modul).


addLibEnv :: LibEnv -> LIB_NAME -> Node -> DGraph -> LibEnv
addLibEnv le libName n dg =
          let 
            nodeLab = getNodeContent n dg
            imp = EmptyNode (Logic Haskell)
            params = []
            parsig = dgn_sign nodeLab -- empty_signature Haskell
            body = NodeSig (n, (dgn_sign nodeLab))
            globalEnv = Map.insert (getDgn_name nodeLab) (SpecEntry (imp,params,parsig,body)) Map.empty
          in
            Map.insert libName (emptyGlobalAnnos, globalEnv, dg) le

lookupNode :: LIB_NAME -> LibEnv -> Node
lookupNode ln le = 
           let Just (_, globalEnv, _) = Map.lookup ln le
               (_, (SpecEntry (_, _, _, body))) = Map.elemAt 0 globalEnv
           in
               case (getNode body) of
                 Just n -> n
                 Nothing -> (-1)

aHsMod2SimpleId :: AModule -> Maybe SIMPLE_ID
aHsMod2SimpleId (AModule name) = Just (Token { tokStr = name, tokPos = nullPos })

fileName :: AModule -> String
fileName (AModule name) = name ++ ".hs"

joinDG :: DGraph -> DGraph -> DGraph
joinDG _ _ = empty

getNodeContent :: Node -> DGraph -> DGNodeLab
getNodeContent n dg =
               case (match n dg) of
                 (Just (_,_,nodeLab,_), _) -> nodeLab
--               | otherwise = ??

getDgn_name :: DGNodeLab -> SIMPLE_ID
getDgn_name nl = let Just(n) = dgn_name nl
                 in  n

parseHsSource :: String -> HsModule
parseHsSource s = case parse s (SrcLoc 1 1) 0 [] of
                      Ok _ e -> e
                      Failed err -> error err

