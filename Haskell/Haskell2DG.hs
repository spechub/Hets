module Haskell.Haskell2DG where

import Options
import Haskell.Hatchet.MultiModuleBasics
import Haskell.Hatchet.MultiModule              (readModuleInfo, readOneImportSpec)
import Haskell.Hatchet.HsParseMonad             (ParseResult (..))
import Haskell.Hatchet.SynConvert               (toAHsModule)
import Haskell.Hatchet.HsParsePostProcess       (fixFunBindsInModule)
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
import Haskell.Hatchet.MultiModuleBasics (ModuleInfo(..))
import Haskell.Hatchet.TIModule
import Haskell.Hatchet.HsSyn
import Static.DevGraph
import Syntax.AS_Library
import Haskell.Hatchet.AnnotatedHsSyn
import Logic.Grothendieck
import Common.Lib.Graph
import Common.Id
import Haskell.Logic_Haskell
import Haskell.HaskellUtils
import GHC.IOBase

-- - Datentyp anlegen für HaskellEnv (Resultat von tiModule)
data HaskellEnv = HasEnv Timing              -- timing values for each stage
                         (Env Scheme)        -- output variable assumptions (may be local, and pattern variables) 
                         (Env Scheme)        -- output data cons assumptions 
                         ClassHierarchy      -- output class Hierarchy 
                         KindEnv             -- output kinds 
                         IdentTable          -- info about identifiers in the module
                         AHsModule           -- renamed module 
                         [AHsDecl]           -- synonyms defined in this module


anaHaskellFile :: HetcatsOpts -> String -> IO (Maybe (LIB_NAME, -- filename
                                                      HsModule, -- as tree
                                                      DGraph,   -- development graph
                                                      LibEnv    -- DGraphs für importierte Module 
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
     --in 
     return (Just(Lib_id(Indirect_link srcFile []), moduleSyntax, hasEnv2DG hasEnv, 
             hasEnv2LG hasEnv))

hasEnv2DG :: HaskellEnv -> DGraph
hasEnv2DG (HasEnv 
             _
             moduleEnv
             dataConEnv
             classHier
             kindInfoTable
             moduleIds
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
                   hsMod2DG aMod modInfo

-- main Module and main ModuleInfo
hsMod2DG :: AHsModule -> ModuleInfo -> DGraph
hsMod2DG (AHsModule name exps imps decls) modInfo = 
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
           dg' = insNode (node,node_contents) dg
        in
           case imps of
             [] -> dg                       -- no imports, no other nodes and edges
             _  -> insImports dg node imps  -- imports -> add imported Modules

-- DGraph consisting in one node (the main Module), this node and ModuleInfo 
-- about imported Modules
insImports :: DGraph ->  Node -> [AHsImportDecl] -> DGraph
insImports dg _ [] = dg
insImports dg n ((AHsImportDecl src name b mbm mayBeHiding):idecls) = 
        let idecl = AHsImportDecl src name b mbm mayBeHiding
            node_contents = DGNode {
                               dgn_name = aHsMod2SimpleId name,
                               dgn_sign = G_sign Haskell (unsafePerformIO 
                                                          (readOneImportSpec idecl)),
                               dgn_sens = G_l_sentence Haskell [],
                               dgn_origin = DGBasic }
            [node] = newNodes 0 dg
            dg' = insNode(node,node_contents) dg
            link = createDGLinkLabel idecl
            dg'' = insEdge (node,n,link) dg'
        in
           insImports dg'' n idecls

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

aHsMod2SimpleId :: AModule -> Maybe SIMPLE_ID
aHsMod2SimpleId (AModule name) = Just (Token { tokStr = name, tokPos = nullPos })
                              
hasEnv2LG :: HaskellEnv -> LibEnv
hasEnv2LG _ = emptyLibEnv

-- utilities

-- call the haskell parser and check for errors

parseHsSource :: String -> HsModule
parseHsSource s = case parse s (SrcLoc 1 1) 0 [] of
                      Ok _ e -> e
                      Failed err -> error err

