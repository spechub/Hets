module Haskell.Haskell2DG where

import Options

import Haskell.Hatchet.MultiModuleBasics

import Haskell.Hatchet.MultiModule              (writeModuleInfo, readModuleInfo, toString)

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

import Haskell.Hatchet.AnnotatedHsSyn
                                (AHsDecl,
                                 AHsName (..),
                                 AModule (..),
                                 AHsModule)
 
import Haskell.Hatchet.Rename   (renameTidyModule,
                                 IdentTable,
                                 printIdentTable)

import Haskell.Hatchet.KindInference
                                (KindEnv,
                                 kiModule)

import Haskell.Hatchet.Representation
                                (Kind,
                                 Scheme,
                                 Assump (..))

import Haskell.Hatchet.TidyModule (tidyModule, 
                                 TidyModule (..),
                                 tidyModuleToAHsModule)

import Haskell.Hatchet.Class    (ClassHierarchy)

import Haskell.Hatchet.Env      (Env,
                                 listToEnv)

import Haskell.Hatchet.MultiModuleBasics (ModuleInfo(..))

import Haskell.Hatchet.TIModule

import Haskell.Hatchet.HsSyn

import Static.DevGraph

import Syntax.AS_Library

import Haskell.Hatchet.AnnotatedHsSyn

import Logic.Grothendieck

import Common.Lib.Graph

import Common.Id

-- import Haskell.Logic_Haskell

data Haskell = Haskell deriving (Show)

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
anaHaskellFile opts srcFile = 
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
     return (Just(Lib_id(Indirect_link srcFile []), moduleSyntax, hasEnv2DG hasEnv, hasEnv2LG hasEnv))

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
                   mod = AHsModule name exps imps decls
               in
                   hsMod2DG mod modInfo

hsMod2DG :: AHsModule -> ModuleInfo -> DGraph
hsMod2DG (AHsModule name _ imps decls) modInfo = 
       let node_contents  | imps == [] =
                             DGNode {
                               dgn_name = aHsMod2SimpleId name,
                               dgn_sign = G_sign Haskell modInfo,
                               dgn_sens = G_l_sentence Haskell [],
                               dgn_origin = DGBasic }
                          | otherwise =
                             DGNode {
                               dgn_name = aHsMod2SimpleId name,
                               dgn_sign = G_sign Haskell modInfo,
                               dgn_sens = G_l_sentence Haskell [],
                               dgn_origin = DGExtension }
           dg = buildGr []
           [node] = newNodes 0 dg
           dg' = insNode (node,node_contents) dg
           link = createDGLink imps
           dg'' = insEdge (node,node,link) dg'
        in
           buildGr []

createDGLink :: [AHsImportDecl] -> DGLinkLab
createDGLink _ = DGLink  {
                  dgl_morphism = (),
                  dgl_type = GlobalDef,
                  dgl_origin = DGExtension }

aHsMod2SimpleId :: AModule -> Maybe SIMPLE_ID
aHsMod2SimpleId (AModule name) = Just (Token { tokStr = name, tokPos = nullPos })
                              

-- newtype AModule = AModule String
--   deriving (Eq,Ord,Show)

-- data AHsModule = AHsModule AModule (Maybe [AHsExportSpec])
--                          [AHsImportDecl] [AHsDecl]
--   deriving Show

-- data AHsImportDecl
-- 	 = AHsImportDecl ASrcLoc AModule Bool (Maybe AModule)
-- 	                (Maybe (Bool,[AHsImportSpec]))
--   deriving (Eq,Show)

hasEnv2LG :: HaskellEnv -> LibEnv
hasEnv2LG _ = emptyLibEnv

-- utilities

-- call the haskell parser and check for errors

parseHsSource :: String -> HsModule
parseHsSource s = case parse s (SrcLoc 1 1) 0 [] of
                      Ok state e -> e
                      Failed err -> error err

