{- HetCATS/Haskell/Haskell2DG.hs
   Authors: S. Groening
   Year:    2003
-}

module Haskell.Haskell2DG (anaHaskellFile) where

import Options
import Haskell.Hatchet.MultiModule  (readModuleInfo,
                                     writeModuleInfo)
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
import Haskell.Hatchet.AnnotatedHsSyn (AHsDecl, 
                                       AModule (..), 
                                       AHsModule)
import Haskell.Hatchet.Rename   (IdentTable)
import Haskell.Hatchet.KindInference (KindEnv)
import Haskell.Hatchet.Representation (Scheme)
import Haskell.Hatchet.Class    (ClassHierarchy)
import Haskell.Hatchet.Env      (Env, listToEnv)
import Haskell.Hatchet.MultiModuleBasics (ModuleInfo (..),
                                          joinModuleInfo,
                                          getTyconsMembers,
                                          getInfixDecls)
import Haskell.Hatchet.TIModule (tiModule, Timing)
import Haskell.Hatchet.HsSyn    (SrcLoc (..), HsModule (..))
import Haskell.Hatchet.Utils    (getAModuleName)
    
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


data HaskellEnv = 
     HasEnv Timing       -- timing values for each stage
            (Env Scheme) -- output variable assumptions (may
                         -- be local, and pattern variables) 
            (Env Scheme) -- output data cons assumptions 
            ClassHierarchy -- output class Hierarchy 
            KindEnv      -- output kinds 
            IdentTable   -- info about identifiers in 
                         -- the module
            AHsModule    -- renamed module 
            [AHsDecl]    -- synonyms defined in this module

-- toplevel function: Creates DevGraph and 
--   LibEnv from a .hs file
--   (including all imported modules)
anaHaskellFile :: HetcatsOpts 
                   -> String
                   -> IO (Maybe (LIB_NAME, -- filename
                                 HsModule, -- as tree
                                 DGraph,   -- development graph
                                 LibEnv))  -- DGraphs for 
                                            -- imported modules 
                                            --  incl. main module
anaHaskellFile _ srcFile = anaHaskellFileAux srcFile empty

anaHaskellFileAux :: String -> DGraph -> 
                       IO (Maybe (LIB_NAME, HsModule, 
                                  DGraph, LibEnv))
anaHaskellFileAux srcFile dg =
   do
    -- read and parse source
     src <- readFile srcFile
     let moduleSyntax = parseHsSource src

    -- re-group matches into their associated 
    -- funbinds (patch up the output from the parser)
     let moduleSyntaxFixedFunBinds = fixFunBindsInModule moduleSyntax

    -- map the abstract syntax into the annotated abstract syntax
     let annotatedSyntax = toAHsModule moduleSyntaxFixedFunBinds

    -- this is the ModuleInfo that we were passing into tiModule
    -- earlier (just the Prelude stuff)
     let preludeModInfo =
           ModuleInfo {
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

     let modInfo = ModuleInfo { varAssumps = moduleEnv, 
                                moduleName = getAModuleName annotatedSyntax,
                                dconsAssumps = dataConEnv, 
                                classHierarchy = newClassHierarchy,
                                kinds = newKindInfoTable,
                                tyconsMembers = getTyconsMembers moduleRenamed,
                                infixDecls = getInfixDecls moduleRenamed,
                                synonyms = moduleSynonyms }

     let hasEnv = HasEnv timings 
                         moduleEnv
                         dataConEnv
                         newClassHierarchy
                         newKindInfoTable
                         moduleIds
                         moduleRenamed
                         moduleSynonyms

    -- write .ti file
     writeModuleInfo (hsToTI srcFile) annotatedSyntax modInfo 

     let libName = Lib_id(Indirect_link srcFile [])

    -- convert HaskellEnv to DGraph, build up corresponding LibEnv
     (dg',le) <- hasEnv2DG dg libName hasEnv
     return (Just(libName, moduleSyntax, dg', le))
     where hsToTI s = Just ((takeWhile noDot s) ++ ".ti")
           noDot '.' = False
           noDot _ = True

hasEnv2DG :: DGraph -> LIB_NAME -> HaskellEnv -> IO (DGraph, LibEnv)
hasEnv2DG dg ln (HasEnv _ moduleEnv dataConEnv classHier kindInfoTable _
                       (AHsModule name exps imps decls) moduleSynonyms) =
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
                   createDGraph dg ln aMod modInfo
                   

-- input: (so far generated) DGraph, 
--        a module's abstract syntax and its ModuleInfo
-- task: adds a new node (representing the module)
--       to the DGraph checks whether there are 
--       imported modules or not
createDGraph :: DGraph -> LIB_NAME -> AHsModule 
                       -> ModuleInfo -> IO(DGraph, LibEnv)
createDGraph dg ln (AHsModule name exps imps decls) modInfo = 
      -- create a node, representing the module
       let node_contents 
             | imps == [] =   -- module with no imports
                DGNode {
                  dgn_name = aHsMod2SimpleId name,
                  dgn_sign = G_sign Haskell modInfo,
                  dgn_sens = G_l_sentence Haskell 
                              (extractSentences (AHsModule name 
                                              exps imps decls)),
                  dgn_origin = DGBasic }
             | otherwise =    -- module with imports
                DGNode {
                  dgn_name = aHsMod2SimpleId name,
                  dgn_sign = G_sign Haskell modInfo,
                  dgn_sens = G_l_sentence Haskell
                              (extractSentences (AHsModule name
                                              exps imps decls)),
                  dgn_origin = DGExtension }
           [node] = newNodes 0 dg
          -- add node to DGraph
           dg' = insNode(node, node_contents) dg
        in
           case imps of
            -- no imports -> no other nodes and edges
             [] -> return (dg', 
                    (addDG2LibEnv emptyLibEnv ln node dg'))
            -- imports -> add imported Modules
             _  -> insImports ln dg' node emptyLibEnv imps

-- input: LibName of (current treated) 'main module', 
--        (so far generated) DGraph, 
--        node representing the 'main module', 
--        (so far generated) LibEnv, 
--        List of importDecls (from 'main module')
-- task: call anaHaskellFileAux for each imported module
--       and add a link between 'the' node and the node
--       representing an imported module
insImports :: LIB_NAME -> DGraph 
                       -> Node 
                       -> LibEnv 
                       -> [AHsImportDecl] 
                       -> IO (DGraph,LibEnv)
insImports ln dg n le [] 
    = return (dg, (addDG2LibEnv le ln n dg))
insImports ln dg n le 
    ((AHsImportDecl src name b mbm mayBeHiding):idecls) = 
      do 
        let lnTest = Lib_id(Indirect_link (fileName name) [])
        case (Map.member lnTest le) of
         -- analyse imported module just like the main module
          False -> do Just(libName, _, dg', libEnv) 
                        <- anaHaskellFileAux (fileName name) dg
                      let idecl = AHsImportDecl src name
                                            b mbm mayBeHiding
          
                          -- unite the old 'big' LibEnv 
                          -- le with the one for the
                          -- imported module
                      let le' = le `Map.union` libEnv
          
                          -- lookup node for imported module
                      let node = lookupNode libName libEnv

                          -- create LinkLabel
                      let link = createDGLinkLabel idecl

                          -- insert new edge with LinkLabel
                      let linkedDG = insEdge (node,n,link)
                                                  dg'

                      insImports ln linkedDG n le' idecls
          True   ->  insImports ln dg n le idecls


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
                        
addDG2LibEnv :: LibEnv -> LIB_NAME -> Node -> DGraph -> LibEnv
addDG2LibEnv le libName n dg =
          let 
            nodeLab = getNodeContent n dg
            imp = EmptyNode (Logic Haskell)
            params = []
            parsig = dgn_sign nodeLab -- empty_signature Haskell
            body = NodeSig (n, (dgn_sign nodeLab))
            globalEnv = Map.insert (getDgn_name nodeLab) 
                                   (SpecEntry (imp,params,parsig,body)) 
                                   Map.empty
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
aHsMod2SimpleId (AModule name) = Just (Token { tokStr = name, 
                                               tokPos = nullPos })

fileName :: AModule -> String
fileName (AModule name) = name ++ ".hs"

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

