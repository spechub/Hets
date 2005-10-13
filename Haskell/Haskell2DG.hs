{-| 
Module      :  $Header$
Copyright   :  (c) Sonja Groening, Christian Maeder, Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

-} 

module Haskell.Haskell2DG (anaHaskellFile) where

import Driver.Options
    
import Static.DevGraph          (DGNodeLab (..),
                                 DGLinkLab (..),
                                 DGLinkType (..),
                                 DGOrigin (..),
                                 DGraph,
                                 LibEnv,
                                 GlobalEntry(..),
                                 NodeSig(..),
                                 getNode)
import Syntax.AS_Library        (LIB_NAME (..),
                                 LIB_ID (..))
import Logic.Grothendieck        (G_sign (..),
                                  G_l_sentence_list (..),
                                  G_morphism (..),
                                  gEmbed)
import Logic.Logic               
import Data.Graph.Inductive.Graph(Node,
                                  empty,
                                  insNode,
                                  insEdge,
                                  newNodes,
                                  match)

import Common.Id                 (Token (..),
                                  SIMPLE_ID,
                                  nullPos)

import qualified Common.Lib.Map as Map
import Common.GlobalAnnotations  (emptyGlobalAnnos)

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
anaHaskellFile _ srcFile = anaHaskellFileAux srcFile

anaHaskellFileAux :: String -> -- DGraph -> 
                       IO (Maybe (LIB_NAME, HsModule, 
                                  DGraph, LibEnv))
anaHaskellFileAux srcFile =
  do 
     moduleSyntax <- fmap cvrtHsModule $ parseFile srcFile
     (absSyn, modInfo, le) <- typeInference moduleSyntax
     let libName = Lib_id(Indirect_link srcFile [])
    -- convert HaskellEnv to DGraph, build up corresponding LibEnv
     let (dg',le') = hasEnv2DG libName absSyn modInfo le
     return (Just(libName, moduleSyntax, dg', le'))

typeInference :: HsModule 
              -> IO (AHsModule, ModuleInfo, LibEnv)
typeInference moduleSyntax =
   do
     let annotatedSyntax = getAnnotedSyntax moduleSyntax

     (modInfos, le) <- anaImportDecls annotatedSyntax

     -- concat all modInfos
     let importedModInfo = concatModuleInfos modInfos

    -- this is the ModuleInfo that we were passing into tiModule
    -- earlier (just the Prelude stuff)

     let initialModInfo = joinModuleInfo preludeModInfo importedModInfo

    -- call the type inference code for this module 
         (moduleEnv, 
          dataConEnv,
          newClassHierarchy, 
          newKindInfoTable,
          moduleRenamed,
          moduleSynonyms) = tiModule annotatedSyntax initialModInfo

     let modInfo = ModuleInfo { varAssumps = moduleEnv, 
                                moduleName = getAModuleName annotatedSyntax,
                                dconsAssumps = dataConEnv, 
                                classHierarchy = newClassHierarchy,
                                kinds = newKindInfoTable,
                                tyconsMembers = getTyconsMembers moduleRenamed,
                                infixDecls = getInfixDecls moduleRenamed,
                                synonyms = moduleSynonyms }

     return (moduleRenamed, modInfo, le)

anaImportDecls :: AHsModule -> IO ([ModuleInfo], LibEnv)
anaImportDecls (AHsModule _ _ idecls _) = anaImports idecls [] Map.empty

anaImports :: [AHsImportDecl] -> [ModuleInfo] -> LibEnv 
                              -> IO ([ModuleInfo], LibEnv)
anaImports [] modInfos le = do return (modInfos, le)
anaImports (imp:imps) modInfos le = 
  do
    (newModInfo, le') <- anaOneImport imp le
    anaImports imps (newModInfo:modInfos) le'

anaOneImport :: AHsImportDecl -> LibEnv 
                              -> IO (ModuleInfo, LibEnv)
anaOneImport (AHsImportDecl _ aMod _ _ maybeListOfIdents) le = do
         let ln = toLibName aMod
         modSyn <- parseFile (fileName aMod)
         (annoSyn, modInfo, leImports) <- typeInference modSyn
         let le' = le `Map.union` leImports
             filteredModInfo = filtModInfo aMod modInfo maybeListOfIdents
             (dg,node) = addNode empty annoSyn filteredModInfo
         case annoSyn of
              AHsModule _ _ idecls  _ -> case idecls of
                 [] -> return (filteredModInfo,addDG2LibEnv le' ln node dg)
                 _ -> return (filteredModInfo, addDG2LibEnv le' ln node 
                             $ addLinks idecls dg node le')

 where filtModInfo _ modInfo Nothing = modInfo
                              -- we're not imposing restrictions
       filtModInfo aModule modInfo (Just (_, importSpecs)) =
              filterModuleInfo aModule modInfo $
               expandDotsInTyCons aModule (tyconsMembers modInfo) $
                map importSpecToExportSpec importSpecs

toLibName :: AModule -> LIB_NAME
toLibName aMod = Lib_id(Indirect_link (fileName aMod) [])

addLinks :: [AHsImportDecl] -> DGraph -> Node -> LibEnv 
                            -> DGraph
addLinks [] dg _ _ = dg
addLinks (idecl:idecls) dg mainNode le = 
         let ln = toLibName (getModName idecl)
             node = lookupNode ln le
             (dgWithRef, ref) = addDGRef ln dg node
             link = createDGLinkLabel idecl
                          -- insert new edge with LinkLabel
             linkedDG = insEdge (ref,mainNode,link) dgWithRef
         in addLinks idecls linkedDG mainNode le
         where getModName (AHsImportDecl _ name _ _ _) = name
               

hasEnv2DG :: LIB_NAME -> AHsModule -> ModuleInfo 
                      -> LibEnv -> (DGraph, LibEnv)
hasEnv2DG ln aMod modInfo le =
     let (dg, node) = addNode empty aMod modInfo
         dg' = addLinks (getImps aMod) dg node le
     in (dg', (addDG2LibEnv le ln node dg'))
     where getImps (AHsModule _ _ imps _) = imps

-- input: (so far generated) DGraph, 
--        a module's abstract syntax and its ModuleInfo
-- task: adds a new node (representing the module)
--       to the DGraph 
addNode :: DGraph -> AHsModule -> ModuleInfo
                  -> (DGraph, Node)
addNode dg (AHsModule name exps imps decls) modInfo = 
      -- create a node, representing the module
       let node_contents 
             | imps == [] =   -- module with no imports
                DGNode {
                  dgn_name = aHsMod2SimpleId name,
                  dgn_sign = G_sign Haskell modInfo,
                  dgn_sens = G_l_sentence_list Haskell 
                              (extractSentences (AHsModule name 
                                              exps imps decls)),
                  dgn_origin = DGBasic }
             | otherwise =    -- module with imports
                DGNode {
                  dgn_name = aHsMod2SimpleId name,
                  dgn_sign = G_sign Haskell modInfo,
                  dgn_sens = G_l_sentence_list Haskell
                              (extractSentences (AHsModule name
                                              exps imps decls)),
                  dgn_origin = DGExtension }
           [node] = newNodes 0 dg
          -- add node to DGraph
       in (insNode (node, node_contents) dg, node)

addDGRef :: LIB_NAME -> DGraph -> Node -> (DGraph, Node)
addDGRef ln dg node =
       let node_contents = 
            DGRef {
             dgn_name = ln2SimpleId ln,
             dgn_libname = ln,
             dgn_node = node }
           [newNode] = newNodes 0 dg
       in (insNode (newNode, node_contents) dg, newNode)

ln2SimpleId :: LIB_NAME -> Maybe (SIMPLE_ID)
ln2SimpleId (Lib_id (Indirect_link modName _)) =
               Just (Token { tokStr = modName, 
                             tokPos = nullPos })
ln2SimpleId (Lib_id (Direct_link modName _)) =
               Just (Token { tokStr = modName, 
                             tokPos = nullPos })
ln2SimpleId (Lib_version link _) = ln2SimpleId (Lib_id link)


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
            Just(nodeLab) = getNodeContent n dg
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

getNodeContent :: Node -> DGraph -> Maybe (DGNodeLab)
getNodeContent n dg =
               case (match n dg) of
                 (Just (_,_,nodeLab,_), _) -> Just (nodeLab)
                 _                         -> Nothing

getDgn_name :: DGNodeLab -> SIMPLE_ID
getDgn_name nl = let Just(n) = dgn_name nl
                 in  n



