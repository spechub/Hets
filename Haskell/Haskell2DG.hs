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

import Haskell.Hatchet.Env      (listToEnv,
                                 getNamesFromEnv,
                                 Env,
                                 envToList,
                                 pprintEnv,
                                 joinEnv,
                                 showEnv)

import Haskell.Hatchet.MultiModuleBasics (ModuleInfo(..))

import Haskell.Hatchet.TIModule

import Haskell.Hatchet.HsSyn

import Static.DevGraph

import Syntax.AS_Library

import GHC.IOBase

-- - Datentyp anlegen für HaskellEnv (Resultat von tiModule)
data HaskellEnv = HasEnv Timing              -- timing values for each stage
                         (Env Scheme)          -- output variable assumptions (may be local, and pattern variables) 
                         (Env Scheme)          -- output data cons assumptions 
                         ClassHierarchy      -- output class Hierarchy 
                         KindEnv             -- output kinds 
                         IdentTable          -- info about identifiers in the module
                         AHsModule           -- renamed module 
                         [AHsDecl]          -- synonyms defined in this module


anaHaskellFile :: HetcatsOpts -> String -> IO (Maybe (LIB_NAME, -- filename
                                                      HsModule, -- as tree
                                                      String, --DGraph, -- development graph
                                                      LibEnv -- DGraphs für importierte Module 
                                                      ))
anaHaskellFile ho s = returnIO Nothing

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


hasEnv2DG :: HaskellEnv -> String -- DGraph
hasEnv2DG he = ""

hasEnv2LG :: HaskellEnv -> LibEnv
hasEnv2LG _ = emptyLibEnv

-- utilities

-- call the haskell parser and check for errors

parseHsSource :: String -> HsModule
parseHsSource s = case parse s (SrcLoc 1 1) 0 [] of
                      Ok state e -> e
                      Failed err -> error err

-- - anaHaskellFile benötigt Funktion, die ein HaskellEnv in einen
--   DGraph konvertiert (siehe Statc/DevGaph.hs)
--   Graph-Bibliothek (functional graph library, fgl): Common/Lib/Graph
--   Knoten: sind die Haskell-Module
--     dgn_name = Modulname
--     dgn_sign = Signatur (HsDecls)
--     dgn_sens = Programmdefs
--     dgn_origin = DGBasic (bei keinen Importen)
--                = DGExtension (bei Importen)
--   Kanten: entlang der Modul-Importe (d.h. vom importierten zum Importeur)
--    dgl_morphism = ()  (siehe Logic_Haskell.hs)
--    dgl_type = GlobalDef, wenn nichts versteckt wird
--             = HidingDef, wenn etwas versteckt wird
--    dgl_origin = DGExtension
