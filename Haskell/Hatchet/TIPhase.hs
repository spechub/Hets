{-| 
   
Module      :  $Header$
Copyright   :  (c) Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

a couple of analysis phases taken from the original Hatchet 
TIModule and Main module

-}

{-------------------------------------------------------------------------------

        Copyright:              The Hatchet Team (see file Contributors)

        Module:                 TIModule

        Description:            Type checking for a single module given 
                                information about imported entities.

        Primary Authors:        Bernie Pope, Bryn Humberstone

        Notes:                  See the file License for license information

-------------------------------------------------------------------------------}

module Haskell.Hatchet.TIPhase where

import Haskell.Hatchet.Infix (infixer)


import Haskell.Hatchet.HsSyn (HsModule, SrcLoc(..))
import Haskell.Hatchet.AnnotatedHsSyn(
                                 bogusASrcLoc,
                                 AHsDecl,
                                 AHsName (..),
                                 AModule (..),
                                 AHsModule)

import Haskell.Hatchet.HsParsePostProcess (fixFunBindsInModule)
import Haskell.Hatchet.SynConvert (toAHsModule)
import Haskell.Hatchet.HsParseMonad (ParseResult (..))
import Haskell.Hatchet.HsParser (parse)

import Haskell.Hatchet.Desugar  (desugarTidyModule)

import Haskell.Hatchet.TIMain   (TypeEnv, Program, tiProgram)

import Haskell.Hatchet.Rename   (renameTidyModule, IdentTable)

import Haskell.Hatchet.KindInference (KindEnv, kiModule)

import Haskell.Hatchet.Representation (Scheme)

import Haskell.Hatchet.DataConsAssump (dataConsEnv)

import Haskell.Hatchet.Utils    (Binding (..), getDeclName)

import Haskell.Hatchet.FiniteMaps (addToFM)

import Haskell.Hatchet.TidyModule (TidyModule (..))

import Haskell.Hatchet.TypeSigs (SigEnv, collectSigs)

import Haskell.Hatchet.Class    (-- addInstancesToHierarchy,
                                 -- instanceToTopDecls,
                                 addClassToHierarchy,
                                 ClassHierarchy,
                                 classMethodAssumps)

import Haskell.Hatchet.Env      (listToEnv,
                                 getNamesFromEnv,
                                 Env,
                                 joinEnv)

import Haskell.Hatchet.Type     (assumpId, assumpToPair)

import Haskell.Hatchet.MultiModuleBasics (ModuleInfo(..))

import Haskell.Hatchet.DependAnalysis (getBindGroups)

import Haskell.Hatchet.DeclsDepends (getDeclDeps)

import Haskell.Hatchet.HaskellPrelude
                                (tyconsMembersHaskellPrelude, 
                                 preludeDefs, 
                                 preludeSynonyms,
                                 preludeTyconAndClassKinds,
                                 preludeClasses,
                                 preludeInfixDecls,
                                 preludeDataCons)

-- | read the source file and parse
parseFile :: String -> IO HsModule
parseFile srcFile =
  do
     src <- readFile srcFile
     return (parseHsSource src)

-- | call the haskell parser and check for errors
parseHsSource :: String -> HsModule
parseHsSource s = case parse s (SrcLoc 1 1) 0 [] of
                      Ok _ e -> e
                      Failed err -> error err

-- | prelude module
preludeModInfo :: ModuleInfo
preludeModInfo = ModuleInfo {
               moduleName = AModule "Prelude",
               varAssumps = (listToEnv $ map assumpToPair preludeDefs),
               tyconsMembers = tyconsMembersHaskellPrelude, 
               dconsAssumps = (listToEnv $ map assumpToPair preludeDataCons),
               classHierarchy = listToEnv preludeClasses,
               kinds = (listToEnv preludeTyconAndClassKinds),
               infixDecls = preludeInfixDecls,
               synonyms = preludeSynonyms
              }

-- | map the abstract syntax into the annotated abstract syntax
getAnnotedSyntax :: HsModule -> AHsModule
getAnnotedSyntax moduleSyntax = 
{- re-group matches into their associated funbinds 
   (patch up the output from the parser) -}
     let moduleSyntaxFixedFunBinds = fixFunBindsInModule moduleSyntax
     in  toAHsModule moduleSyntaxFixedFunBinds 

desugarTM :: ModuleInfo -> TidyModule -> TidyModule
desugarTM imports tidyMod = desugarTidyModule (synonyms imports) tidyMod

renameTM :: ModuleInfo -> TidyModule -> (TidyModule, IdentTable)
renameTM imports desugaredTidyModule =
         -- TODO: we probably need to worry about synonyms and 
         --       the like as well but at the moment we can live
         --       with vars and datacons only.
     let importVarEnv = varAssumps imports
         importDConsEnv = dconsAssumps imports
         importClassHierarchy = classHierarchy imports
         importKindEnv = kinds imports
         importTyconMembers = tyconsMembers imports
         importedNames = getNamesFromEnv importVarEnv 
                      ++ getNamesFromEnv importDConsEnv
                      ++ getNamesFromTycons importTyconMembers
                      ++ getNamesFromEnv importClassHierarchy 
                      ++ getNamesFromEnv importKindEnv         
         getNamesFromTycons :: [(AHsName, [AHsName])] -> [AHsName]
         getNamesFromTycons = concatMap snd 
	 (renamedTidyModule', identTable) = 
	     renameTidyModule importedNames desugaredTidyModule
	     -- we pass in the imported infix decls 
	     -- and also the ones from the local module
         renamedTidyModule = infixer (tidyInFixDecls renamedTidyModule' 
				      ++ infixDecls imports) renamedTidyModule'
	 in (renamedTidyModule, identTable)

-- | collect all the type signatures from the module 
-- (this must be done after renaming)
getAllTypeSigs :: TidyModule -> [AHsDecl]
getAllTypeSigs renamedTidyModule = 
     let rTySigs     = tidyTySigs     renamedTidyModule 
         rFunBinds   = tidyFunBinds   renamedTidyModule 
         rPatBinds   = tidyPatBinds   renamedTidyModule 
	 in collectSigs (rFunBinds ++ rPatBinds) ++ rTySigs


-- | kind inference for all type constructors type variables and classes
getKindInfo :: TidyModule -> ModuleInfo -> KindEnv
getKindInfo renamedTidyModule imports = 
     let rDataDecls  = tidyDataDecls  renamedTidyModule 
         rNewTyDecls = tidyNewTyDecls renamedTidyModule 
         rClassDecls = tidyClassDecls renamedTidyModule 
	 classAndDataDecls = rDataDecls ++ rNewTyDecls ++ rClassDecls
     in kiModule (kinds imports) classAndDataDecls

-- | collect types for data constructors
getLocalDConsEnv :: TidyModule -> KindEnv -> TypeEnv
getLocalDConsEnv = getLocalDConsEnv2 True
 
-- | True gets constructors, False selectors
getLocalDConsEnv2 :: Bool -> TidyModule -> KindEnv -> TypeEnv
getLocalDConsEnv2 b renamedTidyModule kindInfo = 
     let rNewTyDecls = tidyNewTyDecls renamedTidyModule 
         rDataDecls  = tidyDataDecls  renamedTidyModule 
     in dataConsEnv b kindInfo (rDataDecls ++ rNewTyDecls)

getGlobalDConsEnv :: Env Scheme -> ModuleInfo -> TypeEnv
getGlobalDConsEnv localDConsEnv imports = 
    localDConsEnv `joinEnv` dconsAssumps imports

getClassHierarchy :: TidyModule -> ModuleInfo -> KindEnv -> ClassHierarchy
getClassHierarchy renamedTidyModule imports kindInfo = 
     let mname  = tidyModName    renamedTidyModule
         importClassHierarchy = classHierarchy imports
         rClassDecls = tidyClassDecls renamedTidyModule 
         resultClassHierarchy = foldl (flip (addClassToHierarchy mname 
				       kindInfo)) importClassHierarchy
			  rClassDecls 
{- add type class instances to the class hierarchy XXX this is broken 
    addInstancesToHierarchy kindInfo classHierarchy 
    (rinstanceDecls ++ rdataDecls) -}
     in resultClassHierarchy 

{-
 -- lift the instance methods up to top-level decls

     let liftedInstances 
            = concatMap (instanceToTopDecls cHierarchyWithInstances) 
                           rinstanceDecls
     let liftedInstanceNames 
            = mapMaybe maybeGetDeclName liftedInstances 
     let identTableWithInstances
            = foldl (\fm name -> addToFM name (bogusASrcLoc, Instance) fm) 
                         identTable liftedInstanceNames


     when (doDump dumps "instances") $
        do {putStrLn " \n\n ---- lifted instance declarations ---- \n\n",
            putStr $ 
               unlines $ 
               map (renderWithMode prettySemiColonMode . AHsPretty.ppAHsDecl) 
	             liftedInstances}
-}

getIdentTableWithMethods :: IdentTable -> ClassHierarchy -> IdentTable
getIdentTableWithMethods identTable cHierarchyWithInstances =
     let classMethodAssumptions = classMethodAssumps cHierarchyWithInstances
         classMethodNames = map (\assump -> assumpId assump) 
			    classMethodAssumptions
     in foldl (\fm name -> addToFM name (bogusASrcLoc, ClassMethod) fm) 
	       identTable classMethodNames

-- | binding groups for top-level variables
getProgramBgs :: TidyModule -> [[AHsDecl]]
getProgramBgs renamedTidyModule = 
     let rFunBinds   = tidyFunBinds   renamedTidyModule 
         rPatBinds   = tidyPatBinds   renamedTidyModule 
     in  getBindGroups (rFunBinds ++ rPatBinds) getDeclName getDeclDeps

-- sigEnv = listSigsToSigEnv kindInfo allTypeSigs 
-- program = makeProgram sigEnv programBgs

-- | type inference checking for all variables
getLocalVarEnv :: TidyModule -> ModuleInfo -> SigEnv -> KindEnv 
	       -> ClassHierarchy -> TypeEnv -> Program -> TypeEnv
getLocalVarEnv renamedTidyModule imports sigEnv kindInfo
	       cHierarchyWithInstances globalDConsEnv program =
    let sels = getLocalDConsEnv2 False renamedTidyModule kindInfo
        importVarEnv = varAssumps imports
        mname  = tidyModName renamedTidyModule
     in tiProgram 
                 mname                
		 -- name of the module
                 sigEnv                    
		 -- environment of type signatures
                 kindInfo  
		 -- kind information about classes and type constructors
                 cHierarchyWithInstances        
		 -- class hierarchy with instances
                 globalDConsEnv                 
		 -- data constructor type environment 
                 (joinEnv sels importVarEnv)                   
		 -- type environment
                 program                        
		 -- binding groups
