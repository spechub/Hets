{-------------------------------------------------------------------------------

        Copyright:              The Hatchet Team (see file Contributors)

        Module:                 TIModule

        Description:            Type checking for a single module given 
                                information about imported entities.

        Primary Authors:        Bernie Pope, Bryn Humberstone

        Notes:                  See the file License for license information

-------------------------------------------------------------------------------}

module Haskell.Hatchet.TIHetsModule (tiModule) where

import Haskell.Hatchet.Infix                    (infixer)

import Haskell.Hatchet.AnnotatedHsSyn
                                (ASrcLoc (..),
                                 bogusASrcLoc,
                                 AHsDecl,
                                 AHsName (..),
                                 AModule (..),
                                 AHsModule)

import Haskell.Hatchet.SynConvert
                                (fromAHsModule,
                                 fromAHsDecl)

import qualified Haskell.Hatchet.AHsPretty as AHsPretty
                                (ppAHsModule,
                                 render,
                                 ppAHsDecl)

import qualified Haskell.Hatchet.PPrint as PPrint         (render)

import Haskell.Hatchet.Desugar  (desugarTidyModule)

import Haskell.Hatchet.TIMain   (getFunDeclsBg,
                                 makeProgram,
                                 tiProgram)

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


import Haskell.Hatchet.DataConsAssump    (dataConsEnv)

import Haskell.Hatchet.Utils    (maybeGetDeclName,
                                 rJustify,
                                 lJustify,
                                 Binding (..),
                                 getAModuleName,
                                 getDeclName,
                                 fromAHsName,
                                 doDump)

import Haskell.Hatchet.FiniteMaps (toListFM,
                                 zeroFM,
                                 addToFM)

import Haskell.Hatchet.TidyModule (tidyModule, 
                                 TidyModule (..),
                                 tidyModuleToAHsModule)


import Haskell.Hatchet.TypeSigs (collectSigs,
                                 listSigsToSigEnv)


import Haskell.Hatchet.Class    (--addInstancesToHierarchy,
                                 printClassHierarchy,
                                 -- instanceToTopDecls,
                                 addClassToHierarchy,
                                 ClassHierarchy,
                                 classMethodAssumps)

import Maybe    (mapMaybe)

import Haskell.Hatchet.Env      (listToEnv,
                                 getNamesFromEnv,
                                 Env,
                                 envToList,
                                 pprintEnv,
                                 joinEnv,
                                 showEnv)

import Haskell.Hatchet.Type     (assumpId)

import Haskell.Hatchet.MultiModuleBasics (ModuleInfo(..))

import Haskell.Hatchet.DependAnalysis (getBindGroups)

import Haskell.Hatchet.DeclsDepends (getDeclDeps,
                                 debugDeclBindGroups)

--------------------------------------------------------------------------------

-- type check a single module 

tiModule :: [String]                    -- dump flags  
         -> AHsModule                   -- syntax of module after parsing
         -> ModuleInfo                  -- info about imported entities
         -> (Env Scheme,          -- output variable assumptions (may be local, and pattern variables) 
             Env Scheme,          -- output data cons assumptions 
             ClassHierarchy,      -- output class Hierarchy 
             KindEnv,             -- output kinds 
             IdentTable,          -- info about identifiers in the module
             AHsModule,           -- renamed module 
             [AHsDecl])           -- synonyms defined in this module

tiModule dumps modSyntax imports 
   = let importVarEnv = varAssumps imports
         importDConsEnv = dconsAssumps imports
         importClassHierarchy = classHierarchy imports
         importKindEnv = kinds imports
         importSynonyms = synonyms imports
         importTyconMembers = tyconsMembers imports


-- print the name of the module being typed

         moduleName = getAModuleName modSyntax
   

-- split the module into seperate components

         tidyMod = tidyModule modSyntax

-- make all pattern bindings simple and remove type synonyms, convert do-notation into expression form

         desugaredTidyModule = desugarTidyModule importSynonyms tidyMod

-- uniquely rename variables and generate a table of information about identifiers

         -- TODO: we probably need to worry about synonyms and 
         --       the like as well but at the moment we can live
         --       with vars and datacons only.
         importedNames = getNamesFromEnv importVarEnv 
                      ++ getNamesFromEnv importDConsEnv
                      ++ getNamesFromTycons importTyconMembers
                      ++ getNamesFromEnv importClassHierarchy 
                      ++ getNamesFromEnv importKindEnv         
                     --  ++ getNamesFromInfix  -- shouldn't need this as we get
                     -- them as part of getting their types in the varEnv
         -- because we need to know to rename True to Prelude.True
         -- as well, and this is a convenient way to do it:
         getNamesFromTycons :: [(AHsName, [AHsName])] -> [AHsName]
         getNamesFromTycons = concatMap snd 

         (renamedTidyModule', identTable) = renameTidyModule importedNames desugaredTidyModule
         -- we pass in the imported infix decls and also the ones from the local module
         renamedTidyModule = Haskell.Hatchet.Infix.infixer (tidyInFixDecls renamedTidyModule' ++ infixDecls imports) renamedTidyModule'

-- All the names are getting qualified but they are unqualified by fromAHsModule

     -- separate the renamed decls apart
         rTyDecls    = tidyTyDecls    renamedTidyModule 
         rDataDecls  = tidyDataDecls  renamedTidyModule 
         rNewTyDecls = tidyNewTyDecls renamedTidyModule 
         rClassDecls = tidyClassDecls renamedTidyModule 
         rInstDecls  = tidyInstDecls  renamedTidyModule 
         rTySigs     = tidyTySigs     renamedTidyModule 
         rFunBinds   = tidyFunBinds   renamedTidyModule 
         rPatBinds   = tidyPatBinds   renamedTidyModule 


-- collect all the type signatures from the module (this must be done after renaming)

         allTypeSigs = (collectSigs (rFunBinds ++ rPatBinds)) ++ rTySigs

-- kind inference for all type constructors type variables and classes in the module

         classAndDataDecls = rDataDecls ++ rNewTyDecls ++ rClassDecls

         kindInfo = kiModule importKindEnv classAndDataDecls

-- collect types for data constructors

         localDConsEnv = dataConsEnv moduleName kindInfo (rDataDecls ++ rNewTyDecls)

         globalDConsEnv = localDConsEnv `joinEnv` importDConsEnv

-- generate the class hierarchy skeleton

         classHier =
               foldl (flip (addClassToHierarchy moduleName kindInfo)) 
	             importClassHierarchy                   
		     rClassDecls

     -- add type class instances to the class hierarchy XXX this is broken

         cHierarchyWithInstances 
            -- = addInstancesToHierarchy kindInfo classHierarchy (rinstanceDecls ++ rdataDecls)
            = classHier

{-
 -- lift the instance methods up to top-level decls

     let liftedInstances 
            = concatMap (instanceToTopDecls cHierarchyWithInstances) rinstanceDecls
     let liftedInstanceNames 
            = mapMaybe maybeGetDeclName liftedInstances 
     let identTableWithInstances
            = foldl (\fm name -> addToFM name (bogusASrcLoc, Instance) fm) identTable liftedInstanceNames


     when (doDump dumps "instances") $
        do {putStrLn " \n\n ---- lifted instance declarations ---- \n\n",
            putStr $ 
               unlines $ 
               map (renderWithMode prettySemiColonMode . AHsPretty.ppAHsDecl) liftedInstances}
-}

-- build an environment of assumptions for all the type signatures

         sigEnv = listSigsToSigEnv kindInfo allTypeSigs 

         classMethodAssumptions = classMethodAssumps cHierarchyWithInstances
     
         classMethodNames = map (\assump -> assumpId assump) classMethodAssumptions

         identTableWithMethods
            -- = foldl (\fm name -> addToFM name (bogusASrcLoc, ClassMethod) fm) identTableWithInstances classMethodNames 
            = foldl (\fm name -> addToFM name (bogusASrcLoc, ClassMethod) fm) identTable classMethodNames 

-- binding groups for top-level variables

         programBgs 
            = getBindGroups (rFunBinds ++ rPatBinds) getDeclName getDeclDeps

         program = makeProgram sigEnv programBgs

-- type inference/checking for all variables

         localVarEnv
            = tiProgram 
                 moduleName                     -- name of the module
                 sigEnv                         -- environment of type signatures
                 kindInfo                       -- kind information about classes and type constructors
                 cHierarchyWithInstances        -- class hierarchy with instances
                 globalDConsEnv                 -- data constructor type environment 
                 importVarEnv                   -- type environment
                 program                        -- binding groups

     in (localVarEnv, 
         localDConsEnv,
         cHierarchyWithInstances, 
         kindInfo, 
         identTableWithMethods, 
         tidyModuleToAHsModule renamedTidyModule,
         tidyTyDecls tidyMod) 
