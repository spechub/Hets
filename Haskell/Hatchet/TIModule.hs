{-------------------------------------------------------------------------------

        Copyright:              The Hatchet Team (see file Contributors)

        Module:                 TIModule

        Description:            Type checking for a single module given 
                                information about imported entities.

        Primary Authors:        Bernie Pope, Bryn Humberstone

        Notes:                  See the file License for license information

-------------------------------------------------------------------------------}

module TIModule (tiModule, Timing (..)) where

import Infix                    (infixer)

import Monad                    (when)

import AnnotatedHsSyn           (ASrcLoc (..),
                                 bogusASrcLoc,
                                 AHsDecl,
                                 AHsName (..),
                                 AModule (..),
                                 AHsModule)

import SynConvert               (fromAHsModule,
                                 fromAHsDecl)

import qualified AHsPretty      (ppAHsModule,
                                 render,
                                 ppAHsDecl)

import qualified PPrint         (render)

import Desugar                  (desugarTidyModule)

import TIMain                   (getFunDeclsBg,
                                 makeProgram,
                                 tiProgram)

import Rename                   (renameTidyModule,
                                 IdentTable,
                                 printIdentTable)

import KindInference            (KindEnv,
                                 kiModule)

import Representation           (Kind,
                                 Scheme,
                                 Assump (..))


import DataConsAssump           (dataConsEnv)

import CPUTime                  (getCPUTime,
                                 cpuTimePrecision)

import Utils                    (maybeGetDeclName,
                                 rJustify,
                                 lJustify,
                                 Binding (..),
                                 getAModuleName,
                                 getDeclName,
                                 fromAHsName,
                                 doDump)

import FiniteMaps               (toListFM,
                                 zeroFM,
                                 addToFM)

import TidyModule               (tidyModule, 
                                 TidyModule (..),
                                 tidyModuleToAHsModule)


import TypeSigs                 (collectSigs,
                                 listSigsToSigEnv)


import Class                  (--addInstancesToHierarchy,
                                 printClassHierarchy,
                                 -- instanceToTopDecls,
                                 addClassToHierarchy,
                                 ClassHierarchy,
                                 classMethodAssumps)

import Maybe                    (mapMaybe)

import IO

import Env                      (listToEnv,
                                 getNamesFromEnv,
                                 Env,
                                 envToList,
                                 pprintEnv,
                                 joinEnv,
                                 showEnv)

import Type                     (assumpId)

import MultiModuleBasics        (ModuleInfo(..))

import DependAnalysis           (getBindGroups)

import DeclsDepends             (getDeclDeps,
                                 debugDeclBindGroups)

--------------------------------------------------------------------------------

-- collection of Timing information

data Timing = Timing { desugarTime   :: Integer,
                       renameTime     :: Integer,
                       classTime      :: Integer,
                       kindsTime      :: Integer,
                       dconstypesTime :: Integer,
                       typeInferTime  :: Integer,
                       total          :: Integer }

-- type check a single module 

tiModule :: [String]                    -- dump flags  
         -> AHsModule                   -- syntax of module after parsing
         -> ModuleInfo                  -- info about imported entities
         -> IO (Timing,              -- timing values for each stage
                Env Scheme,          -- output variable assumptions (may be local, and pattern variables) 
                Env Scheme,          -- output data cons assumptions 
                ClassHierarchy,      -- output class Hierarchy 
                KindEnv,             -- output kinds 
                IdentTable,          -- info about identifiers in the module
                AHsModule,           -- renamed module 
                [AHsDecl])           -- synonyms defined in this module

tiModule dumps modSyntax imports 
   = do 
  
-- set all times to zero intially 

     initialTime <- getCPUTime

     let timingInfo = Timing { desugarTime   = 0,
                               renameTime     = 0,
                               classTime      = 0,
                               kindsTime      = 0,
                               dconstypesTime = 0,
                               typeInferTime  = 0,
                               total          = 0 }

     let importVarEnv = varAssumps imports
         importDConsEnv = dconsAssumps imports
         importClassHierarchy = classHierarchy imports
         importKindEnv = kinds imports
         importSynonyms = synonyms imports
         importTyconMembers = tyconsMembers imports


-- print the name of the module being typed

     let moduleName = getAModuleName modSyntax
     putStr $ "\n\n ---- Type checking " ++ show moduleName ++ " ----\n\n"
   
-- print the syntax tree: depending on command line arguments

     when (doDump dumps "syntax" ) $
        do {putStr "\n\n ---- Initial Syntax Tree ---- \n\n";
            putStr $ show modSyntax}

-- split the module into seperate components

     let tidyMod = tidyModule modSyntax

-- make all pattern bindings simple and remove type synonyms, convert do-notation into expression form

     beforeTime <- getCPUTime

     let desugaredTidyModule = desugarTidyModule importSynonyms tidyMod

     when (doDump dumps "desugar") $
          do {putStrLn "\n\n ---- desugared code ---- \n\n";
              putStrLn $ AHsPretty.render 
                       $ AHsPretty.ppAHsModule 
                       $ tidyModuleToAHsModule desugaredTidyModule}

     afterTime <- getCPUTime

     let desugarT = afterTime - beforeTime

-- uniquely rename variables and generate a table of information about identifiers

     beforeTime <- getCPUTime
     

         -- TODO: we probably need to worry about synonyms and 
         --       the like as well but at the moment we can live
         --       with vars and datacons only.
     let importedNames = getNamesFromEnv importVarEnv 
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

     let (renamedTidyModule', identTable) = renameTidyModule importedNames desugaredTidyModule
         -- we pass in the imported infix decls and also the ones from the local module
         renamedTidyModule = Infix.infixer (tidyInFixDecls renamedTidyModule' ++ infixDecls imports) renamedTidyModule'

-- All the names are getting qualified but they are unqualified by fromAHsModule

     when (doDump dumps "renamed") $
          do {putStrLn " \n\n ---- renamed code ---- \n\n";
              putStrLn $ AHsPretty.render 
                       $ AHsPretty.ppAHsModule 
                       $ tidyModuleToAHsModule renamedTidyModule}

     when (doDump dumps "idents") $
          do {putStrLn " \n\n ---- identifiers ---- \n\n";
              printIdentTable identTable}

     afterTime <- getCPUTime

     let renameT = afterTime - beforeTime

     -- separate the renamed decls apart
     let rTyDecls    = tidyTyDecls    renamedTidyModule 
         rDataDecls  = tidyDataDecls  renamedTidyModule 
         rNewTyDecls = tidyNewTyDecls renamedTidyModule 
         rClassDecls = tidyClassDecls renamedTidyModule 
         rInstDecls  = tidyInstDecls  renamedTidyModule 
         rTySigs     = tidyTySigs     renamedTidyModule 
         rFunBinds   = tidyFunBinds   renamedTidyModule 
         rPatBinds   = tidyPatBinds   renamedTidyModule 


-- collect all the type signatures from the module (this must be done after renaming)

     let allTypeSigs = (collectSigs (rFunBinds ++ rPatBinds)) ++ rTySigs

     when (doDump dumps "srcsigs") $
          do {putStrLn " \n\n ---- type signatures from source code (after renaming) ---- \n\n";
              putStr $ unlines $ map (AHsPretty.render . AHsPretty.ppAHsDecl) allTypeSigs}

-- kind inference for all type constructors type variables and classes in the module

     let classAndDataDecls = rDataDecls ++ rNewTyDecls ++ rClassDecls

     beforeTime <- getCPUTime

     let kindInfo = kiModule importKindEnv classAndDataDecls

     when (doDump dumps "kinds") $
          do {putStrLn " \n\n ---- kind information ---- \n\n";
              putStr $ PPrint.render $ pprintEnv kindInfo}


     afterTime <- getCPUTime
     let kindsT = afterTime - beforeTime

-- collect types for data constructors

     beforeTime <- getCPUTime

     let localDConsEnv = dataConsEnv moduleName kindInfo (rDataDecls ++ rNewTyDecls)

     when (doDump dumps "dconstypes") $
          do {putStr "\n\n ---- data constructor assumptions ---- \n\n";
              putStrLn $ PPrint.render $ pprintEnv localDConsEnv}

     afterTime <- getCPUTime
     let dconstypesT = afterTime - beforeTime

     let globalDConsEnv = localDConsEnv `joinEnv` importDConsEnv

-- generate the class hierarchy skeleton

     beforeTime <- getCPUTime
     let classHierarchy 
            = foldl (flip (addClassToHierarchy moduleName kindInfo)) importClassHierarchy rClassDecls

     -- add type class instances to the class hierarchy XXX this is broken

     let cHierarchyWithInstances 
            -- = addInstancesToHierarchy kindInfo classHierarchy (rinstanceDecls ++ rdataDecls)
            = classHierarchy 

     when (doDump dumps "classes") $
          do {putStrLn " \n\n ---- class hierarchy ---- \n\n";
              printClassHierarchy cHierarchyWithInstances}

     afterTime <- getCPUTime
     let classT = afterTime - beforeTime

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

     let sigEnv = listSigsToSigEnv kindInfo allTypeSigs 

     let classMethodAssumptions = classMethodAssumps cHierarchyWithInstances
     
     let classMethodNames = map (\assump -> assumpId assump) classMethodAssumptions

     let identTableWithMethods
            -- = foldl (\fm name -> addToFM name (bogusASrcLoc, ClassMethod) fm) identTableWithInstances classMethodNames 
            = foldl (\fm name -> addToFM name (bogusASrcLoc, ClassMethod) fm) identTable classMethodNames 

-- binding groups for top-level variables

     let programBgs 
            = getBindGroups (rFunBinds ++ rPatBinds) getDeclName getDeclDeps

     when (doDump dumps "varbindgroups") $
          do {putStrLn " \n\n ---- toplevel variable binding groups ---- ";
              putStrLn " ---- Bindgroup # = [members] [vars depended on] [missing vars] ---- \n";
              putStr $ debugDeclBindGroups programBgs}

     let program = makeProgram sigEnv programBgs

-- type inference/checking for all variables

     let localVarEnv
            = tiProgram 
                 moduleName                     -- name of the module
                 sigEnv                         -- environment of type signatures
                 kindInfo                       -- kind information about classes and type constructors
                 cHierarchyWithInstances        -- class hierarchy with instances
                 globalDConsEnv                 -- data constructor type environment 
                 importVarEnv                   -- type environment
                 program                        -- binding groups

     beforeTime <- getCPUTime

     when (doDump dumps "types") $
          do {putStr "\n\n ---- the types of identifiers ---- \n\n";
              putStrLn $ PPrint.render $ pprintEnv localVarEnv}

     afterTime <- getCPUTime

     let typeInferT = afterTime - beforeTime

     let timingInfo = Timing {desugarTime    = desugarT,
                              renameTime     = renameT,
                              classTime      = classT,
                              kindsTime      = kindsT,
                              dconstypesTime = dconstypesT,
                              typeInferTime  = typeInferT,
                              total          = afterTime - initialTime}

     return (timingInfo, 
             localVarEnv, 
             localDConsEnv,
             cHierarchyWithInstances, 
             kindInfo, 
             identTableWithMethods, 
             tidyModuleToAHsModule renamedTidyModule,
             tidyTyDecls tidyMod) 
