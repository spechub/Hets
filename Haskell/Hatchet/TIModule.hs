{-------------------------------------------------------------------------------

        Copyright:              The Hatchet Team (see file Contributors)

        Module:                 TIModule

        Description:            Type checking for a single module given 
                                information about imported entities.

        Primary Authors:        Bernie Pope, Bryn Humberstone

        Notes:                  See the file License for license information

-------------------------------------------------------------------------------}

module Haskell.Hatchet.TIModule (tiModule, Timing (..)) where

import Monad                    (when)

import Haskell.Hatchet.AnnotatedHsSyn
                                (AHsDecl,
                                 AHsModule)

import qualified Haskell.Hatchet.AHsPretty as AHsPretty
                                (ppAHsModule,
                                 render,
                                 ppAHsDecl)

import qualified Haskell.Hatchet.PPrint as PPrint         (render)

import Haskell.Hatchet.TIMain   (makeProgram)

import Haskell.Hatchet.Rename   (IdentTable,
                                 printIdentTable)

import Haskell.Hatchet.KindInference (KindEnv)

import Haskell.Hatchet.Representation (Scheme)

import CPUTime  (getCPUTime)

import Haskell.Hatchet.Utils    (getAModuleName,
                                 doDump)

import Haskell.Hatchet.TidyModule (tidyModule, 
                                 TidyModule (..),
                                 tidyModuleToAHsModule)


import Haskell.Hatchet.TypeSigs (listSigsToSigEnv)


import Haskell.Hatchet.Class    (printClassHierarchy,
                                 ClassHierarchy)

import IO

import Haskell.Hatchet.Env      (Env,
                                 pprintEnv)

import Haskell.Hatchet.MultiModuleBasics (ModuleInfo(..))

import Haskell.Hatchet.DeclsDepends (debugDeclBindGroups)

import Haskell.Hatchet.TIPhase

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
  
     initialTime <- getCPUTime

-- print the name of the module being typed
     putStr $ "\n\n ---- Type checking " ++ show (getAModuleName modSyntax) 
		++ " ----\n\n"
   
-- print the syntax tree: depending on command line arguments

     when (doDump dumps "syntax" ) $
        do {putStr "\n\n ---- Initial Syntax Tree ---- \n\n";
            putStr $ show modSyntax}

-- split the module into seperate components

     let tidyMod = tidyModule modSyntax

-- make all pattern bindings simple and remove type synonyms, convert do-notation into expression form

     beforeTime <- getCPUTime

     let desugaredTidyModule = desugarTM imports tidyMod 

     when (doDump dumps "desugar") $
          do {putStrLn "\n\n ---- desugared code ---- \n\n";
              putStrLn $ AHsPretty.render 
                       $ AHsPretty.ppAHsModule 
                       $ tidyModuleToAHsModule desugaredTidyModule}

     afterTime <- getCPUTime

     let desugarT = afterTime - beforeTime

-- uniquely rename variables and generate a table of information about identifiers

     beforeTime <- getCPUTime

     let (renamedTidyModule, identTable) = renameTM imports desugaredTidyModule

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

-- collect all the type signatures from the module (this must be done after renaming)

     let allTypeSigs = getAllTypeSigs renamedTidyModule

     when (doDump dumps "srcsigs") $
          do {putStrLn " \n\n ---- type signatures from source code (after renaming) ---- \n\n";
              putStr $ unlines $ map (AHsPretty.render . AHsPretty.ppAHsDecl) allTypeSigs}

-- kind inference for all type constructors type variables and classes in the module

     beforeTime <- getCPUTime

     let kindInfo = getKindInfo renamedTidyModule imports

     when (doDump dumps "kinds") $
          do {putStrLn " \n\n ---- kind information ---- \n\n";
              putStr $ PPrint.render $ pprintEnv kindInfo}


     afterTime <- getCPUTime
     let kindsT = afterTime - beforeTime

-- collect types for data constructors

     beforeTime <- getCPUTime

     let localDConsEnv = getLocalDConsEnv renamedTidyModule kindInfo

     when (doDump dumps "dconstypes") $
          do {putStr "\n\n ---- data constructor assumptions ---- \n\n";
              putStrLn $ PPrint.render $ pprintEnv localDConsEnv}

     afterTime <- getCPUTime
     let dconstypesT = afterTime - beforeTime

     let globalDConsEnv = getGlobalDConsEnv localDConsEnv imports

-- generate the class hierarchy skeleton

     beforeTime <- getCPUTime

     let cHierarchyWithInstances 
            = getClassHierarchy renamedTidyModule imports kindInfo

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
     let identTableWithMethods = getIdentTableWithMethods identTable
				 cHierarchyWithInstances 
     let programBgs 
            = getProgramBgs renamedTidyModule

     when (doDump dumps "varbindgroups") $
          do {putStrLn " \n\n ---- toplevel variable binding groups ---- ";
              putStrLn " ---- Bindgroup # = [members] [vars depended on] [missing vars] ---- \n";
              putStr $ debugDeclBindGroups programBgs}

     let program = makeProgram sigEnv programBgs

-- type inference/checking for all variables

     let localVarEnv = getLocalVarEnv 
		       renamedTidyModule imports sigEnv kindInfo
		       cHierarchyWithInstances globalDConsEnv program

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
             tidyTyDecls renamedTidyModule) 
