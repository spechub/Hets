{-------------------------------------------------------------------------------

        Copyright:              The Hatchet Team (see file Contributors)

        Module:                 MultiModule

        Description:            Support code for type checking multi-module
                                programs, including representation of
                                module-wise static information and reading
                                and writing intermediate files (.ti).

        Primary Authors:        Bryn Humberstone 

        Notes:                  See the file License for license information

-------------------------------------------------------------------------------}

module Haskell.Hatchet.ModuleIO(
    writeModuleInfo,
    readModuleInfo,
    readOneImportSpec,
  fromString, 
  toString,       -- eventually we shouldn't export these
    ) where

import List                     (intersect)
import Haskell.Hatchet.MultiModuleBasics
import Haskell.Hatchet.MultiModule
import Haskell.Hatchet.PlainShowParse
import Haskell.Hatchet.Env                      (Env, listToEnv)
import Haskell.Hatchet.KindInference            (KindEnv)
import Haskell.Hatchet.HsSyn
import Haskell.Hatchet.FiniteMaps               (toListFM, listToFM)
import Haskell.Hatchet.AnnotatedHsSyn  
import Haskell.Hatchet.Utils                    (getUnQualName, qualifyName)
import Haskell.Hatchet.Rename                   (getAHsNamesAndASrcLocsFromAHsDecl, unRename)
import Haskell.Hatchet.Representation           (Scheme)
import Haskell.Hatchet.Class                    (ClassHierarchy)

--------------------------------------------------------------------------------

readModuleInfo :: AHsModule -> IO ModuleInfo
readModuleInfo (AHsModule _ _ imports _) 
    = do
      allModInfos <- mapM readOneImportSpec imports
      return (concatModuleInfos allModInfos)
--    where
    -- take one declaration and build a ModuleInfo from it
readOneImportSpec :: AHsImportDecl -> IO ModuleInfo
readOneImportSpec (AHsImportDecl _ mod _ _ maybeListOfIdents)
        = do
          moduleInfoUnParsed <- readFile (modToFilePath mod)
          let modInfoUnFiltered :: ModuleInfo
              modInfoUnFiltered = fromString moduleInfoUnParsed
          case maybeListOfIdents of
               Nothing -> return modInfoUnFiltered -- we're not imposing restrictions
               Just (_, importSpecs) -> 
                   let ans = filterModuleInfo mod modInfoUnFiltered $
                             expandDotsInTyCons mod (tyconsMembers modInfoUnFiltered) $
                             map importSpecToExportSpec importSpecs
                   in  do return ans

-- this is one of the main functions of the module
writeModuleInfo :: Maybe FilePath -> AHsModule -> ModuleInfo -> IO ()
writeModuleInfo alternateFileName (AHsModule amod exports _ tree) modInfo
    = do

      -- figure out what needs to go into the file
      let topLevel :: [AHsExportSpec]    -- this is the maximum that we can export
          topLevel = getTopLevelBindings tree
        
          actualExports :: [AHsExportSpec]
          actualExports = 
              case exports of Nothing -> topLevel  -- no restrictions
                              Just list -> intersectAHsExportSpecs topLevel list

      let filteredVarAssumps 
             = filterSchemes amod actualExports $ toListFM $ varAssumps modInfo
          filteredDConsAssumps 
             = filterSchemes amod actualExports $ toListFM $ dconsAssumps modInfo
          newKinds
             = filterInOnlyThisModuleAndQualifyIfNecessary $ toListFM $ kinds modInfo
          newClassHierarchy
             = filterInOnlyThisModuleAndQualifyIfNecessary $ toListFM $ classHierarchy modInfo

          {- to get the new kind table just include the kinds from the kind table
             returned and qualify if necessary (and don't include ones from other
             modules). -}
          -- this is Bryn's attempt to beat Bernie in the longest identifier competition 
          filterInOnlyThisModuleAndQualifyIfNecessary :: [(AHsName, a)] -> [(AHsName, a)]
          filterInOnlyThisModuleAndQualifyIfNecessary name_pairs
             = [ (qualifyName amod ahsname, kind)
                    | (ahsname, kind) <- name_pairs,
                      case ahsname of (AUnQual _) -> True
                                      (AQual mod _) -> mod == amod
               ]
                 
          writableModInfo 
            = modInfo { varAssumps = listToFM filteredVarAssumps,
                        dconsAssumps = listToFM filteredDConsAssumps,
                        kinds = listToFM newKinds,
                        classHierarchy = listToFM newClassHierarchy
                      }
                           
          stuffForFile = toString writableModInfo 

      let intermediateFilePath 
             = case alternateFileName of
                 Nothing -> modToFilePath amod
                 Just f  -> f

      writeFile intermediateFilePath stuffForFile















