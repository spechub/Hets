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

module MultiModule(
    ModuleInfo(..),
    writeModuleInfo,
    readModuleInfo,
  fromString, 
  toString       -- eventually we shouldn't export these
    ) where

import List                     (intersect)
import MultiModuleBasics
import Env                      (Env, listToEnv)
import KindInference            (KindEnv)
import HsSyn
import FiniteMaps               (toListFM, listToFM)
import AnnotatedHsSyn  
import Utils                    (getUnQualName, qualifyName)
import Rename                   (getAHsNamesAndASrcLocsFromAHsDecl, unRename)
import Representation           (Scheme)
import Class                    (ClassHierarchy)

--------------------------------------------------------------------------------

readModuleInfo :: AHsModule -> IO ModuleInfo
readModuleInfo (AHsModule _ _ imports _) 
    = do
      allModInfos <- mapM readOneImportSpec imports
      return (concatModuleInfos allModInfos)
    where
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
                    
    -- e.g. rewrite Bool(..) to Bool(True, False). Second argument is the 
    -- list of tyconsMembers. First is imported mod's name (because we'll
    -- be looking in a list of qualified names)
    expandDotsInTyCons :: AModule -> [(AHsName, [AHsName])] -> 
				[AHsExportSpec] -> [AHsExportSpec]
    expandDotsInTyCons modName tyconInfo specs 
        = [ case lookup (qualifyName modName tycon) tyconInfo of 
                     Just dcons -> AHsEThingWith tycon dcons
                     Nothing -> error $ "MultiModule.readModuleInfo: Couldn't "
			            ++  "find the data\n"
                        ++  "constructors corresponding to " 
			            ++ show tycon ++ " in the list " 
			            ++ show tyconInfo 
                 | (AHsEThingAll tycon) <- specs ] ++
          filter (not . tyConWithDots) specs  -- the only thing we modify is the Foo(..) type
                                              -- exports. Others we just leave the same.
        where
        tyConWithDots (AHsEThingAll _) = True
        tyConWithDots _ = False

-- pass in the module's name, all of its info and the list of things that
-- we want to include from it and return the new moduleInfo. Although these
-- are AHsExportSpecs we can convert ImportSpecs to this with the same
-- effect
filterModuleInfo :: AModule -> ModuleInfo -> [AHsExportSpec] -> ModuleInfo
filterModuleInfo amod modInfo exports 
    = modInfo {
        varAssumps   = applyFilter varAssumps,
        dconsAssumps = applyFilter dconsAssumps
      }
    where
    applyFilter field = listToFM $ filterSchemes amod exports $ 
                                   toListFM (field modInfo)


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

importSpecToExportSpec :: AHsImportSpec -> AHsExportSpec
importSpecToExportSpec imp 
    = case imp of AHsIVar n -> AHsEVar n
                  AHsIAbs n -> AHsEAbs n
                  AHsIThingAll n -> AHsEThingAll n
                  AHsIThingWith a b -> AHsEThingWith a b

    
-- filterSchemes currentMod exports schemes  
-- goes through schemes and includes only the types for things that also
-- appear in the list exports (needs to know currentMod so it can try the
-- qualified name also).
filterSchemes :: AModule -> [AHsExportSpec] -> [(AHsName, Scheme)] -> [(AHsName, Scheme)]
filterSchemes currentMod exports [] = []
filterSchemes currentMod exports name_schemes@((name,scheme):rest)
    | any (varWhoseNameIs unRenamedName) exports = 
          (qualifyName currentMod unRenamedName,scheme):restFiltered
    | otherwise                                  = restFiltered
    where 
    restFiltered = filterSchemes currentMod exports rest
    unRenamedName = unRename name -- get rid of renaming first

    varWhoseNameIs name (AHsEVar export) 
        = unifiableNames currentMod name export

    -- e.g. name = "Prelude.True" and we know we can export
    -- Bool(True, False) then we should include name (i.e. return True)
    -- I've been a bit lazy and converted it to an AHsEVar to use
    -- the unifier
    varWhoseNameIs name (AHsEThingWith _tycon datacons)
        = any (unifiableNames currentMod name) datacons

    -- AHsEThingAll is a pain because we can't recover the constructors for it, so an invariant
    -- is that we never should get them here (if we knew Bool(..) and we wnat to discover whether
    -- True should be included then what can we do?)
    varWhoseNameIs name (AHsEThingAll _) = error $ "in MultiModule.filterSchemes we don't want AHsEThingAlls" ++ "filterSchemes called with " ++ show currentMod ++ "\n\n" ++ show exports ++ "\n\n" ++ show name_schemes
    varWhoseNameIs _    _           = False   -- trying to match with a non AHsEVar. 
           

    -- this tests to see whether you can unify the name we're 
    -- thinking about including with a name in the export list.
    unifiableNames :: AModule -> AHsName -> AHsName -> Bool
    unifiableNames currentMod name1 name2
        = name1 == name2   -- if they're identical AHsNames then we say it's a match
       || (getUnQualName name1 == getUnQualName name2
           && (case (name1, name2) of   
                    (AUnQual _, AQual mod _) -> mod == currentMod   -- unqualified names implicitly from currentMod
                    (AQual mod _, AUnQual _) -> mod == currentMod 
              )
          )




-- takes the list of toplevel bindings (as an exportspec) and the explicit exports
-- and intersects them
intersectAHsExportSpecs :: [AHsExportSpec] -> [AHsExportSpec] -> [AHsExportSpec]
intersectAHsExportSpecs _ [] = []
intersectAHsExportSpecs [] _ = []
intersectAHsExportSpecs (x:xs) other
    = let rest = intersectAHsExportSpecs xs other 
      in if x `elem` other then x:rest else
         case x of 
              (AHsEVar _)            -> rest   -- if it wasn't found in other then don't include it
              (AHsEModuleContents _) -> rest   -- if it wasn't found in other then don't include it
              (AHsEAbs name) -> 
                  case findSameConstructor name other of Just _  -> x:rest
                                                         Nothing -> rest
              (AHsEThingAll name) -> 
                  case findSameConstructor name other of Just foo -> foo:rest   -- foo will have to be more restrictive 
                                                         Nothing  -> rest       -- which is why we're including it
              
              (AHsEThingWith name cons) ->
                  case findSameConstructor name other of 
                       Just (AHsEThingAll _) -> x:rest   -- no restrictions from other
                       Just foo@(AHsEAbs _) ->  foo:rest  -- this says just export the name so we choose it 
                       -- this is the most interesting case: just intersect the two dataconstructor lists
                       Just (AHsEThingWith _ cons') ->
                            (AHsEThingWith name (List.intersect cons cons')):rest
                       Nothing -> rest
      where
      findSameConstructor :: AHsName -> [AHsExportSpec] -> Maybe AHsExportSpec
      findSameConstructor name xs = 
          case filter (sameConstructor name) xs of
               [] -> Nothing
               [a] -> Just a
               _  -> error $ "Found more than one occurrence of constructor " 
                                ++ show name
                                ++ " in export list"

      sameConstructor n (AHsEAbs name)        = n == name
      sameConstructor n (AHsEThingAll name)   = n == name
      sameConstructor n (AHsEThingWith name _) = n == name
      sameConstructor _ _ = False


-- take the syntax tree (easily attainable from an AHsModule) get all the top-level bindings
getTopLevelBindings :: [AHsDecl] -> [AHsExportSpec]
getTopLevelBindings ahsDecls
    = concatMap getNamesFromDecl ahsDecls
    where
     getNamesFromDecl decl
        = case decl of
               (AHsTypeDecl	  _ name _ _) -> [AHsEAbs name]   -- I think it's an AHsEAbs?
               (AHsDataDecl	  _ _ name _ datacons _classes) -> 
                    [AHsEThingWith name (map getConstructorName datacons)] -- so we know all the names of datacons
               (AHsNewTypeDecl _ _ name names _ _) -> [AHsEThingWith name names] 
               _ -> 
                    map (AHsEVar . fst)
                        (getAHsNamesAndASrcLocsFromAHsDecl decl) -- use the Rename one for normal bindings

     getConstructorName :: AHsConDecl -> AHsName
     getConstructorName (AHsConDecl _ name _) = name
     getConstructorName (AHsRecDecl _ name _) = name

    
