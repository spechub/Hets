{-------------------------------------------------------------------------------

        Copyright:              The Hatchet Team (see file Contributors)

        Module:                 Main

        Description:            The driver for Hatchet.

        Primary Authors:        Bernie Pope

        Notes:                  See the file License for license information

-------------------------------------------------------------------------------}

module Main where

import Monad                    (when)

import List                     (null)

import MultiModule              (writeModuleInfo, readModuleInfo, toString)

import MultiModuleBasics        -- (ModuleInfo(..), joinModuleInfo)

import TIModule                 (tiModule, 
                                 Timing (..))

import HsParser                 (parse)

import HsSyn                    (HsModule, 
                                 SrcLoc (..))

import AnnotatedHsSyn           (ASrcLoc (..),
                                 bogusASrcLoc,
                                 AModule(..),
                                 AHsModule)

import HsParseMonad             (ParseResult (..))


import Env                      (listToEnv)

import System                   (getArgs,
                                 getProgName)


import HaskellPrelude           (tyconsMembersHaskellPrelude, 
                                 preludeDefs, 
                                 preludeSynonyms,
                                 preludeTyconAndClassKinds,
                                 preludeClasses,
                                 preludeInfixDecls,
                                 preludeDataCons)


import Opts                     (processCmdLine,
                                 makeUsageInfo,
                                 usageHeader)

import CPUTime                  (getCPUTime,
                                 cpuTimePrecision)


import Utils                    (rJustify,
                                 lJustify,
                                 getAModuleName,
                                 doDump
                                 )

import Class                    (emptyClassHierarchy)

import FiniteMaps               (listToFM,
                                 filterFM)

import Type                     (assumpToPair)

import Representation           (Assump (..))

import SynConvert               (toAHsModule)

import HsParsePostProcess       (fixFunBindsInModule)

--------------------------------------------------------------------------------

-- here's where the action begins

main =
   do

-- get the name of the program

     progName <- getProgName

-- process command line arguments
 
     cmdline <- getArgs
     let (srcFile,          -- name of file to process
          dumps,            -- flags indicating which structures to dump 
          pHelp,            -- print help information 
          pTime,            -- flag to say whether timing info should be printed 
          intermediateFile) -- possible intermediate file for printing type info
             = processCmdLine progName cmdline

-- possibly print usage information

     when pHelp $ do {putStrLn $ makeUsageInfo $ usageHeader progName} 

-- read the source file and parse

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
      moduleSynonyms) <- tiModule dumps annotatedSyntax initialModInfo

    -- this is the modInfo to print into an intermediate file
     let modInfo = ModuleInfo { varAssumps = moduleEnv, 
                                moduleName = Utils.getAModuleName annotatedSyntax,
                                dconsAssumps = dataConEnv, 
                                classHierarchy = newClassHierarchy,
                                kinds = newKindInfoTable,
                                tyconsMembers = MultiModuleBasics.getTyconsMembers moduleRenamed,
                                infixDecls = MultiModuleBasics.getInfixDecls moduleRenamed,
                                synonyms = moduleSynonyms }

-- possibly write the intermediate file, if command line specifies so

     case intermediateFile of
        Nothing                        -> return ()
        Just possibleIntermediateName  -> writeModuleInfo possibleIntermediateName annotatedSyntax modInfo

-- dump crude timing information if requested

     when pTime $ do {dumpTimes dumps timings}

-- THE END.

--------------------------------------------------------------------------------

-- utilities

-- call the haskell parser and check for errors

parseHsSource :: String -> HsModule
parseHsSource s = case parse s (SrcLoc 1 1) 0 [] of
                      Ok state e -> e
                      Failed err -> error err


-- A factor to convert pico seconds to milli seconds

timeScale :: Integer
timeScale = 10^12

-- pretty prints a time (an integer in picoseconds)

showTime time
  = rJustify 3 (show (time `div` timeScale)) ++ "."
       ++ take 3 (show (time `mod` timeScale) ++ repeat '0') ++ " seconds"


-- A displays the time taken for a section with some extra info

dumpTimes :: [String] -> Timing -> IO ()
dumpTimes dumps timings
  = do
      let precision = cpuTimePrecision
          suffix =  "seconds" ++ show (precision `div` timeScale) ++ "ms\n"

      putStr $ "\n\n ---- time taken for program phases ---- \n\n"

      when (doDump dumps "desugar") $
           putStrLn $ (lJustify 40 "desugaring: ") ++ (showTime $ desugarTime timings)

      when (doDump dumps "renamed" || doDump dumps "idents" || doDump dumps "typesigs") $
           putStrLn $ (lJustify 40 "uniquely renaming variables: ") ++ (showTime $ renameTime timings)

      when (doDump dumps "classes") $
           putStrLn $ (lJustify 40 "generating class hierarchy: ") ++ (showTime $ classTime timings)

      when (doDump dumps "kinds") $
           putStrLn $ (lJustify 40 "kind inference: ") ++ (showTime $ kindsTime timings)

      when (doDump dumps "dconstypes") $
           putStrLn $ (lJustify 40 "analysing data constructor types: ") ++ (showTime $ dconstypesTime timings)

      when (doDump dumps "types") $
           putStrLn $ (lJustify 40 "full module type inference: ") ++ (showTime $ typeInferTime timings)

      when (not $ null dumps) $
           putStrLn $ (lJustify 40 "total time:           ") ++ (showTime $ total timings)

      putStrLn $ "\n   (times are accurate to " ++ showTime precision ++ ")"
      putStrLn $   "   (and include the printing time)"


