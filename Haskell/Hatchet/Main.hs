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

import Haskell.Hatchet.ModuleIO              (writeModuleInfo, readModuleInfo)

import Haskell.Hatchet.MultiModuleBasics

import Haskell.Hatchet.TIModule                 (tiModule, 
                                 Timing (..))

import System.Environment       (getArgs,
                                 getProgName)



import Haskell.Hatchet.Opts                     (processCmdLine,
                                 makeUsageInfo,
                                 usageHeader)

import CPUTime                  (cpuTimePrecision)


import Haskell.Hatchet.Utils                    (rJustify,
                                 lJustify,
                                 getAModuleName,
                                 doDump
                                 )

import Haskell.Hatchet.TIPhase

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

     moduleSyntax <- parseFile srcFile
     let annotatedSyntax = getAnnotedSyntax moduleSyntax

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
      _moduleIds,
      moduleRenamed,
      moduleSynonyms) <- tiModule dumps annotatedSyntax initialModInfo

    -- this is the modInfo to print into an intermediate file
     let modInfo = ModuleInfo { varAssumps = moduleEnv, 
                                moduleName = getAModuleName annotatedSyntax,
                                dconsAssumps = dataConEnv, 
                                classHierarchy = newClassHierarchy,
                                kinds = newKindInfoTable,
                                tyconsMembers = getTyconsMembers moduleRenamed,
                                infixDecls = getInfixDecls moduleRenamed,
                                synonyms = moduleSynonyms }

-- possibly write the intermediate file, if command line specifies so

     case intermediateFile of
        Nothing                        -> return ()
        Just possibleIntermediateName  -> 
	    writeModuleInfo possibleIntermediateName annotatedSyntax modInfo

-- dump crude timing information if requested

     when pTime $ do {dumpTimes dumps timings}

-- THE END.

--------------------------------------------------------------------------------
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
          _suffix =  "seconds" ++ show (precision `div` timeScale) ++ "ms\n"

      putStr $ "\n\n ---- time taken for program phases ---- \n\n"

      when (doDump dumps "desugar") $
           putStrLn $ (lJustify 40 "desugaring: ") ++ 
			(showTime $ desugarTime timings)

      when (doDump dumps "renamed" || doDump dumps "idents" || 
	    doDump dumps "typesigs") $
           putStrLn $ (lJustify 40 "uniquely renaming variables: ") ++ 
			(showTime $ renameTime timings)

      when (doDump dumps "classes") $
           putStrLn $ (lJustify 40 "generating class hierarchy: ") ++ 
			(showTime $ classTime timings)

      when (doDump dumps "kinds") $
           putStrLn $ (lJustify 40 "kind inference: ") ++ 
			(showTime $ kindsTime timings)

      when (doDump dumps "dconstypes") $
           putStrLn $ (lJustify 40 "analysing data constructor types: ") ++ 
			(showTime $ dconstypesTime timings)

      when (doDump dumps "types") $
           putStrLn $ (lJustify 40 "full module type inference: ") ++ 
			(showTime $ typeInferTime timings)

      when (not $ null dumps) $
           putStrLn $ (lJustify 40 "total time:           ") ++ 
			(showTime $ total timings)

      putStrLn $ "\n   (times are accurate to " ++ showTime precision ++ ")"
      putStrLn $   "   (and include the printing time)"
