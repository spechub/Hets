{-------------------------------------------------------------------------------

        Copyright:              The Hatchet Team (see file Contributors)

        Module:                 Opts

        Description:            Command line processing for Hatchet.

        Primary Authors:        Bernie Pope

        Notes:                  See the file License for license information

                                If you want to figure out how this works 
                                look in the file GetOpt.hs

-------------------------------------------------------------------------------}

module Opts (processCmdLine, 
             makeUsageInfo,
             usageHeader) where

import GetOpt (OptDescr (..),
               ArgDescr (..),
               getOpt,
               usageInfo,
               ArgOrder (..))

--------------------------------------------------------------------------------


data Flag = Dump String        -- what data to dump
          | Help               -- print help/usage message
          | Time               -- do we count the time for stages?
          | Intermediate (Maybe String)  -- do we want an intermediate file, and what to
                                         -- call the file, default is M.ti for some
                                         -- module called "M"

options :: [OptDescr Flag]

options
 = [
    Option ['h']    ["help"] (NoArg Help)       
                                   ("\n\n    displays a usage message\n\n"),
    Option ['d']    ["dump"] (ReqArg Dump "SECTION")       
                                   ("\n\n    dumps some info on a given SECTION\n"
   ++ "    case SECTION of\n"
   ++ "     \"syntax\"        -> syntax tree after parsing\n"
   ++ "     \"desugar\"       -> source after desugaring\n"
   ++ "     \"renamed\"       -> source after unique renaming\n"
   ++ "     \"idents\"        -> each identifier's location and binding\n"
   ++ "     \"dconstypes\"    -> type assumptions for data constructors\n"
   ++ "     \"kinds\"         -> kinds of type constructors, classes and type variables\n"
   ++ "     \"types\"         -> type of top and let/where bound variables\n"
   ++ "     \"classes\"       -> class hierarchy\n"
   ++ "     \"srcsigs\"       -> type signatures provided in the source code\n"
   ++ "     \"instances\"     -> type class methods after they have been\n"
   ++ "                          lifted to the top-level\n"
   ++ "     \"varbindgroups\" -> binding groups or top-level variables\n"
   ++ "     \"all\"           -> all the above data\n\n")
    ,
    Option ['t']    ["time"] (NoArg Time)       
                                   ("\n\n    displays the time taken to generate the dumped sections\n\n")   
    ,
    Option ['i']    ["intermediate"] (OptArg Intermediate "INTERMEDIATE_FILE")
                                   ("\n\n    prints types to an intermediate file.\n"
   ++ "      For a module called \"M\", the default behaviour is to write\n"
   ++ "      to M.ti, unless another filename is specified as INTERMEDIATE_FILE\n")

   ]


processCmdLine :: String -> [String] -> (String,               -- haskell src 
                                         [String],             -- dumps 
                                         Bool,                 -- help 
                                         Bool,                 -- timing 
                                         Maybe (Maybe String)) -- intermediate file, with possible new name 

processCmdLine progName cmdLine 
   = case getOpt RequireOrder options cmdLine of
          ([Help], _, _)              -> error $ makeUsageInfo (usageHeader progName)
          (_, [],  _)                 -> error $ makeUsageInfo errorMsg1 
          (_, (_:_:_) , [])           -> error $ makeUsageInfo errorMsg2 
          (opts, [hsFile], [])        -> findFlags hsFile opts
          (_,  _, errs)               -> error $ concat errs ++ makeUsageInfo (usageHeader progName)
   where
   errorMsg1 = progName ++ ": no haskell input file specified\n"
   errorMsg2 = progName ++ ": too many input files specified\n"

findFlags :: String -> [Flag] -> (String, 
                                  [String], 
                                  Bool, 
                                  Bool, 
                                  Maybe (Maybe String))
findFlags hsFile fs
   = case dumps of
        -- by default we dump the types if no other dumps are requested
        []       -> (hsFile, ["types"], pHelp, pTime, intermediateFile)
        ds@(_:_) -> (hsFile, dumps, pHelp, pTime, intermediateFile) 
   where
   dumps = findDumps fs
   pHelp = findPHelp fs
   pTime = findPTime fs
   intermediateFile = findIntermediate fs

   findDumps :: [Flag] -> [String]
   findDumps [] = []
   findDumps (Dump d:flags) = d : (findDumps flags)
   findDumps (_:flags) = findDumps flags

   findPHelp :: [Flag] -> Bool
   findPHelp [] = False
   findPHelp (Help:flags) = True
   findPHelp (_:flags) = findPHelp flags

   findPTime :: [Flag] -> Bool
   findPTime [] = False
   findPTime (Time:flags) = True
   findPTime (_:flags) = findPTime flags

   findIntermediate :: [Flag] -> Maybe (Maybe String)
   findIntermediate [] = Nothing 
   findIntermediate (Intermediate i : _flags) = Just i
   findIntermediate (_:flags) = findIntermediate flags

usageHeader progName = "Usage: " ++ progName ++ " [OPTION...] HaskellSrcFile\n"

makeUsageInfo :: String -> String
makeUsageInfo errMsg
   = usageInfo errMsg options 
