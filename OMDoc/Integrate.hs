{- |
Module      :  $Header$
Copyright   :  (c) Hendrik Iben, Uni Bremen 2005-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  hiben@tzi.de
Stability   :  provisional
Portability :  non-portable(Logic)

Aims at glueing together all needed modules
        for Hets<->Omdoc-conversion.
-}
module OMDoc.Integrate where

import qualified OMDoc.HetsInterface as Hets
import qualified Common.Id as Id
import qualified Syntax.AS_Library as ASL

import Static.DevGraph
import qualified Data.Graph.Inductive.Graph as Graph

-- Often used symbols from HXT
import Text.XML.HXT.Parser
        ( (.>), xshow, isTag, getChildren
          , getValue, emptyRoot
                , v_1, v_0, a_issue_errors, a_source
                , a_validate, a_check_namespaces
        )
        
import qualified Text.XML.HXT.Parser as HXT hiding (run, trace, when)
import qualified Text.XML.HXT.DOM.XmlTreeTypes as HXTT hiding (when)
--import qualified Text.XML.HXT.XPath as XPath

import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set

import qualified Common.Result as Result

--import qualified Logic.Logic as Logic

import Data.Maybe (fromMaybe)
import Data.List (isPrefixOf)

import qualified Driver.Options as DOptions

import Control.Exception

import qualified System.IO.Error as System.IO.Error
import qualified System.Exit as Exit

import qualified System.Environment as Env
import qualified System.Console.GetOpt as GetOpt

import Control.Monad

import Char (toLower, isSpace)

import OMDoc.Util
import OMDoc.KeyDebug
import OMDoc.XmlHandling
import OMDoc.OMDocDefs
import OMDoc.OMDocInput
import OMDoc.OMDocOutput

-- | processing options for getopt              
data PO =
        POInput String
        | POInputType String
        | POOutput String
        | POOutputType String
        | POShowGraph
        | POLib String
        | POSandbox String
        | POHelp
        | PODTDURI String
        | PODebug
        | PODebugKey String
        | PODebugKeys String
        | PODebugDisKey String
        | PODebugKeyPolicy DbgKeyPolicy
        | PODebugDisKeyPolicy DbgKeyPolicy
        | PODisableDTD
        
data POType =
        POTInput
        | POTInputType
        | POTOutput
        | POTOutputType
        | POTShowGraph
        | POTLib
        | POTSandbox
        | POTHelp
        | POTDTDURI
        | POTDebug
        | POTDebugKey
        | POTDebugKeys
        | POTDebugDisKey
        | POTDebugKeyPolicy
        | POTDebugDisKeyPolicy
        | POTDisableDTD
        deriving Eq
        
poToPOT::PO->POType
poToPOT (POInput _) = POTInput
poToPOT (POInputType _) = POTInputType
poToPOT (POOutput _) = POTOutput
poToPOT (POOutputType _) = POTOutputType
poToPOT (POLib _) = POTLib
poToPOT (POSandbox _) = POTSandbox
poToPOT (PODTDURI _) = POTDTDURI
poToPOT POShowGraph = POTShowGraph
poToPOT POHelp = POTHelp
poToPOT PODebug = POTDebug
poToPOT (PODebugKey _) = POTDebugKey
poToPOT (PODebugKeys _) = POTDebugKeys
poToPOT (PODebugDisKey _) = POTDebugDisKey
poToPOT (PODebugKeyPolicy _) = POTDebugKeyPolicy
poToPOT (PODebugDisKeyPolicy _) = POTDebugDisKeyPolicy
poToPOT PODisableDTD = POTDisableDTD
                
processingOptions::[GetOpt.OptDescr PO]
processingOptions =
        [
          GetOpt.Option ['i'] ["input"] (GetOpt.ReqArg POInput "INPUT") "File to read from"
        , GetOpt.Option ['r'] ["input-type"] (GetOpt.ReqArg POInputType "INPUTTYPE (casl, omdoc, env)") "Type of input"
        , GetOpt.Option ['o'] ["output"] (GetOpt.ReqArg POOutput "OUTPUT") "File to write to"
        , GetOpt.Option ['w'] ["output-type"] (GetOpt.ReqArg POOutputType "OUTPUTTYPE (omdoc, env, fullenv)") "Type of output"
        , GetOpt.Option ['l'] ["library"] (GetOpt.ReqArg POLib "LIBDIR") "Directory to search for input files"
        , GetOpt.Option ['g'] ["showgraph"] (GetOpt.NoArg POShowGraph) "Show Graph"
        , GetOpt.Option ['a'] ["all-libs"] (GetOpt.OptArg (POSandbox . (fromMaybe "")) "OUTDIR") "Output all used libraries [to dir]"
        , GetOpt.Option ['h'] ["help"] (GetOpt.NoArg POHelp) "print this info"
        , GetOpt.Option ['d'] ["dtd-uri"] (GetOpt.ReqArg PODTDURI "DTDURI") "URI for OMDoc-DTD"
        , GetOpt.Option [] ["debug"] (GetOpt.NoArg PODebug) "enable debugging-messages"
        , GetOpt.Option [] ["debug-key"] (GetOpt.ReqArg PODebugKey "KEY") "add a debugging key (or 'all' for all)"
        , GetOpt.Option [] ["debug-keys"] (GetOpt.ReqArg PODebugKeys "KEY") "add debugging keys with policy (or 'all' for all)"
        , GetOpt.Option [] ["debug-disable-key"] (GetOpt.ReqArg PODebugDisKey "KEY") "disable a debugging key (from all)"
        , GetOpt.Option [] ["debug-key-policy"] (GetOpt.ReqArg (PODebugKeyPolicy . fromMaybe (error "Invalid policy...") . stringToPolicy) "POLICY") "set key policy"
        , GetOpt.Option [] ["debug-diskey-policy"] (GetOpt.ReqArg (PODebugDisKeyPolicy . fromMaybe (error "Invalid policy...") . stringToPolicy) "POLICY") "set dis-key policy"
        , GetOpt.Option [] ["disable-dtd"] (GetOpt.NoArg PODisableDTD) "disable putting DTD-location in OMDoc-Output"
        ]
        
usageString::String
usageString = GetOpt.usageInfo "Integrate [-r type] [-i <input>] [-w type] [-o <output>] [-l dir] [-g] [-a[<directory>]] [-d <dtd-uri>]" processingOptions

-- | convert a file name that may have a suffix to a library name
-- taken from AnalysisLibrary (not exported)
fileToLibName :: DOptions.HetcatsOpts -> FilePath -> ASL.LIB_NAME
fileToLibName opts efile =
    let path = DOptions.libdir opts
        file = DOptions.rmSuffix efile -- cut of extension
        nfile = dropWhile (== '/') $         -- cut off leading slashes
                if isPrefixOf path file
                then drop (length path) file -- cut off libdir prefix
                else file
    in ASL.Lib_id $ ASL.Indirect_link nfile Id.nullRange
        
data FileType = FTCASL | FTOMDoc | FTEnv | FTFullEnv | FTNone
        deriving Eq
        
instance Show FileType where
        show FTCASL = "CASL"
        show FTOMDoc = "OMDoc"
        show FTEnv = "Environment"
        show FTFullEnv = "Full-Environment"
        show FTNone = "None"
        
instance Read FileType where
        readsPrec _ r =
                let
                        wsdroplen = length $ takeWhile Char.isSpace r
                in
                        (\s ->
                                if isPrefixOf "casl" s then [(FTCASL, drop (4+wsdroplen) r)]
                                else
                                if isPrefixOf "omdoc" s then [(FTOMDoc, drop (5+wsdroplen) r)]
                                else
                                if isPrefixOf "xml" s then [(FTOMDoc, drop (3+wsdroplen) r)]
                                else
                                if isPrefixOf "env" s then [(FTEnv, drop (3+wsdroplen) r)]
                                else
                                if isPrefixOf "fenv" s then [(FTFullEnv, drop (4+wsdroplen) r)]
                                else
                                if isPrefixOf "none" s then [(FTNone, drop (4+wsdroplen) r)]
                                else
                                if isPrefixOf "-" s then [(FTNone, drop (1+wsdroplen) r)]
                                else
                                        []
                        ) $ map Char.toLower $ drop wsdroplen r 

type FileTypes = [FileType]
        
supportedInput::FileTypes
supportedInput = [FTCASL, FTOMDoc, FTEnv]

supportedOutput::FileTypes
supportedOutput = [FTOMDoc, FTEnv, FTNone]

-- | tries to determine the type of a file by its extension
-- "-" and "none" lead to FTNone
fileType::String->Maybe FileType
fileType s =
        let
                suffix = reverse $ takeWhile (/='.') $ reverse s
                parse = readsPrec 0 suffix
        in
                case parse of
                        [(ft, "")] -> Just ft
                        _ -> Nothing
                        
optFilter::POType->[PO]->[PO]
optFilter pot =
        filter (\i -> pot == poToPOT i)
        
-- | some basic interface for command-line use... 
-- you can read in CASL, OMDoc or Environments (ATerm) and ouput OMDoc or
-- Environments.
-- Currently there are two forms of environments. One that is the output from
-- Hets - a single GlobalContext - and a second that is a full environment 
-- with the name of the library that was read in and all related GlobalContexts.
-- Actually the latter is not really what is wanted and will be removed when
-- better ways of retrieving related DGraphs are developed.
--
-- DebugKeys to disable normaly (huge amount of output) :
--  iGTDGNXN sXNWONFX mNNTDGNL dGTXCMPIOXN

main::IO ()
main =
        do
                args <- Env.getArgs
                (options, nonoptions) <-
                        case GetOpt.getOpt GetOpt.Permute processingOptions args of
                                (o' ,n,[]) -> return (o' ,n)
                                (_,_,errs) -> ioError (userError (concat errs ++ usageString))
                when
                        -- no arguments or Help requested
                        (       ((length args) == 0) ||
                                ((length
                                        (filter
                                                (\op -> case op of POHelp -> True; _ -> False)
                                                options)
                                        ) /= 0)
                        )
                        (do
                                -- print usage and exit
                                putStrLn usageString
                                Exit.exitWith (Exit.ExitSuccess))
                -- filter out options
                inputopts <- return $ optFilter POTInput options
                inputtypeopts <- return $ optFilter POTInputType options
                libopts <- return $ optFilter POTLib options
                outputopts <- return $ optFilter POTOutput options
                outputtypeopts <- return $ optFilter POTOutputType options
                alloutopts <- return $ optFilter POTSandbox options
                showgraphopts <- return $ optFilter POTShowGraph options
                dtduriopts <- return $ optFilter POTDTDURI options
                debugopts <- return $ optFilter POTDebug options
                debugkeyopts <- return $ optFilter POTDebugKey options
                debugkeysopts <- return $ optFilter POTDebugKeys options
                debugdiskeyopts <- return $ optFilter POTDebugDisKey options
                debugkeypolopts <- return $ optFilter POTDebugKeyPolicy options
                debugdiskeypolopts <- return $ optFilter POTDebugDisKeyPolicy options
                disabledtdopts <- return $ optFilter POTDisableDTD options
                
                dodebug <- return $ not $ null debugopts
                disabledtd <- return $ not $ null disabledtdopts
                searchpath <- return $ map (\(POLib s) -> s) libopts
                debugkeys <- return $ map (\(PODebugKey s) -> s) debugkeyopts
                debugkeyslist <- return $ map (\(PODebugKeys s) -> s) debugkeysopts
                debugdiskeys <- return $ map (\(PODebugDisKey s) -> s) debugdiskeyopts
                debugkeypol <- return $ (\(PODebugKeyPolicy p) -> p) $
                        head (debugkeypolopts ++ [PODebugKeyPolicy KPExact]) 
                debugdiskeypol <- return $ (\(PODebugDisKeyPolicy p) -> p) $
                        head (debugdiskeypolopts  ++ [PODebugDisKeyPolicy KPExact])
                l1dbginf <- return $ foldl (\dbginf s ->
                        mergeDbgInf dbginf (mkDebugKeys s)
                        ) emptyDbgInf debugkeyslist
                l2dbginf <- return $ mkDebugExt debugkeys debugdiskeys debugkeypol debugdiskeypol
                finaldbginf <- return $ mergeDbgInf l1dbginf l2dbginf
                globalOptions <- return $ emptyGlobalOptions { dbgInf = finaldbginf }
                input <- return $ case inputopts of
                                        [] -> case nonoptions of
                                                [] -> "-"
                                                _ -> head nonoptions
                                        ((POInput s):_) -> s
                                        _ -> error "wierd entry for input..."
                -- determine input type from parameter or filename
                inputtype <-
                        case inputtypeopts of
                                [] ->
                                        do
                                        when
                                                dodebug
                                                (putStrLn "No Input-Type given. Trying to find out...")
                                        mft <- return $ fileType input
                                        case mft of
                                                (Just ft) -> return ft
                                                Nothing ->
                                                        ioError (userError "Cannot determine Input-Type!")
                                ((POInputType s):_) -> return $ read s
                                _ -> error "wierd entry for inputtype..."
                when
                        dodebug
                        (putStrLn ("Input-Type is : " ++ (show inputtype)))
                -- check if this type is supported
                unless
                        (elem inputtype supportedInput)
                        (ioError (userError "Unsupported type of input..."))
                output <- return $ case outputopts of
                                        [] -> ""
                                        ((POOutput s):_) -> s
                                        _ -> error "wierd entry for output..."
                -- determine output type from parameter or filename
                outputtype <-
                        case outputtypeopts of
                                [] ->
                                        do
                                        when
                                                dodebug
                                                (putStrLn
                                                        "No Output-Type given. Trying to find out..."
                                                )
                                        mft <- return $ fileType output
                                        case mft of
                                                (Just ft) -> return ft
                                                Nothing ->
                                                        if (length output) == 0 then
                                                                        return FTNone
                                                                else
                                                                        ioError
                                                                                (userError "Cannot determine Output-Type!")
                                ((POOutputType s):_) -> return $ read s
                                _ -> error "wierd entry for outputtype..."
                when
                        dodebug
                        (putStrLn ("Output-Type is : " ++ (show outputtype)))
                -- check if this type is supported
                unless
                        (elem outputtype supportedOutput)
                        (ioError (userError "Unsupported type of output..."))
                when
                        dodebug
                        (putStrLn ("Include-Paths: " ++ (show searchpath)))
                sandbox <- return $ case alloutopts of
                        [] -> ""
                        ((POSandbox s):_) -> s
                        _ -> error "wierd entry for sandbox..."
                when
                        dodebug
                        (putStrLn ("Sandbox set to : \"" ++ sandbox++ "\""))  
                doshow <- return $ (length showgraphopts) /= 0
                when
                        dodebug
                        (putStrLn ("Graph-Output : " ++ (if doshow then "Yes" else "No"))) 
                dtduri <- return $ case dtduriopts of
                        [] -> defaultDTDURI
                        ((PODTDURI s):_) -> s
                        _ -> error "wierd entry for dtduri..."
                when
                        (dodebug && disabledtd)
                        (putStrLn "DTD-Output disabled...")
                when
                        dodebug
                        (
                                (putStrLn ("Debug-Keys : " ++ (show (dbgKeys finaldbginf)))) >>
                                (putStrLn ("Disabled-Keys : " ++ (show (dbgDisKeys finaldbginf))))
                        )
                when
                        dodebug
                        (putStrLn
                                ((show inputtype) ++ "(" ++ input ++ ") -> "
                                        ++ (show outputtype) ++ "(" ++ output ++ ")"))
                -- get input
                (ln, dg, lenv) <-
                        case ((\inty -> case inty of FTFullEnv -> FTEnv; _ -> inty) inputtype) of
                                FTOMDoc ->
                                                do
                                                when dodebug (putStrLn ("Trying to load omdoc-file..."))
                                                ig <- makeImportGraphFullXml globalOptions input searchpath
                                                (return $ dGraphGToLibEnvOmdocId globalOptions $
                                                        hybridGToDGraphG globalOptions $
                                                                processImportGraphXN globalOptions ig)
--                                                      (if newinput then processImportGraphXN else processImportGraph) globalOptions ig)
                                FTCASL->
                                                do
                                                when dodebug (putStrLn ("Trying to load casl-file..."))
                                                menv <- Hets.runLib (headorempty searchpath) input
                                                (ln' ,lenv' ) <- case menv of
                                                        Nothing ->
                                                                ioError
                                                                        (userError "Could not load CASL-File...")
                                                        (Just env) -> return env
                                                dg <- case Map.lookup ln' lenv' of
                                                        Nothing ->
                                                                ioError
                                                                        (userError "Could not get DGraph...")
                                                        (Just gc) -> return $ devGraph gc
                                                return (ln' ,dg,lenv' )
                                FTEnv ->
                                                {- -- currently environment processing is done in one
                                                -- section to handle full and non-full environments
                                                -- this may change... -}
                                                -- disabled FullEnvironment-Support while integrating
                                                -- Hets-based environment I/O. Will disappear likely...
                                                do
                                                when dodebug (putStrLn "Trying to load env-file...")
                                                s <- readFile input
                                                -- parse input for both variants (lazy)
{-                                              (Result.Result _ menv) <-
                                                        return
                                                                ((Hets.fromShATermString s)::(Result.Result (ASL.LIB_NAME, LibEnv)))
                                                (Result.Result _ mgc) <-
                                                        return
                                                                ((Hets.fromShATermString s)::(Result.Result GlobalContext)) -}
                                                (Result.Result _ mlngc) <-
                                                        return
                                                                ((Hets.fromShATermString s)::(Result.Result (ASL.LIB_NAME, GlobalContext)))
                                                -- parser will use error if it is not it's type...
{-                                              (Control.Exception.catch
                                                        (
                                                                do
                                                                when
                                                                        dodebug
                                                                        (putStr "...as full environment...")
                                                                (return menv) >>= \x -> case x of
                                                                        (Just me) -> return me >>=  
                                                                                \me' @(_, melenv) ->
                                                                                do
                                                                                         -- evaluate to trigger error
                                                                                        _ <- return $! Map.size $! melenv
                                                                                        return $ lnLibEnvToLnDGLibEnv me' 
                                                                        Nothing ->
                                                                                error "Error processing environment..."
                                                        )
                                                        (\_ ->
                                                                -- if the first parser triggers this exception
                                                                -- the next parser tries the other variant -}
                                                r <- (Control.Exception.catch
                                                        (
                                                        do
{-                                                                      when
                                                                dodebug
                                                                (putStr
                                                                        "...as globalcontext...") -}
                                                        (return mlngc) >>= \x -> case x of
                                                                (Just (ln,gc)) ->
                                                                                do
                                                                                        {-lname <-
                                                                                                return
                                                                                                        (fileToLibName Hets.dho input) -}
                                                                                         -- evaluate to trigger error
                                                                                        _ <-
                                                                                                return $! Graph.nodes $!
                                                                                                        (devGraph gc)
                                                                                        return
                                                                                                (ln, --lname,
                                                                                                (devGraph gc),
                                                                                                (Map.fromList
                                                                                                        [(ln, gc)]
                                                                                                        )
                                                                                                )
                                                                Nothing -> error "Error processing environment..."
                                                        )
                                                        (\_ ->
                                                                -- if this exception is triggered, no parser
                                                        -- was able to process the file...
                                                                when
                                                                dodebug
                                                                (putStrLn "failed.")
                                                        >> ioError
                                                                (userError
                                                                        "Unable to process env-file..."
                                                                )
                                                        )
                                                        ) >>= \e -> -- one of the parsers succeeded
                                                                when
                                                                        dodebug
                                                                        (putStrLn "...success.")
                                                                >> return e
                                                return r
                                _ -> -- no input (?)
                                                do
                                                ioError (userError "No input to process...")
                when dodebug
                        (putStrLn ("Theories in input : " ++ (show $ Set.map snd $ Hets.getNodeNames dg)))
                when doshow
                                (when dodebug (putStrLn "Showing Graph...") >>
                                showdg (ln,lenv))
                case outputtype of
                        FTOMDoc ->
                                do
                                when dodebug (putStrLn ("Outputting OMDoc..."))
                                omdoc <- devGraphToOmdocCMPIOXN globalOptions dg (stripLibName (show ln))
--                              omdoc <- (if newoutput then devGraphToOmdocCMPIOXN else devGraphToOmdocCMPIO) globalOptions dg (stripLibName (show ln))
                                case output of
                                        "" -> return ()
                                                -- show/writeOmdocDTD :: IO XmlTrees --> return ()
                                        "-" -> (if disabledtd then showOmdoc else showOmdocDTD dtduri) omdoc >> return ()
                                        _ -> (if disabledtd then writeOmdoc else writeOmdocDTD dtduri) omdoc output >> return ()
                                case sandbox of
                                        "" -> return ()
                                        _ ->
                                                        let
                                                                igdg = libEnvToDGraphG (ln,dg,lenv)
                                                        in
                                                                do
                                                                        igx <- dGraphGToXmlGXN igdg
                                                                        writeXmlG dtduri igx sandbox
                        FTEnv -> -- on output separate functions are used for environment
                                do
                                when dodebug (putStrLn ("Outputting Environment..."))
                                ga <- case Map.lookup ln lenv of
                                        Nothing -> ioError (userError "Lookup failed...")
                                        (Just ga' ) -> return ga'
                                case output of
                                        "" -> return ()
                                        "-" ->
                                                Hets.toShATermString (ln,ga) >>= putStrLn
                                        _ ->
                                                Hets.writeShATermFileSDoc output (ln,ga)
                        {-FTFullEnv ->
                                do
                                when debug (putStrLn ("Outputting Full Environment..."))
                                case output of
                                        "" -> return ()
                                        "-" ->
                                                Hets.toShATermString (ln,lenv) >>= putStrLn
                                        _ ->
                                                Hets.writeShATermFile output (ln,lenv)-}
                        _ ->
                                return ()
                return ()
                
lnLibEnvToLnDGLibEnv::(ASL.LIB_NAME, LibEnv)->(ASL.LIB_NAME, DGraph, LibEnv)
lnLibEnvToLnDGLibEnv (ln,lenv) =
        let
                dg = case Map.lookup ln lenv of
                        (Just gc) -> devGraph gc
                        Nothing -> error "Cannot lookup DGraph in LibEnv!"
        in
                (ln, dg, lenv)
                
-- not used in program (for ghci)               
libEnvFromOmdocFile::GlobalOptions->String->[String]->IO (ASL.LIB_NAME, DGraph, LibEnv)
libEnvFromOmdocFile go f l = makeImportGraphFullXml go f l >>= return . dGraphGToLibEnv go . hybridGToDGraphG go . processImportGraphXN go

-- not used in program (for ghci)
-- | loads an omdoc-file and returns it even if there are errors
-- fatal errors lead to IOError
loadOmdoc ::String->(IO HXT.XmlTrees)
loadOmdoc f =
        do
                tree <- (
                        HXT.run' $
                        HXT.parseDocument
                                [
                                         (a_source, f)
                                        ,(a_validate, v_0) -- validation is nice, but HXT does not give back even a partial document then...
                                        ,(a_check_namespaces,v_1) -- needed,really...
                                        ,(a_issue_errors, v_0)
                                ]
                                emptyRoot
                        )
                status <- return ( (
                        read $
                        xshow $
                        applyXmlFilter (getValue "status") tree
                        ) :: Int )
                if status <= HXT.c_err
                        then
                                return $ applyXmlFilter (getChildren .> isTag "omdoc") tree
                                                
                        else
                                ioError $ userError ("Error loading \"" ++ f ++ "\"")

stripLibName::String->String
stripLibName s = implode "." $ initorall $ explode "."  $ last $ explode "/" s
                        
-- | shows a developement-graph and it's environment using the
-- uniform-workbench                    
showdg::(ASL.LIB_NAME, LibEnv)->IO ()
showdg (ln,lenv) =
        -- dho is 'defaultHetcatsOpts' (not visible here)...
        Hets.showGraph "" Hets.dho (Just (ln, lenv))

