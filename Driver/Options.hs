{-|
Module      :  $Header$
Copyright   :  (c) Martin Kühl, Christian Maeder, Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

Datatypes for options that hets understands.
   Useful functions to parse and check user-provided values.
-}

module Driver.Options
    ( defaultHetcatsOpts
    , showDiags
    , showDiags1
    , guess
    , existsAnSource
    , downloadExtensions
    , rmSuffix
    , checkUri
    , checkRecentEnv
    , checkEitherDirOrExFile
    , doIfVerbose
    , putIfVerbose
    , hetcatsOpts
    , hasEnvOut
    , addEnvOut
    , HetcatsOpts(..)
    , GuiType(..)
    , InType(..)
    , AnaType(..)
    , RawOpt(..)
    , OutType(..)
    , HetOutFormat(..)
    , HetOutType(..)
    , PrettyType(..)
    , ATType(..)
    , GraphType(..)
    , Flattening(..)
    ) where

import Driver.Version
import Common.Utils
import Common.Id
import Common.Result
import Common.Amalgamate

import System.Directory
import System.Environment
import System.Console.GetOpt
import System.IO.Error
import System.Exit

import Data.List

bracket :: String -> String
bracket s = "[" ++ s ++ "]"

-- use the same strings for parsing and printing!
verboseS, intypeS, outtypesS, rawS, skipS, structS,
     guiS, onlyGuiS, libdirS, outdirS, amalgS, specS :: String

verboseS = "verbose"
intypeS = "input-type"
outtypesS = "output-types"
rawS = "raw"
skipS = "just-parse"
structS = "just-structured"
guiS = "gui"
onlyGuiS = "only-gui"
libdirS = "hets-libdir"
outdirS = "output-dir"
amalgS = "casl-amalg"
specS = "spec"

asciiS, latexS, textS, texS :: String
asciiS = "ascii"
latexS = "latex"
textS = "text"
texS = "tex"

genTermS, treeS, bafS, astS :: String
genTermS = "gen_trm"
treeS = "tree."
bafS = ".baf"
astS = "ast"

graphS, ppS, envS, naxS, thyS, comptableXmlS :: String
graphS = "graph."
ppS = "pp."
envS = "env"
naxS = ".nax"
thyS = "thy"
comptableXmlS = "comptable.xml"

showOpt :: String -> String
showOpt s = if null s then "" else " --" ++ s

showEqOpt :: String -> String -> String
showEqOpt k s = if null s then "" else showOpt k ++ "=" ++ s

-- main Datatypes --

-- | 'HetcatsOpts' is a record of all options received from the command line
data HetcatsOpts =        -- for comments see usage info
    HcOpt { analysis :: AnaType
          , gui      :: GuiType
          , infiles  :: [FilePath] -- files to be read
          , specNames :: [SIMPLE_ID] -- specs to be processed
          , intype   :: InType
          , libdir   :: FilePath
          , outdir   :: FilePath
          , outtypes :: [OutType]
          , rawopts  :: [RawOpt]
          , verbose  :: Int
          , defLogic :: String
          , outputToStdout :: Bool    -- flag: output diagnostic messages?
          , caslAmalg :: [CASLAmalgOpt]
          }

instance Show HetcatsOpts where
    show opts =  showEqOpt verboseS (show $ verbose opts)
                ++ show (gui opts)
                ++ show (analysis opts)
                ++ showEqOpt libdirS (libdir opts)
                ++ showEqOpt intypeS (show $ intype opts)
                ++ showEqOpt outdirS (outdir opts)
                ++ showEqOpt outtypesS (showOutTypes $ outtypes opts)
                ++ showEqOpt specS (joinWith ',' $ map show $ specNames opts)
                ++ showRaw (rawopts opts)
                ++ showEqOpt amalgS ( tail $ init $ show $
                                      case caslAmalg opts of
                                      [] -> [NoAnalysis]
                                      l -> l)
                ++ " " ++ showInFiles (infiles opts)
        where
        showInFiles  = joinWith ' '
        showOutTypes = joinWith ',' . map show
        showRaw = joinWith ' ' . map show

-- | 'makeOpts' includes a parsed Flag in a set of HetcatsOpts
makeOpts :: HetcatsOpts -> Flag -> HetcatsOpts
makeOpts opts flg = case flg of
    Analysis x -> opts { analysis = x }
    Gui x      -> opts { gui = x }
    InType x   -> opts { intype = x }
    LibDir x   -> opts { libdir = x }
    OutDir x   -> opts { outdir = x }
    OutTypes x -> opts { outtypes = x }
    Specs x    -> opts { specNames = x }
    Raw x      -> opts { rawopts = x }
    Verbose x  -> opts { verbose = x }
    DefaultLogic x -> opts { defLogic = x }
    CASLAmalg x   -> opts { caslAmalg = x }
    Quiet         -> opts { verbose = 0 }
    Help          -> opts -- skipped
    Version       -> opts -- skipped

-- | 'defaultHetcatsOpts' defines the default HetcatsOpts, which are used as
-- basic values when the user specifies nothing else
defaultHetcatsOpts :: HetcatsOpts
defaultHetcatsOpts =
    HcOpt { analysis = Basic
          , gui      = Not
          , infiles  = []
          , specNames = []
          , intype   = GuessIn
          , libdir   = ""
          , outdir   = ""
          , outtypes = [defaultOutType]
          -- better default options, but not implemented yet:
          --, outtypes = [HetCASLOut OutASTree OutXml]
          , rawopts  = []
          , defLogic = "CASL"
          , verbose  = 1
          , outputToStdout = True
          , caslAmalg = [Cell]
          }

defaultOutType :: OutType
defaultOutType = PrettyOut PrettyAscii

-- | every 'Flag' describes an option (see usage info)
data Flag = Verbose  Int
          | Quiet
          | Version
          | Help
          | Gui      GuiType
          | Analysis AnaType
          | DefaultLogic String
          | InType   InType
          | LibDir   FilePath
          | OutDir   FilePath
          | OutTypes [OutType]
          | Specs    [SIMPLE_ID]
          | Raw      [RawOpt]
          | CASLAmalg [CASLAmalgOpt]

-- | 'AnaType' describes the type of analysis to be performed
data AnaType = Basic | Structured | Skip

instance Show AnaType where
    show a = case a of
             Basic -> ""
             Structured -> showOpt structS
             Skip -> showOpt skipS

-- | 'GuiType' determines if we want the GUI shown
data GuiType = Only | Also | Not

instance Show GuiType where
    show g = case g of
             Only -> showOpt onlyGuiS
             Also -> showOpt guiS
             Not  -> ""

-- | 'InType' describes the type of input the infile contains
data InType = ATermIn ATType | ASTreeIn ATType | CASLIn | HetCASLIn | OWL_DLIn
            | HaskellIn | GuessIn

instance Show InType where
    show i = case i of
             ATermIn at -> genTermS ++ show at
             ASTreeIn at -> astS ++ show at
             CASLIn -> "casl"
             HetCASLIn -> "het"
             OWL_DLIn -> "owl"
             HaskellIn -> "hs"
             GuessIn -> ""

-- maybe this optional tree prefix can be omitted
instance Read InType where
    readsPrec _ s = let f = filter ( \ o -> (case o of
                                 ATermIn _ -> isPrefixOf (treeS ++ show o) s
                                 _ -> False) || isPrefixOf (show o) s)
                            (plainInTypes ++ aInTypes)
                        in case f of
                           [] -> []
                           t : _ -> [(t, drop (length (show t) +
                                             case t of
                                             ATermIn _ -> if isPrefixOf treeS s
                                               then length treeS else 0
                                             _ -> 0) s)]

-- | 'ATType' describes distinct types of ATerms
data ATType = BAF | NonBAF

instance Show ATType where
    show a = case a of BAF -> bafS
                       NonBAF -> ""

plainInTypes :: [InType]
plainInTypes = [CASLIn, HetCASLIn, OWL_DLIn, HaskellIn]

aInTypes :: [InType]
aInTypes = [ f x | f <- [ASTreeIn, ATermIn], x <- [BAF, NonBAF] ]

-- | 'OutType' describes the type of outputs that we want to generate
data OutType = PrettyOut PrettyType
             | HetCASLOut HetOutType HetOutFormat
             | GraphOut GraphType
             | EnvOut
             | ThyFile -- isabelle theory file
             | ComptableXml

instance Show OutType where
    show o = case o of
             PrettyOut p -> ppS ++ show p
             HetCASLOut h f -> show h ++ "." ++ show f
             GraphOut f -> graphS ++ show f
             EnvOut -> envS
             ThyFile -> thyS
             ComptableXml -> comptableXmlS

instance Read OutType where
    readsPrec  _ s = if isPrefixOf ppS s then
        case reads $ drop (length ppS) s of
                 [(p, r)] -> [(PrettyOut p, r)]
                 _ -> hetsError (s ++ " expected one of " ++ show prettyList)
        else if isPrefixOf graphS s then
        case reads $ drop (length graphS) s of
                 [(t, r)] -> [(GraphOut t, r)]
                 _ -> hetsError (s ++ " expected one of " ++ show graphList)
        else if isPrefixOf envS s then
             [(EnvOut, drop (length envS) s)]
        else if isPrefixOf thyS s then
             [(ThyFile, drop (length thyS) s)]
        else if isPrefixOf comptableXmlS s then
             [(ComptableXml, drop (length comptableXmlS) s)]
        else [(HetCASLOut h f, u) | (h, d : t) <- reads s,
              d == '.' , (f, u) <- reads t]

-- | 'PrettyType' describes the type of output we want the pretty-printer
-- to generate
data PrettyType = PrettyAscii | PrettyLatex | PrettyHtml

instance Show PrettyType where
    show p = case p of
             PrettyAscii -> "het"
             PrettyLatex -> "tex"
             PrettyHtml -> "html"

instance Read PrettyType where
    readsPrec _ = readShow prettyList

prettyList :: [PrettyType]
prettyList = [PrettyAscii,  PrettyLatex, PrettyHtml]

-- | 'HetOutType' describes the type of Output we want Hets to create
data HetOutType = OutASTree | OutDGraph Flattening Bool

instance Show HetOutType where
    show h = case h of
             OutASTree -> astS
             OutDGraph f b -> show f ++ "dg" ++ if b then naxS else ""

instance Read HetOutType where
    readsPrec _ s = if isPrefixOf astS s then
                    [(OutASTree, drop (length astS) s)]
                    else case readShow outTypeList s of
                    l@[(OutDGraph f _, r)] -> if isPrefixOf naxS r then
                             [(OutDGraph f True, drop (length naxS) r)]
                             else l
                    _ -> hetsError (s ++ " is not a valid OTYPE")

outTypeList :: [HetOutType]
outTypeList = [ OutDGraph f False | f <- [ Flattened, HidingOutside, Full]]

-- | 'Flattening' describes how flat the Earth really is (TODO: add comment)
data Flattening = Flattened | HidingOutside | Full

instance Show Flattening where
    show f = case f of
             Flattened -> "f"
             HidingOutside -> "h"
             Full -> ""

-- | 'HetOutFormat' describes the format of Output that HetCASL shall create
data HetOutFormat = OutAscii | OutTerm | OutTaf | OutHtml | OutXml

instance Show HetOutFormat where
    show f = case f of
             OutAscii -> "het"
             OutTerm -> "trm"
             OutTaf -> "taf"
             OutHtml -> "html"
             OutXml -> "xml"

instance Read HetOutFormat where
    readsPrec _ = readShow formatList

formatList :: [HetOutFormat]
formatList = [OutAscii, OutTerm, OutTaf, OutHtml, OutXml]

-- | 'GraphType' describes the type of Graph that we want generated
data GraphType = Dot | PostScript | Davinci

instance Show GraphType where
    show g = case g of
             Dot -> "dot"
             PostScript -> "ps"
             Davinci -> "davinci"

instance Read GraphType where
    readsPrec _ = readShow graphList

graphList :: [GraphType]
graphList = [Dot, PostScript, Davinci]

-- | 'RawOpt' describes the options we want to be passed to the Pretty-Printer
data RawOpt = RawAscii String | RawLatex String

instance Show RawOpt where
    show r = case r of
             RawAscii s -> showRawOpt asciiS s
             RawLatex s -> showRawOpt latexS s
             where showRawOpt f = showEqOpt (rawS ++ "=" ++ f)

-- | 'options' describes all available options and is used to generate usage
-- information
options :: [OptDescr Flag]
options =
    [ Option ['v'] [verboseS] (OptArg parseVerbosity "Int")
      "set verbosity level, -v1 is the default"
    , Option ['q'] ["quiet"] (NoArg Quiet)
      "same as -v0, no output at all to stdout"
    , Option ['V'] ["version"] (NoArg Version)
      "print version number and exit"
    , Option ['h'] ["help", "usage"] (NoArg Help)
      "print usage information and exit"
    , Option ['g'] [guiS] (NoArg (Gui Also))
      "show graphical output in a GUI window"
    , Option ['G'] [onlyGuiS] (NoArg $ Gui Only)
      "like -g but write no output files"
    , Option ['p'] [skipS]  (NoArg $ Analysis Skip)
      "skip static analysis, just parse"
    , Option ['s'] [structS]  (NoArg $ Analysis Structured)
      "skip basic, just do structured analysis"
    , Option ['l'] ["logic"] (ReqArg DefaultLogic "LOGIC")
      "choose initial logic, the default is CASL"
    , Option ['L'] [libdirS]  (ReqArg LibDir "DIR")
      "source directory of [Het]CASL libraries"
    , Option ['i'] [intypeS]  (ReqArg parseInType "ITYPE")
      ("input file type can be one of:" ++ crS ++ joinBar
       (map show plainInTypes ++
        map (++ bracket bafS) [astS, bracket treeS ++ genTermS]))
    , Option ['O'] [outdirS]  (ReqArg OutDir "DIR")
      "destination directory for output files"
    , Option ['o'] [outtypesS] (ReqArg parseOutTypes "OTYPES")
      ("output file types, default " ++ show defaultOutType ++ "," ++ crS ++
       listS ++ crS ++ bS ++ envS ++ crS ++ bS ++
       thyS ++ crS ++ bS ++ comptableXmlS ++ crS ++ bS ++
       ppS ++ joinBar (map show prettyList) ++ crS ++ bS ++
       graphS ++ joinBar (map show graphList) ++ crS ++ bS ++
       astS ++ formS ++ crS ++ bS ++
       joinBar (map show outTypeList) ++ bracket naxS ++ formS)
    , Option ['n'] [specS] (ReqArg parseSpecOpts "SPECS")
      ("process specs option " ++ crS ++ listS ++ " SIMPLE-ID")
    , Option ['r'] [rawS] (ReqArg parseRawOpts "RAW")
      ("raw options for pretty printing" ++ crS ++ "RAW is "
       ++ joinBar [asciiS, textS, latexS, texS]
       ++ "=STRING where " ++ crS ++
       "STRING is passed to the appropriate printer")
    , Option ['a'] [amalgS] (ReqArg parseCASLAmalg "ANALYSIS")
      ("CASL amalgamability analysis options" ++ crS ++ listS ++
       crS ++ joinBar (map show caslAmalgOpts))
    ] where listS = "is a comma-separated list without blanks"
                    ++ crS ++ "of one or more from:"
            crS = "\n  "
            bS = "| "
            joinBar l = "(" ++ joinWith '|' l ++ ")"
            formS = '.' : joinBar (map show formatList)

-- parser functions returning Flags --

-- | 'parseVerbosity' parses a 'Verbose' Flag from user input
parseVerbosity :: (Maybe String) -> Flag
parseVerbosity Nothing = Verbose 2
parseVerbosity (Just s)
    = case reads s of
                   [(i,"")] -> Verbose i
                   _        -> hetsError (s ++ " is not a valid INT")

-- | intypes useable for downloads
downloadExtensions :: [String]
downloadExtensions = map ('.' :) $ 
         map show plainInTypes
         ++ map ((treeS ++) . show) [ATermIn BAF, ATermIn NonBAF]
         ++ map show aInTypes
         
-- | remove the extension from a file
rmSuffix :: FilePath -> FilePath
rmSuffix = fst . stripSuffix downloadExtensions

-- |
-- checks if a source file for the given file name exists
existsAnSource :: HetcatsOpts -> FilePath -> IO (Maybe FilePath)
existsAnSource opts file = do
       let base = rmSuffix file 
           exts = case intype opts of 
                  GuessIn -> downloadExtensions
                  e@(ATermIn _) -> ['.' : show e, '.' : treeS ++ show e]
                  e -> ['.' : show e]
           names = map (base ++) $ exts
       -- look for the first existing file
       validFlags <- mapM checkInFile names
       return (find fst (zip validFlags names) >>= (return . snd))

-- | should env be written
hasEnvOut :: HetcatsOpts -> Bool
hasEnvOut = any ( \ o -> case o of EnvOut -> True
                                   _ -> False) . outtypes

-- | add EnvOut option for imported libraries
addEnvOut :: HetcatsOpts -> HetcatsOpts
addEnvOut opts = if hasEnvOut opts then opts else
                 opts { outtypes = EnvOut : outtypes opts }

-- |
-- gets two Paths and checks if the first file is more recent than the
-- second one
checkRecentEnv :: HetcatsOpts -> FilePath -> FilePath -> IO Bool
checkRecentEnv opts fp1 base2 =
   do fp1_valid <- checkInFile fp1
      if not fp1_valid then return False
       else do
        maybe_source_file <- existsAnSource opts base2
        maybe (return False)
             (\ fp2 ->     do fp1_time <- getModificationTime fp1
                              fp2_time <- getModificationTime fp2
                              return (fp1_time > fp2_time))
             maybe_source_file

-- |
-- gets a FilePath and checks whether it is a directory or an executable File;
-- * Just True: it is a dir
--
-- * Just False: it is an executable file
--
-- * Nothing: it is nothing of the two above
--
-- /Warning: Not compatible with GUI.hets_cgi.hs/
checkEitherDirOrExFile :: FilePath -> IO (Maybe Bool)
checkEitherDirOrExFile fp =
    do isDir <- doesDirectoryExist fp
       (isRead,isExec,isSearch) <- catch getPerms errs
       return (if isDir && isSearch && isRead
               then Just True
               else if isRead && isExec
                    then Just False
                    else Nothing)
    where getPerms = do p <- getPermissions fp
                        return (readable p,
                                executable p,
                                searchable p)
          errs ex
               | isPermissionError ex ||
                 isDoesNotExistError ex = return (False,False,False)
               | otherwise = ioError ex

-- | 'parseInType' parses an 'InType' Flag from user input
parseInType :: String -> Flag
parseInType = InType . parseInType1


-- | 'parseInType1' parses an 'InType' Flag from a String
parseInType1 :: String -> InType
parseInType1 str =
  case reads str of
    [(t, "")] -> t
    _ -> hetsError (str ++ " is not a valid ITYPE")
      {- the mere typo read instead of reads caused the runtime error:
         Fail: Prelude.read: no parse -}

-- 'parseOutTypes' parses an 'OutTypes' Flag from user input
parseOutTypes :: String -> Flag
parseOutTypes str = case reads $ bracket str of
    [(l, "")] -> OutTypes l
    _ -> hetsError (str ++ " is not a valid OTYPES")

-- | 'parseSpecOpts' parses a 'Specs' Flag from user input
parseSpecOpts :: String -> Flag
parseSpecOpts s = Specs $ map mkSimpleId $ splitOn ',' s

-- | 'parseRawOpts' parses a 'Raw' Flag from user input
parseRawOpts :: String -> Flag
parseRawOpts s =
    let (prefix, string) = break (== '=') s
        parsePrefix p = if p `elem` [asciiS, textS] then RawAscii
                        else if p `elem` [latexS, texS] then RawLatex
                        else hetsError (s ++ " is not a valid RAW String")
    in Raw [(parsePrefix prefix) (drop 1 string)]

-- | guesses the InType
guess :: String -> InType -> InType
guess file GuessIn = guessInType file
guess _file itype  = itype

-- | 'guessInType' parses an 'InType' from the FilePath to our 'InFile'
guessInType :: FilePath -> InType
guessInType file =
    case fileparse downloadExtensions file of
      (_,_,Just ('.' : suf)) -> parseInType1 suf
      (_,_,_)  -> GuessIn

-- | 'parseCASLAmalg' parses CASL amalgamability options
parseCASLAmalg :: String -> Flag
parseCASLAmalg str =
    case reads $ bracket str of
    [(l, "")] -> CASLAmalg $ filter ( \ o -> case o of
                                      NoAnalysis -> False
                                      _ -> True ) l
    _ -> hetsError (str ++
                    " is not a valid CASL amalgamability analysis option list")

-- main functions --

-- | 'hetcatsOpts' parses sensible HetcatsOpts from ARGV
hetcatsOpts :: [String] -> IO HetcatsOpts
hetcatsOpts argv =
  let argv' = filter (not . isUni) argv
      isUni s = take 5 s == "--uni"
   in case (getOpt Permute options argv') of
        (opts,non_opts,[]) ->
            do flags <- checkFlags opts
               infs  <- checkInFiles non_opts
               hcOpts <- return $
                         foldr (flip makeOpts) defaultHetcatsOpts flags
               let hcOpts' = hcOpts { infiles = infs }
               seq (length $ show hcOpts') $ return $ hcOpts'
        (_,_,errs) -> hetsError (concat errs)

-- | 'checkFlags' checks all parsed Flags for sanity
checkFlags :: [Flag] -> IO [Flag]
checkFlags fs =
    let collectFlags = (collectDirs
                        . collectOutTypes
                        . collectVerbosity
                        . collectRawOpts
                        . collectSpecOpts
                        -- collect some more here?
                   )
    in do if not $ null [ () | Help <- fs]
             then do putStrLn hetsUsage
                     exitWith ExitSuccess
             else return [] -- fall through
          if not $ null [ () | Version <- fs]
             then do putStrLn ("version of hets: " ++ hetcats_version)
                     exitWith ExitSuccess
             else return [] -- fall through
          fs' <- collectFlags fs
          return fs'

-- | 'checkInFiles' checks all given InFiles for sanity
checkInFiles :: [String] -> IO [FilePath]
checkInFiles fs =
       case fs of
                []  -> hetsError "No valid input file specified"
                _  -> do
                   let ifs = filter (not . checkUri) fs
                       efs = filter hasExtension ifs
                       hasExtension f = any ( \ e -> isSuffixOf e f)
                                        downloadExtensions
                   bs <- mapM checkInFile efs
                   if and bs
                      then return fs
                      else hetsError $ "invalid input files: " ++
                        (unwords $ map snd $ filter (not . fst) $ zip bs efs)

-- auxiliary functions: FileSystem interaction --

-- | 'checkInFile' checks a single InFile for sanity
checkInFile :: FilePath -> IO Bool
checkInFile file =
    do exists <- doesFileExist file
       perms  <- catch (getPermissions file) (\_ -> return noPerms)
       return $ exists && readable perms

-- | check if infile is uri
checkUri :: FilePath -> Bool
checkUri file = let (_, t) = span (/=':') file in
                   if length t < 4 then False
                      else let (_:c2:c3:_) = t in
                              if c2 == '/' && c3 == '/' then True
                              -- (http://, https://, ftp://, file://, etc.)
                                 else False

-- | 'checkOutDirs' checks a list of OutDir for sanity
checkOutDirs :: [Flag] -> IO [Flag]
checkOutDirs fs = do
    case fs of
        [] -> return ()
        [f] -> checkOutDir f
        _ -> hetsError
            "Only one output directory may be specified on the command line"
    return fs

-- | 'checkLibDirs' checks a list of LibDir for sanity
checkLibDirs :: [Flag] -> IO [Flag]
checkLibDirs fs = do
    case fs of
        [] -> do
            s <- catch (getEnv "HETS_LIB") (const $ return "")
            if null s then return [] else do
                let d = LibDir s
                checkLibDir d
                return [d]
        [f] -> checkLibDir f >> return fs
        _ -> hetsError
            "Only one library directory may be specified on the command line"

-- | 'checkLibDir' checks a single LibDir for sanity
checkLibDir :: Flag -> IO ()
checkLibDir (LibDir file) =
    do exists <- doesDirectoryExist file
       perms  <- catch (getPermissions file) (\_ -> return noPerms)
       if exists && readable perms then return ()
          else hetsError $ "Not a valid library directory: " ++ file
checkLibDir _ = return ()

-- | 'checkOutDir' checks a single OutDir for sanity
checkOutDir :: Flag -> IO ()
checkOutDir (OutDir file) =
    do exists <- doesDirectoryExist file
       perms  <- catch (getPermissions file) (\_ -> return noPerms)
       if exists && writable perms then return ()
          else hetsError $ "Not a valid output directory: " ++ file
checkOutDir _ = return ()


-- Nil Permissions. Returned, if an Error occurred in FS-Interaction
noPerms :: Permissions
noPerms = Permissions { readable = False
                      , writable = False
                      , executable = False
                      , searchable = False
                      }

-- auxiliary functions: collect flags --

collectDirs :: [Flag] -> IO [Flag]
collectDirs fs =
    let (ods,fs') = partition isOutDir fs
        (lds,fs'') = partition isLibDir fs'
        isOutDir (OutDir _) = True
        isOutDir _          = False
        isLibDir (LibDir _) = True
        isLibDir _          = False
    in do ods' <- checkOutDirs ods
          lds' <- checkLibDirs lds
          return $ ods' ++ lds' ++ fs''

collectVerbosity :: [Flag] -> [Flag]
collectVerbosity fs =
    let (vs,fs') = partition isVerb fs
        verbosity = (sum . map (\(Verbose x) -> x)) vs
        isVerb (Verbose _) = True
        isVerb _           = False
        vfs = Verbose verbosity : fs'
    in if not $ null [() | Quiet <- fs'] then Verbose 0 : fs' else
       if null vs then Verbose 1 : fs' else vfs

collectOutTypes :: [Flag] -> [Flag]
collectOutTypes fs =
    let (ots,fs') = partition isOType fs
        isOType (OutTypes _) = True
        isOType _            = False
        otypes = foldl concatOTypes [] ots
        concatOTypes = (\os (OutTypes ot) -> os ++ ot)
    in if null otypes || not (null [() | Gui Only <- fs'])
        then fs'
        else ((OutTypes otypes):fs')

collectRawOpts :: [Flag] -> [Flag]
collectRawOpts fs =
    let (rfs,fs') = partition isRawOpt fs
        isRawOpt (Raw _) = True
        isRawOpt _       = False
        raws = foldl concatRawOpts [] rfs
        concatRawOpts = (\os (Raw ot) -> os ++ ot)
    in if (null raws) then fs' else ((Raw raws):fs')

collectSpecOpts :: [Flag] -> [Flag]
collectSpecOpts fs =
    let (rfs,fs') = partition isSpecOpt fs
        isSpecOpt (Specs _) = True
        isSpecOpt _       = False
        specs = foldl concatSpecOpts [] rfs
        concatSpecOpts = (\os (Specs ot) -> os ++ ot)
    in if null specs then fs' else (Specs specs : fs')

-- auxiliary functions: error messages --

-- | 'hetsError' is a generic Error messaging function that prints the Error
-- and usage information, if the user caused the Error
hetsError :: String -> a
hetsError errorString = error (errorString ++ "\n" ++ hetsUsage)

-- | 'hetsUsage' generates usage information for the commandline
hetsUsage :: String
hetsUsage = usageInfo header options
    where header = "Usage: hets [OPTION...] file ... file"

-- | 'putIfVerbose' prints a given String to StdOut when the given HetcatsOpts'
-- Verbosity exceeds the given level
putIfVerbose :: HetcatsOpts -> Int -> String -> IO ()
putIfVerbose opts level str =
    if outputToStdout opts
       then doIfVerbose opts level (putStrLn str)
    else return()

-- | 'doIfVerbose' executes a given function when the given HetcatsOpts'
-- Verbosity exceeds the given level
doIfVerbose :: HetcatsOpts -> Int -> (IO ()) -> IO ()
doIfVerbose opts level func =
    if (verbose opts) >= level then func
        else return ()

-- | show diagnostic messages (see Result.hs), according to verbosity level
showDiags :: HetcatsOpts -> [Diagnosis] -> IO()
showDiags opts ds = do
    ioresToIO $ showDiags1 opts $ resToIORes $ Result ds Nothing
    return ()

-- | show diagnostic messages (see Result.hs), according to verbosity level
showDiags1 :: HetcatsOpts -> IOResult a -> IOResult a
showDiags1 opts res = do
  if outputToStdout opts
     then do Result ds res' <- ioToIORes $ ioresToIO res
             ioToIORes $ sequence $ map (putStrLn . show) -- take maxdiags
                       $ filter (relevantDiagKind . diagKind) ds
             case res' of
               Just res'' -> return res''
               Nothing    -> resToIORes $ Result [] Nothing
     else res
  where relevantDiagKind Error = True
        relevantDiagKind Warning = (verbose opts) >= 2
        relevantDiagKind Hint = (verbose opts) >= 4
        relevantDiagKind Debug  = (verbose opts) >= 5
        relevantDiagKind MessageW = False
