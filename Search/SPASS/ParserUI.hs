{- |
Module      :  $Header$
Description :  Command line interface, reads dfg files and returns it normalized
Copyright   :  (c) Immanuel Normann, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  inormann@jacobs-university.de
Stability   :  provisional
Portability :  portable
-}
module Search.Main where

import Search.Common.Normalization
import Search.SPASS.DFGParser
import Search.SPASS.Sign
import Search.SPASS.FormulaWrapper
import System.Environment
import System.Directory
import System.Posix.Files
import System.IO
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Char
import MD5

main = do args <- getArgs
	  case args of (flag:path:outpath:_) -> do outHandle <- getHandle outpath
                                                   dispatch (getHandler flag) outHandle path
		       (flag:path:_) -> dispatch (getHandler flag) stdout path
		       ("-h":_) -> helpInfo
		       args -> putStrLn ("not a valid argument list: " ++ (concat args)) >> helpInfo

getHandler :: String -> ParseHandling -> IO ()
getHandler "-v" = validate
getHandler "-p" = readAsSPProblem
getHandler "-w" = weightFormulas
getHandler "-a" = maxACIofFormule
getHandler "-n" = readAndNormalize
getHandler "-s" = createSqlInserts

getHandle :: FilePath -> IO Handle
getHandle path = do fileExists <- doesFileExist path
                    if fileExists
                      then do putStr ("file already exists. overwrite " ++ path ++ "? [y/N] ")
                              hFlush stdout
                              a <- getChar
                              case a of 'y' -> initHandle path
                                        _ -> error "aborted"
                      else initHandle path

initHandle :: FilePath -> IO Handle
initHandle path = do --writeFile path ("Parsing result of input " ++ path ++ "\n")
                     openFile path AppendMode

helpInfo :: IO ()
helpInfo = do putStrLn "dfg-parse -[vpn] <file-or-dir> [out-file] "
	      putStrLn ""
	      putStrLn "  [-v path]\tvalidate path"
	      putStrLn "  [-p path]\tparse path"
	      putStrLn "  [-w path]\tweight formulas in path"
	      putStrLn "  [-a path]\tmaximal number of args of an aci-operator "
	      putStrLn "  [-n path]\tparse path and normalize formulas"
	      putStrLn "  [-s path]\tparse path and normalize formulas and create SQL inserts from it"
	      putStrLn "  [-h]\t\tthis help info"
	      putStrLn "\nthe action is applied on the file if the path points to a file"
	      putStrLn "and to all files with suffix dfg if the path points to a directory."

dispatch :: (ParseHandling -> IO ()) -> Handle -> FilePath -> IO ()
dispatch action outHandle path =
    do st <- getFileStatus path
       if (isDirectory st)
         then do treatDir action outHandle path
                 hClose outHandle
         else if (isRegularFile st)
                then do treatFile action outHandle path
                        hClose outHandle
                else error (path ++ " is neither a file nor a directory")

treatDir :: (ParseHandling -> IO ()) -> Handle -> FilePath -> IO ()
treatDir action outHandle dir =
    do ls <- getDirectoryContents dir
       setCurrentDirectory dir
       mapM (treatFile action outHandle) (filter (isSuffixOf "dfg") ls)
       return () -- otherwise [()] would be returned which causes a type error in dispatch

treatFile :: (ParseHandling -> IO ()) -> Handle -> FilePath -> IO ()
treatFile action outHandle path =
    do putStr path
       result <- parseFromFile parseSPASS path
       case result of Left err  -> msgErr err
		      Right spproblem  -> do action (PH path outHandle spproblem)
                                             hFlush outHandle
                                             msgOk

data ParseHandling =
    PH { inputPath :: FilePath,
         output :: Handle,
         internal :: SPProblem
       } deriving Show

validate :: ParseHandling -> IO ()
validate _ = return ()

readAsSPProblem :: ParseHandling -> IO ()
readAsSPProblem ph = hPrint (output ph) (internal ph)

weightFormulas :: ParseHandling -> IO ()
weightFormulas ph = do {mapM showRecord spformulas; return ()}
    where showRecord spformula = putStrLn ("\nFormula: " ++ show (senName spformula) ++ "\tweight: " ++ show (weight spformula))
	  weight spformula = (count . wrapTerm . sentence) spformula
	  spformulas = getSPFormulas $ internal ph
	  count (Var _ fs) = 1 + (sum (map count fs))
	  count (Const _ fs) = 1 + (sum (map count fs))
	  count (Binder _ vars f) = 1 + (length vars) + (count f)

maxACIofFormule :: ParseHandling -> IO ()
maxACIofFormule ph = do {mapM showRecord spformulas; return ()}
    where showRecord spformula = putStrLn ("\nFormula: " ++ show (senName spformula) ++ "\tmax: " ++ show (weight spformula))
	  weight spformula = (maxACI . cnf . prenex . annotateScope . elemTrueFalse . wrapTerm . sentence) spformula
	  spformulas = getSPFormulas $ internal ph


readAndNormalize :: ParseHandling -> IO ()
readAndNormalize ph =  hPutStrLn (output ph) (concatMap record spterms)
    where spterms = getSPFormulas $ internal ph
          record = (formatNF . (normalizeSPFormula $ inputPath ph)) --  :: SPFormula -> String

createSqlInserts :: ParseHandling -> IO ()
createSqlInserts ph =  hPutStrLn (output ph) (concatMap record spterms)
    where spterms = getSPFormulas $ internal ph
          record = (sqlInsertNF . (normalizeSPFormula $ inputPath ph)) --  :: SPFormula -> String
{- a record of an spterm has the format:
     file-name       line  is-axiom  abstracted-formula     parameter                       length-of-abstraced-formula
eg:  Pelletier57.dfg 14    True      (0 (0 0 0) (0 0 0))    ["F","f","a","b","f","b","c"]   19
-}


-- helpers: ---------------------------------------------------------------

msgOk = putStrLn "\t... ok!"
msgErr err = hPutStrLn stderr ("\t ... failed!\nerror: " ++ show err)

{-md5s $ Str $ show nf
mysql> select * from formulas;
+--------+------+-------------+-------------+
| file   | line | md5         | sceleton    |
+--------+------+-------------+-------------+
| alg1   |   23 | 125kjhf9183 | a^2+b^2=c^2 |
| arith1 |   13 | 125kjhf9183 | x<5=>x6     |
+--------+------+-------------+-------------+
-}

sqlInsertNF (file,line,ax,spterm,abstractSPTerm,parameter,normalizationStrength,size) =
    ("insert into profile values (" ++ (entry $md5s $ Str $ show abstractSPTerm) ++
     (entry file) ++ (entry line) ++ (if ax then "'axiom'," else "'conjecture',") ++
     (entry $ show spterm)  ++ (entry $ show abstractSPTerm) ++ (entry $ show parameter) ++
     (entry normalizationStrength) ++ "'" ++ show size ++ "');\n")
	where entry e = "'" ++ e ++ "',"
--formatNF :: (String, String, Bool, Skeleton SpassConst, [SPIdentifier], Int) -> String
formatNF (file,line,ax,spterm,abstractSPTerm,parameter,normalizationStrength,size) =
    (file ++ "\t" ++ line ++ "\t" ++ show ax ++ "\t" ++ show spterm  ++ "\t" ++ show abstractSPTerm ++ "\t" ++ show parameter ++ "\t" ++ normalizationStrength ++ "\t" ++ show size ++ "\n")

showParams :: [[Char]] -> [Char]
showParams ps = "[" ++ (foldl sep "" ps) ++ "]"
    where sep a b = a ++ " " ++ b

normalizeSPFormula :: String -> SPFormula -> (String, String, Bool, SPTerm,Skeleton SpassConst, [SPIdentifier], String,Int)
normalizeSPFormula file (NamedSen line ax _ spterm) = (file,line,ax,spterm,abstractSPTerm,parameter,normalizationStrength,size)
    where (abstractSPTerm,parameter,normalizationStrength) = (normalize . wrapTerm) spterm
          size = length (show abstractSPTerm)

getSPFormulas :: SPProblem -> [SPFormula]
getSPFormulas spproblem = spformulas
    where (SPProblem _ _ (SPLogicalPart _ _ flsts) _) = spproblem
          spformulas = concatMap (\(SPFormulaList _ f) -> f) flsts

allFilesOfType suffix = do ls <- getDirectoryContents "./"
			   return (filter (isSuffixOf suffix) ls)

isSuffixOf suffix name = hasPrefix (reverse name) (reverse suffix)

hasPrefix (n:ns) (p:ps) = hasPrefix ns ps
hasPrefix ('.':_) [] = True
hasPrefix _ _ = False
