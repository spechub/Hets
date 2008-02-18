{- |
Module      :  $Header$
Description :  Main module to read dfg files into the database
Copyright   :  (c) Immanuel Normann, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  inormann@jacobs-university.de
Stability   :  provisional
Portability :  portable
-}
module Main where

--import Config
import Data.List as L
import Search.Common.Normalization
import Search.Common.Select -- (queryProfileMorphisms) 
import Search.SPASS.DFGParser
import Search.SPASS.Sign
import Search.SPASS.FormulaWrapper
import System.Directory
import System.IO
import Text.ParserCombinators.Parsec
import MD5
import Search.DB.Connection
import System.Environment (getArgs)

main = do args <- getArgs
          case args of
            ("search":file:_) -> searchDFG file >> return ()
            ("insert":lib:dir:file:_) -> indexFile lib dir file  >> return ()
            _ -> error "invalid arguments!\nShould be <library> <dir> <file>"

-- -----------------------------------------------------------
-- * Search
-- -----------------------------------------------------------

{- |
   searchDFG reads in a source theory from file and returns all possible profile morphisms
   from all matching target theories in the database.
-}
searchDFG :: SourceName -> IO [(String, [(Renaming SPIdentifier, LineMap)])]
searchDFG = search readProblemAxioms

{- |
   readProblemAxioms reads in from file a dfg problem and returns
   all axioms but removes duplicates and trivially true axioms.
-}
readProblemAxioms :: SourceName -> IO [(Skel, ([SPIdentifier], Int))]
readProblemAxioms filePath =
    do result <- parseFromFile parseSPASS filePath
       case result 
         of Left err  -> error $ show err
	    Right spproblem  -> 
                let (_,_,lst) = getSPFormulas "lib" "file" spproblem
                    isAxiom (_,_,_,role,_,skel,_,_) = 
                        (role == "axiom") && (skel /= Const TrueAtom [])
                    f (_,_,line,_,_,skel,params,_) = (md5s $ Str $ show skel,(params,line))
                in return $ map f $ filter isAxiom lst

-- -----------------------------------------------------------
-- * Indexing
-- -----------------------------------------------------------


{-|
  indexFile reads the file TheoryName in directory FilePath and feeds it
  to the database. The first argument specifies the library the theory
  should be associated with.
-}
indexFile :: String -> FilePath -> TheoryName -> IO (TheoryName, Int, Int, Int)
indexFile lib dir file =
    do result <- parseFromFile parseSPASS (dir ++ "/" ++file)
       case result 
         of Left err  -> error $ show err
	    --Right spproblem  -> return $ getSPFormulas file spproblem
	    Right spproblem  -> let (nrOfTautologies,nrOfDuplicates,spformulas) = 
                                        getSPFormulas lib file spproblem
                                    len = length spformulas
                                in do multiInsertProfiles spformulas
                                      insertStatistics (lib,file,nrOfTautologies,nrOfDuplicates,len)
                                      -- putStrLn $ showRec (file,nrOfTautologies,nrOfDuplicates,len)
                                      return (file,nrOfTautologies,nrOfDuplicates,len)


{-|
  indexDir reads all files from the directory FilePath and feeds them
  to the database. The first argument specifies the library the theories
  should be associated with.
-}
indexDir :: String -> FilePath -> IO [(TheoryName, Int, Int, Int)]
indexDir lib dir =
    let showRec (file,ts,ds,fs) = file ++ "\t" ++ (show ts) ++ "\t" ++ 
                                  (show ds) ++ "\t" ++ (show fs)
    in do ls <- getDirectoryContents dir
          setCurrentDirectory dir
          rec <- mapM (indexFile lib dir) (L.filter (L.isSuffixOf "dfg") ls)
          putStrLn (concatMap showRec rec)
          return rec

-- -----------------------------------------------------------
-- * SPProblem Normalization
-- -----------------------------------------------------------


{-|
  getSPFormulas translates a SPProblem into a list of tuples
  similiar to a profile record in the database. In particular
  all formulas are normalized.
  The first two arguments are intended to assign a library and theory name
  to the SPProblem.
-}
getSPFormulas :: String
                 -> String
                 -> SPProblem
                 -> (Int,
                     Int,
                     [(String, -- lib
                       String, -- theory
                       Int, -- line
                       String, -- role
                       SPTerm, 
                       Formula (Constant SpassConst) Int, -- formula skeleton
                       [SPIdentifier], -- formula parameter
                       String)])
getSPFormulas lib theory spproblem = (nrOfTautologies,nrOfDuplicates,spformulas)
    where (SPProblem _ _ (SPLogicalPart _ _ flsts) _) = spproblem
          spformulas1 = map (normalizeSPFormula lib theory)
                        (concatMap (\(SPFormulaList _ f) -> f) flsts)
          eqSpterm (_,_,_,_,_,skel1,params1,_) (_,_,_,_,_,skel2,params2,_) =
              skel1 == skel2 && params1 == params2
          isNotTrueAtom (_,_,_,_,_,(Const TrueAtom []),_,_) = False
	  isNotTrueAtom _ = True
          spformulas2 = filter isNotTrueAtom spformulas1
          nrOfTautologies = (length spformulas1) - (length spformulas2)
          spformulas = L.nubBy eqSpterm spformulas2
          nrOfDuplicates = (length spformulas2) - (length spformulas)

{-|
  normalizeSPFormula normalizes a SPFormula and associates it with
  a library and theory name.
-}
normalizeSPFormula :: String -> String -> SPFormula
                   -> (String, String, Int, String, SPTerm,Skeleton SpassConst, [SPIdentifier], String)
normalizeSPFormula lib theory (NamedSen line ax _ spterm) = 
    (lib,theory,line',role,spterm,abstractSPTerm,parameter,normalizationStrength)
        where (abstractSPTerm,parameter,normalizationStrength) = (normalize . wrapTerm) spterm
              line' = read line::Int
              role = if ax then "axiom" else "conjecture"
