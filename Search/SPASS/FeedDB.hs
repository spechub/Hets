{- |
Module      :  $Header$
Description :  Main module to read dfg files into the database
Copyright   :  (c) Immanuel Normann, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  inormann@jacobs-university.de
Stability   :  provisional
Portability :  portable
-}
module Search.Main where

import Config
import Data.List as L
--import Data.Set as S 
import Search.Common.Normalization
import Search.SPASS.DFGParser
import Search.SPASS.Sign
import Search.SPASS.FormulaWrapper
-- import System.Environment
import System.Directory
-- import System.Posix.Files
import System.IO
import Text.ParserCombinators.Parsec
-- import Text.ParserCombinators.Parsec.Char
-- import MD5
import DB.Connection
import System.Environment

main = do args <- getArgs
          case args of -- todo: test ob file existiert
            (lib:dir:file:_) -> treatFile lib dir file
            _ -> error "invalid arguments!\nShould be <library> <dir> <file>"

--treatDir :: (ParseHandling -> IO ()) -> Handle -> FilePath -> IO ()
treatDir lib dir =
    do ls <- getDirectoryContents dir
       setCurrentDirectory dir
       rec <- mapM (treatFile lib dir) (L.filter (L.isSuffixOf "dfg") ls)
       putStrLn (concatMap showRec rec)
       return rec

showRec (file,ts,ds,fs) = file ++ "\t" ++ (show ts) ++ "\t" ++ (show ds) ++ "\t" ++ (show fs)


--treatFile :: SourceName -> IO  (Int,Set SPFormula)
treatFile lib dir file =
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


{- test:
r <- treatFile dfgHome "zfmisc_1__t9_zfmisc_1.dfg"
-}

msgErr err = hPutStrLn stderr ("\t ... failed!\nerror: " ++ show err)

--getSPFormulas :: SPProblem -> (Int,Set SPFormula)
getSPFormulas lib file spproblem = (nrOfTautologies,nrOfDuplicates,spformulas)
    where (SPProblem _ _ (SPLogicalPart _ _ flsts) _) = spproblem
          spformulas1 = map (normalizeSPFormula lib file)
                        (concatMap (\(SPFormulaList _ f) -> f) flsts)
          --eqSpterm (_,_,spterm1,_,_,_,_) (_,_,spterm2,_,_,_,_) = spterm1 == spterm2
          eqSpterm (_,_,_,_,_,skel1,params1,_) (_,_,_,_,_,skel2,params2,_) =
              skel1 == skel2 && params1 == params2
          isNotTrueAtom (_,_,_,_,_,(Const TrueAtom []),_,_) = False
	  isNotTrueAtom _ = True
          spformulas2 = filter isNotTrueAtom spformulas1
          nrOfTautologies = (length spformulas1) - (length spformulas2)
          spformulas = L.nubBy eqSpterm spformulas2
          nrOfDuplicates = (length spformulas2) - (length spformulas)

--normalizeSPFormula :: String -> SPFormula -> (String, String, Bool, SPTerm,Skeleton SpassConst, [SPIdentifier], String,Int)
normalizeSPFormula lib file (NamedSen line ax _ spterm) = 
    (lib,file,line',role,spterm,abstractSPTerm,parameter,normalizationStrength)
        where (abstractSPTerm,parameter,normalizationStrength) = (normalize . wrapTerm) spterm
              line' = read line::Int
              role = if ax then "axiom" else "conjecture"
