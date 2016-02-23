{- |
Module      :  $EmptyHeader$
Description :  <optional short description entry>
Copyright   :  (c) <Authors or Affiliations>
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  <email>
Stability   :  unstable | experimental | provisional | stable | frozen
Portability :  portable | non-portable (<reason>)

<optional description>
-}
module Main where

import Common.AS_Annotation
import Search.Common.Intersection
import Search.Common.Data
import Search.Common.Normalization
import Search.SPASS.FormulaWrapper
import SoftFOL.Sign
import SoftFOL.DFGParser
import Text.ParserCombinators.Parsec hiding (Line)
import System.Environment (getArgs)


main = do (dir:file1:file2:_) <- getArgs
          intersection <- intersectFiles dir file1 file2
          putStrLn $show intersection
          return ()

intersectFiles dir file1 file2 =
    do profiles1 <- getProfiles dir file1
       profiles2 <- getProfiles dir file2
       return (intersectProfiles profiles1 profiles2)

getProfiles dir file = 
    do namedFormulas <- procNamedFormulasFromFile (dir ++ "/" ++ file) normalize
       return (map namedFormulaToProfile namedFormulas)
           where namedFormulaToProfile ((sid,params,_),line) = Profile file line sid params

procNamedFormulasFromFile :: SourceName -> (Formula (Constant SpassConst) SPIdentifier -> c) -> IO [(c,Int)]
procNamedFormulasFromFile path proc =
    do result <- parseFromFile parseSPASS path
       case result of Left err  -> error (show err)
		      Right spproblem  -> do return (getNamedFormulas proc spproblem)

getNamedFormulas :: (Formula (Constant SpassConst) SPIdentifier -> b)
		 -> SPProblem
		 -> [(b, Int)]
getNamedFormulas proc spproblem = map procNamedFormula spformulas
    where (SPProblem _ _ (SPLogicalPart _ _ flsts _ _) _) = spproblem
          spformulas = concatMap (\(SPFormulaList _ f) -> f) flsts
	  procNamedFormula spformula = (proc $ wrapTerm $ sentence spformula, read $ senAttr spformula)

{-
let dir = "/home/inormann/dfg/query-files"
-}