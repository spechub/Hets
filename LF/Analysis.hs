{- |
Module      :  $Header$
Description :  Static analysis for the Edinburgh Logical Framework
Copyright   :  (c) Kristina Sojakova, DFKI Bremen 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  k.sojakova@jacobs-university.de
Stability   :  experimental
Portability :  portable

  Currently not used; requires refactoring of Twelf2DG.hs  
-}

module LF.Analysis
  ( basicAnalysis
  , symbAnalysis
  , symbMapAnalysis
  ) where

import LF.AS
import LF.Sign
import LF.Twelf2DG

import Common.DocUtils
import Common.ExtSign
import Common.GlobalAnnotations
import Common.AS_Annotation
import Common.Id
import Common.Result

import qualified Data.Set as Set
import qualified Data.Map as Map

import Static.DevGraph

import System.FilePath

gen_file :: String
gen_file = "gen_twelf_file.elf"

gen_sig :: String
gen_sig = "GEN_SIG"

gen_ax :: String
gen_ax = "gen_ax"

senSuf :: String -> String
senSuf sn = sn ++ "_SEN"

numSuf :: String -> Int -> String
numSuf s i = s ++ "_" ++ show i

wrapInSig :: String -> String -> String
wrapInSig sn cont = "%sig " ++ sn ++ " = {\n" ++ cont ++ "}."

wrapInIncl :: String -> String
wrapInIncl sn = "%include " ++ sn ++ " %open."

getSentenceAnnos :: [Annoted BASIC_ITEM] -> 

-----------------------------------------------------------------
-----------------------------------------------------------------

-- basic analysis for LF
basicAnalysis :: (BASIC_SPEC, Sign, GlobalAnnos) ->
  Result (BASIC_SPEC, ExtSign Sign Symbol, [Named EXP])
basicAnalysis (bs, initsig, _) =
  if initsig /= emptySig
     then error "Structuring for LF nyi."
     else do makeTwelfFile gen_file gen_sig bs
             (sig,sen) <- getSigSen gen_file
             let syms = getAllSymbols sig
             let fs = makeNamedFormulas sen          
             return $ Just $ (bs, ExtSign sig syms, fs)

makeNamedFormulas :: Sign -> [Named EXP]
makeNamedFormulas (Sign _ _ ds) =
  map (  ->  ds 

makeNamedFormula :: DEF -> Named EXP
makeNamedFormula (Def s t _) =
  let isImplies = or $ map isImplies annos
      isImplied = or $ map isImplied annos
      isTheorem = isImplies || isImplied
  

 
-- converts the basic spec into a Twelf file
makeTwelfFile :: FilePath -> String -> BASIC_SPEC -> IO ()
makeTwelfFile file sn (Basic_spec items) = do
  let sig = wrapInSig sn $ printSigItems items
  let sen = wrapInSig (senSuf sn) $
              wrapInIncl sn ++ printSenItems items
  writeFile file $ sig ++ "\n\n" ++ sen

printSigItems :: [Annoted BASIC_ITEM] -> String
printSigItems [] = ""
printSigItems (i:is) =
  case i of
    Annoted (Decl d) _ _ _ -> d ++ ".\n" ++ printSigItems is
    _ -> printSigItems is

printSenItems :: [Annoted BASIC_ITEM] -> String
printSenItems items = printSenItemsH 0 items

printSenItemsH :: Int -> [Annoted BASIC_ITEM] -> String
printSenItemsH _ [] = ""
printSenItemsH num (i:is) =
  case i of
    Annoted (Form f) _ _ _ ->
      let label = getRLabel i
          nam = if null label then numSuf gen_ax num else label
          num' = if null label then num + 1 else num
          in nam ++ " : " ++ f ++ ".\n" ++ printSenItemsH num' is
    _ -> printSenItemsH num is

-- retrieves the signatures containing basic spec declarations and sentences
getSigSen :: FilePath -> String -> IO (Sign,Sign)
getSigSen fp sn = do
  file <- resolveToCur fp
  runTwelf file
  (_,_,(sigmap,_)) <- buildGraph file (emptyLibEnv,emptyGrMap)
  let base = dropExtension file
  let sn' = senSuf sn
  let sig1 = Map.findWithDefault (error $ sn ++ " not found.") 
               (base,sn) sigmap
  let sig2 = Map.findWithDefault (error $ sn' ++ " not found.")
               (base,sn') sigmap
  return (sig1,sig2)

  
