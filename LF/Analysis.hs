{- |
Module      :  $Header$
Description :  Static analysis for the Edinburgh Logical Framework
Copyright   :  (c) Kristina Sojakova, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  k.sojakova@jacobs-university.de
Stability   :  experimental
Portability :  portable
-}
module LF.Analysis where

import LF.AS
import LF.Sign
import LF.Twelf2GR

import Common.ExtSign
import Common.GlobalAnnotations
import Common.AS_Annotation
import Common.Result
import Common.DocUtils

import qualified Data.Map as Map

import System.IO.Unsafe

sen_type_exp :: EXP
sen_type_exp = Type

gen_file :: String
gen_file = gen_base

gen_sig1 :: String
gen_sig1 = gen_module

gen_sig2 :: String
gen_sig2 = "GEN_SIG_SEN"

gen_ax :: String
gen_ax = "gen_ax"

numSuf :: String -> Int -> String
numSuf s i = s ++ "_" ++ show i

mkSig :: String -> String -> String
mkSig n cont = "%sig " ++ n ++ " = {\n" ++ cont ++ "}.\n"

mkIncl :: String -> String
mkIncl n = "%include " ++ n ++ " %open.\n"

mkRead :: String -> String
mkRead n = "%read \"" ++ n ++ "\".\n" 

getSigItems :: [Annoted BASIC_ITEM] -> [Annoted BASIC_ITEM]
getSigItems = filter ( \ (Annoted i _ _ _) ->
  case i of
    Decl _ -> True
    Form _ -> False )

getSenItems :: [Annoted BASIC_ITEM] -> [Annoted BASIC_ITEM]
getSenItems = filter ( \ (Annoted i _ _ _) ->
  case i of
    Decl _ -> False
    Form _ -> True )

printSigItems :: [Annoted BASIC_ITEM] -> String
printSigItems is =
  concat $ map (\ (Annoted i _ _ _) ->
     case i of
          Decl d -> d ++ ".\n"
          _ -> ""
     ) is

printSenItems :: String -> [Annoted BASIC_ITEM] -> String
printSenItems sen_type items = printSenItemsH sen_type 0 items

printSenItemsH :: String -> Int -> [Annoted BASIC_ITEM] -> String
printSenItemsH _ _ [] = ""
printSenItemsH sen_type num (i:is) =
  case i of
    Annoted (Form f) _ _ _ ->
      let lab  = getRLabel i
          lab' = if null lab then numSuf gen_ax num else lab
          num' = if null lab then num + 1 else num
          in lab' ++ " : " ++ sen_type ++ " = " ++ f ++ ".\n" ++
             printSenItemsH sen_type num' is
    _ -> printSenItemsH sen_type num is

makeNamedForms :: [(NAME,Sentence)] -> [[Annotation]] -> [Named Sentence]
makeNamedForms ss as = map makeNamedForm $ zip ss as

makeNamedForm :: ((NAME,Sentence),[Annotation]) -> Named Sentence
makeNamedForm ((n,s),annos) =
  let implies = or $ map isImplies annos
      implied = or $ map isImplied annos
      isTheorem = implies || implied
      in (makeNamed n s) {isAxiom = not isTheorem}

getSigFromLibs :: MODULE -> LIBS -> Sign
getSigFromLibs n libs =
  let (sigs,_) = Map.findWithDefault (error "Library not found.") gen_file libs
  in Map.findWithDefault (error $ "Signature " ++ n ++ " not found.") n sigs

getLocalDefs :: Sign -> [DEF]
getLocalDefs sig = filter (\ (Def s _ _) -> isLocalSym s sig) $ getDefs sig

getAnnoSyms :: [DEF] -> [(Symbol,(EXP,EXP))]
getAnnoSyms ds =
  map (\ (Def s t v) -> 
        case v of
          Nothing -> error $ "Symbol " ++ (show $ pretty s) ++
                             "does not have a value."
          Just v' -> (s,(v',t))
      ) ds

-----------------------------------------------------------------
-----------------------------------------------------------------

-- basic analysis for LF
basicAnalysis :: (BASIC_SPEC, Sign, GlobalAnnos) ->
                 Result (BASIC_SPEC, ExtSign Sign Symbol, [Named EXP])
basicAnalysis (bs@(Basic_spec items), initsig, _) = do
  let (sig,sens) = unsafePerformIO $ makeSigSen initsig items
  let syms = getSymbols sig
  let fs = makeNamedForms sens $ map r_annos $ getSenItems items
  return (bs, ExtSign sig syms, fs)

-- constructs the signatures and sentences
makeSigSen :: Sign -> [Annoted BASIC_ITEM] -> IO (Sign,[(NAME,Sentence)])
makeSigSen sig items = do
  -- make a Twelf file
  let sen_type = show $ pretty sen_type_exp
  let cont1 = if (sig == emptySig) then "" else show (pretty sig) ++ "\n"
  let cont2 = printSigItems $ getSigItems items
  let cont3 = printSenItems sen_type $ getSenItems items
  let s1 = mkSig gen_sig1 $ cont1 ++ cont2
  let s2 = mkSig gen_sig2 $ mkIncl gen_sig1 ++ cont3
  let contents = s1 ++ "\n" ++ s2
  writeFile gen_file contents
  
  -- run Twelf on the created file
  libs <- twelf2SigMor gen_file

  -- construct the signature and sentences
  let sig1 = getSigFromLibs gen_sig1 libs
  let sig2 = getSigFromLibs gen_sig2 libs
  let sens = map (\ (s,(v,_)) -> (symName s, v)) $ getAnnoSyms $
                getLocalDefs sig2
  return (sig1,sens)              

-----------------------------------------------------------------
-----------------------------------------------------------------

-- symbol analysis for LF 
symbAnalysis :: [SYMB_ITEMS] -> Result [String]
symbAnalysis ss = Result [] $ Just $ concat $ map (\ (Symb_items s) -> s) ss

-- symbol map analysis for LF 
symbMapAnalysis :: [SYMB_MAP_ITEMS] -> Result (Map.Map String String)
symbMapAnalysis ss = Result [] $ Just $
  foldl (\ m s -> Map.union m (makeSymbMap s)) Map.empty ss

makeSymbMap :: SYMB_MAP_ITEMS -> Map.Map String String
makeSymbMap (Symb_map_items ss) =
   foldl (\ m s -> case s of
                     Symb s1 -> Map.insert s1 s1 m
                     Symb_map s1 s2 -> Map.insert s1 s2 m
         )
         Map.empty
         ss

-----------------------------------------------------------------
-----------------------------------------------------------------

{- converts a mapping of raw symbols to a mapping of symbols to expressions
   annotated with their type -}
mapAnalysis :: Map.Map String String -> Sign -> Map.Map Symbol (EXP,EXP)
mapAnalysis m sig = unsafePerformIO $ mapAnalysisIO m sig

mapAnalysisIO :: Map.Map String String -> Sign -> IO (Map.Map Symbol (EXP,EXP))
mapAnalysisIO m sig = do
  -- make a Twelf file
  let cont1 = show $ pretty sig
  let cont2 = concat $ map (\ (k,v) -> k ++ " = " ++ v ++ ".\n") $ Map.toList m
  let s1 = mkSig gen_sig1 cont1
  let s2 = mkSig gen_sig2 $ mkIncl gen_sig1 ++ cont2
  let contents = s1 ++ "\n" ++ s2
  writeFile gen_file contents

  -- run Twelf on the created file
  libs <- twelf2SigMor gen_file
  
  -- construct the mapping
  let sig' = getSigFromLibs gen_sig2 libs
  return $ Map.fromList $ getAnnoSyms $ getLocalDefs sig'
