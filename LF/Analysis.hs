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

import Data.List
import qualified Data.Map as Map
import qualified Data.Set as Set

import System.IO.Unsafe

sen_type_exp :: EXP
sen_type_exp = Type

gen_file :: String
gen_file = gen_base

gen_sig1 :: String
gen_sig1 = gen_module

gen_sig2 :: String
gen_sig2 = gen_module ++ "'"

gen :: String
gen = "gen_"

genPref :: String -> String
genPref s = gen ++ s

gen_ax :: String
gen_ax = genPref "ax"

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
  let (sigs,_) = Map.findWithDefault (error badLibError) gen_file libs
  in Map.findWithDefault (error $ badSigError n) n sigs

getUnknownSyms :: [RAW_SYM] -> Sign -> [RAW_SYM]
getUnknownSyms syms sig =
  syms \\ (Set.toList $ Set.map symName $ getLocalSyms sig)

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
  let cont1 = if (null $ getDefs sig) then "" else show (pretty sig) ++ "\n"
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
  let sens = getSens sig2
  return (sig1,sens)

getSens :: Sign -> [(NAME,Sentence)]
getSens sig = 
  map (\ (Def s _ v) ->
         case v of
           Nothing -> error $ badValError $ symName s
           Just v' -> (symName s, v')
      ) $ getLocalDefs sig

-----------------------------------------------------------------
-----------------------------------------------------------------

-- symbol analysis for LF 
symbAnalysis :: [SYMB_ITEMS] -> Result [RAW_SYM]
symbAnalysis ss = Result [] $ Just $ concat $ map (\ (Symb_items s) -> s) ss

-- symbol map analysis for LF 
symbMapAnalysis :: [SYMB_MAP_ITEMS] -> Result (Map.Map RAW_SYM RAW_SYM)
symbMapAnalysis ss = Result [] $ Just $
  foldl (\ m s -> Map.union m (makeSymbMap s)) Map.empty ss

makeSymbMap :: SYMB_MAP_ITEMS -> Map.Map RAW_SYM RAW_SYM
makeSymbMap (Symb_map_items ss) =
   foldl (\ m s -> case s of
                     Symb s1 -> Map.insert s1 s1 m
                     Symb_map s1 s2 -> Map.insert s1 s2 m
         ) Map.empty ss

-----------------------------------------------------------------
-----------------------------------------------------------------

-- converts a mapping of raw symbols to a mapping of symbols
renamMapAnalysis :: Map.Map RAW_SYM RAW_SYM -> Sign -> Map.Map Symbol Symbol
renamMapAnalysis m sig =
  let syms1 = getUnknownSyms (Map.keys m) sig
      syms2 = filter (\ s -> not $ isSym s) $ Map.elems m
      syms  = syms1 ++ syms2
      in if not (null syms) then error $ badSymsError syms else
            Map.fromList $ map (\ (k,v) -> (toSym k, toSym v)) $ Map.toList m

{- converts a mapping of raw symbols to a mapping of symbols to expressions
   annotated with their type -}
translMapAnalysis :: Map.Map RAW_SYM RAW_SYM -> Sign -> Sign ->
                     Map.Map Symbol (EXP,EXP)
translMapAnalysis m sig1 sig2 =
  let syms = getUnknownSyms (Map.keys m) sig1
      in if not (null syms) then error $ badSymsError syms else
         unsafePerformIO $ codAnalysis m sig2

codAnalysis :: Map.Map RAW_SYM RAW_SYM -> Sign -> IO (Map.Map Symbol (EXP,EXP))
codAnalysis m sig2 = do
  -- make a Twelf file
  let cont1 = (show $ pretty sig2) ++ "\n"
  let cont2 = concat $ map (\ (k,v) -> (genPref k) ++ " = " ++ v ++ ".\n") $
                 Map.toList m
  let s1 = mkSig gen_sig1 cont1
  let s2 = mkSig gen_sig2 $ mkIncl gen_sig1 ++ cont2
  let contents = s1 ++ "\n" ++ s2
  writeFile gen_file contents

  -- run Twelf on the created file
  libs <- twelf2SigMor gen_file
  
  -- construct the mapping
  let sig' = getSigFromLibs gen_sig2 libs
  return $ getMap sig'

getMap :: Sign -> Map.Map Symbol (EXP,EXP)
getMap sig = Map.fromList $ map
    (\ (Def s t v) ->
       case v of
         Nothing -> error $ badValError $ symName s
         Just v' -> let Just n = stripPrefix gen $ symName s
                        in (toSym n, (v',t))
    ) $ getLocalDefs sig

---------------------------------------------------------------------------
---------------------------------------------------------------------------

-- ERROR MESSAGES
badLibError :: String
badLibError = "Library not found."

badSigError :: MODULE -> String
badSigError n = "Signature " ++ n ++ " not found."

badSymsError :: [String] -> String
badSymsError ss = "Symbols " ++ (show ss) ++
  " are unknown or are not locally accessible."

badValError :: String -> String
badValError s = "Symbol " ++ s ++ "does not have a value."
