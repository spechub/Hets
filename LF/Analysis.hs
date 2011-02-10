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

getSensFromDefs :: [DEF] -> [(NAME,Sentence)]
getSensFromDefs [] = []
getSensFromDefs ((Def s _ (Just v)):ds) = (symName s, v) : getSensFromDefs ds
getSensFromDefs _ = error "Sentences cannot be retrieved from definitions."

makeNamedForms :: [(NAME,Sentence)] -> [[Annotation]] -> [Named Sentence]
makeNamedForms ss as = map makeNamedForm $ zip ss as

makeNamedForm :: ((NAME,Sentence),[Annotation]) -> Named Sentence
makeNamedForm ((n,s),annos) =
  let implies = or $ map isImplies annos
      implied = or $ map isImplied annos
      isTheorem = implies || implied
      in (makeNamed n s) {isAxiom = not isTheorem}

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
  let contents = makeFile sig (getSigItems items) (getSenItems items)
  writeFile gen_file contents
  libs <- twelf2SigMor gen_file
  getSigSen libs

{- constructs the contents of a Twelf file used to analyze the signature
   and sentences -}
makeFile :: Sign -> [Annoted BASIC_ITEM] -> [Annoted BASIC_ITEM] -> String
makeFile sig sig_items sen_items =
  let sen_type = show $ pretty sen_type_exp
      cont1 = if (sig == emptySig) then "" else show (pretty sig) ++ "\n"
      cont2 = printSigItems sig_items
      cont3 = printSenItems sen_type sen_items
      sig1 = mkSig gen_sig1 $ cont1 ++ cont2
      sig2 = mkSig gen_sig2 $ mkIncl gen_sig1 ++ cont3
      in sig1 ++ "\n" ++ sig2

printSigItems :: [Annoted BASIC_ITEM] -> String
printSigItems [] = ""
printSigItems (i:is) =
  case i of
    Annoted (Decl d) _ _ _ -> d ++ ".\n" ++ printSigItems is
    _ -> printSigItems is

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

{- retrieves the signature and sentences corresponding to the
   original basic spec out of a Twelf file -}
getSigSen :: LIBS -> IO (Sign,[(NAME,Sentence)])
getSigSen libs = do
  let (sigs,_) = Map.findWithDefault (error "Library not found.")
                   gen_file libs
  let sig1 = Map.findWithDefault (er gen_sig1) gen_sig1 sigs
  let sig2 = Map.findWithDefault (er gen_sig2) gen_sig2 sigs
  let sens = getSensFromDefs $ filter (\ d -> isLocalSym (getSym d) sig2)
               $ getDefs sig2
  return (sig1,sens)
  where er n = error $ "Signature " ++ n ++ " not found."
