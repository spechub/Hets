{- |
Module      :  $Header$
Description :  Static analysis for the Edinburgh Logical Framework
Copyright   :  (c) Kristina Sojakova, DFKI Bremen 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

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

import qualified Data.Map as Map

import System.IO.Unsafe

gen_file :: String
gen_file = "LF/test/gen_twelf_file.elf"

gen_sig :: String
gen_sig = "GEN_SIG"

gen_ax :: String
gen_ax = "gen_ax"

senSuf :: String -> String
senSuf sn = sn ++ "_SEN"

numSuf :: String -> Int -> String
numSuf s i = s ++ "_" ++ show i

wrapInSig :: String -> String -> String
wrapInSig sn cont = "%sig " ++ sn ++ " = {\n" ++ cont ++ "}.\n"

wrapInIncl :: String -> String
wrapInIncl sn = "%include " ++ sn ++ " %open.\n"

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
basicAnalysis (bs@(Basic_spec items), initsig, _) =
  if initsig /= emptySig
     then error "Structuring for LF nyi."
     else do
       let (sig,sen) = unsafePerformIO $
             constructSigSen gen_file gen_sig items
       let syms = getSymbols sig
       let fs = makeNamedForms sen $ map r_annos $ getSenItems items
       return (bs, ExtSign sig syms, fs)

-- constructs the signatures and sentences
constructSigSen :: BASE -> MODULE -> [Annoted BASIC_ITEM] ->
                   IO (Sign,[(NAME,Sentence)])
constructSigSen fp name items = do
  file <- resolveToCur fp
  makeTwelfFile file name (getSigItems items) (getSenItems items)
  retrieveSigSen file name

-- constructs a Twelf file to analyze the signature and sentences
makeTwelfFile :: BASE -> MODULE -> [Annoted BASIC_ITEM] ->
                 [Annoted BASIC_ITEM] -> IO ()
makeTwelfFile file name sig_items sen_items = do
  let sen_type = "type"
  let sig1 = wrapInSig name $ printSigItems sig_items
  let sig2 = wrapInSig (senSuf name) $ wrapInIncl name ++
               printSenItems sen_type sen_items
  writeFile file $ sig1 ++ "\n" ++ sig2

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
retrieveSigSen :: BASE -> MODULE -> IO (Sign,[(NAME,Sentence)])
retrieveSigSen file name = do
  libs <- twelf2SigMor file
  let (sigs,_) = Map.findWithDefault (error $ "Library not found.")
                   (toLibName file) libs
  let name' = senSuf name
  let sig = Map.findWithDefault (er name) name sigs
  let sig' = Map.findWithDefault (er name') name' sigs
  let sens = getSensFromDefs $ filter (\ d -> isLocalSym (getSym d) sig')
               $ getDefs sig'
  return (sig,sens)
  where er n = error $ "Signature " ++ n ++ " not found."
