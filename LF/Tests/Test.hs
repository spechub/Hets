{- |
Description :  Test file for Sign
-}

import LF.Sign
import LF.Morphism
import Common.Doc
import Common.DocUtils
import qualified Data.Map as Map
import qualified Data.Set as Set
import LF.Twelf2DG
import System.Directory
import Network.URI

import Text.XML.Light.Input
import Text.XML.Light.Types
import Text.XML.Light.Proc

import System.Exit
import System.IO
import System.Process
import System.FilePath

import Common.Utils

fp :: FilePath
fp = "/home/mathias/twelf/specs/math/algebra/algebra3.elf"

twelfTest :: FilePath -> IO ()
twelfTest file = do
  dir <- getEnvDef "TWELF_LIB" ""
  if null dir 
     then error "environment variable TWELF_LIB is not set"
     else do
       (_, _, _, pr) <- runInteractiveProcess (concat [dir, "/" ,twelf])
                                              (options ++ [file])
                                              Nothing
                                              Nothing 
       
       exitCode <- getProcessExitCode pr
       case exitCode of
            Nothing -> return ()
            Just ExitSuccess -> error "Twelf terminated immediately."
            Just (ExitFailure i) -> 
              error $ "Calling Twelf failed with exitCode: " ++ show i

nat,mat :: EXP
nat = Const $ Symbol "file1" "sig1" "nat"
mat = Const $ Symbol "file2" "sig2" "mat"

t0, t1, t2, t3, t4, t5, t6 :: EXP

t0 = Pi [("m", nat),("n", nat)] $ 
     Func [Appl mat [Var "m", Var "n"], Appl mat [Var "m", Var "n"]] $ Appl mat [Var "m", Var "n"]
t1 = Pi [("m",  nat),("m0",  nat)] $ 
     Func [Appl mat [Var "m", Var "m0"], Appl mat [Var "m", Var "m0"]] $ Appl mat [Var "m", Var "m0"]
t2 = Func [] $ recForm t0
t3 = Pi [("m", Var "nat"),("n",  nat)] $ 
     Func [Appl mat [Var "m", Var "n"], Appl mat [Var "m", Var "n"]] $ Appl mat [Var "m", Var "n"]
t4 = Pi [("m", mat),("n",  nat)] $ 
     Func [Appl mat [Var "m", Var "n"], Appl mat [Var "m", Var "n"]] $ Appl mat [Var "m", Var "n"]
t5 = Pi [("x",Type)] $ Pi [("n",Type)] $ Appl nat [Var "x", Var "n"]
t6 = Pi [("m",Type)] $ Pi [("x",Type)] $ Appl mat [Var "m", Var "x"]

sig1, sig2 :: Sign
sig1 = Sign "file1" "sig1" 
 [Def (Symbol "file1" "sig1" "nat") t0 Nothing,
  Def (Symbol "file2" "sig2" "mat") t0 $ Just t5]
sig2 = Sign "file1" "sig2" 
 [Def (Symbol "file1" "sig1" "nat") t1 Nothing]

m :: Morphism
m = Morphism sig1 sig2 $ Map.fromList [(Symbol "file1" "sig1" "nat", t0)]

Just r = mapSymbol m $ Symbol "file2" "sig2" "mat"

b = getSymValue sig1 $ Symbol "file2" "sig2" "mat"

inc = "/home/mathias/twelf/specs/logics/first-order/proof_theory/derived.elf"

toDoc :: (SIG_VIEW_NAME,Sign) -> Doc
toDoc ((b,m),sig) = vcat [text b, text m, pretty sig]

test :: FilePath -> IO Doc
test file = do
  (sigs,_) <- twelf2SigsAndMorphs file
  return $ vcat $ map toDoc $ Map.toList sigs  
  



