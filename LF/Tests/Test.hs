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

import Text.XML.Light.Input
import Text.XML.Light.Types
import Text.XML.Light.Proc

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

fp :: FilePath
fp = "../twelf/specs/math/algebra/algebra1.elf"

res :: IO Doc
res = do
  (s,m) <- test fp
  let ((b,m),sig1) = (Map.toList s) !! 0
  return $ vcat [text b, text m, pretty sig1]

test :: FilePath -> IO SIGS_AND_MORPHS
test file = do
  let omdoc_file = concat[reverse $ drop 3 $ reverse file, "omdoc"]
  xml <- readFile omdoc_file
  let elems = onlyElems $ parseXML xml
  let elems1 = filter (\ e -> elName e == omdocQN) elems
  case elems1 of
       [root] -> do
          let th = (elChildren root) !! 0
          return $ addSign file th (Map.empty, Map.empty) 
       _ -> fail "Not an OMDoc file."

