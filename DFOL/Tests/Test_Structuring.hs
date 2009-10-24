{- |
Description :  Test file for structuring mechanisms
-}

import DFOL.AS_DFOL
import DFOL.Analysis_DFOL
import DFOL.Sign
import DFOL.Morphism
import Common.Id
import Data.Maybe
import Common.DocUtils
import qualified Common.Result as Result
import qualified Data.Map as Map
import qualified Data.Set as Set

mkTok :: String -> Token
mkTok s = Token s nullRange

iTok, jTok, pTok, cTok, dTok :: NAME
iTok = mkTok "i"
jTok = mkTok "j"
pTok = mkTok "p"
cTok = mkTok "c"
dTok = mkTok "d"

i,j,c,d,p :: TERM

i = Identifier iTok
j = Identifier jTok
p = Identifier pTok
c = Identifier cTok
d = Identifier dTok

sig1 :: Sign
sig1 = Sign [([iTok], Sort)]                        

sig2 :: Sign
sig2 = Sign [([iTok], Sort),
             ([cTok], Func [Univ i] $ Univ i)]

sig :: Sign
sig = Sign [([iTok], Sort),
            ([jTok], Sort),
            ([dTok], Func [Univ j] $ Univ j)]

sig3 :: Sign
sig3 = Sign [([iTok], Sort)]            
             
m1,m2 :: Morphism
m1 = Morphism sig1 sig3 $ Map.fromList $ [(iTok,jTok)]
m2 = Morphism sig2 sig $ Map.fromList $ [(cTok,dTok)]

Result.Result ds (Just m) = morphUnion m1 m2


