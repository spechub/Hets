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
module MySat where
import List
import Ratio
import Maybe
import Debug.Trace

newtype Clause a = Clause ([a],[a]) deriving (Eq,Show)

class (Eq f,Show f) => Logic f where 
	ff :: f; tt :: f;
	x :: f; y :: f; z :: f;
	neg :: f -> f
	(/\) :: f -> f -> f
	(\/) :: f -> f -> f
	onlybox :: f -> [f]
	disj :: [f] -> f
	ma :: f -> [f]
	eval :: f -> Clause f -> Bool
	provable :: f -> Bool

class (Logic f,Logic g) => Strip f g where
	strip :: f -> [g]
	
class (Logic f, Logic g) => UnaryMatch f g | f -> g where
	matchu :: Clause f -> [[g]]
	
class (Logic f, Logic g, Logic h) => BinaryMatch f g h | f -> g, f -> h where
	matchb :: Clause f -> [([g],[h])]
	
