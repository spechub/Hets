-- error messages

module Result where

import Id

data Diagnosis = Error String Pos
               | Warning String Pos
		 deriving (Show)

newtype Result a = Result ([Diagnosis],Maybe a)
    deriving (Show)

instance Monad Result where
  return x = Result ([],Just x)
  Result (errs, Nothing) >>= f = Result (errs,Nothing)
  Result (errs1, Just x) >>= f = Result (errs1++errs2,y)
     where Result (errs2,y) = f x
  fail s = Result ([Error ("Fail: "++s) nullPos],Nothing)