{-| 
   
 > HetCATS/hetcats/Result.hs
 > $Id$
 > Authors: Till Mossakowski, Klaus Lüttich
 > Year:   2002

   This module provides a Result type and some monadic functions to
   use this type for accumulation of errors and warnings occuring
   during the analyse phases.

-}

module Result where

import Id
import PrettyPrint
import Pretty

data Diagnosis = Error String Pos
	       | FatalError String Pos
               | Warning String Pos

data Result a = Result [Diagnosis] (Maybe a)
    deriving (Show)

instance Monad Result where
  return x = Result [] $ Just x
  Result errs Nothing >>= _ = Result errs Nothing
  Result errs1 (Just x) >>= f = Result (errs1++errs2) y
     where Result errs2 y = f x
  fail s = fatal_error s nullPos

fatal_error :: String -> Pos -> Result a
fatal_error s p = Result [FatalError s p] Nothing  

non_fatal_error :: a -> String -> Pos -> Result a
non_fatal_error x s p = Result [Error s p] $ Just x  

warning :: a -> String -> Pos -> Result a
warning x s p = Result [Warning s p] $ Just x  

instance Show Diagnosis where
    showsPrec _ d = case d of
		    Error s p      -> 
			showString "Error: "      . showPosString p s
		    FatalError s p -> 
			showString "FatalError: " . showPosString p s
		    Warning s p    -> 
			showString "Warning: "    . showPosString p s
	where 
	showPosString :: Pos -> String -> String -> String 
	showPosString p s = showString p' . showString s 
	    where p' = case p of 
		       (l,c) -> (showString "in line " .
				 showsPrec 0 l .
				 showString " at char " .
				 showsPrec 0 c) ": "
    showList [] = showString ""
    showList [d] = showsPrec 0 d
    showList (d:ds) = showsPrec 0 d . showString "\n" . showList ds

instance PrettyPrint Diagnosis where
    printText0 _ = ptext . show

instance PrettyPrint a => PrettyPrint (Result a) where
    printText0 g (Result ds m) = vcat ((case m of 
				       Nothing -> empty
				       Just x -> printText0 g x) :
					    (map (printText0 g) ds))
							