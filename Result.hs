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
import ParsecPos
import PrettyPrint
import Pretty

data DiagKind = FatalError | Error | Warning | Hint deriving (Eq, Ord, Show)

data Diagnosis = Diag { diagKind :: DiagKind
		      , diagString :: String
		      , diagPos :: Pos 
		      }

data Result a = Result { diags :: [Diagnosis]
	               , maybeResult :: (Maybe a)
		       } deriving (Show)

instance Monad Result where
  return x = Result [] $ Just x
  Result errs Nothing >>= _ = Result errs Nothing
  Result errs1 (Just x) >>= f = Result (errs1++errs2) y
     where Result errs2 y = f x
  fail s = fatal_error s nullPos

ioBind :: IO(Result a) -> (a -> IO(Result b)) -> IO(Result b)
x `ioBind` f = do
  res <- x
  case res of
    Result errs Nothing -> return (Result errs Nothing)
    Result errs1 (Just x) -> do
      Result errs2 y <- f x
      return (Result (errs1++errs2) y)


fatal_error :: String -> Pos -> Result a
fatal_error s p = Result [Diag FatalError s p] Nothing  

plain_error :: a -> String -> Pos -> Result a
plain_error x s p = Result [Diag Error s p] $ Just x  

warning :: a -> String -> Pos -> Result a
warning x s p = Result [Diag Warning s p] $ Just x  

maybeToResult :: Pos -> String -> Maybe a -> Result a
maybeToResult pos err (Just x) = return x
maybeToResult pos err Nothing = 
  fatal_error err pos


instance Show Diagnosis where
    showsPrec _ (Diag k s sp) = 
	shows k . colonS . 
	showString "in line " . shows (sourceLine sp) .
	showString " at char " . shows (sourceColumn sp) . 
	colonS . showString s 
	       where colonS = showString ": "
    showList [] = id
    showList [d] = shows d
    showList (d:ds) = shows d . showString "\n" . showList ds

instance PrettyPrint Diagnosis where
    printText0 _ (Diag k s sp) = 
	ptext (show k)
        <+> parens (int (sourceLine sp) <> comma <> int (sourceColumn sp))
	<+> text s

instance PrettyPrint a => PrettyPrint (Result a) where
    printText0 g (Result ds m) = vcat ((case m of 
				       Nothing -> empty
	 			       Just x -> printText0 g x) :
					    (map (printText0 g) ds))
							
