{-| 
   
 > HetCATS/hetcats/Result.hs
 > $Id$
 > Authors: Till Mossakowski, Klaus Lüttich
 > Year:   2002

   This module provides a Result type and some monadic functions to
   use this type for accumulation of errors and warnings occuring
   during the analyse phases.

-}

module Common.Result (module Common.Result, showPretty) where

import Common.Id
import Common.PrettyPrint
import Common.Lib.Pretty

data DiagKind = FatalError | Error | Warning | Hint deriving (Eq, Ord, Show)

data Diagnosis = Diag { diagKind :: DiagKind
		      , diagString :: String
		      , diagPos :: Pos 
		      }

mkDiag :: (PosItem a, PrettyPrint a) => DiagKind -> String -> a -> Diagnosis
mkDiag k s a =
    Diag k (s ++ " '" ++ showPretty a "'") $
		 case get_pos a of 
		 Nothing -> nullPos
		 Just p -> p

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
    Result errs1 (Just v) -> do
      Result errs2 y <- f v
      return (Result (errs1++errs2) y)

newtype IOResult a = IOResult (IO(Result a))
instance Monad IOResult where
  return x = IOResult (return (return x))
  IOResult x >>= f = IOResult (x `ioBind` (\y -> let IOResult z = f y in z))

ioresToIO :: IOResult a -> IO(Result a)
ioresToIO (IOResult x) = x

ioToIORes :: IO a -> IOResult a
ioToIORes = IOResult . (fmap return)

resToIORes :: Result a -> IOResult a
resToIORes = IOResult . return

fatal_error :: String -> Pos -> Result a
fatal_error s p = Result [Diag FatalError s p] Nothing  

plain_error :: a -> String -> Pos -> Result a
plain_error x s p = Result [Diag Error s p] $ Just x  

warning :: a -> String -> Pos -> Result a
warning x s p = Result [Diag Warning s p] $ Just x  

maybeToResult :: Pos -> String -> Maybe a -> Result a
maybeToResult p s m = Result (case m of 
		              Nothing -> [Diag FatalError s p]
			      Just _ -> []) m

instance Show Diagnosis where
    showsPrec _ = showPretty

instance PrettyPrint Diagnosis where
    printText0 _ (Diag k s sp) = 
	ptext (show k)
        <+> text (show sp)
	<+> text s

instance PrettyPrint a => PrettyPrint (Result a) where
    printText0 g (Result ds m) = vcat ((case m of 
				       Nothing -> empty
	 			       Just x -> printText0 g x) :
					    (map (printText0 g) ds))
							
