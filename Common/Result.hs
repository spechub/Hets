{-| 
   
 > HetCATS/hetcats/Result.hs
 > $Id$
 > Authors: Till Mossakowski, Klaus Lüttich, Christian Maeder
 > Year:   2002, 2003

   This module provides a 'Result' type and some monadic functions to
   use this type for accumulation of errors and warnings occuring
   during the analyse phases.

-}

module Common.Result (module Common.Result, showPretty) where

import Common.Id
import Common.PrettyPrint
import Common.Lib.Pretty
import Data.List
import Common.Lib.Parsec.Pos

-- ---------------------------------------------------------------------
-- diagnostic messages
-- ---------------------------------------------------------------------

-- | maximum number of messages that are output
maxdiags :: Int
maxdiags = 20

-- | severness of diagnostic messages
data DiagKind = FatalError | Error | Warning | Hint deriving (Eq, Ord, Show)

-- | a diagnostic message with a position
data Diagnosis = Diag { diagKind :: DiagKind
		      , diagString :: String
		      , diagPos :: Pos 
		      } deriving Eq

-- | construct a message for a printable item that carries a position
mkDiag :: (PosItem a, PrettyPrint a) => DiagKind -> String -> a -> Diagnosis
mkDiag k s a =
    Diag k (s ++ " '" ++ showPretty a "'") $ getMyPos a 

-- | Check whether a diagnosis list contains errors
hasErrors :: [Diagnosis] -> Bool
hasErrors = any (\d -> diagKind d `elem` [FatalError,Error])

-- ---------------------------------------------------------------------
-- uniqueness check
-- ---------------------------------------------------------------------

-- | errors for duplicates in argument, selector or constructor lists. 
checkUniqueness :: (PrettyPrint a, PosItem a, Ord a) => [a] -> [Diagnosis]
checkUniqueness l = 
    let vd = filter ( not . null . tail) $ group $ sort l
    in map ( \ vs -> mkDiag Error ("duplicates at '" ++
	                          showSepList (showString " ") shortPosShow
				  (map getMyPos (tail vs)) "'" 
				   ++ " for")  (head vs)) vd
    where shortPosShow :: Pos -> ShowS
	  shortPosShow p = showParen True 
			   (shows (sourceLine p) . 
			    showString "," . 
			    shows (sourceColumn p))

-- ---------------------------------------------------------------------
-- the Result monad
-- ---------------------------------------------------------------------

-- | The 'Result' monad.  
-- A failing 'Result' should include a 'FatalError' message.
-- Otherwise diagnostics should be non-fatal.
data Result a = Result { diags :: [Diagnosis]
	               , maybeResult :: (Maybe a)
		       } deriving (Show)

instance Functor Result where
    fmap f (Result errs m) = Result errs $ fmap f m
 
instance Monad Result where
  return x = Result [] $ Just x
  Result errs Nothing >>= _ = Result errs Nothing
  Result errs1 (Just x) >>= f = Result (errs1++errs2) y
     where Result errs2 y = f x
  fail s = fatal_error s nullPos

-- ---------------------------------------------------------------------
-- merging for instances of Logic.signature_union
-- ---------------------------------------------------------------------

-- | merge together repeated or extended items
class Mergeable a where
    merge :: a -> a -> Result a 
    -- diff :: a -> a -> a 
    -- with if (c <- a `merge` b)  then (c `diff' a == b)  

-- ---------------------------------------------------------------------
-- Result with IO
-- ---------------------------------------------------------------------

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

-- ---------------------------------------------------------------------
-- contructing a Result
-- ---------------------------------------------------------------------

-- | a failing result with a proper position
fatal_error :: String -> Pos -> Result a
fatal_error s p = Result [Diag FatalError s p] Nothing  

-- | add an error message but continue (within do)
plain_error :: a -> String -> Pos -> Result a
plain_error x s p = Result [Diag Error s p] $ Just x  

-- | add a warning
warning :: a -> String -> Pos -> Result a
warning x s p = Result [Diag Warning s p] $ Just x  

-- | add a fatal error message to a failure (Nothing)
maybeToResult :: Pos -> String -> Maybe a -> Result a
maybeToResult p s m = Result (case m of 
		              Nothing -> [Diag FatalError s p]
			      Just _ -> []) m

-- ---------------------------------------------------------------------
-- instances for Result
-- ---------------------------------------------------------------------

instance Show Diagnosis where
    showsPrec _ = showPretty

instance PrettyPrint Diagnosis where
    printText0 _ (Diag k s sp) = 
	ptext (show k)
        <+> text (show sp)
	<+> text s

instance PosItem Diagnosis where
    up_pos fn1 d  = d { diagPos = fn1 $ diagPos d }
    get_pos = Just . diagPos

instance PrettyPrint a => PrettyPrint (Result a) where
    printText0 g (Result ds m) = vcat ((case m of 
				       Nothing -> empty
	 			       Just x -> printText0 g x) :
					    (map (printText0 g) ds))
