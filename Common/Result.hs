{- |
Module      :  $Header$
Copyright   :  (c) K. Lüttich, T. Mossakowski, C. Maeder, Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  till@tzi.de
Stability   :  provisional
Portability :  portable

This module provides a 'Result' type and some monadic functions
   for accumulating 'Diagnosis' messages during analysis phases.
-}

module Common.Result where

import Common.Id
import Common.PrettyPrint
import Common.Lib.Pretty
import Data.List
import Text.ParserCombinators.Parsec.Error
import Common.Lexer (fromSourcePos)

-- | severness of diagnostic messages
data DiagKind = Error | Warning | Hint | Debug
              | MessageW -- ^ used for messages in the web interface
                deriving (Eq, Ord, Show)

-- | a diagnostic message with 'Pos'
data Diagnosis = Diag { diagKind :: DiagKind
                      , diagString :: String
                      , diagPos :: Range
                      } deriving Eq

-- | construct a message for a printable item that carries a position
mkDiag :: (PosItem a, PrettyPrint a) => DiagKind -> String -> a -> Diagnosis
mkDiag k s a = let q = char '\'' in
    Diag k (s ++ show (space <> q <> nest 2 (printText a) <> q)) $ getRange a

-- | check whether a diagnosis is an error
isErrorDiag :: Diagnosis -> Bool
isErrorDiag d = case diagKind d of
                Error -> True
                _ -> False

-- | Check whether a diagnosis list contains errors
hasErrors :: [Diagnosis] -> Bool
hasErrors = any isErrorDiag

-- | add range to a diagnosis
adjustDiagPos :: Range -> Diagnosis -> Diagnosis
adjustDiagPos r d = d { diagPos = appRange r $ diagPos d }

-- | A uniqueness check yields errors for duplicates in a given list.
checkUniqueness :: (PrettyPrint a, PosItem a, Ord a) => [a] -> [Diagnosis]
checkUniqueness l =
    let vd = filter ( not . null . tail) $ group $ sort l
    in map ( \ vs -> mkDiag Error ("duplicates at '" ++
                                  showSepList (showString " ") shortPosShow
                                  (concatMap getPosList (tail vs)) "'"
                                   ++ " for")  (head vs)) vd
    where shortPosShow :: Pos -> ShowS
          shortPosShow p = showParen True
                           (shows (sourceLine p) .
                            showString "," .
                            shows (sourceColumn p))

-- | The result monad. A failing result should include an error message.
data Result a = Result { diags :: [Diagnosis]
                       , maybeResult :: (Maybe a)
                       } deriving (Show)

instance Eq a => Eq (Result a) where
  Result _ res1 == Result _ res2 = res1==res2

instance Functor Result where
    fmap f (Result errs m) = Result errs $ fmap f m

instance Monad Result where
  return x = Result [] $ Just x
  Result errs Nothing >>= _ = Result errs Nothing
  Result errs1 (Just x) >>= f = Result (errs1++errs2) y
     where Result errs2 y = f x
  fail s = fatal_error s nullRange

appendDiags :: [Diagnosis] -> Result ()
appendDiags ds = Result ds (Just ())

-- | join two results
joinResultWith :: (a -> b -> c) -> Result a -> Result b -> Result c
joinResultWith f (Result d1 m1) (Result d2 m2) = Result (d1 ++ d2) $
    do r1 <- m1
       r2 <- m2
       return $ f r1 r2

-- | join a list of results that are independently computed
mapR :: (a -> Result a) -> [a] -> Result [a]
mapR ana = foldr (joinResultWith (:)) (Result [] $ Just []) . map ana

-- | bind results within the 'IO' monad
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

instance Functor IOResult where
  fmap f m = m >>= (return . f)

-- | unpack an IOResult
ioresToIO :: IOResult a -> IO(Result a)
ioresToIO (IOResult x) = x

-- | pack an IO value as IOResult
ioToIORes :: IO a -> IOResult a
ioToIORes = IOResult . (fmap return)

-- | pack a pure result as IOResult
resToIORes :: Result a -> IOResult a
resToIORes = IOResult . return

-- | a failing result with a proper position
fatal_error :: String -> Range -> Result a
fatal_error s p = Result [Diag Error s p] Nothing

-- | a failing result using pretty printed 'Doc'
pfatal_error :: Doc -> Range -> Result a
pfatal_error s p = fatal_error (show s) p

-- | a failing result constructing a message from a type
mkError :: (PosItem a, PrettyPrint a) => String -> a -> Result b
mkError s c = Result [mkDiag Error s c] Nothing

-- | add a debug point
debug :: (PosItem a, PrettyPrint a) => Int -> (String, a) -> Result ()
debug n (s, a) = Result [mkDiag Debug
                         (" point " ++ show n ++ "\nVariable "++s++":\n") a ]
                 $ Just ()

-- | add an error message but don't fail
plain_error :: a -> String -> Range -> Result a
plain_error x s p = Result [Diag Error s p] $ Just x

-- | add an error message using a pretty printed 'Doc' but don't fail
pplain_error :: a -> Doc -> Range -> Result a
pplain_error x s p = plain_error x (show s) p

-- | add a warning
warning :: a -> String -> Range -> Result a
warning x s p = Result [Diag Warning s p] $ Just x

-- | add a warning using a pretty printed 'Doc'
pwarning :: a -> Doc -> Range -> Result a
pwarning x s p = warning x (show s) p

-- | add a hint
hint :: a -> String -> Range -> Result a
hint x s p = Result [Diag Hint s p] $ Just x

-- | add a hint using a pretty printed 'Doc'
phint :: a -> Doc -> Range -> Result a
phint x s p = hint x (show s) p

-- | add a (web interface) message
message :: a -> String -> Result a
message x m = Result [Diag MessageW m nullRange] $ Just x

-- | add a failure message to 'Nothing'
maybeToResult :: Range -> String -> Maybe a -> Result a
maybeToResult p s m = Result (case m of
                              Nothing -> [Diag Error s p]
                              Just _ -> []) m

-- | add a failure message to 'Nothing'
-- (alternative for 'maybeToResult' without 'Range')
maybeToMonad :: Monad m => String -> Maybe a -> m a
maybeToMonad s m = case m of
                        Nothing -> fail s
                        Just v -> return v

-- | check whether no errors are present, coerce into 'Maybe'
resultToMaybe :: Result a -> Maybe a
resultToMaybe (Result ds val) = if hasErrors ds then Nothing else val

-- | adjust positions of diagnoses
adjustPos :: Range -> Result a -> Result a
adjustPos p r =
  r {diags = map (adjustDiagPos p) $ diags r}

-- | Propagate errors using the error function
propagateErrors :: Result a -> a
propagateErrors r =
  case (hasErrors $ diags r, maybeResult r) of
    (False,Just x) -> x
    _ -> error $ unlines $ map show $ diags r

-- ---------------------------------------------------------------------
-- instances for Result
-- ---------------------------------------------------------------------

-- | showing (Parsec) parse errors using our own 'showPos' function
showErr :: ParseError -> String
showErr err
    = showPos (fromSourcePos $ errorPos err) ":" ++
      showErrorMessages "or" "unknown parse error"
                        "expecting" "unexpected" "end of input"
                       (errorMessages err)

instance Show Diagnosis where
    showsPrec _ = showPretty

instance PrettyPrint Diagnosis where
    printText0 _ (Diag k s (Range sp)) =
        (if isMessageW
            then empty
            else text (case k of
                  Error -> "***"
                  _ -> "###") <+> text (show k))
        <> (case sp of
             [] | isMessageW -> empty
                | otherwise  -> comma
             _ -> space <> let
                      mi = minimumBy comparePos sp
                      ma = maximumBy comparePos sp
                  in case comparePos mi ma of
                     EQ -> text (showPos ma ",")
                     _ -> text $ showPos mi "-"
                          ++ showPos ma {sourceName = ""} "," )
        <+> text s
        where isMessageW = case k of
                           MessageW -> True
                           _        -> False

instance PosItem Diagnosis where
    getRange d = diagPos d

instance PrettyPrint a => PrettyPrint (Result a) where
    printText0 g (Result ds m) = vcat ((case m of
                                       Nothing -> empty
                                       Just x -> printText0 g x) :
                                           map (printText0 g) ds)

