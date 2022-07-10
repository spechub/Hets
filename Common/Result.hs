{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./Common/Result.hs
Description :  Result monad for accumulating Diagnosis messages
Copyright   :  (c) T. Mossakowski, C. Maeder, Uni Bremen 2002-2008
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

'Result' monad for accumulating 'Diagnosis' messages
               during analysis phases.
-}

module Common.Result
  ( DiagKind (..)
  , Diagnosis (..)
  , mkDiag
  , mkNiceDiag
  , isErrorDiag
  , hasErrors
  , addErrorDiag
  , checkUniqueness
  , Result (..)
  , appendDiags
  , joinResultWith
  , joinResult
  , mapR
  , fatal_error
  , mkError
  , debug
  , plain_error
  , warning
  , justWarn
  , hint
  , justHint
  , message
  , maybeToResult
  , resultToMonad
  , resultToMaybe
  , adjustPos
  , updDiagKind
  , propagateErrors
  , showErr
  , prettyRange
  , filterDiags
  , showRelDiags
  , printDiags
  ) where

import Common.Doc as Doc
import Common.DocUtils
import Common.GlobalAnnotations
import Common.Id
import Common.Lexer

import Control.Applicative
import Control.Monad.Identity
import qualified Control.Monad.Fail as Fail

import Data.Data
import Data.Function
import Data.List

import Text.ParserCombinators.Parsec.Error
import Text.ParserCombinators.Parsec.Char (char)
import Text.ParserCombinators.Parsec (parse)

-- | severness of diagnostic messages
data DiagKind = Error | Warning | Hint | Debug
              | MessageW -- ^ used for messages in the web interface
                deriving (Show, Eq, Ord, Typeable, Data)

-- | a diagnostic message with 'Pos'
data Diagnosis = Diag { diagKind :: DiagKind
                      , diagString :: String
                      , diagPos :: Range
                      } deriving (Eq, Typeable, Data)

-- | construct a message for a printable item that carries a position
mkDiag :: (GetRange a,
 Pretty a) => DiagKind -> String -> a -> Diagnosis
mkDiag k s a = let q = text "'" in
    Diag k (show $ sep [text s, q <> pretty a <> q]) $ getRangeSpan a

-- | construct a message for a printable item that carries a position
mkNiceDiag :: (GetRange a, Pretty a) => GlobalAnnos
       -> DiagKind -> String -> a -> Diagnosis
mkNiceDiag ga k s a = let q = text "'" in
    Diag k (renderText ga $ sep [text s, q <> pretty a <> q])
      $ getRangeSpan a

-- | check whether a diagnosis is an error
isErrorDiag :: Diagnosis -> Bool
isErrorDiag d = case diagKind d of
                Error -> True
                _ -> False

-- | Check whether a diagnosis list contains errors
hasErrors :: [Diagnosis] -> Bool
hasErrors = any isErrorDiag

-- | add a further error message to explain a failure
addErrorDiag :: (GetRange a, Pretty a) => String -> a -> Result b -> Result b
addErrorDiag str a r@(Result ds ms) = if hasErrors ds then
  Result (mkDiag Error str a : ds) ms else r

-- | add range to a diagnosis
adjustDiagPos :: Range -> Diagnosis -> Diagnosis
adjustDiagPos r d = if isNullRange $ diagPos d then d { diagPos = r } else d

-- | change the diag kind of a diagnosis
updDiagKind :: (DiagKind -> DiagKind) -> Diagnosis -> Diagnosis
updDiagKind f d = d { diagKind = f $ diagKind d }

-- | A uniqueness check yields errors for duplicates in a given list.
checkUniqueness :: (Pretty a, GetRange a, Ord a) => [a] -> [Diagnosis]
checkUniqueness l =
    let vd = filter ( not . null . tail) $ group $ sort l
    in map (\ vs -> mkDiag Error ("duplicates at '" ++
                                  showSepList (showString " ") shortPosShow
                                  (concatMap getPosList (tail vs)) "'"
                                   ++ " for") (head vs)) vd
    where shortPosShow :: Pos -> ShowS
          shortPosShow p = showParen True
                           (shows (sourceLine p) .
                            showString "," .
                            shows (sourceColumn p))

-- | The result monad. A failing result should include an error message.
data Result a = Result { diags :: [Diagnosis]
                       , maybeResult :: Maybe a
                       } deriving (Show, Typeable, Data)

instance Functor Result where
    fmap f (Result errs m) = Result errs $ fmap f m

instance Applicative Result where
    pure = return
    (<*>) = ap

instance Monad Result where
  return = Result [] . Just
  r@(Result e m) >>= f = case m of
      Nothing -> Result e Nothing
      Just x -> joinResult r $ f x

instance Alternative Result where
    (<|>) = mplus
    empty = mzero

instance MonadPlus Result where
   mzero = Result [] Nothing
   r1@(Result _ m) `mplus` r2 = case m of
                                 Nothing -> r2
                                 Just _ -> r1

instance Fail.MonadFail Result where
  fail s = fatal_error s nullRange

appendDiags :: [Diagnosis] -> Result ()
appendDiags ds = Result ds (Just ())

-- | join two results with a combining function
joinResultWith :: (a -> b -> c) -> Result a -> Result b -> Result c
joinResultWith f (Result d1 m1) (Result d2 m2) = Result (d1 ++ d2) $
    do r1 <- m1
       r2 <- m2
       return $ f r1 r2

-- | join two results
joinResult :: Result a -> Result b -> Result b
joinResult = joinResultWith (\ _ b -> b)

-- | join a list of results that are independently computed
mapR :: (a -> Result b) -> [a] -> Result [b]
mapR ana = foldr (joinResultWith (:) . ana) $ Result [] $ Just []

-- | a failing result with a proper position
fatal_error :: String -> Range -> Result a
fatal_error s p = Result [Diag Error s p] Nothing

-- | a failing result constructing a message from a type
mkError :: (GetRange a, Pretty a) => String -> a -> Result b
mkError s c = Result [mkDiag Error s c] Nothing

-- | add a debug point
debug :: (GetRange a, Pretty a) => Int -> (String, a) -> Result ()
debug n (s, a) = Result
  [mkDiag Debug (unlines [" point " ++ show n, "Variable " ++ s ++ ":"]) a ]
  $ Just ()

-- | add an error message but don't fail
plain_error :: a -> String -> Range -> Result a
plain_error x s p = Result [Diag Error s p] $ Just x

-- | add a warning
warning :: a -> String -> Range -> Result a
warning x s p = Result [Diag Warning s p] $ Just x

-- | just add a warning without position information
justWarn :: a -> String -> Result a
justWarn x s = warning x s nullRange

-- | add a hint
hint :: a -> String -> Range -> Result a
hint x s p = Result [Diag Hint s p] $ Just x

-- | just add a hint without position information
justHint :: a -> String -> Result a
justHint x s = hint x s nullRange

-- | add a (web interface) message
message :: a -> String -> Result a
message x m = Result [Diag MessageW m nullRange] $ Just x

-- | add a failure message to 'Nothing'
maybeToResult :: Range -> String -> Maybe a -> Result a
maybeToResult p s m = Result (case m of
                              Nothing -> [Diag Error s p]
                              Just _ -> []) m

-- | check whether no errors are present, coerce into 'Maybe'
resultToMaybe :: Result a -> Maybe a
resultToMaybe = resultToMonad ""

-- | adjust positions of diagnoses
adjustPos :: Range -> Result a -> Result a
adjustPos p r =
  r {diags = map (adjustDiagPos p) $ diags r}

-- | Propagate errors using the error function
resultToMonad :: Monad m => String -> Result a -> m a
resultToMonad pos r = let ds = diags r in
  case (hasErrors ds, maybeResult r) of
    (False, Just x) -> return x
    _ -> error $ pos ++ ' ' : showRelDiags 2 ds

-- | Propagate errors using the error function
propagateErrors :: String -> Result a -> a
propagateErrors pos = runIdentity . resultToMonad pos

-- | showing (Parsec) parse errors using our own 'showPos' function
showErr :: ParseError -> String
showErr err = let
    (lookAheads, msgs) = partition (\ m -> case m of
                     Message str -> isPrefixOf lookaheadPosition str
                     _ -> False) $ errorMessages err
    readPos :: String -> Maybe Pos
    readPos s = case parse (do
            ls <- getNumber
            char '.'
            cs <- getNumber
            return $ newPos "" (value 10 ls) (value 10 cs)) "" s of
                  Left _ -> Nothing
                  Right x -> Just x
    pos = fromSourcePos (errorPos err)
    poss = pos : foldr (\ s l -> case readPos $
                                 drop (length lookaheadPosition)
                                 $ messageString s of
                        Just p -> p {sourceName = sourceName pos} : l
                        _ -> l) [] lookAheads
    in shows (prettySingleSourceRange poss) ":" ++
       showErrorMessages "or" "unknown parse error"
           "expecting" "unexpected" "end of input" msgs

prettySingleSourceRange :: [Pos] -> Doc
prettySingleSourceRange sp = let
    mi = minimum sp
    ma = maximum sp
    in case compare mi ma of
          EQ -> text (showPos ma "")
          _ -> text $ showPos mi "-"
               ++ showPos ma {sourceName = ""} ""

prettyRange :: [Pos] -> Doc
prettyRange = sepByCommas . map prettySingleSourceRange
    . groupBy (on (==) sourceName) . sort

instance Pretty Range where
    pretty = prettyRange . rangeToList

relevantDiagKind :: Int -> DiagKind -> Bool
relevantDiagKind v k = case k of
    Error -> True
    Warning -> v >= 2
    Hint -> v >= 4
    Debug -> v >= 5
    MessageW -> False

filterDiags :: Int -> [Diagnosis] -> [Diagnosis]
filterDiags v = filter $ relevantDiagKind v . diagKind

showRelDiags :: Int -> [Diagnosis] -> String
showRelDiags v = unlines . map show . filterDiags v

printDiags :: Int -> [Diagnosis] -> IO ()
printDiags v = putStr . showRelDiags v

instance Show Diagnosis where
    showsPrec _ = shows . pretty

instance Pretty Diagnosis where
    pretty (Diag k s (Range sp)) = sep
        [ sep [case sp of
            [] -> Doc.empty
            _ -> prettyRange sp <> colon
        , case k of
            MessageW -> Doc.empty
            _ -> text (case k of
                  Error -> "***"
                  _ -> "###") <+> text (show k) <> colon
        ]
      , text s]

instance GetRange Diagnosis where
    getRange = diagPos

instance Pretty a => Pretty (Result a) where
    pretty (Result ds m) = vcat $ pretty m : map pretty ds
