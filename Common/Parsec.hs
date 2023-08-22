{- |
Module      :  ./Common/Parsec.hs
Description :  Parsec extensions
Copyright   :  (c) Christian Maeder, DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

frequently useful shortcuts mainly for character parsers
-}

module Common.Parsec where

import Text.ParserCombinators.Parsec
import Control.Monad

-- * monad shortcuts

infixl 1 <<

(<<) :: Monad m => m a -> m b -> m a
(<<) = liftM2 const

forget :: Monad m => m a -> m ()
forget = (>> return ())

pair :: Monad m => m a -> m b -> m (a, b)
pair = liftM2 (,)

infixr 5 <:>

(<:>) :: Monad m => m a -> m [a] -> m [a]
(<:>) = liftM2 (:)

infixr 5 <++>

(<++>) :: Monad m => m [a] -> m [a] -> m [a]
(<++>) = liftM2 (++)

infixl 4 >->

(>->) :: Monad m => m a -> (a -> b) -> m b
(>->) p f = liftM f p

single :: Monad m => m a -> m [a]
single = liftM return

flat :: Monad m => m [[a]] -> m [a]
flat = liftM concat

enclosedBy :: Monad m => m [a] -> m a -> m [a]
enclosedBy p q = q <:> p <++> single q

-- * parsec shortcuts

-- | parse an optional list
optionL :: GenParser tok st [a] -> GenParser tok st [a]
optionL = option []

-- | shortcut for @try . string@
tryString :: String -> CharParser st String
tryString = try . string

-- | nested comments, open and closing strings must have at least one char
nestedComment :: String -> String -> CharParser st String
nestedComment op cl =
    let inComment = tryString cl
           <|> (nestedComment op cl <|> single anyChar) <++> inComment
    in tryString op <++> inComment

-- | a literal enclosed in quotes and a backslash as escape character
quotedLit :: Char -> CharParser st String
quotedLit q = enclosedBy (flat $ many $ single (noneOf ['\\', q])
                        <|> char '\\' <:> single anyChar) $ char q

-- | text in double quotes
stringLit :: CharParser st String
stringLit = quotedLit '"'

-- | text in single quotes
sQuoted :: CharParser st String
sQuoted = quotedLit '\''

-- | non-nested block
plainBlock :: String -> String -> CharParser st String
plainBlock op cl = tryString op >> manyTill anyChar (tryString cl)

reserved :: [String] -> CharParser st String -> CharParser st String
-- | reject keywords
reserved l p = try $ do
  s <- p
  if elem s l then unexpected $ "keyword " ++ show s else return s

{- | Similar to 'lookAhead', but runs the parser in an isolated sandbox.
The function is monadic but in a read-only manner.  Useful if 'lookAhead'
taints error messages. -}
sneakAhead :: CharParser st a -> CharParser st (Either ParseError a)
sneakAhead p = do
  i <- getInput
  state <- getParserState
  return $ runParser (setParserState state >> p) (stateUser state) "" i
