{- |
Module      :  $Header$
Description :  Parsec extensions
Copyright   :  (c) Christian Maeder, DFKI GmbH 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
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

single :: Monad m => m a -> m [a]
single = liftM return

flat :: Monad m => m [[a]] -> m [a]
flat = liftM concat

begDoEnd :: Monad m => m a -> m [a] -> m a -> m [a]
begDoEnd open p close = open <:> p <++> single close

enclosedBy :: Monad m => m [a] -> m a -> m [a]
enclosedBy p q = begDoEnd q p q

-- * parsec shortcuts

-- | parse an optional list
optionL :: GenParser tok st [a] -> GenParser tok st [a]
optionL = option []

-- | shortcut for @try . string@
tryString :: String -> CharParser st String
tryString = try . string

-- | nested comments, open and closing strings must have at least two chars
nestedComment :: String -> String -> CharParser st String
nestedComment op cl = case (op, cl) of
  (oh : ot : _, ch : ct : _) ->
    tryString op <++>
    flat (many $ single
          (noneOf [oh, ch]
           <|> try (char ch << notFollowedBy (char ct))
           <|> try (char oh << notFollowedBy (char ot)))
          <|> nestedComment op cl)
    <++> string cl
  _ -> error "nestedComment"

-- | non-nested block
plainBlock :: String -> String -> CharParser st String
plainBlock op cl = tryString op >> manyTill anyChar (tryString cl)

reserved :: [String] -> CharParser st String -> CharParser st String
-- | reject keywords
reserved l p = try $ do
  s <- p
  if elem s l then unexpected $ show s else return s
