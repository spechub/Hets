{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{- |
Module      :  $Header$
Description :  A couple helper functions
Copyright   :  (c) J. von Schroeder, DFKI Bremen 2012
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Jonathan von Schroeder <j.von_schroeder@dfki.de>
Stability   :  provisional
Portability :  non-portable

-}
module THF.Utils (
 Unique,
 evalUnique,
 numbered
) where

import THF.As

import Common.Id (Token(..))

import Control.Monad.State
import Control.Monad.Identity

{- taken from http://www.haskell.org/haskellwiki/New_monads/MonadUnique -}
newtype UniqueT m a = UniqueT (StateT Integer m a)
    deriving (Functor, Monad, MonadTrans, MonadIO)
 
newtype Unique a = Unique (UniqueT Identity a)
    deriving (Functor, Monad, MonadUnique)
 
class Monad m => MonadUnique m where
    fresh :: m Integer
 
instance (Monad m) => MonadUnique (UniqueT m) where
    fresh = UniqueT $ do
                n <- get
                put (succ n)
                return n

evalUniqueT :: Monad m => UniqueT m a -> m a
evalUniqueT (UniqueT s) = evalStateT s 1

evalUnique :: Unique a -> a
evalUnique (Unique s) = runIdentity (evalUniqueT s)

addSuffix :: String -> AtomicWord -> AtomicWord
addSuffix s a = case a of
  A_Lower_Word t    -> A_Lower_Word $ rename t
  A_Single_Quoted t -> A_Single_Quoted $ rename t
 where rename = (\t -> t { tokStr = (tokStr t) ++ s})

numbered :: AtomicWord -> Unique AtomicWord
numbered a = do
 f <- fresh
 return (addSuffix ("_"++show f) a)
