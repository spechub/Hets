{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./MMT/Tools.hs
Description :  parse tree produced by MMT
Copyright   :
License     :
Maintainer  :  a.jakubauskas@jacobs-university.de
Stability   :  experimental
Portability :
-}
module MMT.Tools where
import Data.Typeable

-- | identifier is just a string
type Id = String

{- |
tree:
  variables

  func. application
    Maybe( patternName, instanceName)
    name
    arguments
  OR
  symbol (0 args)

  binding

  typed binding
-}
data Tree = Variable Id |
    Application Id (Maybe (Id, Id)) [Tree] |
    Bind Id Id Tree |
    Tbind Id Id Tree Tree deriving (Show, Typeable)

-- declaration - represents instance of pattern
data Decl = Decl Id Id [Tree] deriving (Show, Typeable)

-- signature
data Sign = Sign [Decl] deriving (Show, Typeable)

-- theory
data Theo = Theo {sign :: Sign, axioms :: [Tree]} deriving (Show, Typeable)
