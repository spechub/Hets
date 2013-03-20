module MMT.Tools where

-- identifier
type Id = String

{- tree:
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
    Application Id (Maybe(Id, Id)) [Tree] |
    Bind Id Id Tree |
    Tbind Id Id Tree Tree deriving (Show)

-- declaration - represents instance of pattern
data Decl = Decl Id Id [Tree] deriving (Show)

-- signature
data Sign = Sign [Decl] deriving (Show)

-- theory
data Theo = Theo{sign::Sign, axioms::[Tree]} deriving (Show)
