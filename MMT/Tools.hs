module MMT.Tools where

--data Id   = String

data Tree = Variable String | 
    Application String [Tree] | 
    Bind String String Tree | 
    Tbind String String Tree Tree deriving (Show)

data Decl = Decl String String [Tree] deriving (Show)

data Sign = Sign [Decl] deriving (Show)

-- shouldn't it be Theo Sign [Decl] ?
data Theo = Theo Sign [Tree] deriving (Show)

{-
parseSpec String 
          ParseTree
parseSpec text = 
  1. call mmt on the text
  2. transform mmt output into ParseTree

  -}
{-
parseSpec :: String
parseSpec specFN = ()
-}
