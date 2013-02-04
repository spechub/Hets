module Generic.Tools where

data Id   = String

data Tree = Variable Id | Application Id [Tree] | Bind Id Id Tree | Tbind Id Id Tree Tree

data Decl = Decl Id Id [Tree]

data Sign = Sign [Decl]

data Theo = Theo Sign [Tree]

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
