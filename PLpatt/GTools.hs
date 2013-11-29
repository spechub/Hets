module Generic.Tools where

-- TODO: Do we actually need this module?

data Tree = Variable Id |
            Application Id [Tree] |
            Bind Id Id Tree |
            Tbind Id Id Tree Tree

{- the following function:
  1. call mmt on the text
  2. transform mmt output into ParseTree -}
toPT :: String -> Tree
toPT = theo_to_lf
