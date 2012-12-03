module Generic.Tools where


<insert>


-- the following function:
--  1. call mmt on the text
--  2. transform mmt output into ParseTree
toPT :: String -> Tree
toPT s = theo_to_lf s
