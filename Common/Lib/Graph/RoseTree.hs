--
--  RoseTree.hs -- Rose Trees
--
module RoseTree (
   -- type
   Tree (..),
   -- functions
   postorder,postorderF,preorder,preorderF
) where


data Tree a = Br a [Tree a]
     deriving (Eq)

instance Show a => Show (Tree a) where
  showsPrec _ (Br x []) = shows x
  showsPrec _ (Br x hs) = shows x . ('<':) . shows hs

postorder :: Tree a -> [a]
postorder (Br v ts) = postorderF ts ++ [v]

postorderF :: [Tree a] -> [a]
postorderF ts = concat (map postorder ts)

preorder :: Tree a -> [a]
preorder (Br v ts) = v:preorderF ts

preorderF :: [Tree a] -> [a]
preorderF ts = concat (map preorder ts)


