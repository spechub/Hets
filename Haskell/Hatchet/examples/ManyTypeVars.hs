-- ManyTypeVars.hs
-- Output: (False,False)

main = cmp 0 0 0 0 0 1 2 3 4

cmp :: (Eq a, Ord b) => c -> b -> d -> b -> e -> a -> f -> a -> g -> (Bool, Bool)
cmp a w b x c y d z e
  = (w < x, y == z)

cmp2 :: Ord a => a -> a -> Bool
cmp2 w x
  = w < x

alphabet :: a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k -> l -> m ->
            n -> o -> p -> q -> r -> s -> t -> u -> v -> w -> x -> y -> z -> a1
alphabet a b c d e f g h i j k l m n o p q r s t u v w x y z = error "sorry"
