module Utils where

unjust:: Maybe String -> String
unjust s = case s of
	Nothing -> ""
	Just t -> t

