----------------------------------------------------------------
-- the Generic Model Parser Abstract Syntax
-- Copyright 2007, Lutz Schroeder and Georgel Calin
----------------------------------------------------------------

module GMPAS where

-- import Language.Haskell.Pretty -- this may not be needed

----------------------------------------------------------------
-- Abstract Syntax
----------------------------------------------------------------

type Mindex 	= String           -- index of the Modal Operator

data Otype 		= Square | Angle   -- type of the Modal Operator

data Mop 		= Mindex Otype     -- Modal Operator

data Formula 	= F                -- datatype for the formulae
				| T

				| Neg Formula			-- "~"
				| And Formula Formula	-- "/\"
				| Or Formula Formula	-- "\/"

				| If Formula Formula 	-- "->"
				| Fi Formula Formula 	-- "<-"
				| Iff Formula Formula	-- "<->"

				| Mop Formula			

----------------------------------------------------------------
-- Print Abstract Syntax
----------------------------------------------------------------
{-
instance Show Mop where
	show (Mop x Square) = "[" ++ show x ++ "]"
	show (Mop x Angle) = "<" ++ show x ++ ">"
-}
instance Show Formula where
	show (F) = "F"
	show (T) = "T"

	show (Neg x) = "~" ++ show x
	show (And x y) = "(" ++ show x ++"/\\" ++ show y ++ ")"
	show (Or x y) = "(" ++ show x ++"\\/" ++ show y ++ ")"

	show (If x y) = show x ++ "->" ++ show y
	show (Fi x y) = show x ++ "<-" ++ show y
	show (Iff x y) = show x ++ "<->" ++ show y

	show ((Mop y Square) x) = "[" ++ show y ++ "]" ++ show x
	show ((Mop y Angle) x) = "<" ++ show y ++ ">" ++ show x

-- the last section needs to be debugged
