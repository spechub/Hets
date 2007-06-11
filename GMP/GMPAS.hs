----------------------------------------------------------------
-- the Generic Model Parser Abstract Syntax
-- Copyright 2007, Lutz Schroeder and Georgel Calin
----------------------------------------------------------------

module GMPAS where

import Language.Haskell.Pretty

----------------------------------------------------------------
-- Abstract Syntax
----------------------------------------------------------------

type Mindex 	= String           -- index of the Modal Operator

data Otype 		= Square | Angle   -- type of the Modal Operator

data Mop 		= Mindex Otype 	   -- Modal Operator

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
-- Pretty print Abstract Syntax
----------------------------------------------------------------
type ShowF = String -> String
showsFormula :: (Show a) => Formula a -> ShowF
showsFormula F = shows "F"
showsFormula T = shows "T"

showsFormula Neg x = ('~') . showsFormula x
showsFormula And x y = ('(') . showsFormula x . ('/') . ('\\') . showsFormula y . (')')
showsFormula Or x y = ('(') . showsFormula x . ('\\') . ('/') . showsFormula y . (')')

showFormula If x y = showsFormula x . ('-') . ('>') . showsFormula y
showFormula Fi x y = showsFormula x . ('<') . ('-') . showsFormula y
showFormula Iff x y = showsFormula x . ('<') . ('-') . ('>') . showsFormula y

showFormula Mop x = showsFormula x
						
instance Show a => Show (Formula a) where
	show f = showsFormula f

-- the last section needs to be debugged
