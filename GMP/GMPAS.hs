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

instance Show Formula where

-- to be done
