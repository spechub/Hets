----------------------------------------------------------------
-- the Generic Model Parser Abstract Syntax
-- Copyright 2007, Lutz Schroeder and Georgel Calin
----------------------------------------------------------------

module GMPAS where

-- import Language.Haskell.Pretty -- this may not be needed

----------------------------------------------------------------
-- Abstract Syntax
----------------------------------------------------------------

type Mindex = String          -- index of the Modal Operator

data Otype = Square | Angle   -- type of the Modal Operator

-- data Junctor = And | Or | If | Fi | Iff

data Mop = Mindex Formula Otype     -- Modal Operator

data Formula  = F                -- datatype for the formulae
              | T
              | Neg Formula

--            | Junctor Junctor Formula Formula 
              | And Formula Formula
              | Or Formula Formula
              | If Formula Formula
              | Fi Formula Formula
              | Iff Formula Formula

              | Mop Mop Formula                       

----------------------------------------------------------------
-- Print Abstract Syntax
----------------------------------------------------------------
{-
instance Show Mop where
        show (Mop x Square) = "[" ++ show x ++ "]"
        show (Mop x Angle) = "<" ++ show x ++ ">"
-}
{-
instance Show Junctor where
    show j = case Junctor j of
        And -> "/\\"
        Or  -> "\\/"
        If  -> "->"
        Fi  -> "<-"
        Iff -> "<->"
        _   -> error "GMPAS.ShowJunctor"

-}
instance Show Formula where
    show f = case f of 
        F -> "F"
        T -> "T"
        Neg x -> "~" ++ show x
--      Junctor (Junctor j) x y -> "(" ++ show x ++ show j ++ show y ++ ")"

        And x y -> "(" ++ show x ++ "/\\" ++ show y ++ ")"
        Or x y -> "(" ++ show x ++"\\/" ++ show y ++ ")"
        If x y -> show x ++ "->" ++ show y
        Fi x y -> show x ++ "<-" ++ show y
        Iff x y -> show x ++ "<->" ++ show y

        Mop (Mindex y Square) x -> "[" ++ show y ++ "]" ++ show x
        Mop (Mindex y Angle) x ->  "<" ++ show y ++ ">" ++ show x

----------------------------------------------------------------
-- File brought to working state. More work needed for simplifying the code via the "Junctor" datatype.
----------------------------------------------------------------
