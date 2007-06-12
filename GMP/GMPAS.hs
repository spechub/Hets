----------------------------------------------------------------
-- the Generic Model Parser Abstract Syntax
-- Copyright 2007, Lutz Schroeder and Georgel Calin
----------------------------------------------------------------

module GMPAS where

----------------------------------------------------------------
-- Abstract Syntax
----------------------------------------------------------------

type Mindex = String          -- index of the Modal Operator

data Otype = Square | Angle   -- type of the Modal Operator

data Junctor = And | Or | If | Fi | Iff

data Mop = Mindex Formula Otype     -- Modal Operator

data Formula  = F                -- datatype for the formulae
              | T
              | Neg Formula

              | Junctor Formula Junctor Formula 
              
              | Mop Mop Formula                       

----------------------------------------------------------------
-- Print Abstract Syntax
----------------------------------------------------------------
{-
instance Show Mop where
        show (Mop x Square) = "[" ++ show x ++ "]"
        show (Mop x Angle) = "<" ++ show x ++ ">"
-}

instance Show Junctor where
    show j = case j of
        And -> "/\\"
        Or  -> "\\/"
        If  -> "->"
        Fi  -> "<-"
        Iff -> "<->"

instance Show Formula where
    show f = case f of 
        F -> "F"
        T -> "T"
        Neg x -> "~" ++ show x

        Junctor x j y -> "(" ++ show x ++ " " ++ show j ++ " " ++ show y ++ ")"

        Mop (Mindex y Square) x -> "[" ++ show y ++ "]" ++ show x
        Mop (Mindex y Angle) x ->  "<" ++ show y ++ ">" ++ show x

----------------------------------------------------------------
-- 
----------------------------------------------------------------
