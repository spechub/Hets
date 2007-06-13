----------------------------------------------------------------
-- the Generic Model Parser Abstract Syntax
-- Copyright 2007, Lutz Schroeder and Georgel Calin
----------------------------------------------------------------

module GMPAS where

----------------------------------------------------------------
-- Abstract Syntax
----------------------------------------------------------------

type Mindex = String             -- index of the Modal Operator

data Otype = Square | Angle      -- type of the Modal Operator

data Junctor = And | Or | If | Fi | Iff

data Mop = Mop Mindex Otype      -- Modal Operator

data Formula  = F                -- datatype for the formulae
              | T
              | Neg Formula

              | Junctor Formula Junctor Formula 
              
              | Mapp Mop Formula -- modal application constructor

----------------------------------------------------------------
-- Print Abstract Syntax
----------------------------------------------------------------
instance Show Mop where
        show m = case m of
            Mop x Square -> "[" ++ show x ++ "]"
            Mop x Angle  -> "<" ++ show x ++ ">"

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
        Mapp m x -> show m ++ " " ++ show x
----------------------------------------------------------------
-- 
----------------------------------------------------------------
