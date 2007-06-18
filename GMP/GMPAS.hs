----------------------------------------------------------------
-- the Generic Model Parser Abstract Syntax
-- Copyright 2007, Lutz Schroeder and Georgel Calin
----------------------------------------------------------------

module GMPAS where

----------------------------------------------------------------
-- Abstract Syntax
----------------------------------------------------------------
data ModalK = ModalK ()                         -- K modal logic
data ModalKD = ModalKD ()                      -- KD modal logic

data BitString = BitString Integer     -- for bit-string indexes

data Kars = Kars [Char]                    -- for string indexes

data Otype = Square | Angle        -- type of the Modal Operator

data Junctor = And | Or | If | Fi | Iff

data Mop a = Mop a Otype         -- Modal Operator: index & type

data Formula a = F                  -- datatype for the formulae
               | T
               | Neg (Formula a)

               | Junctor (Formula a) Junctor (Formula a)
              
               | Mapp (Mop a) (Formula a)   -- modal appl constr

----------------------------------------------------------------
-- Print Abstract Syntax
----------------------------------------------------------------
instance Show a => Show (Mop a) where
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
instance Show a => Show (Formula a) where
    show f = case f of 
        F -> "F"
        T -> "T"
        Neg x -> "~" ++ show x
        Junctor x j y -> "(" ++ show x ++ " " ++ show j ++ " " ++ show y ++ ")"
        Mapp m x -> show m ++ " " ++ show x
instance Show Kars where
    show (Kars l) = show l
instance Show BitString where
    show (BitString s) = let (d,p)=divMod s 2 in
                            if (d == 0) then show p
                                        else show (BitString d) ++ show p
instance Show ModalK where
    show (ModalK ()) = show ()
instance Show ModalKD where
    show (ModalKD ()) = show ()
