----------------------------------------------------------------
-- the Generic Model Parser Abstract Syntax
-- Copyright 2007, Lutz Schroeder and Georgel Calin
----------------------------------------------------------------

module GMPAS where

----------------------------------------------------------------
-- Abstract Syntax
----------------------------------------------------------------
data ModalK = ModalK ()                         -- K modal logic
    deriving (Eq, Ord)
data ModalKD = ModalKD ()                      -- KD modal logic
    deriving (Eq, Ord)
data BitString = BitString Integer     -- for bit-string indexes
    deriving (Eq, Ord)
data Kars = Kars [Char]                    -- for string indexes
    deriving (Eq, Ord)
data Otype = Square | Angle        -- type of the Modal Operator
    deriving (Eq, Ord)
data Junctor = And | Or | If | Fi | Iff
    deriving (Eq, Ord)
data Mop a = Mop a Otype         -- Modal Operator: index & type
    deriving (Eq, Ord)
data Formula a = F                  -- datatype for the formulae
               | T
               | Neg (Formula a)

               | Junctor (Formula a) Junctor (Formula a)
              
               | Mapp (Mop a) (Formula a)   -- modal appl constr
    deriving (Eq, Ord)
-- Datatype for handling the pseudoeval step in the algorithm -- 
data TVandMA a = TVandMA (Formula a, Bool)
    deriving (Eq, Ord)
----------------------------------------------------------------
-- Show Instances 4 Abstract Syntax
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
    show (ModalK ()) = ""
instance Show ModalKD where
    show (ModalKD ()) = ""
instance Show a => Show (TVandMA a) where
    show (TVandMA (x,y)) = "(" ++ show x ++ "," ++ show y ++ ")"
