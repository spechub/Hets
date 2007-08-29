-------------------------------------------------------------------------------
-- the Generic Model Parser Abstract Syntax
-- Copyright 2007, Lutz Schroeder and Georgel Calin
-------------------------------------------------------------------------------

module GMP.GMPAS where

import qualified Data.Set as Set
-------------------------------------------------------------------------------
-- Abstract Syntax
-------------------------------------------------------------------------------
-- Datatype for the clauses ---------------------------------------------------
data PropClause = Pimplies [Int] [Int] 
    deriving Show
-- Datatypes for the modal index ----------------------------------------------
data ModalK = ModalK ()                                  -- K modal logic index
    deriving (Eq, Ord)
data ModalKD = ModalKD ()                               -- KD modal logic index
    deriving (Eq, Ord)
data GML = GML Int                                  -- Graded modal logic index
    deriving (Eq, Ord)
data CL = CL (Set.Set Int)                       -- Coalition modal logic index
    deriving (Eq, Ord)
data ML = ML Int                                  -- Majority modal logic index
        | W
    deriving (Eq, Ord)
data Kars = Kars [Char]                            -- Generic modal logic index
    deriving (Eq, Ord)
-- Formula Datatype -----------------------------------------------------------
data Otype = Square | Angle                       -- type of the Modal Operator
    deriving (Eq, Ord)
data Junctor = And | Or | If | Fi | Iff
    deriving (Eq, Ord)
data Mop a = Mop a Otype                        -- Modal Operator: index & type
    deriving (Eq, Ord)
data Formula a = F                                 -- datatype for the formulae
               | T
               | Neg (Formula a)

               | Junctor (Formula a) Junctor (Formula a)
              
               | Mapp (Mop a) (Formula a)                  -- modal appl constr
               | Var Char Integer                                  -- variables
    deriving (Eq, Ord)
-- Modal Clause (Negated and Positive modal Atoms -----------------------------
data ModClause a = Mimplies [Formula a] [Formula a]
    deriving (Eq, Ord)
-------------------------------------------------------------------------------
-- Show Instances 4 Abstract Syntax
-------------------------------------------------------------------------------
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
        Mapp m x -> show m ++ show x
        Var x i -> show ([x] ++ show i)
instance Show Kars where
    show (Kars l) = show l
instance Show CL where
    show (CL i) = let showSet s =
                        case (Set.size s) of
                          0 -> ""
                          1 -> let (aux, next) = Set.deleteFindMin s
                               in show aux ++ showSet next
                          _ -> let (aux, next) = Set.deleteFindMin s
                               in show aux ++ "," ++ showSet next
                  in "{"++ showSet i ++"}"
instance Show ModalK where
    show (ModalK ()) = ""
instance Show ModalKD where
    show (ModalKD ()) = ""
instance Show GML where
    show (GML n) = show n
instance Show ML where
    show x = case x of
               ML n -> show n
               W -> "W" 
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
