{- | Module     : $Header$
 -  Description : Abstract syntax for the Generic Modal Prover
 -  Copyright   : (c) Georgel Calin & Lutz Schroeder, DFKI Lab Bremen
 -  License     : GPLv2 or higher
 -  Maintainer  : g.calin@jacobs-university.de
 -  Stability   : provisional
 -  Portability : non-portable (various -fglasgow-exts extensions)
 -
 -  Provides data structures and show instances for the more general data types
 -  used in the implementation of the Generic Modal Prover -}
module GMP.GMPAS where

import qualified Data.Set as Set

{- | Datatype with which formulas are handled in the implementation
 - A formula will recurse in a tree-like manner via negation, junction or modal
 - application until one of "true", "false" or "variable" -}
data Formula a = F
               | T
               | Neg (Formula a)
               | Junctor (Formula a) Junctor (Formula a)
               | Mapp (Mop a) (Formula a)
               | Var Char (Maybe Integer)
    deriving (Eq, Ord)
instance Show a => Show (Formula a) where
    show f = case f of
        F -> "F"
        T -> "T"
        Neg x -> "~" ++ show x
        Junctor x j y -> "(" ++ show x ++ " " ++ show j ++ " " ++ show y ++ ")"
        Mapp m x -> show m ++ show x
        Var c i -> case i of
                     Nothing -> [c]
                     Just ii -> [c] ++ show ii

-- | Junctors for "and", "or", "implies", "is implied" and "if and only if"
data Junctor = And | Or | If | Fi | Iff
    deriving (Eq, Ord)
instance Show Junctor where
    show j = case j of
        And -> "/\\"
        Or  -> "\\/"
        If  -> "->"
        Fi  -> "<-"
        Iff -> "<->"

-- | Datatype for the modal operator
data Mop a = Mop a Otype
    deriving (Eq, Ord)
instance Show a => Show (Mop a) where
    show m = case m of
            Mop x Square -> "[" ++ show x ++ "]"
            Mop x Angle  -> "<" ++ show x ++ ">"

-- | Type of the modal operator used in the modal aplication
data Otype = Square | Angle
    deriving (Eq, Ord)

-- | Datatype of the modal index of K modal logic
data ModalK = ModalK ()
    deriving (Eq, Ord)
instance Show ModalK where
    show (ModalK ()) = ""

-- | Datatype of the modal index of KD modal logic
data ModalKD = ModalKD ()
    deriving (Eq, Ord)
instance Show ModalKD where
    show (ModalKD ()) = ""

-- | Datatype of the modal index of Graded modal logic
data GML = GML Int
    deriving (Eq, Ord)
instance Show GML where
    show (GML n) = show n

-- | Datatype of the modal index of Coalition logic
data CL = CL (Set.Set Int) Int
    deriving (Eq, Ord)
instance Show CL where
    show (CL i m) = let showSet s =
                         case (Set.size s) of
                           0 -> ""
                           1 -> let (aux, next) = Set.deleteFindMin s
                                in show aux ++ showSet next
                           _ -> let (aux, next) = Set.deleteFindMin s
                                in show aux ++ "," ++ showSet next
                    in "{" ++ showSet i ++ "}" ++ ":" ++ show m

-- | Datatype of the modal index of Majority logic
data ML = ML Int | W
    deriving (Eq, Ord)
instance Show ML where
    show x = case x of
               ML n -> show n
               W -> "W"

-- | Datatype of the generic (string) modal index
data Kars = Kars [Char]
    deriving (Eq, Ord)
instance Show Kars where
    show (Kars l) = show l

-- | Datatype for the propositional clauses
data PropClause = Pimplies [Int] [Int]
    deriving Show

-- | Datatype for the modal clauses
data ModClause a = Mimplies [Formula a] [Formula a]
    deriving (Show, Eq, Ord)

