module ATermAbstractSyntax where

data ATerm = AAppl String [ATerm]
           | AList [ATerm]
           | AInt Integer
           deriving (Read,Show,Eq)