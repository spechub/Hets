module Kinds where

-- this should produce a kind error

data C x = Foo (B x) (x MyType)
data B y = Bar 

data MyType = MyType
