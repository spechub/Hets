HUnitTest98.lhs  --  test for HUnit, using Haskell language system "98"

$Id$

> module Main (main) where

> import HUnit
> import HUnitTestBase


> main = runTestTT (test [baseTests])
