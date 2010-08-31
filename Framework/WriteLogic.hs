{- |
Module      :  $Header$
Description :  Utility functions for writing object logic instances
Copyright   :  (c) Kristina Sojakova, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  k.sojakova@jacobs-university.de
Stability   :  experimental
Portability :  portable
-}

module Framework.WriteLogic where

import Data.List

tab :: String
tab = "    "

multiOpt :: String
multiOpt = "MultiParamTypeClasses"

synOpt :: String
synOpt = "TypeSynonymInstances"

prefixBy :: String -> [String] -> [String]
prefixBy s xs = map (\ x -> s ++ x) xs

sepHoriz :: [String] -> String
sepHoriz = concat . (prefixBy " ")

sepTabVert :: [String] -> String
sepTabVert = concat . (prefixBy $ "\n" ++ tab)

mkCompOpt :: [String] -> String
mkCompOpt opts = "{-# LANGUAGE " ++ intercalate ", " opts ++ " #-}"

mkModDecl :: String -> String
mkModDecl n = "module " ++ n ++ " where"

mkImports :: [String] -> String
mkImports imps =
  intercalate "\n" $ prefixBy "import " imps

mkLid :: String -> String
mkLid lid = "data " ++ lid ++ " = " ++ lid ++ " deriving Show"

mkImpl :: String -> String -> String -> String
mkImpl f lid imp =
  f ++ " " ++ lid ++ " = " ++ imp

mkInst :: String -> String -> [String] -> [String] -> String
mkInst inst lid args impls =
  let header = "instance " ++ inst ++ " " ++ lid
      argL = length args > 1
      impE = not $ null impls
      in header ++
         if argL && impE then
            sepTabVert $ args ++ ["where"] ++ impls else
            if argL then
               sepTabVert args else
               if impE then
                  sepHoriz args ++ " where" ++ sepTabVert impls else
                  sepHoriz args

mkDecl :: String -> String -> String -> String
mkDecl n t v = n ++ " :: " ++ t ++ "\n" ++ n ++ " = " ++ v
