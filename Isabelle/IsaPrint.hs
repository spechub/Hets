{- |
Module      :  $Header$
Copyright   :  (c) University of Cambridge, Cambridge, England
               adaption (c) Till Mossakowski, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

   Printing functions for Isabelle logic.
-}

module Isabelle.IsaPrint where

import Common.Id 
import Common.PrettyPrint

-- drop special characters from Ids
transChar :: Char -> String
transChar '[' = "__"
transChar ']' = "__"
transChar '?' = "__"
transChar x = [x]

transString :: String -> String
transString = concat . map transChar

showIsa :: Id -> String
showIsa = transString . flip showPretty ""

showIsaSid :: SIMPLE_ID -> String
showIsaSid = transString . flip showPretty ""

-- disambiguation of overloaded ids
showIsaI :: Id -> Int -> String
showIsaI ident i = showIsa ident ++ "__" ++ show i

