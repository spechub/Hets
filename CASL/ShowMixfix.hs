
{- HetCATS/CASL/ShowMixfix.hs
   $Id$
   Author:
   Year:    2002

-}

module CASL.ShowMixfix where

import CASL.AS_Basic_CASL
import CASL.Formula
import Common.Lib.Parsec
import Common.AnnoState
import Common.Id

showTerm :: TERM -> String

showTerm (Simple_id s) = tokStr s
showTerm (Application op_s args _) = showOps op_s ++ "(" ++ ")"
showTerm t = "bla"

showOps :: OP_SYMB -> String
showOps(Op_name i) = showId i ""
showOps(Qual_op_name i t _) = showId i "" ++ "..."