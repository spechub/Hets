{- |
Module      :  $Header$
Description : Constants for the translation of processes from CspCASL
              to IsabelleHOL (CspProver)
Copyright   :  (c) Andy Gimblett, Liam O'Reilly and Markus Roggenbach,
                   Swansea University 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  csliam@swansea.ac.uk
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

Constants for the translation of processes from CspCASL to IsabelleHOL
(CspProver)

-}

module CspCASL.Trans_Consts where

import CASL.AS_Basic_CASL
import Isabelle.IsaConsts
import Isabelle.IsaSign

alphabetS :: String
alphabetS = "Alphabet"

barExtS :: String
barExtS = "_Bar"

classS :: String
classS = "class"

classOp :: Term -> Term
classOp = termAppl (conDouble classS)

-- Convert a SORT to a string
convertSort2String :: SORT -> String
convertSort2String s = show s
