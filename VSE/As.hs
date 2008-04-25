{- |
Module      :  $Header$
Description :  abstract syntax of VSE programs and dynamic logic
Copyright   :  (c) C. Maeder, DFKI 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

CASL extention to VSE programs and dynamic logic
as described on page 4-7 (Sec 2.3.1, 2.5.2, 2.5.4, 2.6) of
Bruno Langenstein's API description
-}

module VSE.As where

import Common.Id
import Common.DocUtils
import CASL.AS_Basic_CASL

-- | further VSE signature entries
data Sigentry = Procedure Id [Procparam] Range deriving (Show, Eq)

-- | a procedure parameter
data Procparam = Procparam Paramkind SORT deriving (Show, Eq)

-- | input or output procedure parameter kind
data Paramkind = In | Out deriving (Show, Eq)

-- | wrapper for positions
data Ranged a = Ranged a Range deriving (Show, Eq, Ord)

-- | programs with ranges
type Program = Ranged PlainProgram

-- | programs based on restricted terms and formulas
data PlainProgram =
    Abort
  | Skip
  | Assign VAR (TERM ())
  | Block [VAR_DECL] Program
  | Seq Program Program
  | If (FORMULA ()) Program Program
  | While (FORMULA ()) Program
  | Call Id [TERM ()] -- ^ a procedure call
    deriving (Show, Eq, Ord)

{- For functions a return is needed, but functions could be emulated
by an extra out parameter -}

{- vardecls do not consider initialization terms here as these may be
seens as initial assignments of the program block -}

-- | extend CASL formulas by box or diamond formulas
data Dlformula = Dlformula BoxOrDiamond Program (FORMULA Dlformula) Range
    deriving (Show, Eq, Ord)

-- | box or diamond indicator
data BoxOrDiamond = Box | Diamond deriving (Show, Eq, Ord)

-- | procedure definitions as basic items becoming sentences
data Defproc = Defproc Id [VAR] Program deriving (Show, Eq, Ord)
-- maybe CASL ops can be associated to programs as well

-- | the sentences for the logic
data Sentence =
    FormulaSen Dlformula
  | DefprocSen [Defproc]
    deriving (Show, Eq, Ord)

{- formula kinds should be covered by Named Sentence -}

-- * Pretty instances

instance Pretty Sigentry

instance Pretty Defproc

instance Pretty Dlformula

instance Pretty Sentence
