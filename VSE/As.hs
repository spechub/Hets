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

import Data.Char
import Common.Id
import Common.Doc
import Common.DocUtils
import CASL.AS_Basic_CASL
import CASL.ToDoc ()

-- | further VSE signature entries
data Sigentry = Procedure Id [Procparam ()] Range deriving (Show, Eq)

-- | a procedure parameter
data Procparam a = Procparam a Paramkind SORT deriving (Show, Eq, Ord)

-- | input or output procedure parameter kind
data Paramkind = In | Out deriving (Show, Eq, Ord)

-- | wrapper for positions
data Ranged a = Ranged a Range deriving (Show, Eq, Ord)

-- | programs with ranges
type Program = Ranged PlainProgram

-- | programs based on restricted terms and formulas
data PlainProgram =
    Abort
  | Skip
  | Assign VAR (TERM ())
  | Call Id [TERM ()] -- ^ a procedure call
  | Return (TERM ())
  | Block [VAR_DECL] Program
  | Seq Program Program
  | If (FORMULA ()) Program Program
  | While (FORMULA ()) Program
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
data Defproc = Defproc Id [Procparam VAR] Program deriving (Show, Eq, Ord)
-- maybe CASL ops can be associated to programs as well

-- | the sentences for the logic
data Sentence =
    FormulaSen Dlformula
  | DefprocSen [Defproc]
    deriving (Show, Eq, Ord)

{- formula kinds should be covered by Named Sentence -}

-- * Pretty instances

ppWithSemis :: Pretty a => [a] -> Doc
ppWithSemis = fsep . punctuate semi . map pretty

proc :: Doc
proc = text "PROCEDURE"

params :: Doc -> Doc
params = (text "PARAMS" <+>)

instance Pretty Sigentry where
  pretty (Procedure p ps _) = fsep
    [ proc <+> idDoc p
    , if null ps then empty else params $ fsep $ punctuate semi
             $ map prettyParam ps ]

prettyParam :: Procparam a -> Doc
prettyParam (Procparam _ m s) = text (map toUpper $ show m) <+> idDoc s

instance Pretty a => Pretty (Procparam a) where
  pretty p@(Procparam v _ _) =
    pretty v <+> colon <+> prettyParam p

block :: Doc -> Doc
block d = vcat [text "BEGIN", d, text "END"]

instance Pretty Defproc where
  pretty (Defproc p ps pr) = vcat
    [ proc <+> idDoc p
    , if null ps then empty else
          params $ ppWithSemis ps
    , text "BODY" <+> pretty pr
    , text "PROCEDUREEND"]

instance Pretty a => Pretty (Ranged a) where
  pretty (Ranged a _) = pretty a

instance Pretty PlainProgram where
  pretty prg = case prg of
    Abort -> text "ABORT"
    Skip -> text "SKIP"
    Assign v t -> pretty v <+> text ":=" <+> pretty t
    Call p ts -> idDoc p <>
      if null ts then empty else parens $ ppWithCommas ts
    Return t -> text "RETURN" <+> pretty t
    Block vs p -> block $ fsep [ppWithSemis vs, pretty p]
    Seq p1 p2 -> vcat [pretty p1 <> semi, pretty p2]
    If f t e -> vcat
      [ text "IF" <+> pretty f
      , text "THEN" <+> pretty t
      , text "ELSE" <+> pretty e
      , text "FI" ]
    While f p -> vcat
      [ text "WHILE" <+> pretty f
      , text "DO" <+> pretty p
      , text "OD" ]

instance Pretty Dlformula where
  pretty (Dlformula b p f _) = let d = pretty p in
    (case b of
       Box -> brackets d
       Diamond -> less <> d <> greater)
    <+> parens (pretty f)

instance Pretty Sentence where
  pretty sen = case sen of
    FormulaSen f -> pretty f
    DefprocSen ps -> ppWithSemis ps
