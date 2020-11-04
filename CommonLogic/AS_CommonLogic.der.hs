{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}
{- |
Module      :  ./CommonLogic/AS_CommonLogic.der.hs
Description :  Abstract syntax for common logic
Copyright   :  (c) Karl Luc, DFKI Bremen 2010, Eugen Kuksa and Uni Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  eugenk@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Definition of abstract syntax for common logic
-}

{-
  Ref.
  ISO/IEC IS 24707:2007(E)
-}

module CommonLogic.AS_CommonLogic where

import Common.Id as Id
import Common.IRI
import Common.Doc
import Common.DocUtils
import Common.Keywords
import qualified Common.AS_Annotation as AS_Anno

import Data.Data
import Data.Set (Set)

import GHC.Generics (Generic)
import Data.Hashable
import Common.Utils

-- DrIFT command
{-! global: GetRange !-}

newtype BASIC_SPEC = Basic_spec [AS_Anno.Annoted BASIC_ITEMS]
                     deriving (Show, Ord, Eq, Typeable)

data BASIC_ITEMS = Axiom_items [AS_Anno.Annoted TEXT_META]
                   deriving (Show, Ord, Eq, Typeable)

type PrefixMapping = (String, IRI)

emptyTextMeta :: TEXT_META
emptyTextMeta = Text_meta { getText = Text [] nullRange
                          , textIri = Nothing
                          , nondiscourseNames = Nothing
                          , prefix_map = [] }

data TEXT_META = Text_meta { getText :: TEXT
                           , textIri :: Maybe IRI
                           , nondiscourseNames :: Maybe (Set NAME)
                           , prefix_map :: [PrefixMapping]
                           } deriving (Show, Eq, Ord, Typeable, Data, Generic)
{- TODO: check static analysis and other features on discourse names,
as soon as parsers of segregated dialects are implemented -}

instance Hashable TEXT_META

-- Common Logic Syntax
data TEXT = Text [PHRASE] Id.Range
          | Named_text NAME TEXT Id.Range
            deriving (Show, Ord, Eq, Typeable, Data, Generic)

instance Hashable TEXT

data PHRASE = Module MODULE
            | Sentence SENTENCE
            | Importation IMPORTATION
            | Comment_text COMMENT TEXT Id.Range
              deriving (Show, Ord, Eq, Typeable, Data, Generic)

instance Hashable PHRASE

data COMMENT = Comment String Id.Range
               deriving (Show, Ord, Eq, Typeable, Data, Generic)

instance Hashable COMMENT

data MODULE = Mod NAME TEXT Id.Range
            | Mod_ex NAME [NAME] TEXT Id.Range
              deriving (Show, Ord, Eq, Typeable, Data, Generic)

instance Hashable MODULE

data IMPORTATION = Imp_name NAME
                   deriving (Show, Ord, Eq, Typeable, Data, Generic)

instance Hashable IMPORTATION

data SENTENCE = Quant_sent QUANT [NAME_OR_SEQMARK] SENTENCE Id.Range
              | Bool_sent BOOL_SENT Id.Range
              | Atom_sent ATOM Id.Range
              | Comment_sent COMMENT SENTENCE Id.Range
              | Irregular_sent SENTENCE Id.Range
                deriving (Show, Ord, Eq, Typeable, Data, Generic)

instance Hashable SENTENCE

data QUANT = Universal | Existential
             deriving (Show, Ord, Eq, Typeable, Data, Generic)

instance Hashable QUANT

data BOOL_SENT = Junction AndOr [SENTENCE]
               | Negation SENTENCE
               | BinOp ImplEq SENTENCE SENTENCE
                 deriving (Show, Ord, Eq, Typeable, Data, Generic)

instance Hashable BOOL_SENT

data AndOr = Conjunction | Disjunction
             deriving (Show, Ord, Eq, Typeable, Data, Generic)

instance Hashable AndOr

data ImplEq = Implication | Biconditional
              deriving (Show, Ord, Eq, Typeable, Data, Generic)

instance Hashable ImplEq

data ATOM = Equation TERM TERM
          | Atom TERM [TERM_SEQ]
            deriving (Show, Ord, Eq, Typeable, Data, Generic)

instance Hashable ATOM

data TERM = Name_term NAME
          | Funct_term TERM [TERM_SEQ] Id.Range
          | Comment_term TERM COMMENT Id.Range
          | That_term SENTENCE Id.Range
            deriving (Show, Ord, Eq, Typeable, Data, Generic)

instance Hashable TERM

data TERM_SEQ = Term_seq TERM
              | Seq_marks SEQ_MARK
                deriving (Show, Ord, Eq, Typeable, Data, Generic)

instance Hashable TERM_SEQ


type NAME = Id.Token
type SEQ_MARK = Id.Token

-- binding seq
data NAME_OR_SEQMARK = Name NAME
                     | SeqMark SEQ_MARK
                       deriving (Show, Eq, Ord, Typeable, Data, Generic)

instance Hashable NAME_OR_SEQMARK

data SYMB_MAP_ITEMS = Symb_map_items [SYMB_OR_MAP] Id.Range
                      deriving (Show, Ord, Eq, Typeable, Data)

data SYMB_OR_MAP = Symb NAME_OR_SEQMARK
                 | Symb_mapN NAME NAME Id.Range
                 | Symb_mapS SEQ_MARK SEQ_MARK Id.Range
                   deriving (Show, Ord, Eq, Typeable, Data)

data SYMB_ITEMS = Symb_items [NAME_OR_SEQMARK] Id.Range
                  -- pos: SYMB_KIND, commas
                  deriving (Show, Ord, Eq, Typeable, Data)


-- pretty printing using CLIF
instance Pretty BASIC_SPEC where
    pretty = printBasicSpec
instance Pretty BASIC_ITEMS where
    pretty = printBasicItems
instance Pretty TEXT_META where
   pretty = printTextMeta
instance Pretty TEXT where
   pretty = printText
instance Pretty PHRASE where
   pretty = printPhrase
instance Pretty MODULE where
   pretty = printModule
instance Pretty IMPORTATION where
   pretty = printImportation
instance Pretty SENTENCE where
   pretty = printSentence
instance Pretty BOOL_SENT where
   pretty = printBoolSent
instance Pretty AndOr where
   pretty = printAndOr
instance Pretty ImplEq where
   pretty = printImplEq
instance Pretty QUANT where
   pretty = printQuant
instance Pretty ATOM where
   pretty = printAtom
instance Pretty TERM where
   pretty = printTerm
instance Pretty TERM_SEQ where
   pretty = printTermSeq
instance Pretty COMMENT where
   pretty = printComment
instance Pretty NAME_OR_SEQMARK where
   pretty = printNameOrSeqMark
instance Pretty SYMB_OR_MAP where
   pretty = printSymbOrMap
instance Pretty SYMB_MAP_ITEMS where
   pretty = printSymbMapItems
instance Pretty SYMB_ITEMS where
   pretty = printSymbItems

printBasicSpec :: BASIC_SPEC -> Doc
printBasicSpec (Basic_spec xs) = vcat $ map pretty xs

printBasicItems :: BASIC_ITEMS -> Doc
printBasicItems (Axiom_items xs) = vcat $ map pretty xs

printTextMeta :: TEXT_META -> Doc
printTextMeta tm = pretty $ getText tm

-- print basic spec as pure clif-texts, without any annotations
exportCLIF :: [AS_Anno.Named TEXT_META] -> Doc
exportCLIF xs = vsep $ map (exportTextMeta . AS_Anno.sentence) xs

exportBasicSpec :: BASIC_SPEC -> Doc
exportBasicSpec (Basic_spec xs) =
  vsep $ map (exportBasicItems . AS_Anno.item) xs

exportBasicItems :: BASIC_ITEMS -> Doc
exportBasicItems (Axiom_items xs) =
  vsep $ map (exportTextMeta . AS_Anno.item) xs

exportTextMeta :: TEXT_META -> Doc
exportTextMeta = pretty . getText

-- using pure clif syntax from here
printText :: TEXT -> Doc
printText s = case s of
  Text x _ -> fsep $ map pretty x
  Named_text x y _ -> parens $ text clTextS <+> pretty x <+> pretty y

printPhrase :: PHRASE -> Doc
printPhrase s = case s of
  Module x -> parens $ text clModuleS <+> pretty x
  Sentence x -> pretty x
  Importation x -> parens $ text clImportS <+> pretty x
  Comment_text x y _ -> parens $ text clCommentS <+> pretty x <+> pretty y

printModule :: MODULE -> Doc
printModule (Mod x z _) = pretty x <+> pretty z
printModule (Mod_ex x y z _) =
  pretty x <+> parens (text clExcludeS <+> fsep (map pretty y)) <+> pretty z

printImportation :: IMPORTATION -> Doc
printImportation (Imp_name x) = pretty x

printSentence :: SENTENCE -> Doc
printSentence s = case s of
    Quant_sent q vs is _ ->
      parens $ pretty q <+> parens (sep $ map pretty vs) <+> pretty is
    Bool_sent xs _ -> parens $ pretty xs
    Atom_sent xs _ -> pretty xs
    Comment_sent x y _ -> parens $ text clCommentS <+> pretty x <+> pretty y
    Irregular_sent xs _ -> parens $ pretty xs

printComment :: COMMENT -> Doc
printComment s = case s of
   Comment x _ -> text x

printQuant :: QUANT -> Doc
printQuant s = case s of
  Universal -> text forallS
  Existential -> text existsS

printBoolSent :: BOOL_SENT -> Doc
printBoolSent s = case s of
   Junction q xs -> pretty q <+> fsep (map pretty xs)
   Negation xs -> text notS <+> pretty xs
   BinOp q x y -> pretty q <+> pretty x <+> pretty y

printAndOr :: AndOr -> Doc
printAndOr s = case s of
  Conjunction -> text andS
  Disjunction -> text orS

printImplEq :: ImplEq -> Doc
printImplEq s = case s of
  Implication -> text ifS
  Biconditional -> text iffS

printAtom :: ATOM -> Doc
printAtom s = case s of
   Equation a b -> parens $ equals <+> pretty a <+> pretty b
   Atom t ts -> parens $ pretty t <+> sep (map pretty ts)

printTerm :: TERM -> Doc
printTerm s = case s of
   Name_term a -> pretty a
   Funct_term t ts _ -> parens $ pretty t <+> fsep (map pretty ts)
   Comment_term t c _ -> parens $ text clCommentS <+> pretty c <+> pretty t
   That_term sent _ -> parens $ text "that" <+> pretty sent

printTermSeq :: TERM_SEQ -> Doc
printTermSeq s = case s of
  Term_seq t -> pretty t
  Seq_marks m -> pretty m

-- Binding Seq
printNameOrSeqMark :: NAME_OR_SEQMARK -> Doc
printNameOrSeqMark s = case s of
  Name x -> pretty x
  SeqMark x -> pretty x
  -- Alt x y -> pretty x <+> pretty y

printSymbOrMap :: SYMB_OR_MAP -> Doc
printSymbOrMap (Symb nos) = pretty nos
printSymbOrMap (Symb_mapN source dest _) =
  pretty source <+> mapsto <+> pretty dest <> space
printSymbOrMap (Symb_mapS source dest _) =
  pretty source <+> mapsto <+> pretty dest <> space
{- space needed. without space the comma (from printSymbMapItems)
would be part of the name @dest@ -}

printSymbMapItems :: SYMB_MAP_ITEMS -> Doc
printSymbMapItems (Symb_map_items xs _) = ppWithCommas xs

printSymbItems :: SYMB_ITEMS -> Doc
printSymbItems (Symb_items xs _) = fsep $ map pretty xs

-- keywords, reservednames in CLIF
orS :: String
orS = "or"

iffS :: String
iffS = "iff"

clCommentS :: String
clCommentS = "cl-comment"

clTextS :: String
clTextS = "cl-text"

clImportS :: String
clImportS = "cl-imports"

clModuleS :: String
clModuleS = "cl-module"

clExcludeS :: String
clExcludeS = "cl-excludes"
