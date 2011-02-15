{- |
Module      :  $Header$
Description :  abstract syntax for FPL
Copyright   :  (c) Christian Maeder, DFKI GmbH 2011
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

abstract syntax for FPL, logic for functional programs
as CASL extension
-}

module Fpl.As where

-- DrIFT command
{-! global: GetRange !-}

import Common.AS_Annotation
import Common.AnnoState
import Common.Doc as Doc
import Common.DocUtils
import Common.Id
import Common.Keywords
import Common.Lexer
import Common.Parsec
import Common.Token hiding (innerList)

import Text.ParserCombinators.Parsec

import CASL.AS_Basic_CASL
import CASL.Formula
import CASL.SortItem
import CASL.OpItem
import CASL.ToDoc

type FplBasicSpec = BASIC_SPEC FplExt () TermExt

type FplTerm = TERM TermExt
type FplForm = FORMULA TermExt

data FplExt =
    FplSortItems [Annoted FplSortItem] Range
  | FplOpItems [Annoted FplOpItem] Range
  deriving Show

data FplSortItem =
    FreeType DATATYPE_DECL
  | CaslSortItem (SORT_ITEM TermExt)
  deriving Show

data FplOpItem =
    FunOp FunDef
  | CaslOpItem (OP_ITEM TermExt)
  deriving Show

prepPunctBar :: [Doc] -> [Doc]
prepPunctBar = prepPunctuate (bar <> Doc.space)

printDD :: DATATYPE_DECL -> Doc
printDD (Datatype_decl s as _) =
    sep [pretty s <+> keyword freeS <+> keyword withS
        , sep $ prepPunctBar
          $ map (printAnnoted printALTERNATIVE) as ]

instance ListCheck FplOpItem where
  innerList i = case i of
    FunOp _ -> [()]
    CaslOpItem oi -> innerList oi

instance ListCheck FplSortItem where
  innerList i = case i of
    FreeType _ -> [()]
    CaslSortItem si -> innerList si

instance Pretty FplExt where
  pretty e = case e of
    FplSortItems ds _ ->
        topSigKey (sortS ++ pluralS ds) <+> semiAnnos pretty ds
    FplOpItems ds _ -> topSigKey (opS ++ pluralS ds) <+> semiAnnos pretty ds

instance Pretty FplSortItem where
  pretty e = case e of
    FreeType d -> printDD d
    CaslSortItem s -> printSortItem pretty s

instance Pretty FplOpItem where
  pretty e = case e of
    FunOp o -> pretty o
    CaslOpItem s -> printOpItem pretty s

data FunDef = FunDef OP_NAME [VAR_DECL] SORT (Annoted FplTerm) Range
  deriving (Show, Eq, Ord)

instance Pretty FunDef where
  pretty (FunDef n vs s t _) =
    fsep [keyword functS
         , pretty n <>
          (if null vs then empty else parens (printVarDecls vs))
         , colon <+> pretty s
         , equals <+> printAnnoted pretty t]

data TermExt =
    FixDef FunDef -- ^ formula
  | Case FplTerm [(FplTerm, FplTerm)] Range
  | Let FunDef FplTerm Range
  | IfThenElse FplForm FplTerm FplTerm Range
  deriving (Show, Eq, Ord)

instance Pretty TermExt where
  pretty t = case t of
    FixDef fd -> pretty fd
    Case c l _ ->
      sep $ (keyword caseS <+> pretty c <+> keyword ofS)
          : prepPunctBar
            (map (\ (p, e) -> fsep [pretty p, implies, pretty e]) l)
    Let fd i _ -> sep [keyword letS <+> pretty fd <+> keyword inS, pretty i]
    IfThenElse i d e _ ->
        fsep [ keyword ifS <+> pretty i
             , keyword thenS <+> pretty d
             , keyword elseS <+> pretty e ]

fplReservedWords :: [String]
fplReservedWords = [barS, functS, caseS, ofS, letS]

funDef :: [String] -> AParser st FunDef
funDef ks = do
  q <- asKey functS
  o <- parseId ks
  (vs, qs) <- optVarDecls ks
  c <- anColon
  s <- sortId ks
  e <- equalT
  a <- annos
  t <- term ks
  return $ FunDef o vs s (Annoted t nullRange a [])
         $ appRange (toRange q qs c) $ tokPos e

optVarDecls :: [String] -> AParser st ([VAR_DECL], [Token])
optVarDecls ks =
    (oParenT >> separatedBy (varDecl ks) anSemi << cParenT)
    <|> return ([], [])

fplTerm :: [String] -> AParser st TermExt
fplTerm ks = caseTerm ks <|> letTerm ks <|> ifThenElse ks

caseTerm :: [String] -> AParser st TermExt
caseTerm ks = do
  c <- asKey caseS
  t <- mixTerm ks
  o <- asKey ofS
  (cs, qs) <- separatedBy (patTermPair ks) barT
  return $ Case t cs $ toRange c qs o

patTermPair :: [String] -> AParser st (FplTerm, FplTerm)
patTermPair ks = do
  p <- mixTerm ks
  implKey
  t <- mixTerm ks
  return (p, t)

letTerm :: [String] -> AParser st TermExt
letTerm ks = do
  l <- asKey letS
  d <- funDef ks
  i <- asKey inS
  t <- term ks
  return $ Let d t $ toRange l [] i

ifThenElse :: [String] -> AParser st TermExt
ifThenElse ks = do
  i <- ifKey
  f <- primFormula ks
  t <- asKey thenS
  a <- mixTerm ks
  e <- asKey elseS
  b <- mixTerm ks
  return $ IfThenElse f a b $ toRange i [t] e

instance TermParser TermExt where
  termParser b = if b then fplTerm fplReservedWords else
    fmap FixDef $ funDef fplReservedWords

fplExt :: [String] -> AParser st FplExt
fplExt ks = itemList ks sortS fplSortItem FplSortItems
  <|> itemList ks opS fplOpItem FplOpItems

fplSortItem :: [String] -> AParser st FplSortItem
fplSortItem ks = do
    s <- sortId ks
    fmap CaslSortItem (subSortDecl ks ([s], nullRange) <|> commaSortDecl ks s
          <|> isoDecl ks s <|> return (Sort_decl [s] nullRange))
      <|> freeType ks s

freeType :: [String] -> SORT -> AParser st FplSortItem
freeType ks s = do
  f <- asKey freeS
  asKey withS
  fmap FreeType $ parseDatatype ks s f

fplOpItem :: [String] -> AParser st FplOpItem
fplOpItem ks = fmap CaslOpItem (opItem ks)
  <|> fmap FunOp (funDef ks)

instance AParsable FplExt where
  aparser = fplExt fplReservedWords
