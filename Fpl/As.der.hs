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

import Data.List (delete)

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
prepPunctBar = punctuate (Doc.space <> bar)

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

data FunDef = FunDef OP_NAME OP_HEAD (Annoted FplTerm) Range
  deriving (Show, Eq, Ord)

kindHead :: OpKind -> OP_HEAD -> OP_HEAD
kindHead k (Op_head _ args r ps) = Op_head k args r ps

instance Pretty FunDef where
  pretty (FunDef i h@(Op_head _ l _ _) t _) =
    sep [keyword functS
      , sep [ (if null l then sep else cat)
              [idLabelDoc i, pretty $ kindHead Total h]
            , equals <+> printAnnoted pretty t]]

{- | extra terms of FPL. if-then-else must use a term as guard with result
sort @Bool@. To allow @true@, @false@ and an equality test an extra term
parser is needed that must not be used when parsing formulas. -}
data TermExt =
    FixDef FunDef -- ^ formula
  | Case FplTerm [(FplTerm, FplTerm)] Range
  | Let FunDef FplTerm Range
  | IfThenElse FplTerm FplTerm FplTerm Range
  | EqTerm FplTerm FplTerm Range
  | BoolTerm FplTerm
  deriving (Show, Eq, Ord)

instance Pretty TermExt where
  pretty t = case t of
    FixDef fd -> pretty fd
    Case c l _ ->
      sep $ (keyword caseS <+> pretty c <+> keyword ofS)
          : prepPunctBar
            (map (\ (p, e) -> fsep [pretty p, implies, pretty e]) l)
    Let fd i _ -> sep [keyword letS <+> pretty fd, keyword inS <+> pretty i]
    IfThenElse i d e _ ->
        fsep [ keyword ifS <+> pretty i
             , keyword thenS <+> pretty d
             , keyword elseS <+> pretty e ]
    EqTerm t1 t2 r -> pretty $ Strong_equation t1 t2 r
    BoolTerm f -> pretty f

fplReservedWords :: [String]
fplReservedWords = [barS, functS, caseS, ofS, letS]

funDef :: [String] -> AParser st FunDef
funDef ks = do
  q <- asKey functS
  o <- parseId ks
  h <- opHead ks
  e <- equalT
  a <- annos
  t <- eqTerm ks
  return $ FunDef o (kindHead Partial h)
    (Annoted t nullRange a []) $ toRange q [] e

optVarDecls :: [String] -> AParser st ([VAR_DECL], [Token])
optVarDecls ks =
    (oParenT >> separatedBy (varDecl ks) anSemi << cParenT)
    <|> return ([], [])

constBool :: AParser st FplTerm
constBool = fmap Mixfix_token (asKey trueS <|> asKey falseS)

boolTerm :: [String] -> AParser st FplTerm
boolTerm ks = constBool <|> mixTerm ks

eqTerm :: [String] -> AParser st FplTerm
eqTerm ks = do
  b <- boolTerm ks
  option b $ do
    e <- equalT
    b2 <- boolTerm ks
    return $ ExtTERM $ EqTerm b b2 $ tokPos e

{- | extra formulas to compare bool terms with true or false.
Interpreting boolean valued terms as formulas is still missing. -}
eqForm :: [String] -> AParser st TermExt
eqForm ks = do
    (c, t) <- try $ pair constBool equalT
    e <- mixTerm ks
    return $ EqTerm c e $ tokPos t
  <|> fmap (\ (e, (t, c)) -> EqTerm e c $ tokPos t)
    (try $ pair (mixTerm ks) $ pair equalT constBool)

fplTerm :: [String] -> AParser st TermExt
fplTerm ks = caseTerm ks <|> letTerm ks <|> ifThenElse ks

caseTerm :: [String] -> AParser st TermExt
caseTerm ks = do
  c <- asKey caseS
  t <- eqTerm ks
  o <- asKey ofS
  (cs, qs) <- separatedBy (patTermPair ks) barT
  return $ Case t cs $ toRange c qs o

patTermPair :: [String] -> AParser st (FplTerm, FplTerm)
patTermPair ks = do
  p <- eqTerm ks
  implKey
  t <- eqTerm ks
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
  f <- eqTerm ks
  t <- asKey thenS
  a <- eqTerm ks
  e <- asKey elseS
  b <- eqTerm ks
  return $ IfThenElse f a b $ toRange i [t] e

instance TermParser TermExt where
  termParser b = if b then fplTerm fplReservedWords else
    fmap FixDef (funDef fplReservedWords) <|> eqForm fplReservedWords

fplExt :: [String] -> AParser st FplExt
fplExt ks = itemList ks sortS fplSortItem FplSortItems
  <|> itemList (delete functS ks) opS fplOpItem FplOpItems

fplSortItem :: [String] -> AParser st FplSortItem
fplSortItem ks = do
    s <- sortId ks
    freeType ks s <|>
      fmap CaslSortItem (subSortDecl ks ([s], nullRange) <|> commaSortDecl ks s
          <|> isoDecl ks s <|> return (Sort_decl [s] nullRange))

freeType :: [String] -> SORT -> AParser st FplSortItem
freeType ks s = do
  f <- asKey freeS
  asKey withS
  fmap FreeType $ parseDatatype ks s f

fplOpItem :: [String] -> AParser st FplOpItem
fplOpItem ks = fmap FunOp (funDef ks) <|> fmap CaslOpItem (opItem ks)

instance AParsable FplExt where
  aparser = fplExt fplReservedWords
