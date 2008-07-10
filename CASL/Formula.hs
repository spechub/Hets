{- |
Module      :  $Header$
Description :  Parser for CASL terms and formulae
Copyright   :  (c) Christian Maeder, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

parse terms and formulae
-}

{-
   http://www.cofi.info/Documents/CASL/Summary/
   from 25 March 2001
   C.2.1 Basic Specifications with Subsorts

   remarks:

   when-else-TERMs are non-mixfix,
   because when-else has lowest precedence.
   C.3.1 Precedence

   Sorted (or casted) terms are not directly recognized,
   because "u v : s" may be "u (v:s)" or "(u v):s"

   No term or formula may start with a parenthesized argument list that
   includes commas.

   The arguments of qualified ops or preds can only be given by a following
   parenthesized argument list.

   Braced or bracketed term-lists including commas stem from a possible
   %list-annotation or (for brackets) from compound lists.

   C.6.3 Literal syntax for lists

   `%list b1__b2, c, f'.
   b1 must contain at least one open brace or bracket ("{" or [")
   and all brackets must be balanced in "b1 b2" (the empty list).

   all parsers are paramterized with a String list containing additional
   keywords
-}

module CASL.Formula
    ( term
    , primFormula
    , formula
    , anColon
    , varDecl
    , opSort
    , opFunSort
    , opType
    , predType
    , predUnitType
    , qualPredName
    ) where

import Common.AnnoState
import Common.Id
import Common.Keywords
import Common.Lexer
import Common.Token
import CASL.AS_Basic_CASL
import Text.ParserCombinators.Parsec

simpleTerm :: [String] -> AParser st (TERM f)
simpleTerm k = fmap Mixfix_token $ pToken
    ( scanFloat
  <|> scanString
  <|> scanQuotedChar
  <|> scanDotWords
  <|> reserved (k ++ casl_reserved_fwords) scanAnyWords
  <|> reserved (k ++ casl_reserved_fops) scanAnySigns
  <|> placeS
  <?> "id/literal" )

restTerms :: AParsable f => [String] -> AParser st [TERM f]
restTerms k = (tryItemEnd startKeyword >> return [])
  <|> bind (:) (restTerm k) (restTerms k)
  <|> return []

startTerm :: AParsable f => [String] -> AParser st (TERM f)
startTerm k =
    parenTerm <|> braceTerm <|> bracketTerm <|> try (addAnnos >> simpleTerm k)

restTerm :: AParsable f => [String] -> AParser st (TERM f)
restTerm k = startTerm k <|> typedTerm k <|> castedTerm k

mixTerm :: AParsable f => [String] -> AParser st (TERM f)
mixTerm k = do
  l <- startTerm k <:> restTerms k
  return $ if isSingle l then head l else Mixfix_term l

-- | when-else terms
term :: AParsable f => [String] -> AParser st (TERM f)
term k = do
  t <- mixTerm k
  option t $ do
    w <- asKey whenS
    f <- formula k
    e <- asKey elseS
    r <- term k
    return $ Conditional t f r $ toRange w [] e

anColon :: AParser st Token
anColon = wrapAnnos colonST

typedTerm :: [String] -> AParser st (TERM f)
typedTerm k = do
  c <- colonT
  t <- sortId k
  return $ Mixfix_sorted_term t $ tokPos c

castedTerm :: [String] -> AParser st (TERM f)
castedTerm k = do
  c <- asT
  t <- sortId k
  return $ Mixfix_cast t $ tokPos c

terms :: AParsable f => [String] -> AParser st ([TERM f], [Token])
terms k = term k `separatedBy` anComma

qualVarName :: Token -> AParser st (TERM f)
qualVarName o = do
  v <- asKey varS
  i <- varId []
  c <- colonT
  s <- sortId [] << addAnnos
  p <- cParenT
  return $ Qual_var i s $ toRange o [v, c] p

qualOpName :: Token -> AParser st (TERM f)
qualOpName o = do
  v <- asKey opS
  i <- parseId []
  c <- anColon
  t <- opType [] << addAnnos
  p <- cParenT
  return $ Application (Qual_op_name i t $ toRange o [v, c] p) [] nullRange

opSort :: [String] -> GenParser Char st (Bool, Id, Range)
opSort k = fmap (\s -> (False, s, nullRange)) (sortId k) <|> do
  q <- quMarkT
  s <- sortId k
  return (True, s, tokPos q)

opFunSort :: [String] -> [Id] -> [Token] -> GenParser Char st OP_TYPE
opFunSort k ts ps = do
  a <- pToken (string funS)
  (b, s, qs) <- opSort k
  return $ Op_type (if b then Partial else Total) ts s
             $ appRange (catRange $ ps ++ [a]) qs

opType :: [String] -> AParser st OP_TYPE
opType k = do
  (b, s, p) <- opSort k
  if b then return $ Op_type Partial [] s p else do
      c <- crossT
      (ts, ps) <- sortId k `separatedBy` crossT
      opFunSort k (s : ts) (c : ps)
    <|> opFunSort k [s] []
    <|> return (Op_type Total [] s nullRange)

parenTerm :: AParsable f => AParser st (TERM f)
parenTerm = do
  o <- wrapAnnos oParenT
  qualVarName o <|> qualOpName o <|> qualPredName [] o <|> do
    (ts, ps) <- terms []
    c <- addAnnos >> cParenT
    return (Mixfix_parenthesized ts $ toRange o ps c)

braceTerm :: AParsable f => AParser st (TERM f)
braceTerm = do
  o <- wrapAnnos oBraceT
  (ts, ps) <- option ([], []) $ terms []
  c <- addAnnos >> cBraceT
  return $ Mixfix_braced ts $ toRange o ps c

bracketTerm :: AParsable f => AParser st (TERM f)
bracketTerm = do
  o <- wrapAnnos oBracketT
  (ts, ps) <- option ([], []) $ terms []
  c <- addAnnos >> cBracketT
  return $ Mixfix_bracketed ts $ toRange o ps c

quant :: AParser st (QUANTIFIER, Token)
quant = choice (map (\ (q, s) -> do
    t <- asKey s
    return (q, t))
  [ (Unique_existential, existsS ++ exMark)
  , (Existential, existsS)
  , (Universal, forallS) ])
  <?> "quantifier"

quantFormula :: AParsable f => [String] -> AParser st (FORMULA f)
quantFormula k = do
  (q, p) <- quant
  (vs, ps) <- varDecl k `separatedBy` anSemi
  d <- dotT
  f <- formula k
  return $ Quantification q vs f $ toRange p ps d

varDecl :: [String] -> AParser st VAR_DECL
varDecl k = do
  (vs, ps) <- varId k `separatedBy` anComma
  c <- colonT
  s <- sortId k
  return $ Var_decl vs s (catRange ps `appRange` tokPos c)

predType :: [String] -> AParser st PRED_TYPE
predType k = do
    (ts, ps) <- sortId k `separatedBy` crossT
    return (Pred_type ts (catRange ps))
  <|> predUnitType

predUnitType :: GenParser Char st PRED_TYPE
predUnitType = do
  o <- oParenT
  c <- cParenT
  return $ Pred_type [] (tokPos o `appRange` tokPos c)

qualPredName :: [String] -> Token -> AParser st (TERM f)
qualPredName k o = do
  v <- asKey predS
  i <- parseId k
  c <- colonT
  s <- predType k << addAnnos
  p <- cParenT
  return $ Mixfix_qual_pred $ Qual_pred_name i s $ toRange o [v, c] p

parenFormula :: AParsable f => [String] -> AParser st (FORMULA f)
parenFormula k = do
  o <- oParenT << addAnnos
  do  q <- qualPredName [] o <|> qualVarName o <|> qualOpName o
      l <- restTerms []  -- optional arguments
      termFormula k $ if null l then q else Mixfix_term $ q : l
    <|> do
      f <- formula [] << addAnnos
      case f of
        Mixfix_formula t -> do
          c <- cParenT
          l <- restTerms k
          let tt = Mixfix_parenthesized [t] $ toRange o [] c
              ft = if null l then tt else Mixfix_term $ tt : l
          termFormula k ft -- commas are not allowed
        _ -> cParenT >> return f

termFormula :: AParsable f => [String] -> (TERM f) -> AParser st (FORMULA f)
termFormula k t = do
    e <- asKey exEqual
    r <- term k
    return $ Existl_equation t r $ tokPos e
  <|> do
    try $ string exEqual
    unexpected $ "sign following " ++ exEqual
  <|> do
    e <- equalT
    r <- term k
    return $ Strong_equation t r $ tokPos e
  <|> do
    e <- asKey inS
    s <- sortId k
    return $ Membership t s $ tokPos e
  <|> return (Mixfix_formula t)

primFormula :: AParsable f => [String] -> AParser st (FORMULA f)
primFormula k = do
    f <- aparser
    return $ ExtFORMULA f
  <|> do
    c <- asKey trueS
    return $ True_atom $ tokPos c
  <|> do
    c <- asKey falseS
    return $ False_atom $ tokPos c
  <|> do
    c <- asKey defS
    t <- term k
    return $ Definedness t $ tokPos c
  <|> do
    c <- asKey notS <|> asKey negS <?> "\"not\""
    f <- primFormula k
    return $ Negation f $ tokPos c
  <|> parenFormula k
  <|> quantFormula k
  <|> (term k >>= termFormula k)

andKey :: AParser st Token
andKey = asKey lAnd

orKey :: AParser st Token
orKey = asKey lOr

andOrFormula :: AParsable f => [String] -> AParser st (FORMULA f)
andOrFormula k = do
  f <- primFormula k
  do  c <- andKey
      (fs, ps) <- primFormula k `separatedBy` andKey
      return $ Conjunction (f : fs) $ catRange $ c : ps
    <|> do
      c <- orKey
      (fs, ps) <- primFormula k `separatedBy` orKey
      return $ Disjunction (f : fs) $ catRange $ c : ps
    <|> return f

implKey :: AParser st Token
implKey = asKey implS

ifKey :: AParser st Token
ifKey = asKey ifS

formula :: AParsable f => [String] -> AParser st (FORMULA f)
formula k = do
  f <- andOrFormula k
  do  c <- implKey
      (fs, ps) <- andOrFormula k `separatedBy` implKey
      return $ makeImpl True (f : fs) $ catPosAux $ c : ps
    <|> do
      c <- ifKey
      (fs, ps) <- andOrFormula k `separatedBy` ifKey
      return $ makeIf (f : fs) $ catPosAux $ c : ps
    <|> do
      c <- asKey equivS
      g <- andOrFormula k
      return $ Equivalence f g $ tokPos c
    <|> return f
    where makeImpl b [f, g] p = Implication f g b (Range p)
          makeImpl b (f : r) (c : p) =
              Implication f (makeImpl b r p) b (Range [c])
          makeImpl _ _ _ = error "makeImpl got illegal argument"
          makeIf l p = makeImpl False (reverse l) $ reverse p
