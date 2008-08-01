{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Description :  lexical matters

-}

module Common.CaslLanguage where
import Text.ParserCombinators.Parsec
import qualified Text.ParserCombinators.Parsec.Token as P
import qualified Text.ParserCombinators.Parsec.Pos as Pos
import Text.ParserCombinators.Parsec.Language (emptyDef)

import Common.Id
import Common.Lexer(fromSourcePos)

type GParser a = forall st. GenParser Char st a

------ helper functions ------

convToPos :: Pos.SourcePos -> Range
convToPos p = Range [fromSourcePos p]

------------------------------

casl_letter :: [Char]
casl_letter = ['a'..'z'] ++ ['A'..'Z'] ++
              [toEnum(192) .. toEnum(207)] ++
              [toEnum(209) .. toEnum(214)] ++
              [toEnum(216) .. toEnum(221)] ++
              [toEnum(223) .. toEnum(239)] ++ -- icelandic eth
              [toEnum(241) .. toEnum(246)] ++
              [toEnum(248) .. toEnum(253)] ++ -- icelandic thorn
              [toEnum(255)]

casl_no_bracket_sign :: [Char]
casl_no_bracket_sign = "+-*/|\\&=`<>!?:$@#^~" ++
   "\161\191\215\247\163\169\177\182\167\185\178\179\162\176\172\181.\183"
 -- "¡¿×÷£©±¶§¹²³¢°¬µ.·"

casl_reserved_words :: String
casl_reserved_words =
    "and arch as assoc axiom axioms closed comm def else end " ++
    "exists false fit forall free from generated get given " ++
    "hide idem if in lambda library local not op ops pred preds " ++
    "result reveal sort sorts spec then to true type types " ++
    "unit units var vars version view when with within . \183"

casl_reserved_ops :: String
casl_reserved_ops =
    ": :? ::= = => <=> . \183 | |-> \\/ /\\ \172"

caslDef :: forall st. P.LanguageDef st
caslDef = ( emptyDef {P.nestedComments = True
                     ,P.commentStart   = "%["
                     ,P.commentEnd     = "]%"
                     ,P.identStart     = oneOf casl_letter
                     ,P.identLetter    = (try infix_underscore
                                          <|>
                                          oneOf(casl_letter ++ "'")
                                          <|>
                                          digit)
                     ,P.reservedNames  = words casl_reserved_words
                     ,P.opStart = oneOf casl_no_bracket_sign
                     ,P.opLetter = oneOf casl_no_bracket_sign
                     ,P.reservedOpNames = words casl_reserved_ops
                     })

infix_underscore :: GParser Char
infix_underscore = do uc <- try (char '_')
                      notFollowedBy (oneOf(" _\n" ++
                                           casl_no_bracket_sign))
                      return uc

casl_lexer :: forall st. P.TokenParser st
casl_lexer = P.makeTokenParser caslDef

whiteSpace :: forall st. CharParser st ()
whiteSpace    = P.whiteSpace casl_lexer
lexeme :: forall st a. CharParser st a -> CharParser st a
lexeme        = P.lexeme casl_lexer

symbol :: forall st. String -> CharParser st String
symbol        = P.symbol casl_lexer
natural :: forall st. CharParser st Integer
natural       = P.natural casl_lexer

parens :: forall st a. CharParser st a -> CharParser st a
parens        = P.parens casl_lexer
braces :: forall st a. CharParser st a -> CharParser st a
braces        = P.braces casl_lexer
squares :: forall st a. CharParser st a -> CharParser st a
squares       = P.squares casl_lexer

semi :: forall st. CharParser st String
semi          = P.semi casl_lexer
comma :: forall st. CharParser st String
comma         = P.comma casl_lexer
colon :: forall st. CharParser st String
colon         = P.colon casl_lexer

commaSep1 :: forall st a. CharParser st a -> CharParser st [a]
commaSep1 = P.commaSep1 casl_lexer
semiSep1 :: forall st a. CharParser st a -> CharParser st [a]
semiSep1 = P.semiSep1 casl_lexer

identifier :: forall st. CharParser st String
identifier    = P.identifier casl_lexer
operator :: forall st. CharParser st String
operator      = P.operator casl_lexer

reserved :: forall st. String -> CharParser st ()
reserved      = P.reserved casl_lexer
reservedOp :: forall st. String -> CharParser st ()
reservedOp    = P.reservedOp casl_lexer

charLiteral :: forall st. CharParser st Char
charLiteral   = P.charLiteral casl_lexer
stringLiteral :: forall st. CharParser st String
stringLiteral = P.stringLiteral casl_lexer


-- parses an Identifier without consuming following whitespaces
casl_words :: GParser String
casl_words = do c  <- (P.identStart caslDef)
                cs <- many(P.identLetter caslDef)
                return (c:cs)

dot_words :: GParser String
dot_words = try (do dot  <- char '.'
                    word <- casl_words
                    return (dot:word)
                )
            <?> "dot word"

-- parsers for reserved words and ops with two different signs, bat
-- the same meaning
reserved_dot :: GParser ()
reserved_dot = (reserved "\183") <|> (reserved ".")

reserved_not :: GParser ()
reserved_not = (reservedOp "\172") <|> (reserved "not")

reserved_op :: GParser ()
reserved_op = (reserved "ops") <|> (reserved "op")

reserved_sort :: GParser ()
reserved_sort = (reserved "sorts") <|> (reserved "sort")

reserved_pred :: GParser ()
reserved_pred = (reserved "preds") <|> (reserved "pred")

-- parsers returning Ids according Id.hs
simple_id:: GParser Id
simple_id = do sp <- getPosition
               i  <- identifier
               return $ mkId [Token i (convToPos sp)]

casl_id :: GParser Id
casl_id = comp_id

token_id :: GParser Id
token_id = do tok <- try Common.CaslLanguage.token
              return $ mkId [tok]

token :: GParser Token
token = do sp  <- getPosition
           tok <-  choice [identifier,
                             lexeme dot_words,
                             operator,
                             fmap (\x -> show x) (charLiteral),
                             fmap (:"") (digit)]
           return $ Token tok (convToPos sp)

place :: GParser Token
place = (do sp  <- getPosition
            try (symbol Common.Id.place)
            return (Token Common.Id.place (convToPos sp))
        ) <?> "place"

place_token :: GParser [Token]
place_token = do pla <- try Common.CaslLanguage.place
                 option ([pla]) (do tok <- try Common.CaslLanguage.token
                                    return [pla,tok])

mixfix_id :: [Token] -> GParser Id
mixfix_id accum = do ts <- (try (fmap (:[]) Common.CaslLanguage.place)
                            <|>
                            try (fmap (:[]) Common.CaslLanguage.token)
                            <|>
                            special_between (symbol "{") (symbol "}")
                            (mkTokLst (mixfix_id []))
                            <|>
                            try (special_between (symbol "[") (symbol "]")
                                 (mkTokLst (mixfix_id [])))
                            <|>
                            bracket_pair "{" "}"
                            <|>
                            bracket_pair "[" "]"
                            <?> "mixfix id"
                           )
                     sqs <- option [] (lookAhead (fmap (:[]) (symbol "[")))
                     fts <- option [] (lookAhead
                                         (fmap (:[]) (Common.CaslLanguage.token)))
                     Id ats _ _ <-
                         let accum_ts = accum ++ ts
                             defId = mkId accum_ts
                             optId = option defId $ mixfix_id accum_ts
                             is_last_op = case (last accum_ts) of
                                          t@(Token s _) -> not
                                                       ((last s) `elem` "[{}]"
                                                        ||
                                                        isPlace (t))
                         in if sqs == [] then
                               if is_last_op then
                                  if fts == [] then optId
                                  else
                                     unexpected "token follows token"
                               else -- not is_last_op
                                  optId
                            else -- sqs \= []
                               if isPlace (last accum_ts) then optId
                               else
                                  return defId
                     return (mkId ats)
    where mkTokLst p = fmap (\(Id ts _cs _pos) -> ts) p
          bracket_pair open close = do o_sp <- getPosition
                                       o <- try (symbol open)
                                       c_sp <- getPosition
                                       c <- try (symbol close)
                                       return [Token o (convToPos o_sp),
                                               Token c (convToPos c_sp)]

special_between :: forall tok st.GenParser tok st String
                   -> GenParser tok st String
                   -> GenParser tok st [Token] -> GenParser tok st [Token]
special_between start end p = do st_sp <- getPosition
                                 st <- start
                                 res <- special_manyTill p end
                                 return ([Token st (convToPos st_sp)] ++
                                           res) -- res also contains end

special_manyTill :: forall tok st.GenParser tok st [Token]
                    -> GenParser tok st String -> GenParser tok st [Token]
special_manyTill p end = scan
    where scan  = do sp <- getPosition
                     e <- end
                     return [Token e (convToPos sp)]
                  <|>
                  do x <- p
                     xs <- scan
                     return (x ++ xs)

comp_id :: GParser Id
comp_id = do Id ts _ _  <- test_mixfix_id (mixfix_id [])
             Id ts' cs pos <- option (mkId ts)
                                   (do cs <- squares (sepBy1 comp_id comma)
                                       return (Id ts cs nullRange)
                                       )
             option (Id ts' cs pos)
                      (do ps <- many Common.CaslLanguage.place
                          return (Id (ts'++ps) cs nullRange))
    where test_mixfix_id p =
              do i@(Id ts _ _) <- p
                 if (case ts of []  -> False
                                [a] -> not (isPlace a)
                                _   -> True)
                   then return i
                   else fail "only one place is not a legal mixfix id "
