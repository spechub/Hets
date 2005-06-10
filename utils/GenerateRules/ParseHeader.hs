{-| 
Module      :  $Header$
Copyright   :  (c) Felix Reckers, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

parse a header file that may contain manually written instances 
or exclude directives 

-}

module ParseHeader where

import Text.ParserCombinators.Parsec
-- maybe the stuff in Parsec.Token should be used (instead of spaces)

type Data   = String
type Exclude = String

header :: Parser [Exclude]
header = do (d,e) <- instances [] []
            return (d ++ e)

instances :: [Data] -> [Exclude] -> Parser ([Data],[Exclude])
instances ds ex = do ex' <- try excludeRule
                     instances ds (ex'++ex) 
                  <|>
                  do try comment
                     instances ds ex
                  <|>
                  do d <- try instances'
                     instances (d:ds) ex 
                  <|> 
                  do try anyToken
                     instances ds ex
                  <|>
                  do eof
                     return (ds,ex)

excludeRule :: Parser [Exclude]
excludeRule = do string "{-|"
                 spaces
                 string "Exclude:"
                 spaces
                 is <- sepBy1 identifier (try comma')
                 spaces
                 string "|-}"
                 return is
    where comma' = do spaces 
                      char ','
                      spaces

instances' :: Parser Data
instances' = do string "instance"
                spaces
                try constraints <|> spaces
                spaces 
                identifier
                spaces
                dataConstructor


constraints :: Parser ()
constraints =  do 
    fmap (:[]) constraint <|> 
             between (char '(')  (char ')') (sepBy1 constraint (char ','))
    spaces
    string "=>"
    spaces
    return ()  

constraint :: Parser () 
constraint = do spaces
                identifier
                spaces1 
                sepBy1 spaces1 lIdentifier
                spaces1
    where spaces1 = skipMany1 space

dataConstructor:: Parser String
dataConstructor = try identifier <|> (char '(' >> identifier)
                                   
           
iRest :: Char -> Parser String
iRest x = fmap (x:) $ many (alphaNum <|> oneOf "_.")

identifier :: Parser String
identifier = upper >>= iRest

lIdentifier :: Parser String
lIdentifier = lower >>= iRest


comment :: Parser ()
comment = do string "{-" 
             manyTill anyChar (try (string "-}"))
             return ()
          <|>
          do string "--"
             manyTill anyChar (try newline)
             return ()
