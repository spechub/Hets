{-| 
   
Module      :  $Header$
Copyright   :  (c) Felix Reckers, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

-}

module ParseHeader where

import Parsec

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
                (try constraints) <|> spaces
                spaces 
                identifier
		spaces
		dataConstructor


constraints :: Parser ()
constraints =  do fmap (\x -> [x]) constraint <|> (between (char '(')  (char ')') (sepBy1 constraint (char ',')))
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

spaces1 = skipMany1 space

dataConstructor:: Parser String
dataConstructor = (try identifier) <|> do char '('
                                          identifier
                                   
           

identifier :: Parser String
identifier = do x <- upper
                xs <- many (alphaNum <|> oneOf "_.")
		return (x:xs)

lIdentifier :: Parser String
lIdentifier = do x <- lower
                 xs <- many (alphaNum <|> oneOf "_.")
		 return (x:xs)

comment :: Parser ()
comment = do string "{-" 
	     manyTill anyChar (try (string "-}"))
	     return ()
	  <|>
          do string "--"
             manyTill anyChar (try newline)
	     return ()
