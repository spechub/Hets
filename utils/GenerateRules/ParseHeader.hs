module ParseHeader where

import Parsec

type Data   = String
type Exclude = String

header :: Parser [Exclude]
header = do (d,e) <- instances [] []
            return (d ++ e)

instances :: [Data] -> [Exclude] -> Parser ([Data],[Exclude])
instances ds ex = do ex' <- try excludeRule
                     instances ds (ex':ex) 
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

excludeRule :: Parser Exclude
excludeRule = do string "{-|"
                 spaces
                 string "Exclude:"
                 spaces
                 i <- identifier
                 spaces
	         string "|-}"
                 return i

instances' :: Parser Data
instances' = do string "instance"
                spaces
                (try constraints) <|> spaces
                spaces 
                identifier
		spaces
		dataConstructor


constraints :: Parser ()
constraints = do try (between (char '(')  (char ')') (sepBy1 constraint (char ','))) <|> sepBy1 constraint (char ',') 
                 spaces
                 string "=>"
		 spaces
                 return ()  

constraint :: Parser () 
constraint = do spaces
	        identifier
                spaces 
                many1 lower 
		spaces

dataConstructor:: Parser String
dataConstructor = (try identifier) <|> do char '('
                                          identifier
                                   
           

identifier :: Parser String
identifier = do x <- upper
                xs <- many (alphaNum <|> oneOf "_-.,")
		return (x:xs)

comment :: Parser ()
comment = do string "{-" 
	     manyTill anyChar (try (string "-}"))
	     return ()
	  <|>
          do string "--"
             manyTill anyChar (try newline)
	     return ()