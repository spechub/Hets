module ParseHeader where

import Parsec

type Data   = String

header :: Parser [Data]
header = instances []
            
instances :: [Data] -> Parser [Data]
instances ds = do try comment
                  instances ds
               <|>
               do d <- try instances'
                  instances (d:ds) 
               <|> 
               do try anyToken
                  instances ds
               <|>
               do eof
                  return ds

instances' :: Parser Data
instances' = do string "instance"
                spaces
                identifier
		spaces
		d <- identifier
                spaces 
                string "where"
                return d

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