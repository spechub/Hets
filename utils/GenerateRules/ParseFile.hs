module ParseFile where

import Parsec

type Modulename = String
type Data   = String
type Import = String

inputFile :: Parser (Modulename,[Data],[Import])
inputFile = do many (comment <|> do {space;return ()})
               string "module"
               spaces
               m <- identifier     
               spaces
	       (ds,is) <- dataOrImport ([],[])
	       return (m,ds,is)

dataOrImport :: ([Data],[Import]) -> Parser ([Data],[Import])
dataOrImport (ds,is) = do try comment
                          dataOrImport (ds,is)
                       <|>
                       do d <- (try dataType)
                          dataOrImport (d:ds,is)
                       <|> 
		       do i <- (try importData)
                          dataOrImport (ds,i:is)
                       <|>
                       do try anyToken
                          dataOrImport (ds,is)
                       <|>
	               do eof
                          return (ds,is)
               
dataType :: Parser Data
dataType = do string "data"
	      spaces
              d <- identifier
              many (noneOf "=") 
              char '='
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

importData :: Parser String
importData = do string "import"
                spaces 
                mod <- try (string "Common.") <|> try (string "Syntax.") <|> (string "Logic.") 
                d <- identifier
                return (mod++d)
  











