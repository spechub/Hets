module ParseFile where

import Parsec
import ParseHeader

type Modulename = String

type Import = String

inputFile :: Parser ([Data],[Import])
inputFile = do (ds,is) <- dataOrImport ([],[])
	       return (ds,is)

dataOrImport :: ([Data],[Import]) -> Parser ([Data],[Import])
dataOrImport (ds,is) = do try comment
                          dataOrImport (ds,is)
                       <|>
                       do m <- (try modulename)
                          dataOrImport (ds,m:is)
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
               
modulename :: Parser Import
modulename = do string "module"
                skipMany1 space
                m <- identifier
		manyTill anyChar (try (string "where"))
                return m

dataType :: Parser Data
dataType = do try (string "data") <|> (string "newtype")
	      skipMany1 space
              d <- identifier
              many (noneOf "=") 
              char '='
              return d 
	      
importData :: Parser String
importData = do string "import"
                skipMany1 space
                qual <- option "" (try (do string "qualified"
					   spaces
                                           return "qualified ")) 
                d <- identifier
                _f <- option "" (try (do spaces
				         b <- between (char '(') (char ')') 
				              (many1 (noneOf "()"))
				         return ("("++b++")")))
                as <- option "" (try (do
				      spaces
				      string "as"
				      spaces
				      c<-identifier
				      return (" as "++c)))  
                return (qual++d++as)
  











