module ParseFile where

import Parsec
import ParseHeader

type Modulename = String
--type Data   = String
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
                spaces
                m <- identifier
                spaces
                return m

dataType :: Parser Data
dataType = do string "data"
	      spaces
              d <- identifier
              many (noneOf "=") 
              char '='
              return d 
	      
{-
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
-}
importData :: Parser String
importData = do string "import"
                spaces 
                qual <- option "" (try (do{string "qualified";spaces;return "qualified "})) 
                d <- identifier
                f <- option "" (try (do{spaces;b <- between (char '(') (char ')') (many1 (noneOf "()"));return ("("++b++")")}))
                as <- option "" (try (do{spaces;string "as";spaces;c<-identifier;return (" as "++c)}))  
                return (qual++d++f++as)
  











