{- Spickzettel für's Parsen -}

-- Definition aus Logic.hs
type ParseFun a = FilePath -> Int -> Int -> String -> (a,String,Int,Int)
                  -- args: filename, line, column, input text
                  -- result: value, remaining text, line, column 

-- ParsecInterface.hs
toParseFun :: GenParser Char st a -> st -> ParseFun a           

-- Klassenfunktion, die meine Instanz implementiert
parse_basic_spec :: id -> Maybe(ParseFun basic_spec)
--                                       ^ Rückgabetyp

module Parse_AS where

-- aus CASL
basicSpec :: GenParser Char st BASIC_SPEC
basicSpec = (fmap Basic_spec $ many1 $ -- 
	    try $ bind addLeftAnno annos basicItems)
            <|> try (oBraceT >> cBraceT >> return (Basic_spec []))