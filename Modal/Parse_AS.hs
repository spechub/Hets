{- Spickzettel für's Parsen 

-- Definition aus Logic.hs
type ParseFun a = FilePath -> Int -> Int -> String -> (a,String,Int,Int)
                  -- args: filename, line, column, input text
                  -- result: value, remaining text, line, column 

-- ParsecInterface.hs
toParseFun :: GenParser Char st a -> st -> ParseFun a           

-- Klassenfunktion, die meine Instanz implementiert
parse_basic_spec :: id -> Maybe(ParseFun basic_spec)
--                                       ^ Rückgabetyp
-}

module Parse_AS where
import AnnoState
import Id
import Token
import Keywords
import Lexer
import AS_Modal
-- import AS_Annotation
-- import Maybe
import Common.Lib.Parsec
--import Formula
--import SortItem
--import OpItem
--import TypeItem
import ItemList

-- aus CASL, kann bleiben
basicSpec :: AParser BASIC_SPEC
basicSpec = (fmap Basic_spec $ many1 $ 
	    try $ annoParser basicItems)
            <|> try (oBraceT >> cBraceT >> return (Basic_spec []))

basicItems :: AParser BASIC_ITEMS
basicItems = fmap Sig_items sigItems
	    <|> dotFormulae    -- später!

sigItems :: AParser SIG_ITEMS
sigItems = propItems 

propItem :: AParser PROP_ITEM 
propItem = do s <- sortId ; -- Props are the same as sorts (in declaration)
		    commaPropDecl s
		    <|> 
		    return (Prop_decl [s] [])

propItems :: AParser SIG_ITEMS
propItems = itemList propS propItem Prop_items

commaPropDecl :: Id -> AParser PROP_ITEM
commaPropDecl s = do c <- anComma
		     (is, cs) <- sortId `separatedBy` anComma
		     let l = s : is 
		         p = tokPos c : map tokPos cs in return (Prop_decl l p)

