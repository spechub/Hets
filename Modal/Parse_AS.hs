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

module Modal.Parse_AS where
import Common.AnnoState
import Common.Id
import Common.Token
import Common.Keywords
import Common.Lexer
import Modal.AS_Modal
-- import Common.AS_Annotation
-- import Data.Maybe
import Common.Lib.Parsec
--import CASL.Formula
--import CASL.SortItem
--import CASL.OpItem
--import CASL.TypeItem
import CASL.ItemList

-- aus CASL, kann bleiben
basicSpec :: AParser BASIC_SPEC
basicSpec = (fmap Basic_spec $ many1 $ 
	    try $ annoParser basicItems)
            <|> try (oBraceT >> cBraceT >> return (Basic_spec []))

basicItems :: AParser BASIC_ITEMS
basicItems = fmap Sig_items sigItems
--	    <|> dotFormulae    -- später!

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

