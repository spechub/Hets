module MixfixParser where

import AS_Basic_CASL 
import Sign
import GlobalAnnotations
import Result
import Id
import Lexer (caslChar)
import ParsecPrim
import qualified Char as C


-- convert LiteralAnnos from Ids to OpItems

data LiteralOpItems = LitItem 
    { emptyString :: Maybe OpItem
    , consString :: Maybe OpItem
    , emptyList :: Maybe OpItem
    , consList :: Maybe OpItem
    , listBrackets :: ([Token],[Token])
    , numberLit :: Maybe OpItem
    , decimalOp  :: Maybe OpItem
    , exponentOp :: Maybe OpItem    
    , negExponent :: Maybe OpItem
    } deriving (Show)

convertLitAnnos is la = 
    LitItem {emptyString = case string_lit la of 
	                   Nothing -> Nothing
	                   Just (c, _) -> case lookupId is 0 c of
	                                  [ci] -> Just ci
	                                  _ -> Nothing
            ,consString  = case string_lit la of 
	                   Nothing -> Nothing
	                   Just (_, f) -> case lookupId is 2 f of
	                                  [fi] -> Just fi
	                                  _ -> Nothing
            ,emptyList   = case list_lit la of 
	                   Nothing -> Nothing
	                   Just (_, c, _) -> case lookupId is 0 c of
	                                  [ci] -> Just ci
	                                  _ -> Nothing
            ,consList    = case list_lit la of 
	                   Nothing -> Nothing
	                   Just (_, _, f) -> case lookupId is 2 f of
	                                  [fi] -> Just fi
	                                  _ -> Nothing
            ,listBrackets = case list_lit la of 
	                    Nothing -> ([], [])
	                    Just(Id bs _ _, _, _) -> 
	                       let (b1, rt) = span (not . isPlace) bs
			       in if null rt || any isPlace (tail rt) 
				  then ([], []) 
				  else (b1, tail rt)
	    ,numberLit   = case number_lit la of 
                           Nothing -> Nothing
			   Just f -> case lookupId is 2 f of 
	                                  [fi] -> Just fi
	                                  _ -> Nothing
            ,decimalOp   = case float_lit la of 
	                   Nothing -> Nothing
	                   Just (f, _) -> case lookupId is 2 f of
	                                  [fi] -> Just fi
	                                  _ -> Nothing
            ,exponentOp  = case float_lit la of 
	                   Nothing -> Nothing
	                   Just (_, g) -> case lookupId is 2 g of
	                                  [gi] -> Just gi
	                                  _ -> Nothing
            ,negExponent = case lookupId is 1 (Id [Token "-" nullPos] [] []) of
				          [fi] -> Just fi
	                                  _ -> Nothing
	    }

-- only check for the correct number of arguments
lookupId :: [OpItem] -> Int -> Id -> [OpItem]
lookupId is args i =
	 filter (\x -> opId x == i && args == length(opArgs(opType x))) is

isChar :: Token -> Bool
isChar t = head (tokStr t) == '\''

isString t = head (tokStr t) == '\"'
isNumber t = C.isDigit $ head (tokStr t)

split ::  GenParser Char () String -> String -> (String, String)
split p s = let ph = do hd <- p;
		        tl <- getInput;
                        return (hd, tl) 
            in case parse ph "" s of
               Left _ -> error"split" 
	       Right x -> x

makeStringTerm :: LiteralOpItems -> [OpItem] -> Token -> ([Diagnosis], [TERM])
makeStringTerm ga is tok = 
  let p = tokPos tok in
	    case emptyString ga of 
	    Nothing -> ([Error "no proper %string annotation" p], [])
            Just x -> let l = init (tail (tokStr tok))
                          y = asAppl x []
	              in if null l then ([], [y])
			 else case consString ga of 
                              Nothing ->  
				  ([Error "no %string constructor" p], [])
                              Just f -> 
				  let (errs, term) = makeStrTerm is y 
						     (asAppl f) p l
				  in (errs, [term])

makeStrTerm :: [OpItem] -> TERM -> ([TERM] -> TERM) 
               -> Pos -> [Char] -> ([Diagnosis], TERM)
makeStrTerm is x f p l = 
    if null l then ([], x)
    else let (hd, tl) = split caslChar l
             incr (line, column) = (line, column+1)
             (errs, rest) = makeStrTerm is x f (incr p) tl
	     real = "'" ++ hd ++ "'"
         in case lookupId is 0 (Id [Token real nullPos] [] []) of 
	    [c] -> (errs, f [asAppl c [], rest])
            _ -> (Error ("missing or ambiguous definition for character " 
			 ++ real) p : errs, rest)

-- convert OpItem's OpType to OP_TYPE
oldOpType :: OpItem -> OP_TYPE
oldOpType f = 
    let t = opType f in
    (case opKind t of 
    Total -> Total_op_type
    Partial -> Partial_op_type) (opArgs t) (opRes t) []

asAppl :: OpItem -> [TERM] -> TERM
asAppl f args = Application (Qual_op_name (opId f) (oldOpType f) []) args []

-- analyse Mixfix_token
{-convertMixfixToken:: GlobalAnnos -> [varDecl] -> [OpItem] -> Token
         -> ([Diagnosis], [TERM]) 

convertMixfixToken ga vs is t = 
     if isPlace t then ([], [Mixfix_token t])
     else if isString t then 
	  case string_lit $ literal_annos ga of
	  Nothing -> ([Error "missing %string annotation" (tokPos t)], [])
          Just (c, f) -> makeStringTerm is c f t
     else error "not implemented yet"
-}