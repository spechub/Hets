module MixfixParser where

import AS_Basic_CASL 
import LocalEnv
import GlobalAnnotations
import Result
import Id
import qualified Char as C


-- analyse Mixfix_token
convertMixfixToken:: GlobalAnnos -> [varDecl] -> [OpItem] -> Token
         -> ([Diagnosis], [TERM]) 

isChar :: Token -> Bool
isChar t = head (tokStr t) == '\''

isString t = head (tokStr t) == '\"'
isNumber t = C.isDigit $ head $ tokStr t

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

makeStringTerm is c f tok = 
	 case filter (\x -> opId x == c && null (opArgs (opType x))) is of
	 [e] -> let ty = opType e
                    ot = (case opKind ty of 
			     Total -> Total_op_type 
			     Partial -> Partial_op_type) [] (opRes ty) []    
		    a = Application (Qual_op_name c ot []) [] [tokPos tok]
                    l = (init (tail (tokStr tok)))
                in ([],[a]) -- continue for l
         _ -> error "not unique" 


convertMixfixToken ga vs is t = 
     if isPlace t then ([], [Mixfix_token t])
     else if isString t then 
	  case string_lit $ literal_annos ga of
	  Nothing -> ([Error "missing %string annotation" (tokPos t)], [])
          Just (c, f) -> makeStringTerm is c f t
     else error "not implemented yet"
