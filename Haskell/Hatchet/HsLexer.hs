module Haskell.Hatchet.HsLexer (Token(..), lexer, parseError,isSymbol) where

import Haskell.Hatchet.HsParseMonad
import Haskell.Hatchet.HsParseUtils
import Haskell.Hatchet.HsSyn(SrcLoc(..))
import Data.List
import Char



data Token 
        = VarId String
        | QVarId (String,String)
        | ConId String
        | QConId (String,String)
        | VarSym String
        | ConSym String
        | QVarSym (String,String)
        | QConSym (String,String)
        | IntTok String
        | FloatTok String
        | Character Char
        | StringTok String

-- Symbols

        | LeftParen
        | RightParen
        | SemiColon
        | LeftCurly
        | RightCurly
        | VRightCurly			-- a virtual close brace
        | LeftSquare
        | RightSquare
        | Comma
        | Underscore
        | BackQuote

-- Reserved operators

	| DotDot
	| DoubleColon
	| Equals
	| Backslash
	| Bar
	| LeftArrow
	| RightArrow
	| At
	| Tilde
	| DoubleArrow
	| Minus
	| Exclamation

-- Reserved Ids

	| KW_As       
	| KW_Case     
	| KW_Class    
	| KW_Data     
	| KW_Default  
	| KW_Deriving 
	| KW_Do       
	| KW_Else     
	| KW_Hiding
	| KW_If       
	| KW_Import   
	| KW_In       
	| KW_Infix    
	| KW_InfixL   
	| KW_InfixR   
	| KW_Instance 
	| KW_Let      
	| KW_Module   
	| KW_NewType  
	| KW_Of       
	| KW_Then     
	| KW_Type     
	| KW_Where    
	| KW_Qualified

-- Reserved Ids Extended Haskell

        | KW_Forall
        | KW_Exists
        | KW_Existsone

-- Extended Haskell Pragma

        | KW_OpenPrag
        | KW_AxiomsPrag
        | KW_ClosePrag

        | EOF
        deriving (Eq,Show)

reserved_ops :: [(String,Token)]
reserved_ops = [
 ( "..", DotDot ),    
 ( "::", DoubleColon ),
 ( "=",  Equals ),    
 ( "\\", Backslash ), 
 ( "|",  Bar ),       
 ( "<-", LeftArrow ), 
 ( "->", RightArrow ),
 ( "@",  At ),        
 ( "~",  Tilde ),     
 ( "=>", DoubleArrow ),
 ( "-",  Minus ),			--ToDo: shouldn't be here
 ( "!",  Exclamation ), 		--ditto
 ( "{-#", KW_OpenPrag ),
 ( "#-}", KW_ClosePrag ),
 ( "AXIOMS",    KW_AxiomsPrag)
 ]

reserved_ids :: [(String,Token)]
reserved_ids = [
 ( "_",         Underscore ),
 ( "case",      KW_Case ),     
 ( "class",     KW_Class ),    
 ( "data",      KW_Data ),     
 ( "default",   KW_Default ),  
 ( "deriving",  KW_Deriving ), 
 ( "do",        KW_Do ),       
 ( "else",      KW_Else ),     
 ( "if",    	KW_If ),       
 ( "import",    KW_Import ),   
 ( "in", 	KW_In ),       
 ( "infix", 	KW_Infix ),    
 ( "infixl", 	KW_InfixL ),   
 ( "infixr", 	KW_InfixR ),   
 ( "instance",  KW_Instance ), 
 ( "let", 	KW_Let ),      
 ( "module", 	KW_Module ),   
 ( "newtype",   KW_NewType ),  
 ( "of", 	KW_Of ),       
 ( "then", 	KW_Then ),     
 ( "type", 	KW_Type ),     
 ( "where", 	KW_Where ),    
 ( "as", 	KW_As ),       
 ( "qualified", KW_Qualified ),
 ( "hiding", 	KW_Hiding ),
 ( "forall",    KW_Forall ),                --ExtHas
 ( "exists",    KW_Exists ),
 ( "existsone", KW_Existsone)
 ]

isIdent  c = isAlpha c || isDigit c || c == '\'' || c == '_'
isSymbol c = elem c ":!#$%&*+./<=>?@\\^|-~"
isWhite  c = elem c " \n\r\t\v\f"

data IntKind
        = Decimal     (String,String)
        | Octal       (String,String)
        | Hexadecimal (String,String)

tAB_LENGTH = 8 :: Int

-- The source location, (y,x), is the coordinates of the previous token.
-- col is the current column in the source file.  If col is 0, we are
-- somewhere at the beginning of the line before the first token.

-- Setting col to 0 is used in two places: just after emitting a virtual
-- close brace due to layout, so that next time through we check whether
-- we also need to emit a semi-colon, and at the beginning of the file,
-- to kick off the lexer.

lexer :: (Token -> P a) -> P a
lexer cont input (SrcLoc y x) col =
        if col == 0
           then tab y x True input
           else tab y col False input -- throw away old x
  where
   	-- move past whitespace and comments
        tab y x bol [] = 
        	cont EOF [] (SrcLoc y x) col
        tab y x bol ('\t':s) =
        	tab y (nextTab x) bol s
        tab y x bol ('\n':s) =
                newLine cont s y
        tab y x bol ('-':'-':s) = 
        	newLine cont (drop 1 (dropWhile (/= '\n') s)) y
        tab y x bol ('{':'-':s)
                | head s == '#' = if bol 
                                    then lexBOL cont ('{':'-':s) (SrcLoc y x) x
                                    else lexToken 
                                          cont ('{':'-':s) (SrcLoc y x) x
                | otherwise = nestedComment tab y x bol s
        tab y x bol (c:s)
        	| isWhite c = tab y (x+1) bol s
        	| otherwise = 
        		if bol 	then lexBOL   cont (c:s) (SrcLoc y x) x
        			else lexToken cont (c:s) (SrcLoc y x) x

	newLine cont s y =  tab (y+1) 1 True s

nextTab x = x + (tAB_LENGTH - (x-1) `mod` tAB_LENGTH)

-- When we are lexing the first token of a line, check whether we need to
-- insert virtual semicolons or close braces due to layout.

lexBOL :: (Token -> P a) -> P a
lexBOL cont s loc@(SrcLoc y x) col context =
--   trace ("lexBOL: y="++show y++" x="++show x) $ 
        if need_close_curly then 
        	-- Set col to 0, indicating that we're still at the
        	-- beginning of the line, in case we need a semi-colon too.
        	-- Also pop the context here, so that we don't insert
        	-- another close brace before the parser can pop it.
        	cont VRightCurly s loc 0 (tail context)
        else if need_semi_colon then
        	cont SemiColon s loc col context
        else
        	lexToken cont s loc col context
 where
        need_close_curly =
        	case context of
        		[] -> False
        		(i:_) -> case i of
        			    NoLayout -> False
        			    Layout n -> x < n
        need_semi_colon =
        	case context of
        		[] -> False
        		(i:_) -> case i of
        			    NoLayout -> False
        			    Layout n -> x == n

lexToken :: (Token -> P a) -> P a
lexToken cont (c:s) loc@(SrcLoc y x') x =
   case c of
-- ExtHas
        '{' | head s == '-' && head(tail s) == '#'->
                        special3 KW_OpenPrag
        '#' | head s == '-' && head(tail s) == '}' ->
                        special3 KW_ClosePrag
-- ExtHas
        -- First the special symbols
        '(' -> special LeftParen
        ')' -> special RightParen
        ',' -> special Comma
        ';' -> special SemiColon
        '[' -> special LeftSquare
        ']' -> special RightSquare
        '`' -> special BackQuote
        '{' -> \ctxt -> special LeftCurly (NoLayout : ctxt)
        '}' -> \stk -> case stk of
                        (_:ctxt) -> special RightCurly ctxt -- pop context on '}'
                        []       -> error "Internal error: empty context in lexToken"

        '\'' -> lexChar cont s loc (x+1)
        '\"'{-"-} -> lexString cont s loc (x+1)
        c | isLower c || c == '_' ->
        	let 
        	    (idtail, rest) = span isIdent s
        	    id = c:idtail
        	    l_id = 1 + length idtail
        	in
        	case lookup id reserved_ids of
        		Just keyword -> forward l_id keyword rest
        		Nothing -> forward l_id (VarId id) rest

          | isUpper c ->
        	let
        	    (contail, rest) = span isIdent s
        	    l_con = 1 + length contail
        	    con = c:contail
        	in
        	case rest of
        	    '.':s1 -> lexConIdOrQualId (c:contail) l_con rest
        	    _ ->          -- not a qualified object
                          if contail == "XIOMS" then forward l_con 
                                                      KW_AxiomsPrag rest
                                                 else forward l_con (ConId con) rest

          | isSymbol c ->
        	let
        	    (symtail, rest) = span isSymbol s
        	    sym = c : symtail
        	    l_sym = 1 + length symtail
        	in
        	case lookup sym reserved_ops of
        	    Just t  -> forward l_sym t rest
        	    Nothing -> case c of
        			':' -> forward l_sym (ConSym sym) rest
        			_   -> forward l_sym (VarSym sym) rest

          | isDigit c ->
        	case lexInt (c:s) of
        	    Decimal     (n,rest) ->
        		case rest of
        		    ('.':c2:rest2) | isDigit c2 ->
        			case lexFloatRest (c2:rest2) of
                                  Nothing -> parseError "Illegal float" s loc x
                                  Just (n2,rest3) -> let f = n ++ ('.':n2)
        			                       in forward (length f) (FloatTok f) rest3
                    	    _ -> forward (length n) (IntTok n) rest
        	    Octal       (n,rest) -> forward (length n) (IntTok n) rest
        	    Hexadecimal (n,rest) -> forward (length n) (IntTok n) rest

          | otherwise ->
        	parseError ("illegal character \'" ++ show c ++ "\'\n") 
        		  s loc x

 where special t = forward 1 t s
       forward n t s = cont t s loc (x+n)
-- forward (l_con+l_con1) (QConId (con, (c1:con1))) rest1
       special3 t = forward 3 t (tail(tail s))

       lexFloatRest r = case span isDigit r of
        		      (r2, 'e':r3) -> lexFloatExp (r2 ++ "e") r3
        		      (r2, 'E':r3) -> lexFloatExp (r2 ++ "e") r3
        		      f@(r2,   r3) -> Just f

       lexFloatExp r1 ('-':r2) = lexFloatExp2 (r1 ++ "-") r2
       lexFloatExp r1 ('+':r2) = lexFloatExp2 (r1 ++ "+") r2
       lexFloatExp r1      r2  = lexFloatExp2 r1          r2

       lexFloatExp2 r1 r2 = case span isDigit r2 of
                                ("", _ ) -> Nothing
                                (ds, r3) -> Just (r1++ds,r3)
       lexConIdOrQualId con l_con (p:c1:s1)
                     | isLower c1 =	-- qualified varid?
        		let
        		    (idtail, rest1) = span isIdent s1
        		    id = c1:idtail
        		    l_id = 1 + length idtail
        		in
        		case lookup id reserved_ids of
        		   -- cannot qualify a reserved word
        		   Just keyword ->
        			forward l_con (ConId con) (c1:s1)
        		   Nothing ->
                                case rest1 of
                                    '.':s2 -> lexConIdOrQualId (con ++ (p:id)) (l_con + l_id) rest1
                                    _      -> forward (l_con+l_id) (QVarId (con, id)) rest1

        	     | isUpper c1 =	-- qualified conid?
        		let 
        		    (con1,rest1) = span isIdent s1
        		    l_con1 = 1 + length con1
        		in
                        case rest1 of
                            '.':s2 -> lexConIdOrQualId (con ++ (p:c1:con1)) (l_con + l_con1) rest1
                            _      -> forward (l_con+l_con1) (QConId (con, (c1:con1))) rest1

        	     | isSymbol c1 =	-- qualified symbol?
        		let
        		    (symtail, rest1) = span isSymbol s1
        		    sym = c1 : symtail
        		    l_sym = 1 + length symtail
        		in
        		case lookup sym reserved_ops of
        		    -- cannot qualify a reserved operator
        		    Just _  -> 
        			forward l_con (ConId con) (c1:s1)
        		    Nothing -> 
                                 case rest1 of
                                     '.':s2 -> lexConIdOrQualId (con ++ (p:sym)) (l_con + l_sym) rest1
                                     _      ->
                                          case c1 of
                                              ':' -> forward (l_con+l_sym) 
        					     (QConSym (con, sym)) rest1
        				      _   -> forward (l_con+l_sym)
        					     (QVarSym (con, sym)) rest1

			      
lexToken _ _ _ _ = error "Internal error: empty input in lexToken"

lexInt ('0':o:d:r) | toLower o == 'o' && isOctDigit d = let (ds,rs)= span isOctDigit r in Octal       ('0':'o':d:ds,rs)
lexInt ('0':x:d:r) | toLower x == 'x' && isHexDigit d = let (ds,rs)= span isHexDigit r in Hexadecimal ('0':'x':d:ds,rs)
lexInt r					        = Decimal (span isDigit r)

lexChar :: (Token -> P a) -> P a
lexChar cont s loc@(SrcLoc _ _) x = case s of
                    '\\':s -> (escapeChar s `thenP` \(e,s,i) _ _ _ ->
                               charEnd e s loc (x+i)) s loc x
                    c:s    -> charEnd c s loc (x+1)
                    []     -> error "Internal error: lexChar"

  where charEnd c ('\'':s) = \loc x -> cont (Character c) s loc (x+1)
        charEnd c s = parseError "Improperly terminated character constant" s

lexString :: (Token -> P a) -> P a
lexString cont s loc@(SrcLoc y _) x = loop "" s x y
  where
     loop e s x y = case s of
            '\\':'&':s  -> loop e s (x+2) y
            '\\':c:s | isSpace c -> stringGap e s (x+2) y
        	     | otherwise -> (escapeChar (c:s) `thenP` \(e',s,i) _ _ _ ->
        		             loop (e':e) s (x+i) y) s loc x
            '\"':s{-"-} -> cont (StringTok (reverse e)) s loc (x+1)
            c:s		-> loop (c:e) s (x+1) y
            []          -> parseError "Improperly terminated string" s loc x

     stringGap e s x y = case s of
        	'\n':s -> stringGap e s 1 (y+1)
        	'\\':s -> loop e s (x+1) y
        	c:s' | isSpace c -> stringGap e s' (x+1) y
        	     | otherwise -> 
        	       parseError "Illegal character in string gap" s loc x
                []     -> error "Internal error: stringGap"

-- ToDo: \o, \x, \<octal> things.

escapeChar :: String -> P (Char,String,Int)
escapeChar s = case s of

-- Production charesc from section B.2 (Note: \& is handled by caller)

  'a':s 	  -> returnP ('\a',s,2)
  'b':s 	  -> returnP ('\b',s,2)
  'f':s 	  -> returnP ('\f',s,2)
  'n':s 	  -> returnP ('\n',s,2)
  'r':s 	  -> returnP ('\r',s,2)
  't':s 	  -> returnP ('\t',s,2)
  'v':s 	  -> returnP ('\v',s,2)
  '\\':s        -> returnP ('\\',s,2)
  '"':s         -> returnP ('\"',s,2)
  '\'':s        -> returnP ('\'',s,2)

-- Production ascii from section B.2

  '^':x@(c:s)   -> cntrl x
  'N':'U':'L':s -> returnP ('\NUL',s,4)
  'S':'O':'H':s -> returnP ('\SOH',s,4)
  'S':'T':'X':s -> returnP ('\STX',s,4)
  'E':'T':'X':s -> returnP ('\ETX',s,4)
  'E':'O':'T':s -> returnP ('\EOT',s,4)
  'E':'N':'Q':s -> returnP ('\ENQ',s,4)
  'A':'C':'K':s -> returnP ('\ACK',s,4)
  'B':'E':'L':s -> returnP ('\BEL',s,4)
  'B':'S':s     -> returnP ('\BS', s,3)
  'H':'T':s  	  -> returnP ('\HT', s,3)
  'L':'F':s 	  -> returnP ('\LF', s,3)
  'V':'T':s 	  -> returnP ('\VT', s,3)
  'F':'F':s 	  -> returnP ('\FF', s,3)
  'C':'R':s 	  -> returnP ('\CR', s,3)
  'S':'O':s 	  -> returnP ('\SO', s,3)
  'S':'I':s 	  -> returnP ('\SI', s,3)
  'D':'L':'E':s -> returnP ('\DLE',s,4)
  'D':'C':'1':s -> returnP ('\DC1',s,4)
  'D':'C':'2':s -> returnP ('\DC2',s,4)
  'D':'C':'3':s -> returnP ('\DC3',s,4)
  'D':'C':'4':s -> returnP ('\DC4',s,4)
  'N':'A':'K':s -> returnP ('\NAK',s,4)
  'S':'Y':'N':s -> returnP ('\SYN',s,4)
  'E':'T':'B':s -> returnP ('\ETB',s,4)
  'C':'A':'N':s -> returnP ('\CAN',s,4)
  'E':'M':s     -> returnP ('\EM', s,3)
  'S':'U':'B':s -> returnP ('\SUB',s,4)
  'E':'S':'C':s -> returnP ('\ESC',s,4)
  'F':'S':s     -> returnP ('\FS', s,3)
  'G':'S':s     -> returnP ('\GS', s,3)
  'R':'S':s     -> returnP ('\RS', s,3)
  'U':'S':s     -> returnP ('\US', s,3)
  'S':'P':s     -> returnP ('\SP', s,3)
  'D':'E':'L':s -> returnP ('\DEL',s,4)

-- Escaped numbers are missing here..

  _             -> parseError "Illegal escape sequence"

-- Production cntrl from section B.2

cntrl :: String -> P (Char,String,Int)
cntrl (c   :s) | isUpper c = returnP (chr (ord c - ord 'A'), s,2)
cntrl ('@' :s)             = returnP ('\^@', s,2)
cntrl ('[' :s)             = returnP ('\^[', s,2)
cntrl ('\\':s)             = returnP ('\^\', s,2)
cntrl (']' :s)             = returnP ('\^]', s,2)
cntrl ('^' :s)             = returnP ('\^^', s,2)
cntrl ('_' :s)             = returnP ('\^_', s,2)
cntrl _                    = parseError "Illegal control character"

nestedComment cont y x bol s =
   case s of
      '-':'}':s -> cont y (x+2) bol s
      '{':'-':s -> nestedComment (nestedComment cont) y (x+2) bol s
      '\t':s    -> nestedComment cont y (nextTab x) bol s
      '\n':s    -> nestedComment cont (y+1) 1 True s
      c:s       -> nestedComment cont y (x+1) bol s
      []        -> error "Internal error: nestedComment"

