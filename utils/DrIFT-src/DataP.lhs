Adaptation and extension of a parser for data definitions given in
appendix of G. Huttons's paper - Monadic Parser Combinators.

Parser does not accept infix data constructors. This is a shortcoming that
needs to be fixed.

>module DataP (Statement(..),Data(..),Type(..),Body(..),
>		Name,Var,Class,Constructor,AtermConst(..),
>		datadecl,newtypedecl,at_constructor)
>where 

>import ParseLib2
>import Char

>data Statement = DataStmt | NewTypeStmt deriving (Eq,Show)
>data Data = D {	name :: Name,		-- type name
>			constraints :: [(Class,Var)], 
>			vars :: [Var],		-- Parameters
>			body :: [Body],
>			derives :: [Class],		-- derived classes
>			statement :: Statement}
>	   | Directive 
>	   | TypeName Name
>		deriving (Eq,Show) 
>data Body = Body { constructor :: Constructor,
>		    labels :: [Name],
>		    types :: [Type],
>	            aterm_constructor :: AtermConst} deriving (Eq,Show) 
>type Name = String
>type Var = String
>type Class = String
>type Constructor = String
>data AtermConst = Const String AtermConst
>	         | Args
>	           deriving (Eq,Show)
>----------------------------------------------------------------------------

 special thing for aterms: 
 it is needed for changing constructor names and for nesting function
 application in aterms. The dots will be replaced with the arguments.

 Syntax:
 {-!==> A(B(C(..))) !-}

>at_constructor = bracket (symbol"{-!") cons (symbol"!-}")
>
>cons = do symbol "==>"
>	   c <- nest_cons
>	   return [c]
>	  
>nest_cons = do c  <- token con_str
>	        nc <- bracket (symbol "(") nest_cons' (symbol ")")
>	        return (Const c nc)
>    where nest_cons' = (do symbol ".."
>		            return Args)
>		         +++  
>		         nest_cons
>	   con_str    = do x <- sat (\x -> isAlpha x)
>		           xs <- many (sat (\x -> isAlphaNum x || 
>				                  x `elem` "*+-_"))
>			   return (x:xs)
>----------------------------------------------------------------------------
>datadecl :: Parser Data
>datadecl = do 
>		symbol "data"
>               con <- opt constraint 
>	        x <- constructorP
>	        xs <- many variable
>	        symbol "="
>	        b <- (conrecdecl {-+++ infixdecl-}) `sepby1` symbol "|"
>		d <- opt deriveP
>               return $D x con xs b d DataStmt

>newtypedecl :: Parser Data
>newtypedecl = do 
>	symbol "newtype"
>	con <- opt constraint
>	x <- constructorP
>	xs <- many variable
>	symbol "="
>	b <- condecl 
>	d <- opt deriveP
>       return $ D x con xs [b] d NewTypeStmt

>---------------------------------------------------------------------------
>constructorP = token $
>       do {x <- upper;xs <- many alphanum;return (x:xs)}

>infixconstr = token $ do
>	x <- char ':'
>	y <- many1 $ sat (\x -> (not . isAlphaNum) x  && (not . isSpace) x)
>	z <- char ':'
>	return (x:y++[z])
>	

>variable = identifier [ "data","deriving","newtype", "type",
>			"instance", "class", "module", "import", 
>			"infixl", "infix","infixr", "default"]

>condecl = do
>	x   <- constructorP
>	ts  <- many type2
>       acs <- opt at_constructor
>       return $ Body x [] ts (choose acs x)
>
>choose acs x = case acs of 
>	       []   -> Const x Args
>	       [ac] -> ac
>	       _    -> error ("something with the constructor "++
>		               x ++ " went wrong")

>conrecdecl = do
>	x <- constructorP
>	(ls,ts) <- record +++ fmap (\a -> ([],a)) (many type2)
>       acs <- opt at_constructor
>       return $ Body x ls ts (choose acs x)

>-- haven't worked infixes into the program yet, as they cause problems 
>-- throughout
>infixdecl = do
>	t1 <- type2
>	x <- infixconstr
>	ts <- many1 type2
>	return $ Body x [] (t1:ts)

>record = do
>       symbol "{"
>       (ls,ts) <- fmap unzip $ rectype `sepby1` symbol ","
>	symbol "}"
>       return (ls,ts)

>constraint = do{x <- constrs; symbol "=>"; return x}
>	where
>	constrs = fmap (\x -> [x]) one +++ 
>		  bracket (symbol "(") (one `sepby` symbol ",") (symbol ")")
>	one = do{c <- constructorP; v <- variable; return (c,v)}

>deriveP = do{symbol "deriving"; one +++ more}
>	where
>	one = fmap(\x -> [x]) constructorP -- well, it has the same form
>	more = bracket  (symbol "(")
>			(constructorP `sepby` symbol ",")
>			(symbol ")")
>---------------------------------------------------------------------------
>data Type	= Arrow Type Type -- fn
>		| Apply Type Type -- application
>		| LApply Type [Type] -- proper application
>		| Var String	  -- variable
>		| Con String      -- constructor
>		| Tuple [Type]	  -- tuple
>		| List Type	  -- list
>			deriving (Eq,Show)
>type0 :: Parser Type
>type0 = type1 `chainr1` fmap (const Arrow) (symbol "->")
>--type1 = type2 `chainl1` (return Apply)
>type1 = (do c <- con
>            as <- many1 type2
>            return (LApply c as)) +++
>        type2
>type2 = var +++ con +++ list +++ tuple

>var = fmap Var variable

>con = fmap Con constructorP

>list = fmap List $ bracket (symbol "[")
>			type0
>			(symbol "]")

>tuple = fmap f $ bracket (symbol "(")
>			(type0 `sepby` symbol ",")
>			(symbol ")")
>	where f [t] = t
>	      f ts = Tuple ts

>--record entry
>rectype :: Parser (String,Type) 
>rectype = do	
>	s <- variable
>	symbol "::"
>       t <- type0
>       return (s,t)
