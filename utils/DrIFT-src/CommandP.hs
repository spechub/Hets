-- parser for derive commands
module CommandP (local,command,header) where

import ParseLib2
import DataP

-- command syntax
{-!global : rule1, rule2, rule !-}
{-! derive : rule1, rule2, !-}
{-! for ty derive : rule , rule 2, .. !-}

command = annotation global +++ annotation forType
local = annotation loc

global = do symbol "global"
	    symbol ":"
	    ts <- tag `sepby` symbol ","
            return (ts,Directive)

forType = do symbol "for"
	     ty <- cap
	     symbol "derive"
	     symbol ":"
	     ts <- tag `sepby` symbol ","
             return (ts,TypeName ty)

loc = do symbol "derive"
	 symbol ":"
	 tag `sepby` symbol ","

cap = token (do x <- upper
                xs <- many alphanum
                return (x:xs))
tag = token (many alphanum)

annotation x = do symbol "{-!"
                  r <- x
                  symbol "!-}"
                  return r

-- parser for module headers

header = do symbol "module"
	    cap
	    opt (do skipNest (symbol "(") (symbol ")")
                    return [])
	    symbol "where"
	    many imports

imports = do symbol "import"
	     opt (symbol "qualified")
	     i <- cap
	     opt (symbol "as" >> cap)
	     opt (symbol "hiding")
	     opt (do skipNest (symbol "(") (symbol ")")
                     return [])
             return i
