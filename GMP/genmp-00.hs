{- General Structure of the datatype holding the modal logics formulae:
phi ::= 'F' | 'T' | '~' phi | phi '/\' phi | phi '\/' phi | phi '->' phi | phi '<-' phi | phi '<->' phi | '[?]' phi | '<?>' phi
-}
module Main where

import IO
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import qualified Text.ParserCombinators.Parsec.Token as P
import Text.ParserCombinators.Parsec.Language( haskellStyle, haskellDef )

-- some of the following might be excluded: to be decided later
lexer :: P.TokenParser ()
lexer = P.makeTokenParser( haskellDef { P.reservedOpNames = ["Neg","And","Or","If","Iff","Fi"] })
whiteSpace = P.whiteSpace lexer
lexeme = P.lexeme lexer
symbol = P.symbol lexer
parens = P.parens lexer
semi = P.semi lexer
identifier = P.identifier lexer
reserved = P.reserved lexer
reservedOp = P.reservedOp lexer


data Mindex = String
data Otype = Square | Angle
data Mop = Mindex Otype 
data Formula = F | T | Neg Formula -- boolean false, true and negation
            | And Formula Formula | Or Formula Formula -- /\ and \/ logic connectors
            | If Formula Formula | Iff Formula Formula | Fi Formula Formula -- ->, <-> and <- connectors
            | Mop Formula -- for the modal logics operators

par5er :: Parser Formula
par5er = do
		return F -- this is obviously incomplete
	

runLex :: Show a => Parser a -> String -> IO ()
runLex p input = run (do { 
	whiteSpace
	; x <- p
	; eof
	; return x
	}) input

run :: Show a => Parser a -> String -> IO ()
run p input
        = case (parse p "" input) of
                Left err -> do{ putStr "parse error at "
                                ; print err
							  }
                Right x -> print x
{- Since "Show" is not defined for our Datatype we might need to implement it
Show :: Formula -> String
Show F = return "F" 
	<|> T = return "T"
	<|> Not x= return ("~" ++ Show x)
	<|> And(x,y) = return ( Show x ++ "/\\" ++ Show y )
	<|> Or(x,y) = return ( Show x ++ "\\/" ++ Show y )
	-- and a few more
-}
main = do
    hSetBuffering stdin LineBuffering
    putStrLn "Give the number of the test file: "
    no <- getLine
    input <- readFile ( "formula" ++ no )
    runLex par5er input

