module Main where

--import GMP.GMPParser
--import GMP.GradedML
import GMP.GMPAS
import GMP.Lexer
import Text.ParserCombinators.Parsec
import System.Environment
import qualified IO as IO

data RFormula = N RFormula            -- negation
              | A RFormula RFormula   -- logical and
              | O  RFormula RFormula  -- logical or
              | I RFormula RFormula   -- implication
              | AL Int RFormula       -- at least
              | AM Int RFormula       -- at most
              | V Char                -- variables
    deriving (Eq, Ord)

instance Show RFormula where
    show f = case f of
        I g h   -> "(concept-subsumes?\n" ++ show g ++ "\n" ++ show h ++ ")"
        N g     -> "(not " ++ show g ++ ")"
        A g h   -> "(and " ++ show g ++ " " ++ show h ++ ")"
        O g h   -> "(or " ++ show g ++ " " ++ show h ++ ")"
        AL i g  -> "\nat-least " ++ show i ++ " R " ++ show g
        AM i g  -> "\nat-most " ++ show i ++ " R " ++ show g
        V c     -> [c]

varP :: CharParser st Char
varP = let isAsciiLower c = c >= 'a' && c <= 'z'
       in satisfy isAsciiLower

rfParser :: forall st. GenParser Char st RFormula
rfParser =  do try (char '~')
               whiteSpace
               f <- rfParser
               return $ N f
        <|> do try (char '&')
               whiteSpace
               f <- rfParser
               whiteSpace
               g <- rfParser
               return $ A f g
        <|> do try (char '|')
               whiteSpace
               f <- rfParser
               whiteSpace
               g <- rfParser
               return $ O f g
        <|> do try (string "al")
               whiteSpace
               n <- natural
               whiteSpace
               f <- rfParser
               return $ AL (fromInteger n) f
        <|> do try (string "am")
               whiteSpace
               n <- natural
               whiteSpace
               f <- rfParser
               return $ AM (fromInteger n) f
        <|> do c <- varP
               return $ V c
        <?> "ToRacer.rfParser"

toFormula :: RFormula -> Formula GML
toFormula f =
    case f of
        N g    -> Neg (toFormula g)
        A g h  -> Junctor (toFormula g) And (toFormula h)
        O g h  -> Junctor (toFormula g) Or (toFormula h)
        I g h  -> Junctor (toFormula g) If (toFormula h)
        V c    -> Var c Nothing
        AL i g -> Mapp (Mop (GML i) Square) (toFormula g)
        AM i g -> let aux = toFormula g
                  in Junctor (Mapp (Mop (GML (i-1)) Angle) aux) And (Neg (Mapp (Mop (GML i) Angle) aux))

help :: IO()
help = do
    putStrLn ("Usage:\n" ++
               "./<exe> <pathi> <pathof> <pathor>\n" ++
               "<exe>    : executable file\n" ++
               "<pathof> : path to file to write formula into\n" ++
               "<pathor> : path to file to write racer formula into\n" ++
               "<pathi>  : path to file to read from\n")

main :: IO()
main = do
    args <- getArgs
    if (args==[])||(head args == "--help")||(length args < 3)
      then help
      else do let pi = head args
                  aux = tail args
                  pf = head aux
                  pr = head (tail aux)
              input <- IO.readFile pi
              print input
--              IO.writeFile pf (show (toFormula input))
--              IO.writeFile pr (show input)
--              f <- runGMP ((par5er parseIndex) :: Parser (Formula GML)) input
--              runLex po f toRparse
