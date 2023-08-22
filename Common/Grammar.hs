-- parse the ISO BNF grammar for DOL

import Common.Parsec

import Control.Monad
import Data.List

import qualified Data.Set as Set

import Text.ParserCombinators.Parsec

data Term =
    Terminal String
  | NT String
  | Alt [Term]
  | Seq [Term]
  | Option Term
  | Many Term Bool

data Rule = Rule { lhs :: String, rhs :: Term }

lhss :: [Rule] -> [String]
lhss = sort . map lhs

nts :: Bool -> Term -> Set.Set String
nts b trm = let unite = Set.unions . map (nts b) in case trm of
  Terminal s -> if b || isPrefixOf "($<$" s then Set.empty
    else Set.singleton . init $ tail s
  NT s -> if b then Set.singleton s else Set.empty
  Alt l -> unite l
  Seq l -> unite l
  Option t -> nts b t
  Many t _ -> nts b t

terms :: Bool -> [Rule] -> Set.Set String
terms b = Set.unions . map (nts b . rhs)

terminals = terms False

undeclared rs = Set.difference (terms True rs) . Set.fromList $ lhss rs
startsyms rs = Set.difference (Set.fromList $ lhss rs) $ terms True rs

doubles = map head . filter ((> 1) . length) . group . lhss

ppRule :: Rule -> String
ppRule (Rule s t) =
 take (max 20 $ length s) (s ++ repeat ' ') ++ " = " ++ (case t of
   Alt (f : l) -> ppTerm f
     ++ concatMap ((("\n" ++ replicate 21 ' ' ++ "| ") ++) . ppTerm) l
   _ -> ppTerm t) ++ " ;"

ppRules :: [Rule] -> String
ppRules = unlines . map ppRule

ppTerm :: Term -> String
ppTerm = pppTerm False

pppTerm :: Bool -> Term -> String
pppTerm p trm = case trm of
  Terminal s -> s
  NT s -> s
  Alt l -> let s = intercalate " | " $ map ppTerm l
    in if p then "( " ++ s ++ " )" else s
  Seq l -> intercalate " , " $ map (pppTerm True) l
  Option t -> "[ " ++ ppTerm t ++ " ]"
  Many t b -> "{ " ++ ppTerm t ++ " }" ++ if b then "" else "-"

nt :: CharParser st String
nt = tok $ letter <:> many (letter <|> digit <|> oneOf "-_")

primTerm :: CharParser st Term
primTerm = fmap Terminal (tok sQuoted)
  <|> fmap (Terminal . (++ "$>$)"))
        (try (string "($<$") <++> manyTill anyChar
         (tok . try $ string "$>$)"))
  <|> fmap NT nt
  <|> (tok (char '(') >> pTerm << tok (char ')'))
  <|> fmap Option (tok (char '[') >> pTerm << tok (char ']'))
  <|> fmap (\ (t, b) -> Many t (b == "}"))
          (pair (tok (char '{') >> pTerm)
             (tok (try (string "}-") <|> string "}")))

seqTerm :: CharParser st Term
seqTerm = fmap
  (\ l -> case l of
    [t] -> t
    _ -> Seq l)
  . sepBy1 primTerm . tok $ char ','

pTerm :: CharParser st Term
pTerm = fmap
  (\ l -> case l of
    [t] -> t
    _ -> Alt l)
  . sepBy1 seqTerm . tok $ char '|'

pRule :: CharParser st Rule
pRule = liftM2 Rule (nt << tok (char '=')) $ pTerm << tok (char ';')

tok :: CharParser st a -> CharParser st a
tok p = p << spaces

main :: IO ()
main = do
  str <- getContents
  case parse (spaces >> many1 pRule << eof) "" str of
    Right e -> do
         let prn f = print $ f e
         prn length
         prn lhss
         prn doubles
         prn undeclared
         prn startsyms
         prn terminals
         putStr $ ppRules e
    Left e -> print e
