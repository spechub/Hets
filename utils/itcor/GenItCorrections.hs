{- |
Module      :  $Header$
Copyright   :  (c) C. Maeder, DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

-}

module Main where

import Text.ParserCombinators.Parsec
import qualified Data.Map as Map
import System.Environment
import System.Exit
import System.Cmd
import Control.Monad

usage :: IO ()
usage = putStrLn
          "Usage: it-corrections \"gen_it_characters\" \"gen_it_words\""

main :: IO ()
main = do
  args <- getArgs
  case args of
   [] -> usage
   [_] -> usage
   [fp1_base, fp2_base] -> do
       let fp1 = fp1_base ++ ".txt"
           fp2 = fp2_base ++ ".txt"
           fp1_tex = fp1_base ++ ".tex"
           fp2_tex = fp2_base ++ ".tex"
           fp1_pdf = fp1_base ++ ".pdf"
           fp2_pdf = fp2_base ++ ".pdf"
       generate_tex_files fp2_tex fp1_tex
       convert_to_txt fp1_tex fp1_pdf
       convert_to_txt fp2_tex fp2_pdf
       str1 <- readFile fp1        -- file with table for every character
       p1 <- parseItTable str1
       str2 <- readFile fp2        -- file with table for combinated characters
       p2 <- parseItTable str2
       let itc = corrections (Map.fromList (zip allCharacters p1))
                          (zip combinations p2)
       str <- output itc ""  -- print itc
       putStrLn ("\nitaliccorrection_map :: Map String Int\n" ++
                 "italiccorrection_map = fromList $ read " ++ post_proc str )
   _ -> usage

convert_to_txt :: FilePath -> FilePath -> IO ()
convert_to_txt tex_name pdf_name = do
  system ("pdflatex -interaction=batchmode " ++ tex_name ++ " >/dev/null") >>=
          \ ec -> when (isFail ec) (fail "pdflatex went wrong")
  rawSystem "pdftotext" ["-raw", "-q", pdf_name] >>=
          \ ec -> when (isFail ec) (fail "pdftotext went wrong")
  return ()
  where isFail ec = case ec of
                      ExitFailure _ -> True
                      _ -> False

generate_tex_files :: String -> String -> IO ()
generate_tex_files filename1 filename2 = do
  writeFile filename1 (tex_file $ writeTexTable combinations)
  writeFile filename2 (tex_file $ writeTexTable [[c] | c <- allCharacters])

output :: [(String, Int)] -> String -> IO String
output [] str = return (init str)
output ((s, i) : xs) str =
    output xs $ str ++ "(\"" ++ s ++ "\"," ++ show i ++ "),"

post_proc :: String -> String
post_proc str = '\"' : '[' : concatMap conv str ++ "]\""
    where conv c = case c of
                   '\"' -> "\\\""
                   -- substitute umlauts with \196\214\220\223\228\246\252
                   '\196' -> "\\196"
                   '\214' -> "\\214"
                   '\220' -> "\\220"
                   '\223' -> "\\223"
                   '\228' -> "\\228"
                   '\246' -> "\\246"
                   '\252' -> "\\252"
                   _ -> [c]

-- -------- Parser for Table generated with "width-it-table.tex" ---------
parseItTable :: String -> IO [Double]
parseItTable str = case (parse itParser "" str) of
    Left err -> do
      putStr "parse error at"
      print err; error ""
    Right x -> return x


itParser :: Parser [Double]
itParser = do
    manyTill anyChar (try (string "wl: "))
    many1 tableEntry
  <|> do
    anyChar
    itParser


tableEntry :: Parser Double
tableEntry = do
    str <- parseDouble
    string "pt"
    spaces
    try (manyTill anyChar $ try $ string "wl: ") <|> manyTill anyChar eof
    return (read str)

parseDouble :: Parser String
parseDouble = many1 double

double :: Parser Char
double = digit <|> char '.'

stringHead :: Parser String
stringHead = do
  c1 <- tableChar
  c2 <- option "" tableChar
  return (c1 ++ c2)

tableChar :: Parser String
tableChar = do
  str <- try letter <|> digit
  return [str]

-- ------------------------------------------------------------------------

corrections :: Map.Map Char Double -> [(String, Double)] -> [(String, Int)]
corrections fm = map (corrections' fm)

corrections' :: Map.Map Char Double -> (String, Double) -> (String, Int)
corrections' fm (str, d) = case str of
  [c1, c2] ->
    let d1 = Map.findWithDefault 0.0 c1 fm
        d2 = Map.findWithDefault 0.0 c2 fm
        dif = round (((d1 + d2) - d) * 0.351 * 1000.0)
    in (str, dif)
  _ -> error "corrections'"

combinations :: [String]
combinations = let z = zipIt allCharacters allCharacters
               in [ c1 : [c2] | (c1, c2) <- z ]
               where
               zipIt :: String -> String -> [(Char, Char)]
               zipIt [] _ = []
               zipIt (a : as) bs = zip [a, a ..] bs ++ zipIt as bs

allCharacters :: String
allCharacters = ['a' .. 'z'] ++ ['A' .. 'Z'] ++ ['0' .. '9']
                ++ "\228\252\246\196\220\214\223"

writeTexTable :: [String] -> String
writeTexTable [] = []
writeTexTable strl = concat
    [ "\\wordline{\\textit{" ++ str ++ "}}\n\\hline\n" | str <- f ]
    ++ "\\end{tabular}\n\\newpage\n\\begin{tabular}{l|l}\n\\hline\n"
    ++ writeTexTable r
    where (f, r) = splitAt 30 strl


tex_file :: String -> String
tex_file str = unlines
  [ "\\documentclass[a4paper]{article}"
  , "\\usepackage{bookman}"
  , "\\usepackage[latin1]{inputenc}"
  , "\\usepackage{german}"
  , "\\usepackage{calc}"
  , "\\usepackage{longtable}"
  , "\\newlength{\\widthofword}"
  , "\\setlength{\\parindent}{0cm}"
  , "\\newcommand{\\wordline}[1]%"
  , "{#1 & wl: \\setlength{\\widthofword}{\\widthof{#1}}\\the\\widthofword\\\\}"
  , "\\title{Useful Widths for Typesetting-CASL}"
  , "\\author{Klaus Luettich}"
  , "\\begin{document}"
  , "\\maketitle"
  , "\\begin{tabular}{l|l}"
  , "\\hline"
  , str
  , "\\end{tabular}"
  , "\\end{document}" ]
