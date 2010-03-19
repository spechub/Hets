{- |
Module      :  $Id$
Copyright   :  (c) Felix Reckers, Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

a very limited Haskell-Parser based on DrIFT's Haskell-Parser

-}

module ParseFile where

import DataP
import CommandP
import ParseLib2

type Import = String

-- result: (datas, imports)
parseInputFile :: FilePath -> String -> Either String ([String], [Import])
parseInputFile fp inp = case (ds, is) of
  (Left s, Left s2) -> Left (s ++ "\n" ++ s2)
  (Left s, Right _) -> Left s
  (Right _, Left s) -> Left s
  (Right x, Right y) -> case y of
    [] -> Right (x, y)
    m : _ -> Right (map ((m ++ ".") ++) x, y)
  where
    datParser = skipUntilOff $ datadecl +++ newtypedecl
    ds = case papply (parse datParser) (0, 0) ((0, 0), inp) of
           [(x, _)] -> Right $ map name x
           _ -> Left (fp ++ ": wrong parse (data)")
    is = case papply (parse allImports) (0, -1) ((0, 0), inp) of
           [(x, _)] -> Right x
           _ -> Left (fp ++ ": wrong parse (imports)")

allImports :: Parser [Import]
allImports = do
    symbol "module"
    m <- cap
    opt (skipNest (symbol "(") (symbol ")") >> return [])
    symbol "where"
    many (fmap (const ()) command +++ comment)
    is <- many importDecl
    return (m : is)

importDecl :: Parser Import
importDecl = do
    symbol "import"
    q <- opt (symbol "qualified")
    i <- cap
    a <- opt (symbol "as" >> cap)
    h <- opt (symbol "hiding")
    hs <- opt $ importList (symbol "(") (symbol ")")
    let add s = if null s then "" else  ' ' : s
    return $ (if null q then "" else q ++ " ")
           ++ i ++ (if null a then "" else " as " ++ a)
           ++ add h ++ add hs

importList :: Parser String -> Parser String -> Parser String
importList start finish = let
    x = finish
        +++ do
          l <- importList start finish
          s <- x
          return (l ++ s)
        +++ do
          c <- item
          s <- x
          return (c : s)
    in do
    s1 <- start
    s2 <- x
    return (s1 ++ s2)
