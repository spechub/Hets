
{- | 

    Module      :  $Header$
    Copyright   :  (c) Felix Reckers, Uni Bremen 2002-2004
    Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt
 
    Maintainer  :  hets@tzi.de
    Stability   :  provisional
    Portability :  portable

   very limited Haskell-Parser 
   based on DrIFT's Haskell-Parser (also very limited)

-}

module ParseFile where

import DataP
import CommandP
import ParseLib2
import Debug.Trace
import Data.List

type Import = String

-- result: (datas,imports)
parseInputFile :: FilePath -> String -> Either String ([String],[Import])
parseInputFile fp inp = case (ds,is) of
			(Left s, Left s2) -> Left (s++"\n"++s2)
			(Left s,Right _)  -> Left s
			(Right _, Left s) -> Left s
			(Right x, Right y) -> Right (x,y)
    where ds = case papply dat (0,0) ((0,0),inp) of
			[]           -> Left (fp++": No parse (data)")
			xs -> case filter (\ (_,(_,rs)) -> True) xs of
			      [] ->Left (fp++":"++
					 show (fst . snd $ (head xs))++
					 ": Ambigous parse (data); no end")
			      ((x,(_,_)):xs) -> 
				   traceERR xs $ Right $ transformD x
		--	_            -> Left (fp++": Ambigous parse (data)")
	  dat = parse . skipUntilOff $ (datadecl +++ newtypedecl)
	  traceERR xxs = trace (concatMap (\ (xx,(p,rs)) -> concat (transformD xx)++","++show p++","++rs++";") xxs)
	  is = case papply (parse header2) (0,-1) ((0,0),inp) of
	       []           -> Left (fp++": No parse (imports)")
	       [(x,_)] -> Right x
	       _            -> Left (fp++": Ambigous parse (imports)")

transformD :: [Data] -> [String]
transformD = map name 

header2 = 
    do symbol "module"
       m <- cap
       opt (do skipNest (symbol "(") (symbol ")")
               return [])
       symbol "where"
       many (fmap (\_->()) command +++ comment)
       is <- many imports2
       return (m:is)
    
imports2 = do symbol "import"
	      q <- fmap (\x->if null x then x else x++" ") 
		        (opt (symbol "qualified"))
	      i <- cap
	      asM <- opt (symbol "as" >> cap)
	      h <- opt (symbol "hiding")
	      hs <- opt $ importList (symbol "(") (symbol ")")
	      let asM' = if null asM then "" else (" as " ++ asM)
	      return (q++i++asM' ++ (if null h then "" else " " ++ h) ++ hs)

importList :: Parser String -> Parser String -> Parser String
importList start finish  = let 
    x = finish
	+++ do{l <- importList start finish; 
               s <- x; 
               return (l ++ s)} 
        +++ do{ c <- item; s <- x; return (c : s) } 
    in do{ s1 <- start; s2 <-x; return (s1 ++ s2)}
