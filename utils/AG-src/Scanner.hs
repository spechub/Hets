{- UU_AG
 - Copyright:  S. Doaitse Swierstra, Arthur I. Baars and Andres Loeh
               Department of Computer Science
               Utrecht University
               P.O. Box 80.089
               3508 TB UTRECHT
               the Netherlands
               {swierstra,arthurb,andres}@cs.uu.nl -}
module Scanner where
import TokenDef

import UU_Parsing_Core
import UU_Parsing
import Maybe
import List
import Char

newtype Input sym = Input [(sym,(Pos, String))]
instance InputState Input where
 splitStateE (Input [])         = Right (Input [])
 splitStateE (Input ((s,_):xs)) = Left  (s,Input xs)

 splitState (Input ((s,_):xs)) = (s,Input xs)

 insertState s1  (Input [])             = Input [(s1,(noPos,[]))]
 insertState s1  (Input xs@((_,inp):_)) = Input ( (s1,inp) : xs)

 firstState (Input [])        = Nothing
 firstState (Input ((s,_):_)) = Just s


agScan = toScan scan


execScan scanner pos inp = Input (scanner pos inp)

toScan :: (a -> b -> Maybe (c,a,b)) -> a -> b -> [(c,(a,b))]
toScan scan p inp = toScan' p inp   where
     toScan' p xs = case scan p xs of
        Nothing         -> []
        Just (t,p2,xs2) -> let input = toScan' p2 xs2
                           in (t,(p,xs)) : input


scan :: Pos -> String -> Maybe (Token Char,Pos,String)
scan p []                        = Nothing
scan p ('-':'-':xs)              = let (com,rest) = span (/= '\n') xs
                                   in advc' (2+length com) p scan rest
scan p ('{':'-':xs)              = advc' 2 p (ncomment scan) xs
scan p ('{'    :xs)              = advc' 1 p codescrap xs
scan p (x:xs) | isSpace x        = updPos'  x p scan  xs
scan p xs = Just (scan' xs)
  where scan' ('.' :rs)          = (Dot         p, advc 1 p, rs)
        scan' ('@' :rs)          = (At          p, advc 1 p, rs)
        scan' (',' :rs)          = (Comma       p, advc 1 p, rs)
        scan' ('_' :rs)          = (UScore      p, advc 1 p, rs)
        scan' ('[' :rs)          = (OBrack      p, advc 1 p, rs)
        scan' (']' :rs)          = (CBrack      p, advc 1 p, rs)
        scan' ('(' :rs)          = (OParens     p, advc 1 p, rs)
        scan' (')' :rs)          = (CParens     p, advc 1 p, rs)
--        scan' ('{'    :rs)       = (OBrace      p, advc 1 p, rs)
--        scan' ('}'    :rs)       = (CBrace      p, advc 1 p, rs)

        scan' ('"' :rs)          = let isOk c = c /= '"' && c /= '\n'
                                       (str,rest) = span isOk rs
                                   in if null rest || head rest /= '"'
                                          then (TkError "unterminated string literal"   p
                                               , advc (1+length str) p,rest)
                                          else (StrLit str p, advc (2+length str) p, tail rest)

        scan' ('=' :rs)          = (Equals      p, advc 1 p, rs)
        scan' (':':'=':rs)       = (ColonEquals p, advc 1 p, rs)

        scan' (':' :rs)          = (Colon       p, advc 1 p, rs)
        scan' ('|' :rs)          = (Bar         p, advc 1 p, rs)

        scan' (x:rs) | isLower x = let (var,rest) = ident rs
                                       str        = (x:var)
                                       tok        = fromMaybe (Varid str) $ lookup str keywords
                                   in (tok p, advc (length var+1) p, rest)
                     | isUpper x = let (var,rest) = ident rs
                                       str        = (x:var)
                                       tok = fromMaybe (Conid str) $ lookup str keywords
                                   in (tok p, advc (length var+1) p,rest)
                     | otherwise = (TkError ("unexpected character " ++ show x) p, advc 1 p, rs)

ident = span isValid
 where isValid x = isAlphaNum x || x =='_' || x == '\''
keywords = [ ("DATA",DATA), ("EXT",EXT), ("ATTR",ATTR), ("SEM",SEM),("TYPE",TYPE)
           , ("USE",USE), ("loc",LOC), ("INCLUDE",INCLUDE)]

ncomment c p ('-':'}':xs) = advc' 2 p c  xs
ncomment c p ('{':'-':xs) = advc' 2 p (ncomment (ncomment c)) xs
ncomment c p (x:xs)       = updPos' x p (ncomment c)  xs
ncomment c p []           = Just (TkError "unterminated nested comment" p, p,[])

codescrap p xs = let (p2,xs2,sc) = codescrap' 1 p xs
                 in case xs2 of
                         ('}':rest) -> Just (Codescrap sc p,advc 1 p2,rest)
                         _          -> Just (TkError "unterminated codescrap" p,p2,xs2)


codescrap' d p [] = (p,[],[])
codescrap' d p ('{':'{':xs) = let (p2,xs2,sc) = advc' 2 p (codescrap' d) xs
                              in (p2,xs2,"{{"++sc)
codescrap' d p ('}':'}':xs) = let (p2,xs2,sc) = advc' 2 p (codescrap' d) xs
                              in (p2,xs2,"}}"++sc)
codescrap' d p ('{':xs)     = let (p2,xs2,sc) = advc' 1 p (codescrap' (d+1)) xs
                              in (p2,xs2,'{' : sc)
codescrap' d p ('}':xs)     | d == 1 = (p,'}':xs,[])
                            | otherwise = let (p2,xs2,sc) = advc' 1 p (codescrap' (d-1)) xs
                                          in (p2,xs2,'}' : sc)
codescrap' d p (x  :xs)     = let (p2,xs2,sc) = updPos' x p (codescrap' d) xs
                              in (p2,xs2,x:sc)
--Literate Mode
scanLit xs = (fs, foldr insNL (const "") codeLns 1)
  where insNL (n,line) rec = \n1 -> replicate (n-n1) '\n' ++ line ++ rec n
        (fs,codeLns,_) = getBlocks ([1..] `zip` lines xs)
        getBlocks [] = ([],[],[])
        getBlocks xs = let (files1,txt1,r1) = getBlock xs
                           (files2,txt2,r2) = getBlocks r1
                       in (files1++files2, txt1++txt2, r2)


        getBlock = getLines . dropWhile comment
        getLines [] = ([],[],[])
        getLines ((n,l):ls) | "\\begin{Code}" `isPrefixOf` l = let (lns,rest) = codelines ls
                                                               in ([],lns,rest)
                            | "\\IN{" `isPrefixOf` l        =
                                     let name = getName l
                                     in  ([name],[],ls)
                            | otherwise = getBlock ls
        comment = not . ("\\" `isPrefixOf`) .snd

codelines [] = error "Unterminated code block"
codelines ((n,l):ls) | "\\end{Code}" `isPrefixOf` l = ([],ls)
                     | otherwise                    = let (lns,r) = codelines ls
                                                      in ((n,l):lns,r)

getName l = case r of
   ('}':_) -> nm
   _       -> error $ "missing '}' in \\IN"
 where (nm,r) = span (/='}') (drop 4 l)