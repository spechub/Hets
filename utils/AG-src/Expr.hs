{- UU_AG
 - Copyright:  S. Doaitse Swierstra, Arthur I. Baars and Andres Loeh
               Department of Computer Science
               Utrecht University
               P.O. Box 80.089
               3508 TB UTRECHT
               the Netherlands
               {swierstra,arthurb,andres}@cs.uu.nl -}
module Expr where
import TokenDef
import UU_BinaryTrees
import List
import Char
import Maybe

data HsToken = AGVar String String !Pos
            | HsToken String !Pos
            | CharToken String !Pos
            | StrToken String !Pos
            | Err String !Pos
         deriving Show
getPos t = case t of
        AGVar     _ _ p -> p
        HsToken   _   p -> p
        CharToken _   p -> p
        StrToken  _   p -> p
        Err       _   p -> p


lexToken :: Pos -> String -> (Pos,String,Maybe HsToken)
lexToken =  scanToken keywordstxt keywordsops specialchars opchars
  where keywordstxt   =  []
        keywordsops   =  [".","=", ":=", ":","|","@"]
        specialchars  =  ";()[],_{}`"
        opchars       =  "!#$%&*+./<=>?@\\^|-~:"

isAGesc c = c == '@'

mkToken  val pos = Just (HsToken val pos)
agVar    f a pos = Just (AGVar f a pos)
charToken  val pos = Just (CharToken val pos)
strToken   val pos = Just (StrToken val pos)
errToken msg pos = Just (Err     msg pos)

scanToken :: [String] -> [String] -> String -> String -> Pos -> String -> (Pos,String,Maybe HsToken)
scanToken keywordstxt keywordsops specchars opchars  pos input
  = doScan pos input

 where
   locatein :: Ord a => [a] -> a -> Bool
   locatein es = isJust . btLocateIn compare (tab2tree (sort es))
   iskw     = locatein keywordstxt
   isop     = locatein keywordsops
   isSymbol = locatein specchars
   isOpsym  = locatein opchars

   isIdStart c = isLower c || c == '_'

   isIdChar c =  isAlphaNum c
              || c == '\''
              || c == '_'

   scanIdent p s = let (name,rest) = span isIdChar s
                   in (name,advc (length name) p,rest)

   doScan p [] = (p,[],Nothing)
   doScan p (c:s)        | isSpace c = let (sp,next) = span isSpace s
                                       in  doScan (foldl (flip updPos)  p (c:sp)) next

   doScan p (c:d:s)  | isAGesc c && isIdStart d =
                                 let (fld,p2,rest) = scanIdent (advc 2 p) s
                                     field = d:fld
                                 in case rest of
                                      ('.':r:rs) -> if isIdStart r
                                                       then let (at,p3,rest2) = scanIdent (advc 2 p2) rs
                                                                attr = r : at
                                                            in (p3,rest2,agVar field attr p)
                                                       else (p2,rest,agVar field "" p)

                                      _
                                               -> (p2,rest,agVar field "" p)
   doScan p ('-':'-':s)  = doScan p (dropWhile (/= '\n') s)
   doScan p ('{':'-':s)  = lexNest doScan (advc 2 p) s
   doScan p ('"':ss)
     = let (s,swidth,rest) = scanString ss
       in if null rest || head rest /= '"'
             then (advc swidth p, rest, errToken "Unterminated string literal" p)
             else (advc (swidth+2) p,tail rest,strToken s p)

   doScan p ('\'':ss)
     = let (mc,cwidth,rest) = scanChar ss
       in case mc of
            Nothing -> (advc cwidth p, rest,errToken "Error in character literal" p)
            Just c  -> if null rest || head rest /= '\''
                          then (advc (cwidth+1) p,rest,errToken "Unterminated character literal" p )
                          else (advc (cwidth+2) p, tail rest,charToken  [c] p)
   doScan p cs@(c:s)
     | isSymbol c = (advc 1 p, s,mkToken [c] p)

     | isIdStart c || isUpper c
         = let (name', p', s')    = scanIdent (advc 1 p) s
               name               = c:name'
               tok                = if iskw name
                                    then mkToken name p               -- keyword
                                    else if null name' && isSymbol c
                                    then mkToken [c] p                -- '_'
                                    else mkToken name p               -- varid / conid
           in (p',s',tok)
     | isOpsym c = let (name, s') = span isOpsym cs
                       tok | isop name = mkToken name p
                           | otherwise = mkToken name p
                   in (foldl (flip updPos)  p name, s',tok)
     | isDigit c = let (base,digs,width,s') = getNumber cs
                       number = case base of
                          8  -> "0o"++digs
                          10 -> digs
                          16 -> "0x"++digs
                   in  (advc width p, s', mkToken number p)
     | otherwise = (updPos  c p, s,errToken ("Unexpected character " ++ show c) p)

lexNest cont pos inp = lexNest' cont pos inp
 where lexNest' c p ('-':'}':s) = c (advc 2 p) s
       lexNest' c p ('{':'-':s) = lexNest' (lexNest' c) (advc 2 p) s
       lexNest' c p (x:s)       = lexNest' c (updPos  x p) s
       lexNest' _ p []          = (p,[],errToken "Unterminated nested comment" pos)

scanString []            = ("",0,[])
scanString ('\\':'&':xs) = let (str,w,r) = scanString xs
                           in (str,w+2,r)
scanString ('\'':xs)     = let (str,w,r) = scanString xs
                           in ('\'': str,w+1,r)
scanString xs = let (ch,cw,cr) = getchar xs
                    (str,w,r)  = scanString cr
                    str' = maybe "" (:str) ch
                in maybe ("",0,xs) (\c -> (c:str,cw+w,r)) ch

scanChar ('"' :xs) = (Just '"',1,xs)
scanChar xs        = getchar xs

getchar []          = (Nothing,0,[])
getchar s@('\n':_ ) = (Nothing,0,s )
getchar s@('\t':_ ) = (Nothing,0,s)
getchar s@('\'':_ ) = (Nothing,0,s)
getchar s@('"' :_ ) = (Nothing,0,s)
getchar   ('\\':xs) = let (c,l,r) = getEscChar xs
                      in (c,l+1,r)
getchar (x:xs)      = (Just x,1,xs)

getEscChar [] = (Nothing,0,[])
getEscChar s@(x:xs) | isDigit x = let (base,n,len,rest) = getNumber s
                                      val = readn base  n
                                  in  if val >= 0 && val <= 255
                                         then (Just (chr val),len, rest)
                                         else (Nothing,1,rest)
                    | otherwise = case x `lookup` cntrChars of
                                 Nothing -> (Nothing,0,s)
                                 Just c  -> (Just c,1,xs)
  where cntrChars = [('a','\a'),('b','\b'),('f','\f'),('n','\n'),('r','\r'),('t','\t')
                    ,('v','\v'),('\\','\\'),('"','\"'),('\'','\'')]

readn base n = foldl (\r x  -> value x + base * r) 0 n

getNumber cs@(c:s)
  | c /= '0'               = num10
  | null s                 = const0
  | hs == 'x' || hs == 'X' = num16
  | hs == 'o' || hs == 'O' = num8
  | otherwise              = num10
  where (hs:ts) = s
        const0 = (10, "0",1,s)
        num10  = let (n,r) = span isDigit cs
                 in (10,n,length n,r)
        num16   = readNum isHexaDigit  ts 16
        num8    = readNum isOctalDigit ts 8
        readNum p ts tk
          = let nrs@(n,rs) = span p ts
            in  if null n then const0
                          else (tk         , n, 2+length n,rs)

isHexaDigit  d = isDigit d || (d >= 'A' && d <= 'F') || (d >= 'a' && d <= 'f')
isOctalDigit d = d >= '0' && d <= '7'

value c | isDigit c = ord c - ord '0'
        | isUpper c = ord c - ord 'A' + 10
        | isLower c = ord c - ord 'a' + 10

showTokens ts = showTokens' tks
 where showTokens' [] = []
       showTokens' xs = let (t,rest) = getLine xs
                        in showLine  t ++ if null rest
                                          then ""
                                          else "\n" ++ showTokens' rest
       tks = map (\t -> let p = getPos t
                        in(line p,(column p,showToken t))
                 ) ts
       getLine []         = ([],[])
       getLine ((l,t):xs) = let (txs,rest) = span ( (l==).fst) xs
                            in (t:map snd txs,rest)
       showLine ts = let f (ct,t) r = \c -> spaces (ct-c) ++ t ++ r (length t+ct)
                         spaces x | x < 0 = ""
                                  | otherwise = replicate x ' '
                     in foldr f (const "") ts 1


showToken t = case t of
    AGVar     f a _ -> let res | f=="loc"  = a
                               | null a    = f
                               | otherwise = f ++ ('_' : a)
                       in '_' : res
    HsToken   s   _ -> s
    CharToken s   _ -> if null s
                          then "''"
                          else showCharShort (head s)
    StrToken  s   _ -> showStrShort s
    Err       _   _ -> ""


showStrShort xs = "\"" ++ concatMap f xs ++ "\""
  where f '"' = "\\\""
        f x   = showCharShort' x

showCharShort '\'' = "'" ++ "\\'" ++ "'"
showCharShort c    = "'" ++ showCharShort' c ++ "'"

showCharShort' '\a'  = "\\a"
showCharShort' '\b'  = "\\b"
showCharShort' '\t'  = "\\t"
showCharShort' '\n'  = "\\n"
showCharShort' '\r'  = "\\r"
showCharShort' '\f'  = "\\f"
showCharShort' '\v'  = "\\v"
showCharShort' '\\'  = "\\\\"
showCharShort' x | isPrint x = [x]
                 | otherwise = '\\' : show (ord x)
