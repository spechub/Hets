module UU_Pretty_ext ( -- Derived from single and multiple
                       (>^<), (>>^<<), (>#<), (>>#<<), wide_text
                     , vlist, hlist, hlist_sp, list_h1, hlist_h1
                     , (>|<<), (>-<<), (>>|<), (>>-<), pp_es
                       -- Displaying the result
                     , vdisp
                       -- Printing brackets
                     , pp_wrap, pp_quotes, pp_doubleQuotes
                     , pp_parens, pp_brackets, pp_braces
                       -- Printing structures
                     , hv, hv_sp, pp_block, pp_ite
                     , pp_list, pp_slist, pp_parens_list
                     ) where

{- Derived pretty-printing combinators. Version 2.0c
   Authors: S. Doaitse Swierstra and Pablo R. Azero
   Date: July, 1999
 -}

import UU_Pretty

infixr 3 >#<, >>#<<, >>|<, >|<<
infixr 2 >>-<, >-<<
infixr 1 >^<, >>^<<

-- -------------------------------------------------------------------
-- PP instances for often used simple data types ---------------------

instance PP Int where
  pp = text . show

instance PP Float where
  pp = text . show

-- -------------------------------------------------------------------
-- Derived from single and multiple ----------------------------------

(>^<), (>#<) :: (PP a, PP b) => a -> b -> PP_Doc
a  >^<  b  =  join  (a  >//<  b)
l  >#<  r  =  l >|< " " >|< r

pp_es string = if null string then empty else pp string

wide_text t s | ls > t    = text s
              | otherwise = text . (if t >= 0 then take t else take 0) $ (s ++ spaces)
  where ls     = length s
        spaces = repeat ' '

hlist, vlist, hlist_sp :: PP a => [a] -> PP_Doc
vlist    = foldr  (>-<) empty
hlist    = foldr  (>|<) empty
hlist_sp = foldr  (>#<) empty

list_h1 :: [PP_Doc] -> [PP_Doc]
list_h1   = map element_h1

hlist_h1  = foldr1 (>|<) . list_h1

(>>^<<), (>>#<<) :: PP_Exp -> PP_Exp -> PP_Exp
a >>^<< b  =  ejoin (a >>//<< b)
l >>#<< r  =  l >>|<< (" " >|<< r)

(>|<<), (>-<<) :: PP a => a -> PP_Exp -> PP_Exp
l >|<< r = c2e l >>|<< r
u >-<< l = c2e u >>-<< l

(>>|<), (>>-<) :: PP a => PP_Exp -> a -> PP_Exp
l >>|< r = l >>|<< c2e r
u >>-< l = u >>-<< c2e l

-- -------------------------------------------------------------------
-- Displaying the result ---------------------------------------------

vdisp :: Int -> [PP_Doc] -> ShowS
vdisp pw = foldr (\f fs -> disp f pw . ("\n"++) . fs) id

-- -------------------------------------------------------------------
-- Printing brackets -------------------------------------------------

pp_wrap :: PP a =>  a -> a -> PP_Doc -> PP_Doc
pp_wrap op cl p = op >|< (p >|< cl)

pp_quotes       = pp_wrap '`' '\''
pp_doubleQuotes = pp_wrap '"' '"'
pp_parens       = pp_wrap '(' ')'
pp_brackets     = pp_wrap '[' ']'
pp_braces       = pp_wrap '{' '}'

-- -------------------------------------------------------------------
-- Printing structures

-- hv: display a list of elements either horizontally or vertically,
-- 2 possible layouts: horizonal or vertical

hv :: PP a => [a] -> PP_Doc
hv = join . foldr onehv (empty >//< empty) . map pp
  where onehv p ps =      eelement_h1 par >>|<< fpar
                   >>//<< par >>-<< spar
                   >>$<   [p, ps]

-- hv_sp: same as hv but inserts spaces between the elements
-- 2 possible layouts: horizonal or vertical

hv_sp :: PP a => [a] -> PP_Doc
hv_sp l | null l    = empty
        | otherwise = lhv_sp . map pp $ l

lhv_sp fs@(f:fss) = hs >>^<< vs >>$< fs
  where (hs, vs)  = foldr paralg (par, par) fss
        paralg    = \_ (nhs,nvs) -> (eelement_h1 par >>#<< nhs, par >>-<< nvs)

-- pp_block: printing of block structures with open, close and separator
--           keywords
-- 2 possible layouts: horizonal or vertical

--pp_block :: String -> String -> String -> [PP_Doc] -> PP_Doc
pp_block okw ckw sep fs
  | null fs   = hv [open, close]
  | otherwise = join
      (      eelement_h1  par >>|<< fpar
      >>//<<              par >>-<< spar
      >>$< [open >|< (indent (startcolumn-lk) . head $ fs), hvopts]
      )
  where lk           =  length okw
        lsep         =  length sep
        startcolumn  =  (lk `max` lsep)
        hvopts       =  foldr hvoptalg dclose (tail fs)
        hvoptalg p ps
          = (       par  >>|<<  eelement_h1 par                   >>|<<  fpar
             >>//<< par  >>|<<  eindent (startcolumn - lsep) par  >>-<<  spar
            ) >>$< [pp_es sep, p, ps]
        dclose       =  eindent (startcolumn-lk) par >>//<< par >>$< [close]
        open         =  pp_es okw
        close        =  pp_es ckw

-- pp_ite: printing an if-then-else-fi statement
-- three possible layouts: horizonal, vertical or mixed

--pp_ite :: (PP a, PP b, PP c, PP d)
--       => a -> b -> c -> d -> PP_Doc -> PP_Doc -> PP_Doc -> PP_Doc
pp_ite kw_if kw_then kw_else kw_fi c t e
  = (     eelement_h1 ( par >>|<< par >>|<< par >>|<< par )
    >>^<< (     (     ( par >>|<< par >>^<< par >>-<< par )
                >>$<< [par, par >>-<< par]
                )
          >>-<< par
          )
    )  >>$< [ kw_if   >|< c
            , kw_then >|< t
            , kw_else >|< e
            , pp kw_fi
            ]

-- pp_slist: printing a list of elements in a "mini page", needs open, close and
--          separator keywords and a "mini page" width
-- one possible layout: depends on the page width given, when it reaches the end
-- of the page it continues on the next line
-- restrictions: only simple elements allowed (no pp_slists or flexible layouts
--               in the list [PP_Doc])

pp_slist :: Int -> String -> String -> String -> [PP_Doc] -> PP_Doc
pp_slist pw ol cl sep fl
  | null fl    =   hv [open, close]
  | otherwise  =   eelement_h1 (par >>|<< par) >>^<< (par >>-<< par)
               >>$< [nes, close]
  where nes    =   fillblock pw (open: ne: map (pp_es sep >|<) (tail fl))
        ne     =   (replicate (if ws == 0 then 0 else ws - 1) ' ')
               >|< (head fl)
        ws     =   length sep
        open   = pp_es ol
        close  = pp_es cl

-- pp_list: printing a list of elements in a "mini page", needs open, close and
--          separator keywords and a "mini page" width
-- one possible layout: depends on the page width given, when it reaches the end
-- of the page it continues on the next line

pp_list :: Int -> String -> String -> String -> [PP_Doc] -> PP_Doc
pp_list pw ol cl _   []     = pp_es (ol ++ cl)
pp_list pw ol cl sep (f:fs)
  = fillblock pw (pp ol: (pp f): (map (pp_es sep >|<) fs) ++ [ pp cl ])

-- pp_parens_list: idem pp_list, with parenthesis and comma separator

pp_parens_list :: Int -> [PP_Doc] -> PP_Doc
pp_parens_list mpw = pp_list mpw "(" ")" ", "