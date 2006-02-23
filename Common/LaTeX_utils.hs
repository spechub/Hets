{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luettich@tzi.de
Stability   :  provisional
Portability :  portable

Useful functions for latex printing
-}

module Common.LaTeX_utils
    ( sp_braces_latex2
    , parens_latex
    , brackets_latex
    , fsep_latex
    , listSep_latex          -- then, and
    , startTab_latex
    , endTab_latex
    , view_hspace            -- structured specs

    , (<~>)
    , (<\+>)

    , hc_sty_hetcasl_keyword -- spec, view, from, then (4)
    , hc_sty_casl_keyword    -- sort, op, pred, type (5)
    , hc_sty_plain_keyword
    , hc_sty_axiom           -- all symbols
    , hc_sty_id              -- assoc, comm, when, else, as, qual-ops, ...
    , hc_sty_structid        -- small-caps for URL and PATH
    , hc_sty_comment         -- only for Annotations, HasCASL comments

    , simple_id_latex        -- hc_sty_structid . tokStr
    , simple_id_indexed_latex -- with index

    , comma_latex
    , semi_latex
    , space_latex
    , equals_latex
    , less_latex
    , colon_latex
    , dot_latex
    , bullet_latex
    , mapsto_latex
    , rightArrow
    , pfun_latex
    , cfun_latex
    , pcfun_latex
    , exequal_latex
    , forall_latex
    , exists_latex
    , unique_latex

    , casl_axiom_latex     -- for printDisplayToken_latex
    , casl_normal_latex

    , semiT_latex
    , commaT_latex
    , crossT_latex
    , barT_latex

    , setTab_latex
    , tabbed_nest_latex
    , set_tabbed_nest_latex  -- with setTab_latex
    , parens_tab_latex       -- parens_latex.set_tabbed_nest_latex
    )
    where

import Common.Id
import Common.Keywords
import Common.GlobalAnnotations
import Common.Lib.Pretty
import Common.PrintLaTeX

import Common.LaTeX_funs hiding (startAnno,endAnno)

listSep_latex :: PrintLaTeX a => Doc -> GlobalAnnos -> [a] -> Doc
listSep_latex p ga = fsep_latex . punctuate p . map (printLatex0 ga)

-- | LaTeX variants
commaT_latex, semiT_latex, crossT_latex
    :: PrintLaTeX a => GlobalAnnos -> [a] -> Doc
commaT_latex = listSep_latex comma_latex
semiT_latex = listSep_latex semi_latex
crossT_latex = listSep_latex (space_latex <> hc_sty_axiom "\\times")

barT_latex :: PrintLaTeX a => GlobalAnnos -> [a] -> Doc
barT_latex ga l = case l of
    [] -> empty
    h : t -> sep_latex
           (hc_sty_axiom defnS <> setTab_latex<~>
              printLatex0 ga h <> casl_normal_latex "~" :
            map (\x -> tabbed_nest_latex (latex_macro
                                                 "\\hspace*{-0.84mm}"<> ---}
                                           casl_normal_latex "\\textbar")
                            <~> printLatex0 ga x <> casl_normal_latex "~") t)

equals_latex, less_latex, colon_latex, dot_latex,
    bullet_latex, mapsto_latex, rightArrow, pfun_latex, cfun_latex,
    pcfun_latex, exequal_latex :: Doc
equals_latex = hc_sty_axiom "="
less_latex   = hc_sty_axiom "<"
colon_latex  = casl_normal_latex ":"
dot_latex    = casl_normal_latex "."
bullet_latex = hc_sty_axiom "\\bullet"
mapsto_latex = hc_sty_axiom "\\mapsto"
rightArrow   = hc_sty_axiom "\\rightarrow"
pfun_latex   = hc_sty_axiom "\\rightarrow?"
cfun_latex   = hc_sty_axiom "\\stackrel{c}{\\rightarrow}"
pcfun_latex  = hc_sty_axiom "\\stackrel{c}{\\rightarrow}?"
exequal_latex = sp_text (axiom_width "=") "\\Ax{\\stackrel{e}{=}}"

forall_latex, exists_latex, unique_latex :: Doc
forall_latex = hc_sty_axiom "\\forall"
exists_latex = hc_sty_axiom "\\exists"
unique_latex = hc_sty_axiom "\\exists!"

sp_braces_latex2 :: Doc -> Doc
sp_braces_latex2 d =
    fcat [casl_normal_latex "\\{"<>d,
          casl_normal_latex "\\}"]

-- | a horizontal space as wide as the keyword view followed by a space
view_hspace :: Doc
view_hspace = hspace_latex $ pt_length
                  (keyword_width "view" + normal_width "~")

-- | print a simple id in SmallCaps
simple_id_latex :: SIMPLE_ID -> Doc
simple_id_latex = hc_sty_structid . tokStr

simple_id_indexed_latex :: SIMPLE_ID -> Doc
simple_id_indexed_latex = hc_sty_structid_indexed . tokStr

parens_tab_latex :: Doc -> Doc
parens_tab_latex = parens_latex

-- |
-- constant document to start indentation by a LaTeX tab stop
startTab_latex :: Doc
startTab_latex = latex_macro startTab

-- |
-- constant document to end indentation by a LaTeX tab stop
endTab_latex :: Doc
endTab_latex = latex_macro endTab

-- |
-- constant document to set a LaTeX tab stop at this position
setTab_latex :: Doc
setTab_latex = latex_macro setTab

-- |
-- function for nice indentation
tabbed_nest_latex :: Doc -> Doc
tabbed_nest_latex d = startTab_latex <> d <> endTab_latex

-- |
-- function for nice indentation together with starting
set_tabbed_nest_latex :: Doc -> Doc
set_tabbed_nest_latex d = setTab_latex <> tabbed_nest_latex d
