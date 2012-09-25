{- |
Module      :  $Header$
Description :  folder description
Copyright   :  (c) Christian Maeder and Uni Bremen 2006
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

The folder Syntax contains abstract syntax, parsing and printing
for heterogeneous structured and architectural specifications and
specification libraries.  Parsing is based on
<http://www.cs.uu.nl/people/daan/parsec.html>,
pretty printing on "Common.Doc".

/Abstract syntax/

"Syntax.AS_Structured"
"Syntax.AS_Architecture"
"Syntax.AS_Library"

/Parsing/

"Syntax.Parse_AS_Structured"
"Syntax.Parse_AS_Architecture"
"Syntax.Parse_AS_Library"

/Pretty printing/

"Syntax.Print_AS_Structured"
"Syntax.Print_AS_Architecture"
"Syntax.Print_AS_Library"
-}
module Syntax where
