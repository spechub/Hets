{- | The folder Syntax contains abstract syntax, parsing and printing
for heterogeneous structured and architectural specifications and
specification libraries.  Parsing is based on 
<http://www.cs.uu.nl/people/daan/parsec.html>,
pretty printing on "Common.Lib.Pretty".
Some modules deal with global annotations (see "Common.AS_Annotation").

/Abstract syntax/

"Syntax.AS_Structured"  
"Syntax.AS_Architecture"        
"Syntax.AS_Library"     

/Global annotations/

"Syntax.GlobalLibraryAnnotations"       
"Syntax.Print_HetCASL"  

/Parsing/

"Syntax.Parse_AS_Structured"    
"Syntax.Parse_AS_Architecture"  
"Syntax.Parse_AS_Library"       

/Pretty printing/
        
"Syntax.Print_AS_Structured"
"Syntax.Print_AS_Architecture"  
"Syntax.Print_AS_Library"

/LaTeX pretty printing/

"Syntax.LaTeX_AS_Structured"
"Syntax.LaTeX_AS_Architecture"  
"Syntax.LaTeX_AS_Library"       


-}
module Syntax.ADoc where
