{- | CspCASL combines the process algebra CSP with CASL;
CASL data elements serve as process alphabet letters.

The modules for CspCASL are built on top of those for "CASL",
using the holes for future extensions that have been left in the
datatypes for CASL.

"CspCASL.AS_CSP_CASL"   abstract syntax

"CspCASL.CCKeywords", "CspCASL.CCLexer",  "CspCASL.CCToken", "CspCASL.Parse_hugo" preliminary parser

"CspCASL.LaTeX_AS_CSP_CASL", "CspCASL.Print_AS_CSP_CASL" pretty printing

"CspCASL.SignCSP" signatures

"CspCASL.StatAnaCSP" static analysis.

"CspCASL.ATC_CspCASL" ATerm conversion

"CspCASL.Logic_CspCASL" the CspCASL instance of 'Logic.Logic.Logic'

See "Tool Support for CSP-CASL", MPhil thesis by Andy Gimblett, 2008.
http://www.cs.swan.ac.uk/~csandy/mphil/

-}
module CspCASL where
