{- | ModalCASL is the modal logic extension of CASL.  See 
/Heterogeneous
specification and the heterogeneous tool set/
(<http://www.tzi.de/~till/papers/habil.ps>), section 3.2.

The modules for ModalCASL largely are built on top of those for "CASL",
using the holes for future extensions that have been left in the
datatypes for CASL.

"Modal.AS_Modal" abstract syntax
        
"Modal.Parse_AS" parser

"Modal.Print_AS" , "Modal.LaTeX_Modal"  pretty printing

"Modal.ModalSign" signatures

"Modal.StatAna" static analysis

"Modal.ModalSystems" recognition of various systems such as S4, S5 etc.

"Modal.ATC_Modal" ATerm conversion

"Modal.Logic_Modal" the ModalCASL instance of type class 'Logic.Logic.Logic'

-}

module Modal where
