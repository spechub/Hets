{- |
Module      :  $Id$
Description :  modal logic extension of CASL
Copyright   :  (c) Christian Maeder and Uni Bremen 2006
License     :  GPLv2 or higher

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable (except Modal.Logic_Modal)

This folder contains the files for ModalCASL basic specs

ModalCASL is the modal logic extension of CASL.  See
/Heterogeneous specification and the heterogeneous tool set/
(<http://www.informatik.uni-bremen.de/~till/papers/habil.ps>), section 3.2.

The modules for ModalCASL largely are built on top of those for "CASL",
using the holes for future extensions that have been left in the
datatypes for CASL.

* "Modal.AS_Modal"     abstract syntax

* "Modal.Parse_AS"     parser

* "Modal.Print_AS"     pretty printing

* "Modal.ModalSign"    signatures

* "Modal.StatAna"      static analysis

* "Modal.ModalSystems" recognition of various systems such as S4, S5 etc.

* "Modal.ATC_Modal"    ATerm conversion

* "Modal.Logic_Modal"  the ModalCASL instance of type class 'Logic.Logic.Logic'

-}
module Modal where
