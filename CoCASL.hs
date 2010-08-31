{- |
Module      :  $Id$
Description :  Co-algebraic CASL extension
Copyright   :  (c) Christian Maeder and Uni Bremen 2006
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable (except CoCASL.Logic_CoCASL)

This folder contains the files for CoCASL basic specs

CoCASL is the coalgebraic extension of CASL.  See /Till
Mossakowski, Lutz Schroeder, Markus Roggenbach, Horst
Reichel. Algebraic-co-algebraic specification in CoCASL. Journal of
Logic and Algebraic Programming. To appear./

The modules for CoCASL largely are built on top of those for "CASL",
using the holes for future extensions that have been left in the
datatypes for CASL.

Special proof tactics for the CoCASL encoding into Isabelle
are delivered in the CASL-lib folder <http://www.cofi.info/Libraries/>
of basic libraries.

* "CoCASL.AS_CoCASL"    abstract syntax of CoCASL specifications

* "CoCASL.ATC_CoCASL"   ATerm conversion

* "CoCASL.CoCASLSign"   CoCASL signatures

* "CoCASL.Logic_CoCASL" the CoCASL instance of type class 'Logic.Logic.Logic'

* "CoCASL.Parse_AS"     CoCASL parser

* "CoCASL.Print_AS"     CoCASL pretty printer

* "CoCASL.StatAna"      CoCASL static analysis

-}
module CoCASL where
