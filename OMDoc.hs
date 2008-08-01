{- |
Module      :  $Id$
Description :  basics of the common algebraic specification language
Copyright   :  (c) DFKI Bremen 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  e.digor@jacobs-university.de
Stability   :  provisional
Portability :  portable

The "OMDoc" folder contains the import and epxort functions from CASL to OMDoc
(see <http://www.omdoc.org>).

There is also an instance of "Logic.Logic" (the data for this is
assembled in "OMDoc.Logic_OMDoc"), but this is not complete yet.

The files "OMDocInput" and "OMDocOutput" are the main files responsible for the export and, respectively, import of the CASL files to OMDoc format. These are the central files, which are characterized by the following hierarchical absrtact layers:

1. CASL Abstract Syntax (which embeddes also the "CASL Text") is the lowest level, responsible for interpreting CASL concepts and syntax.

2. OMDoc Abstract Syntax ( defined in "OMDoc.OMDocInterface" ) is responsbile for representing the OMDoc's logic in an abstract way (with no XML tag deliminters). The communication channel between these 2 first layers is fortified by "OMDocDefs" (deals exclusively with OMDoc namings) and "HetsDefs" (deals with CASL data structures). This layer also communicates with "ATerms" layer via "ATerm"  and "ATC_OMDoc.der" (see "Logic_OMDoc" for details)

3. XML Abstract Syntax is a middle layer, which adds removes the OMDoc tag-elements, while preserving and sending the OMDoc contents to the lower layer (via "OMDoc.OMDocXML" which is responsible for XML conversion for OMDoc model (in out)).

4. OMDoc XML is the top layer, which takes care of the final OMDoc input or output files. It parses the OMDoc documents via an XML handler (see "OMDoc.XmlHandling" and HXT package for details).

The "OMDoc" folder also contains some additional files, which are as well used in the transformation:
"OMDoc.Container" and "OMDoc.Util" - utility functions
"OMDoc.HetsInterface.hspp"  - is a Test function
"OMDoc.KeyDebug" - used in debugging

The "Basic" subdirectory contains the CASL's basic transformation in OMDoc format.

-}

module OMDoc where
