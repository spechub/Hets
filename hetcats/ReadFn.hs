
{- HetCATS/hetcats/ReadFn.hs
   $Id$
   Author: Klaus Lüttich
   Year:   2002

   "reading" ATerms, CASL, HetCASL files and parsing them into an
   appropiate data structure 
 
-}

module ReadFn where

import Options

import ATC_sml_cats
import Syntax.AS_Library

read_LIB_DEFN :: HetcatsOpts -> IO LIB_DEFN
read_LIB_DEFN opt = read_sml_ATerm (infile opt)


