
{- HetCATS/hetcats/ReadFn.hs
   $Id$
   Author: Klaus Lüttich
   Year:   2002

   "reading" ATerms, CASL, HetCASL files and parsing them into an
   appropiate data structure 
 
-}

module ReadFn where

import Options

import ATC.Sml_cats
import Syntax.AS_Library

read_LIB_DEFN :: HetcatsOpts -> IO LIB_DEFN
read_LIB_DEFN opt = read_sml_ATerm (infile opt)
{-
  putStrLn ("Reading " ++ fname)
  case intype opt of
    ATermIn _ -> do read_sml_ATerm (infile opt)
                              
    HetCASLIn -> do
     input <- readFile fname
     let ast = case runParser (library logicGraph) defaultLogic fname input of
                 Left err -> error (show err)
                 Right ast -> ast
-}
