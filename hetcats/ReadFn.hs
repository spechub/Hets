
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

import Syntax.Parse_AS_Structured
import Common.Lib.Parsec
import Logic.LogicGraph

read_LIB_DEFN :: HetcatsOpts -> FilePath -> IO LIB_DEFN
read_LIB_DEFN opt file = 
    do putStrLn ("Reading " ++ file)
       ld <- case (guess (intype opt)) of
         ATermIn _  -> read_sml_ATerm file
         ASTreeIn _ -> error "Abstract Syntax Trees aren't implemented yet"
         CASLIn     -> do
            input <- readFile file
         case runParser (library logicGraph) defaultLogic file input of
            Left err  -> error (show err)
            Right ast -> return ast
         HetCASLIn  -> do
            input <- readFile file
         case runParser (library logicGraph) defaultLogic file input of
            Left err  -> error (show err)
            Right ast -> return ast
         _          -> error "Unknown InType wanted in read_LIB_DEFN"
       return ld
    where
    guess GuessIn = guessInType file
    guess itype   = itype

