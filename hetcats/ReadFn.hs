{-| 
   
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  non-portable(DevGraph)

   reading ATerms, CASL, HetCASL files and parsing them into an
   appropiate data structure 
 
-}

module ReadFn where

import Logic.Logic
import Logic.Grothendieck
import Comorphisms.LogicGraph
import Syntax.AS_Library
import Syntax.Parse_AS_Library
import Static.DevGraph

import ATC.AS_Library
import ATC.DevGraph
import ATC.Sml_cats

import Common.ATerm.Lib
import Common.AnnoState
import Common.Id
import Common.Result
import Common.Lib.Parsec

import Options
import Version

read_LIB_DEFN_M :: Monad m => AnyLogic -> FilePath -> String -> m LIB_DEFN
read_LIB_DEFN_M defl file input = 
    if null input then fail ("empty input file: " ++ file) else
    case runParser (library (defl, logicGraph)) emptyAnnos
	 file input of
	 Left err  -> fail (showErr err)
	 Right ast -> return ast

read_LIB_DEFN_M_WI :: Monad m => AnyLogic -> FilePath -> String -> m (String, LIB_DEFN)
read_LIB_DEFN_M_WI defl file input  =
       case runParser (library (defl, logicGraph)) emptyAnnos
	    file input of
	    Left err  -> return (showErr err, Lib_defn (Lib_id (Indirect_link "" [])) [] [] [])  
	    Right ast -> return ("",ast)


read_LIB_DEFN :: HetcatsOpts -> FilePath -> IO LIB_DEFN
read_LIB_DEFN opt file = 
    do putIfVerbose opt 3 ("Reading file: " ++ file)
       input <- readFile file
       defl <- lookupLogic "logic from command line: " 
		   (defLogic opt) logicGraph	 	
       ld <- case guess file (intype opt) of
         ATermIn _  -> read_sml_ATerm file
         ASTreeIn _ -> error "Abstract Syntax Trees aren't implemented yet"
         CASLIn     -> do
            read_LIB_DEFN_M defl file input
         HetCASLIn  -> do
            read_LIB_DEFN_M defl file input
         _         -> error "Unknown InType wanted in read_LIB_DEFN"
       return ld

readLIB_DEFN_from_file :: FilePath -> IO (Result LIB_DEFN)
readLIB_DEFN_from_file = readShATermFile

readShATermFile :: (ATermConvertible a) => FilePath -> IO (Result a)
readShATermFile fp = do str <- readFile fp
                        return (fromShATermString str) 
                        
fromShATermString :: (ATermConvertible a) => String -> Result a
fromShATermString str = if null str then Result [dia3] Nothing else
    case getATerm att of
    ShAAppl "hets" [versionnr,aterm] [] -> 
        if hetcats_version == (fromShATerm $ getATermByIndex1 versionnr att)
	then Result [] (Just $ fromShATerm $ getATermByIndex1 aterm att)
        else Result [dia1] Nothing
    _                                   ->  Result [dia2] Nothing
    where att  = readATerm str
	  dia1 = Diag Warning "Wrong version number ... re-analyzing" nullPos
	  dia2 = Diag Warning "Couldn't convert ShATerm back from file" 
		      nullPos
          dia3 = Diag Warning "got empty string from file" nullPos

globalContextfromShATerm :: FilePath -> IO (Result GlobalContext)
globalContextfromShATerm = readShATermFile
