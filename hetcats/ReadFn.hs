
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
import ATC.AS_Library

--import Syntax.Parse_AS_Structured
import Syntax.Parse_AS_Library
import Common.Lib.Parsec
import Comorphisms.LogicGraph
import Common.ATerm.Lib
import Common.AnnoState
import Common.Id
import Common.Result
import Version

import Static.DevGraph
import ATC.DevGraph

read_LIB_DEFN :: HetcatsOpts -> FilePath -> IO LIB_DEFN
read_LIB_DEFN opt file = 
    do putIfVerbose opt 3 ("Reading file: " ++ file)
       ld <- case guess file (intype opt) of
         ATermIn _  -> read_sml_ATerm file
         ASTreeIn _ -> error "Abstract Syntax Trees aren't implemented yet"
         CASLIn     -> do
            input <- readFile file
            case runParser (library (defaultLogic, logicGraph)) emptyAnnos
		 file input of
               Left err  -> error (show err)
               Right ast -> return ast
         HetCASLIn  -> do
            input <- readFile file
            case runParser (library (defaultLogic, logicGraph)) emptyAnnos
		 file input of
               Left err  -> error (show err)
               Right ast -> return ast
               _         -> error "Unknown InType wanted in read_LIB_DEFN"
       return ld

readLIB_DEFN_from_file :: FilePath -> IO (Result LIB_DEFN)
readLIB_DEFN_from_file = readShATermFile

readShATermFile :: (ATermConvertible a) => FilePath -> IO (Result a)
readShATermFile fp = do str <- readFile fp
                        return (fromShATermString str) 
                        
fromShATermString :: (ATermConvertible a) => String -> Result a
fromShATermString str = 
    case getATerm att of
    ShAAppl "hets" [versionnr,aterm] [] -> 
        if hetcats_version == (fromShATerm $ getATermByIndex1 versionnr att)
	then Result [] (Just $ fromShATerm $ getATermByIndex1 aterm att)
        else Result [dia1] Nothing
    _                                   ->  Result [dia2] Nothing
    where att  = readATerm str
	  dia1 = Diag Warning "Wrong version number!" nullPos
	  dia2 = Diag Warning "Couldn't convert ShATerm back from file" 
		      nullPos

globalContextfromShATerm :: FilePath -> IO (Result GlobalContext)
globalContextfromShATerm = readShATermFile
{-do str <- readFile fp
                                 att <- return $ readATerm str
                                 case getATerm att of
                                  ShAAppl "globalcontext" [versionnr,aterm] [] -> if hetcats_version == (fromShATerm $ getATermByIndex1 versionnr att)
					                  			   then return $ fromShATerm $ getATermByIndex1 aterm att
                                                                                   else return $ error "Wrong version number!"
                                  _                                            -> return $ error "Couldn't convert ShATerm back from file"-}









