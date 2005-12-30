{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luettich@tzi.de
Stability   :  provisional
Portability :  non-portable(DevGraph)

reading ATerms, CASL, HetCASL files and parsing them into an
   appropriate data structure
-}

module Driver.ReadFn where

import Logic.Logic
import Logic.Grothendieck
import Syntax.AS_Library
import Syntax.Parse_AS_Library
import Static.DevGraph

import ATC.AS_Library()
import ATC.DevGraph()
import ATC.GlobalAnnotations()
import ATC.Sml_cats

import Common.ATerm.Lib
import Common.ATerm.ReadWrite
import Common.AnnoState
import Common.Id
import Common.Result
import Text.ParserCombinators.Parsec

import Driver.Options
import System.Directory

read_LIB_DEFN_M :: Monad m => LogicGraph -> AnyLogic -> HetcatsOpts
                -> FilePath -> String -> m LIB_DEFN
read_LIB_DEFN_M lgraph defl opts file input =
    if null input then fail ("empty input file: " ++ file) else
    case intype opts of
    ATermIn _  -> return $ from_sml_ATermString input
    ASTreeIn _ -> fail "Abstract Syntax Trees aren't implemented yet"
    _ -> case runParser (library (defl, lgraph)) (emptyAnnos defl)
              file input of
         Left err  -> fail (showErr err)
         Right ast -> return ast

readLIB_DEFN_from_file :: FilePath -> IO (Result LIB_DEFN)
readLIB_DEFN_from_file = readShATermFile

readShATermFile :: (ShATermConvertible a) => FilePath -> IO (Result a)
readShATermFile fp = do
    str <- readFile fp
    r <- return $ fromShATermString str
    case r of
      Result _ Nothing -> removeFile fp
      _ -> return ()
    return r

fromVersionedATT :: (ShATermConvertible a) => ATermTable -> Result a
fromVersionedATT att =
    case getATerm att of
    ShAAppl "hets" [versionnr,aterm] [] ->
        if hetsVersion == fromShATerm (getATermByIndex1 versionnr att)
        then Result [] (Just $ fromShATerm $ getATermByIndex1 aterm att)
        else Result [Diag Warning
                     "Wrong version number ... re-analyzing"
                     nullRange] Nothing
    _  ->  Result [Diag Warning
                   "Couldn't convert ShATerm back from ATermTable"
                   nullRange] Nothing

fromShATermString :: (ShATermConvertible a) => String -> Result a
fromShATermString str = if null str then
    Result [Diag Warning "got empty string from file" nullRange] Nothing
    else fromVersionedATT $ readATerm str

globalContextfromShATerm :: FilePath -> IO (Result GlobalContext)
globalContextfromShATerm = readShATermFile

proofStatusFromShATerm :: FilePath -> IO (Result ProofStatus)
proofStatusFromShATerm = readShATermFile
