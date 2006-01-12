{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, C. Maeder, Uni Bremen 2002-2006
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
import Proofs.StatusUtils

import ATC.AS_Library()
import ATC.DevGraph()
import ATC.GlobalAnnotations()
import ATC.Sml_cats

import Common.ATerm.Lib
import Common.ATerm.ReadWrite
import qualified Common.Lib.Map as Map
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

readShATermFile :: ShATermConvertible a => FilePath -> IO (Result a)
readShATermFile fp = do
    str <- readFile fp
    r <- return $ fromShATermString str
    case r of
      Result _ Nothing -> removeFile fp
      _ -> return ()
    return r

fromVersionedATT :: ShATermConvertible a => ATermTable -> Result a
fromVersionedATT att =
    case getATerm att of
    ShAAppl "hets" [versionnr,aterm] [] ->
        if hetsVersion == snd (fromShATermAux versionnr att)
        then Result [] (Just $ snd $ fromShATermAux aterm att)
        else Result [Diag Warning
                     "Wrong version number ... re-analyzing"
                     nullRange] Nothing
    _  ->  Result [Diag Warning
                   "Couldn't convert ShATerm back from ATermTable"
                   nullRange] Nothing

fromShATermString :: ShATermConvertible a => String -> Result a
fromShATermString str = if null str then
    Result [Diag Warning "got empty string from file" nullRange] Nothing
    else fromVersionedATT $ readATerm str

proofStatusFromShATerm :: FilePath -> IO (Result ProofStatus)
proofStatusFromShATerm = readShATermFile

readVerbose :: ShATermConvertible a => HetcatsOpts -> FilePath -> IO (Maybe a)
readVerbose opts file = do
    putIfVerbose opts 1 $ "Reading " ++ file
    Result ds mgc <- readShATermFile file
    showDiags opts ds
    return mgc

-- | create a file name without suffix from a library name
libNameToFile :: HetcatsOpts -> LIB_NAME -> FilePath
libNameToFile opts ln =
           case getLIB_ID ln of
                Indirect_link file _ ->
                  let path = libdir opts
                     -- add trailing "/" if necessary
                  in pathAndBase path file
                Direct_link _ _ -> error "libNameToFile"

readPrfFile :: HetcatsOpts -> LIB_NAME -> IO (LIB_NAME, ProofHistory)
readPrfFile opts ln = do
    let fname = libNameToFile opts ln 
        prfFile = fname ++ prfSuffix
    recent <- checkRecentEnv opts prfFile fname
    h <- if recent then 
          fmap (maybe emptyProofHistory id) $ readVerbose opts prfFile
       else return emptyProofHistory
    return (ln, h)
            
readPrfFiles :: HetcatsOpts -> LIB_NAME -> LibEnv -> IO ProofStatus
readPrfFiles opts ln le = do
    l <- mapM (readPrfFile opts) $ Map.keys le
    return (ln, le, Map.fromList l)
              
    

  
