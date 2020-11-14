{-# LANGUAGE ViewPatterns #-}
module PLpatt.StaticAnaPLpatt
    where

import qualified PLpatt.AS_BASIC_PLpatt as As
import qualified PLpatt.Sign as Sign
import PLpatt.Tools
import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.Result
import Common.ExtSign
import Common.Id
import Data.Maybe
import qualified Data.HashSet as Set
import System.IO.Unsafe (unsafePerformIO)
import qualified MMT.XMLtoPT as XML
import qualified MMT.Tools as PT
import System.IO.Temp
import System.IO
import qualified MMT.Hets2mmt as MMT
import Data.List
import qualified Data.HashMap.Strict as Map
import System.Directory (removeFile)
import Common.Utils (getEnvDef)

import Debug.Trace

basicAna :: (As.Basic_spec, Sign.Sigs, GlobalAnnos) ->
                Result (
                  As.Basic_spec,
                  ExtSign Sign.Sigs As.Symb,
                  [Named As.Bool']
                )
basicAna (bs, Sign.Sigs sg, ann) = let
                                 def_namespace = "http://cds.omdoc.org/hets-test"
                                 namespace = case Map.lookup "namespace:"
                                                   (prefix_map ann) of
                                    Just x -> show x
                                    Nothing -> def_namespace
                                 (newsg, symbs) = mmtAna namespace bs
                                 (sens, sgdcl) = getSens $ Sign.Sigs newsg
                                 sgn = ExtSign (Sign.Sigs (sgdcl ++ sg))
                                               symbs
                                 in
                                 return (bs, sgn, sens)

-- logic id is inserted by MMT
lid :: String
lid = "PLpatt"

hetslib :: String
hetslib = unsafePerformIO $ getEnvDef "HETS_LIB" ""

mmtAna :: String -> As.Basic_spec -> ([As.Decl], Set.HashSet As.Symb)
mmtAna namespace (As.Basic_spec bs) = let
                          tdecls = unsafePerformIO $
                                  getDecls namespace bs
                          decls = map decl2decl tdecls
                          symbs = newSymbs $ map (fromJust . maybeResult) tdecls
                          in
                          (map (fromJust . maybeResult) decls, symbs)

-- separators used by MMT: group s, unit s, record s
gs :: String
gs = "\29"

us :: String
us = "\31"

rs :: String
rs = "\30"

-- compile lines into a temp file
compileMMTsrc :: String -> [String] -> IO FilePath
compileMMTsrc ns rest = do let cont = "namespace " ++ ns ++ gs ++ "\n" ++
                                      "theory " ++ lid ++ "spec : " ++
                                      "?" ++ lid ++
                                      " = \n" ++ "\n" ++
                                      unlines (map (++ rs) rest) ++
                                      "\n" ++ gs
                           (fpath, fhand) <- openTempFile "MMTtmp"
                                                          "input.mmt"
                           hPutStr fhand cont
                           hClose fhand
                           return fpath

-- sort declarations
arrangeFileSrc :: String -> [String] -> [String]
arrangeFileSrc (stripPrefix "namespace" -> Just uri) ls =
  ("namespace" ++ uri) : ls
arrangeFileSrc s ls = ls ++ [s]

-- grab namespace uri
getNamespace :: String -> Maybe String
getNamespace (stripPrefix "namespace " -> Just uri) = Just uri
getNamespace _ = Nothing

getDecls :: String -> [String] -> IO [Result PT.Decl]
getDecls ns sl = do
           fp <- compileMMTsrc ns $ filter (/= "") sl
           MMT.callSpec fp
           XML.parse $ hetslib ++ "MMT/xml/" ++ lid ++ "spec.xml"

{- helper method that translates
   parse tree declarations to logic declarations -}
decl2decl :: Result PT.Decl -> Result As.Decl
decl2decl rsptdcl = let dcl = maybeResult rsptdcl
                in
                case dcl of
                Just mbds -> case decl_from_pt mbds of
                              (Just ds) -> Result [] (Just ds )
                              Nothing -> fatal_error
                                          "failed to parse parse-tree"
                                          nullRange
                Nothing -> fatal_error "Result of parse tree failure"
                                        nullRange

isSen :: As.Decl -> Bool
isSen (As.Dot_decl _) = True
isSen _ = False

splitSen :: [As.Decl] -> ([As.Decl], [As.Decl])
splitSen = partition isSen

decl2sen :: As.Decl -> Maybe (Named As.Bool')
decl2sen (As.Dot_decl (As.Dot name f)) = Just $ makeNamed name f
decl2sen _ = Nothing

getSens :: Sign.Sigs -> ([Named As.Bool'], [As.Decl])
getSens (Sign.Sigs decls) = let
                            (sendcl, sgsdcl) = splitSen decls
                            sens = map (fromJust . decl2sen) sendcl
                            in
                            (sens, sgsdcl)

decl2symb :: PT.Decl -> As.Symb
decl2symb (PT.Decl _ iname _) = As.Symb iname

newSymbs :: [PT.Decl] -> Set.HashSet As.Symb
newSymbs dcls = let sls = map decl2symb dcls
                in foldr Set.insert Set.empty sls
