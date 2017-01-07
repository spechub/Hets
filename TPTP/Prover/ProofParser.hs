{- |
Module      :  ./TPTP/Prover/ProofParser.hs
Description :  Parses a TPTP proof.
Copyright   :  (c) Eugen Kuksa University of Magdeburg 2017
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Eugen Kuksa <kuksa@iks.cs.ovgu.de>
Stability   :  provisional
Portability :  non-portable (imports Logic)
-}

module TPTP.Prover.ProofParser ( axiomsFromProofObject
                               , filterProofLines
                               , findSZS
                               ) where

import TPTP.AS ( Annotated_formula
               , Formula_role (..)
               , Annotations (..)
               , Source (..)
               , External_source (..)
               , File_source (..)
               , formulaRole
               , annotations )
import TPTP.Parser (annotated_formula)
import TPTP.Pretty ()

import Common.DocUtils

import Data.List
import Data.List.Split (splitOn)
import Data.Maybe
import Text.ParserCombinators.Parsec

axiomsFromProofObject :: [String] -> ([String], [String])
axiomsFromProofObject =
  foldr addIfAxiom ([], []) . map parseFormulae . splitFormulae . unlines
  where
    splitFormulae :: String -> [String]
    splitFormulae = init . map (\ s -> s ++ ").\n") . splitOn ").\n"

    parseFormulae :: String -> Either String Annotated_formula
    parseFormulae text = case runParser annotated_formula () "" text of
      Right formula -> Right formula
      Left err -> Left ("Warning: unable to parse proof:\n" ++
                        "Formula in the proof: " ++ text ++ "\n" ++
                        "Error: " ++ show err ++ "\n")

    addIfAxiom :: Either String Annotated_formula
               -> ([String], [String]) -> ([String], [String])
    addIfAxiom formulaOrError (axiomNames, parserErrors) =
      case formulaOrError of
        Left err -> (axiomNames, err : parserErrors)
        Right formula -> (getAxiomName formula ++ axiomNames, parserErrors)

    getAxiomName :: Annotated_formula -> [String]
    getAxiomName formula = case (formulaRole formula, annotations formula) of
      (Axiom, (Annotations mAnnos)) -> case mAnnos of
        Just (Source_external (ExtSrc_file (File_source _ (Just fileInfo))),_) ->
          [show $ pretty fileInfo]
        _ -> []
      _ -> []

-- Find the SZS status line
findSZS :: [String] -> String
findSZS = fst . foldl' checkLine ("Could not determine SZS status", False)
  where
    checkLine :: (String, Bool) -> String -> (String, Bool)
    checkLine (szsStatusLine, found) line =
      if found
      then (szsStatusLine, found)
      else if isPrefixOf "Couldn't find " line
           then (line, found)
           else case getSZSStatusWord line of
             Just szsStatus -> (szsStatus, True)
             _ -> (szsStatusLine, found)

    getSZSStatusWord :: String -> Maybe String
    getSZSStatusWord line = case words $ fromMaybe "" $
      stripPrefix "SZS status" $ dropWhile (`elem` "%# ") line of
        [] -> Nothing
        w : _ -> Just w

-- filters the lines of the proof
filterProofLines :: [String] -> [String]
filterProofLines = fst . foldr addIfInProof ([], False)
  where
    addIfInProof :: String -> ([String], Bool) -> ([String], Bool)
    addIfInProof line (addedLines, insideProof) =
      -- @insideProof@ tells if the line is between "SZS output start/end".
      -- Since the lines are in reverse order (by foldr), we need to parse after
      -- "SZS output end" and before "SZS output start".
      if insideProof
      then if isPrefixOf "SZS output start" $ dropWhile (`elem` "%# ") line
           then (addedLines, False)
           else (line : addedLines, insideProof)
      else if isPrefixOf "SZS output end" $ dropWhile (`elem` "%# ") line
           then (addedLines, True)
           else (addedLines, insideProof)
