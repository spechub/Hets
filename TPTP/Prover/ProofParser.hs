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
                               , graphFromProofObject
                               , filterProofLines
                               , findSZS
                               ) where

import TPTP.AS ( Annotated_formula (..)
               , Formula_role (..)
               , Annotations (..)
               , THF_annotated (..)
               , TFX_annotated (..)
               , TFF_annotated (..)
               , TCF_annotated (..)
               , FOF_annotated (..)
               , CNF_annotated (..)
               , TPI_annotated (..)
               , Source (..)
               , DAG_source (..)
               , External_source (..)
               , File_source (..)
               , Inference_record (..)
               , Parent_info (..)
               , Name (..)
               , formulaRole
               , annotations
               , name )
import TPTP.Parser (annotated_formula)
import TPTP.Pretty ()

import Common.DocUtils
import Common.ProofTree
import Common.Id (Token (..))

import Data.Data (toConstr)
import Data.List
import Data.List.Split (splitOn)
import Data.Maybe
import Data.Graph.Inductive.Graph
import qualified Data.HashMap.Strict as Map
import Text.ParserCombinators.Parsec

axiomsFromProofObject :: [String] -> ([String], [String])
axiomsFromProofObject =
  foldr addIfAxiom ([], []) . map parseFormulae . splitFormulae . unlines
  where
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

splitFormulae :: String -> [String]
splitFormulae = init . map (\ s -> s ++ ").\n") . splitOn ").\n"

parseFormulae :: String -> Either String Annotated_formula
parseFormulae text = case runParser annotated_formula () "" text of
  Right formula -> Right formula
  Left err -> Left ("Warning: unable to parse proof:\n" ++
                    "Formula in the proof: " ++ text ++ "\n" ++
                    "Error: " ++ show err ++ "\n")

graphFromProofObject :: [String] -> ProofTree
graphFromProofObject =
  ProofGraph . uncurry mkGraph . fst . foldl addNode (([], []), (0, Map.empty)) . map parseFormulae . splitFormulae . unlines
  where
    strName :: Name -> String
    strName (NameString t ) = tokStr t
    strName (NameInteger i) = show i
    strSentence :: Annotated_formula -> String
    strSentence a = case a of
      AF_THF_Annotated (THF_annotated _ _ f _) -> show f
      AF_TFX_Annotated (TFX_annotated _ _ f _) -> show f
      AF_TFF_Annotated (TFF_annotated _ _ f _) -> show f
      AF_TCF_Annotated (TCF_annotated _ _ f _) -> show f
      AF_FOF_Annotated (FOF_annotated _ _ f _) -> show f
      AF_CNF_Annotated (CNF_annotated _ _ f _) -> show f
      AF_TPI_Annotated (TPI_annotated _ _ f _) -> show f

    addNode :: (([(Int, ProofGraphNode)], [(Int, Int, Int)]), (Int, Map.HashMap String Int))
            -> Either String Annotated_formula
            -> (([(Int, ProofGraphNode)], [(Int, Int, Int)]), (Int, Map.HashMap String Int))
    addNode args@((nodeList, edgeList), (index, keyIdMap)) formulaOrError =
      case formulaOrError of
        Right formula -> let forName = strName (name formula)
                             forSentence = strSentence formula
                             (anons,infrs,newEdges) = extractParentEdges (annotations formula) in
          -- every formula introduces one sentence node but *at least* one inference node, i.e. its own origin inference and potential anonymous intermediates' inferences
          ((map (\(i,infr)->(i,Left infr)) infrs ++ (index, Right (forName,forSentence)) : nodeList
          -- the origin inference of a sentence with index i has index -i-1
          , newEdges ++ (-index-1,index,-1):edgeList)
          -- the anonymous sentences don't appear as nodes but their respective origin inferences have indices that need to be skipped nonetheless
          ,(index + anons + 1
          -- collecting formula names this way makes it necessary to fold left!
          , Map.insert forName index keyIdMap ))
        _ -> args
      where
        extractParentEdges :: Annotations -> (Int,[(Int,String)],[(Int, Int, Int)])
        -- Computes number of nameless ancestors, list of all inference nodes and list of all origin relations described in annotation's source record,…
        extractParentEdges (Annotations (Just (src, _))) = walkInferences src index index Nothing
        -- if it exists, else there is nothing to report.
        extractParentEdges _ = (0,[],[])
        walkInferences :: Source -> Int -> Int -> Maybe Int -> (Int,[(Int,String)],[(Int, Int, Int)])
        -- Treats a list of parents/inferences as arguments to an inference for child and marks them accordingly
        walkInferences (Source_many srcs) child start _ =
          foldr collectInferences (0,[],[]) (zip [0..] srcs)
            where
              collectInferences :: (Int,Source) (Int,[(Int,String)],[(Int,Int,Int)]) -> (Int,[(Int,String)],[(Int,Int,Int)])
              -- Collect inferences for each source in the list while letting them know of their legacy (child is theirs), the index from which they may count new intermediate inferences and their place in the argument list
              collectInferences (i,s) (oAnons,oInfr,oEdges) =
                let (nAnons,nInfr,nEdges) = walkInferences s child (start + oAnons) (Just i)
                 in (nAnons+oAnons, nInfr ++ oInfr, nEdges ++ oEdges)
        -- We've found the name of a parent!
        walkInferences (Source_DAG (DAGS_name sname)) child _ infrArg =
          -- Again, the default should never be returned and if it is, the resulting cycle should stick out in the DAG
          let parent = Map.lookupDefault child (strName sname) keyIdMap
           in (0,[],[(parent, -child-1, fromMaybe 0 infrArg)])
        -- infrule is child's birthplace, so record who was there!
        walkInferences (Source_DAG (DAGS_record (Inference_record infrule _ parents))) child start infrArg =
          let (nextNode, nextStart, anon, aEdge) =
                case infrArg of
                  -- If this record has no place in an inference's argument list, it must be at top level in the annotation, so no other ancestors to record
                  Nothing -> (child,start,0,[])
                  -- Otherwise we know that child comes from here and whatever we find next (start+1) must be the iArg'th argument to infrule
                  Just iArg -> (start+1,start+1,1,[(-start-2,-child-1,iArg)])
              (nAnons, nInfr, nEdges) =
                -- Find nextNode's parents' origins while remembering what the nextStart-ing node index is
                walkInferences (Source_many $ map (\(Parent_info src _) -> src) parents) nextNode nextStart Nothing
           in (anon+nAnons,(-nextNode-1, tokStr infrule):nInfr,aEdge++nEdges)
        -- If the source is of any other shape, simply record it as origin of child
        walkInferences src child _ _ = (0,[(-child-1,show (toConstr src))],[])

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
