{- |
Module      :  $Header$
Description :  Interface for CASL morphism search
Copyright   :  (c) Immanuel Normann, Uni Bremen 2007
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  inormann@jacobs-university.de
Stability   :  provisional
Portability :  portable
-}
module Search.CASL.Retrieval where

import qualified Data.Set as Set
import qualified Data.Map as Map
import Search.Utils.SetMap
import Search.Common..Retrieval
import qualified Data.Graph.Inductive.Graph as Graph 
import OMDoc.HetsInterface
import qualified Common.AS_Annotation as AS
import qualified Static.DevGraph as DG
import CASL.FormulaWrapper
import Search.Common.Normalization

type NodeId = Int
type TheoryId = (FilePath, Int)
type CaslNFS = NFS CaslConst CaslVar
type CaslMorphism = Morphism CaslVar
type Index = Map.Map  TheoryId CaslNFS


caslQuery :: Index -> FilePath -> IO (Map.Map TheoryId CaslMorphism)
caslQuery index file =
    do dg <- getDG file
       return (query index (normalizeNode (getNodeByNr dg 0)))


buildIndex :: [FilePath] -> IO Index
buildIndex files =
    do dgs <- mapM getDG files
       return (buildIndexFromDgs (zip files dgs))  -- todo: error prone if file can´t be passed.

------------------ help functions:

normalizeNode :: DG.DGNodeLab -> NFS CaslConst CaslVar
normalizeNode n = fromListSetValues $ map (normalizeCaslFormula . AS.sentence) (getNodeSentences n)

normalizeDG :: (Graph.Graph gr) => gr DG.DGNodeLab b -> [NFS CaslConst CaslVar]
normalizeDG dg = map (normalizeNode . snd) (Graph.labNodes dg)




buildIndexFromDgs :: (Graph.Graph gr) =>
		     [(FilePath, gr DG.DGNodeLab b)]
		     -> Index
buildIndexFromDgs fdgs = theoryURLToNFS
    where ndgs = map norms fdgs
	  norms (f,s) = (f,normalizeDG s)
	  dist (f,lst) = map (\n -> ((f,fst n),snd n)) (zip [0..(length lst)] lst)
	  theoryURLToNFS = Map.fromList (concatMap dist ndgs)

{-
*CASL.Retrieval> index <- buildIndex ["./my-casl-lib/Test3.casl"]
*CASL.Retrieval> index
{("./my-casl-lib/Test3.casl",0):={(all (1) (0 1)):={[Qual_pred_name q (Pred_type [N] nullRange) nullRange,:N],[Qual_pred_name r (Pred_type [N] nullRange) nullRange,:N]}}}
*CASL.Retrieval> r <- caslQuery index "./my-casl-lib/Test1.casl"
*CASL.Retrieval> r
{("./my-casl-lib/Test3.casl",0):={{Qual_pred_name q (Pred_type [N] nullRange) nullRange:=Qual_pred_name p (Pred_type [M] nullRange) nullRange,:N:=:M},{Qual_pred_name r (Pred_type [N] nullRange) nullRange:=Qual_pred_name p (Pred_type [M] nullRange) nullRange,:N:=:M}}}

-}
