{- |
Module      :  $Header$
Copyright   :  (c) Maciek Makowski, Warsaw University 2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

  Amalgamability analysis for CASL. 

  Follows the algorithm outlined in MFCS 2001 (LNCS 2136, pp. 451-463, 
  Springer 2001) paper.

-}

module CASL.Amalgamability(-- types
			   CASLSign, CASLMor, 
			   -- functions
			   ensuresAmalgamability) where


import CASL.AS_Basic_CASL
import CASL.LaTeX_CASL
import CASL.Parse_AS_Basic
import CASL.SymbolParser
import CASL.MapSentence
import Common.AS_Annotation
import Common.AnnoState(emptyAnnos)
import Common.Id
import Common.Lib.Graph
import qualified Common.Lib.Map as Map
import Common.Lib.Parsec
import Common.Lib.Pretty
import qualified Common.Lib.Set as Set
import Common.PrettyPrint
import Common.Result
import Logic.Logic
import CASL.ATC_CASL
import CASL.Sublogic
import CASL.Sign
import CASL.StaticAna
import CASL.Morphism
import CASL.SymbolMapAnalysis
import Data.Dynamic

-- Exported types
type CASLSign = Sign () ()
type CASLMor = Morphism () () ()

-- Miscellaneous types
type DiagSort = (Node, SORT) 

-- TODO: test
instance PrettyPrint (Diagram CASLSign CASLMor) where
    printText0 ga diag = 
	ptext "nodes: " 
        <+> (printText0 ga (labNodes diag))
	<+> ptext "\nedges: "
	<+> (printText0 ga (labEdges diag))




-- | Compute the Sorts set -- a disjoint union of all the sets
-- in the diagram.
sorts :: Diagram CASLSign CASLMor -- ^ the diagram to get the sorts from
      -> [DiagSort]
sorts diag = 
    let mkNodeSortPair n sort = (n, sort)
        appendSorts sl (n, Sign { sortSet = s }) =
	    sl ++ (map (mkNodeSortPair n) (Set.toList s))
    in foldl appendSorts [] (labNodes diag)


-- | Compute the simeq relation for given diagram.
simeq :: Diagram CASLSign CASLMor -- ^ the diagram for which the relation should be created
      -> [[DiagSort]]
-- ^ returns the relation represented as a list of equivalence
-- classes (each represented as a list of diagram sorts)
simeq diag =
    -- During the computations the relation is represented as a list of pairs
    -- (DiagSort, DiagSort). The first element is a diagram sort and the second
    -- denotes the equivalence class to which it belongs. All the pairs with
    -- equal second element denote elements of one equivalence class.

    let -- isMorph: return true if there is an edge between srcNode and targetNode
	-- and the morphism with which it's labelled maps srcSort to targetSort
        isMorph (srcNode, srcSort) (targetNode, targetSort) = 
	    let checkEdges [] = False
                checkEdges ((sn, tn, Morphism { sort_map = sm }) : edges) =
		    if sn == srcNode && 
		       tn == targetNode &&
		       mapSort sm srcSort == targetSort 
		       then True else checkEdges edges
	    in checkEdges (out diag srcNode)
			 
	-- merge: propagate the equivalence class tags.
	-- Starting with the first element in the list an element (ds, tag) is taken
	-- and isMorph is subsequently applied to it and all the elements
	-- following it in the list. Whenever an element (ds', tag') 
	-- that is in relation with the chosen one is found, all the equivalence 
	-- class tags in the list that are equal to tag' are updated to tag.
        merge rel pos | pos >= length rel = rel
	merge rel pos | otherwise = 
	    let mergeWith cmpl _ [] = cmpl
		mergeWith cmpl dsp@(ds, ec) toCmpl@((ds', ec') : _) =
		    let (cmpl', toCmpl') = if ec /= ec' && 
					      (isMorph ds ds' || isMorph ds' ds) 
					      then let upd (ds'', ec'') = 
					                   if ec'' == ec' 
							      then (ds'', ec) 
							      else (ds'', ec'')
						   in (map upd cmpl, map upd toCmpl)
					      else (cmpl, toCmpl)
		    in mergeWith (cmpl' ++ [head toCmpl']) dsp (tail toCmpl')
	        (cmpl, (dsp : dsps)) = splitAt pos rel
	        rel' = mergeWith (cmpl ++ [dsp]) dsp dsps
	    in merge rel' (pos + 1)

        -- prepMap: create a map with all the equivalence class tags mapped to
	-- empty lists
        prepMap rel = 
	    foldl (\m -> \k -> Map.insert (snd k) [] m) Map.empty rel

        -- convert the relation representation from list of pairs 
	-- (val, equiv. class tag) to a list of equivalence classes
	convert [] m = map snd (Map.toAscList m)
	convert ((ds, ect) : dsps) m =
	    let m' = Map.update (\ec -> Just (ds : ec)) ect m
	    in convert dsps m'

        -- compute the relation
	rel = map (\ds -> (ds, ds)) (sorts diag)
	rel' = merge rel 0
    in convert rel' (prepMap rel')


-- | Compute the simeq_tau relation for given diagram.
simeq_tau :: Diagram CASLSign CASLMor
	  -> [LEdge CASLMor]
	  -> [[DiagSort]]
-- TODO
simeq_tau _ _ = []


-- | Check that one equivalence relation is a subset of another.
-- The relations are represented as a lists of equivalence classes,
-- where equivalence classes are lists of elements.
subRelation :: Eq a
	    => [[a]]
	    -> [[a]]
	    -> Bool
-- TODO
subRelation _ _ = True


-- | The amalgamability checking function for CASL.
ensuresAmalgamability :: Diagram CASLSign CASLMor -- ^ the diagram to be checked
		      -> [LEdge CASLMor]          -- ^ the sink
		      -> Result Amalgamates
ensuresAmalgamability diag sink = 
    do let s = simeq diag
	   st = simeq_tau diag sink
       if not (subRelation st s)
	  then return No
	  else return DontKnow -- TODO
       --warning DontKnow (showPretty diag "") nullPos -- test
       --warning DontKnow (showPretty s "") nullPos -- test
