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


TODO:

* \comp_\tau and\/or \comp_0 are not computed correctly: see the 
  FailAmalg example, where the amalgamability check should fail but
  succeedes in step 2.

* the rest of the algorithm


-}

module CASL.Amalgamability(-- * Types
			   CASLSign, CASLMor, 
			   -- * Functions
			   ensuresAmalgamability) where


import CASL.AS_Basic_CASL
--import CASL.LaTeX_CASL
--import CASL.Parse_AS_Basic
--import CASL.SymbolParser
--import CASL.MapSentence
--import Common.AS_Annotation
--import Common.AnnoState(emptyAnnos)
import Common.Id
import Common.Lib.Graph
import qualified Common.Lib.Map as Map
--import Common.Lib.Parsec
import Common.Lib.Pretty
import Common.Lib.Rel
import qualified Common.Lib.Set as Set
import Common.PrettyPrint
import Common.Result
import Logic.Logic
--import CASL.ATC_CASL
--import CASL.Sublogic
import CASL.Sign
--import CASL.StaticAna
import CASL.Morphism
--import CASL.SymbolMapAnalysis
--import Data.Dynamic
import List

-- Exported types
type CASLSign = Sign () ()
type CASLMor = Morphism () () ()

-- Miscellaneous types
type CASLDiag = Diagram CASLSign CASLMor
type DiagSort = (Node, SORT) 
type DiagEmb = (Node, SORT, SORT)
type DiagEmbWord = [DiagEmb]
-- | equivalence classes are represented as lists of elements
type EquivClass a = [a]
-- | equivalence relations are represented as lists of equivalence classes
type EquivRel a = [EquivClass a]
-- | or, sometimes, as lists of pairs (element, equiv. class tag)
type EquivRelTagged a = [(a, a)]

-- PrettyPrint instance (for diagnostic output)
instance PrettyPrint (Diagram CASLSign CASLMor) where
    printText0 ga diag = 
	ptext "nodes: " 
        <+> (printText0 ga (labNodes diag))
	<+> ptext "\nedges: "
	<+> (printText0 ga (labEdges diag))


-- | Compute the Sorts set -- a disjoint union of all the sets
-- in the diagram.
sorts :: CASLDiag        -- ^ the diagram to get the sorts from
      -> [DiagSort]
sorts diag = 
    let mkNodeSortPair n sort = (n, sort)
        appendSorts sl (n, Sign { sortSet = s }) =
	    sl ++ (map (mkNodeSortPair n) (Set.toList s))
    in foldl appendSorts [] (labNodes diag)


-- | Convert the relation representation from list of pairs 
-- (val, equiv. class tag) to a list of equivalence classes.
taggedValsToEquivClasses :: Ord a
			 => EquivRelTagged a -- ^ a list of (value, tag) pairs
			 -> EquivRel a
taggedValsToEquivClasses rel =
    let -- prepMap: create a map with all the equivalence class tags mapped to
	-- empty lists
        prepMap rel = 
	    foldl (\m -> \k -> Map.insert (snd k) [] m) Map.empty rel
	-- conv: perform actual conversion
	convert [] m = map snd (Map.toAscList m)
	convert ((ds, ect) : dsps) m =
	    let m' = Map.update (\ec -> Just (ds : ec)) ect m
	    in convert dsps m'
    in convert rel (prepMap rel)


-- | Merge the equivalence classes for elements fulfilling given condition.
mergeEquivClassesBy :: Eq a 
	            => EquivRelTagged a -- ^ the input relation
		    -> (a -> a -> Bool) -- ^ the condition stating when two elements are in relation
		    -> EquivRelTagged a 
-- ^ returns the input relation with equivalence classes merged according to
-- the condition.
mergeEquivClassesBy rel cond =
    -- Starting with the first element in the list an element (elem, tag) is taken
    -- and cond is subsequently applied to it and all the elements
    -- following it in the list. Whenever an element (elem', tag') 
    -- that is in relation with the chosen one is found, all the equivalence 
    -- class tags in the list that are equal to tag' are updated to tag.

    let merge rel pos | pos >= length rel = rel
	merge rel pos | otherwise = 
	    let mergeWith cmpl _ [] = cmpl
		mergeWith cmpl vtp@(elem, ec) toCmpl@((elem', ec') : _) =
		    let (cmpl', toCmpl') = if ec /= ec' && (cond elem elem') 
					     then let upd (elem'', ec'') = 
							  if ec'' == ec' 
							     then (elem'', ec) 
							     else (elem'', ec'')
						  in (map upd cmpl, map upd toCmpl)
					     else (cmpl, toCmpl)
		    in mergeWith (cmpl' ++ [head toCmpl']) vtp (tail toCmpl')
		(cmpl, (vtp : vtps)) = splitAt pos rel
		rel' = mergeWith (cmpl ++ [vtp]) vtp vtps
	    in merge rel' (pos + 1)
    in merge rel 0


-- | Merge the equivalence classes for given tags.
mergeEquivClasses :: Eq a
		  => EquivRelTagged a
		  -> a                -- ^ tag 1
		  -> a                -- ^ tag 2
		  -> EquivRelTagged a
mergeEquivClasses rel tag1 tag2 | tag1 == tag2 = rel
				| otherwise =
    let upd (el, tag) | tag == tag2 = (el, tag1)
		      | otherwise = (el, tag)
    in map upd rel
    

-- | Return true if there is an edge between srcNode and targetNode
-- and the morphism with which it's labelled maps srcSort to targetSort
isMorph :: CASLDiag
	-> DiagSort
	-> DiagSort
	-> Bool
isMorph diag (srcNode, srcSort) (targetNode, targetSort) = 
    let checkEdges [] = False
        checkEdges ((sn, tn, Morphism { sort_map = sm }) : edges) =
	    if sn == srcNode && 
	       tn == targetNode &&
	       mapSort sm srcSort == targetSort 
	       then True else checkEdges edges
    in checkEdges (out diag srcNode)


-- | Compute the simeq relation for given diagram.
simeq :: CASLDiag  -- ^ the diagram for which the relation should be created
      -> EquivRel DiagSort
-- ^ returns the relation represented as a list of equivalence
-- classes (each represented as a list of diagram sorts)
simeq diag =
    -- During the computations the relation is represented as a list of pairs
    -- (DiagSort, DiagSort). The first element is a diagram sort and the second
    -- denotes the equivalence class to which it belongs. All the pairs with
    -- equal second element denote elements of one equivalence class.

    let mergeCond ds ds' = isMorph diag ds ds' || isMorph diag ds' ds

        -- compute the relation
	rel = map (\ds -> (ds, ds)) (sorts diag)
	rel' = mergeEquivClassesBy rel mergeCond
    in taggedValsToEquivClasses rel'


-- | Compute the simeq_tau relation for given diagram.
simeq_tau :: [LEdge CASLMor]
	  -> EquivRel DiagSort
simeq_tau sink = 
    let -- tagEdge: for given morphism m create a list of pairs 
	-- (a, b) where a is DiagSort from the source signature that
	-- is mapped by m to DiagSort b
        tagEdge (sn, tn, Morphism { sort_map = sm }) = 
	    map (\(ss, ts) -> ((sn, ss), (tn, ts))) (Map.toList sm)
        rel = foldl (\l -> \e -> l ++ (tagEdge e)) [] sink
    in taggedValsToEquivClasses rel


-- | Check that one equivalence relation is a subset of another.
-- The relations are represented as a lists of equivalence classes,
-- where equivalence classes are lists of elements.
subRelation :: Eq a
	    => EquivRel a  -- ^ the relation that is supposed to be a subset
	    -> EquivRel a  -- ^ the relation that is supposed to be a superset
	    -> Maybe (a, a)
-- ^ returns a pair of elements that are in the same equivalence class of the 
-- first relation but are not in the same equivalence class of the second 
-- relation or Nothing the first relation is a subset of the second one.
subRelation [] _ = Nothing
subRelation ([] : eqcls) sup = subRelation eqcls sup -- this should never be the case
subRelation ((elt : elts) : eqcls) sup =
    let findEqCl _ [] = [] -- this should never be the case
	findEqCl elt (eqcl : eqcls) =
	    if elem elt eqcl then eqcl else findEqCl elt eqcls
        checkEqCl [] _ = Nothing
	checkEqCl (elt : elts) supEqCl =
	    if elem elt supEqCl 
	       then checkEqCl elts supEqCl
	       else Just elt
	curFail = checkEqCl elts (findEqCl elt sup)
    in case curFail of 
	    Nothing -> subRelation eqcls sup
	    Just elt2 -> Just (elt, elt2)


-- | Compute the set of sort embeddings defined in the diagram.
embs :: CASLDiag
     -> [DiagEmb]
embs diag =
    let embs' [] = []
        embs' ((n, Sign {sortRel = sr}) : lNodes) = 
	    (map (\(s1, s2) -> (n, s1, s2)) (toList sr)) ++ (embs' lNodes)
    in embs' (labNodes diag)


-- | Compute the set of sort embeddings (relations on sorts) defined
-- in the source nodes of the sink.
sinkEmbs :: CASLDiag        -- ^ the diagram
	 -> [LEdge CASLMor] -- ^ the sink
	 -> [DiagEmb]
sinkEmbs _ [] = []
sinkEmbs diag ((srcNode, _, _) : edges) = 
    let (_, _, Sign {sortRel = sr}, _) = context srcNode diag
    in (map (\(s1, s2) -> (srcNode, s1, s2)) (toList sr)) ++ (sinkEmbs diag edges)
    

-- | Check if the two given elements are in the given relation.
inRel :: Eq a 
      => EquivRel a -- ^ the relation
      -> a          -- ^ the first element
      -> a          -- ^ the second element
      -> Bool
inRel [] _ _ = False
inRel (eqc : eqcs) a b | a == b = True
		       | otherwise =
    case find (\x -> x == a) eqc of
         Nothing -> inRel eqcs a b
	 Just _ -> case find (\x -> x == b) eqc of
		        Nothing -> False
			Just _ -> True


-- | Compute the set of all the loopless, admissible
-- words over given set of embeddings.
embWords :: [DiagEmb]         -- ^ the embeddings
	 -> EquivRel DiagSort -- ^ the \simeq relation that defines admissibility
	 -> [DiagEmbWord]
embWords embs simeq =
    let -- can the two embeddings occur subsequently in a word?
        admissible (n1, s1, _) (n2, _, s2) = inRel simeq (n1, s1) (n2, s2)
        -- generate the list of all loopless words over given alphabet
	-- with given suffix
        embWords' suff@(_ : _) embs pos | pos >= length embs = [suff]
	embWords' suff@(e : _) embs pos | otherwise = 
	    let emb = embs !! pos
		embs' = embs \\ [emb]
		ws = if admissible emb e
		       then embWords' (emb : suff) embs' 0
		       else []
	    in ws ++ (embWords' suff embs (pos + 1))
	embWords' [] embs pos | pos >= length embs = []
	embWords' [] embs pos | otherwise = 
	    let emb = embs !! pos
		embs' = embs \\ [emb]
	    in (embWords' [emb] embs' 0) ++ (embWords' [] embs (pos + 1))
    in embWords' [] embs 0


-- | Return the codomain of an embedding path.
wordCod :: DiagEmbWord 
	-> DiagSort
wordCod ((n, _, s2) : _) = (n, s2)


-- | Return the domain of an embedding path.
wordDom :: DiagEmbWord
	-> DiagSort
wordDom w = let (n, s1, _) = last w in (n, s1)


-- | Find an equivalence class tag for given element.
findTag :: Eq a
	=> EquivRelTagged a
	-> a
	-> a
findTag [] w = w -- this should never be the case
findTag ((w', t) : wtps) w = 
    if w == w' then t else findTag wtps w


-- | Compute the left-cancellable closure of a relation on words.
leftCancellableClosure :: EquivRelTagged DiagEmbWord
		       -> EquivRelTagged DiagEmbWord
leftCancellableClosure rel = 
    let -- checkPrefixes: for each common prefix of two given words
	-- merge the equivalence classes of the suffixes
        checkPrefixes [] _ rel = rel
	checkPrefixes _ [] rel = rel
	checkPrefixes w1@(l1 : suf1) w2@(l2 : suf2) rel | w1 == w2 = rel
							| l1 /= l2 = rel
							| otherwise =
	    let tag1 = findTag rel suf1
		tag2 = findTag rel suf2
		rel' = if tag1 == tag2 then rel
		          else let upd (w, t) | t == tag2 = (w, tag1)
					      | otherwise = (w, t)
			       in map upd rel
	    in checkPrefixes suf1 suf2 rel'

        -- iterateWord1: for each pair of related words call checkPrefixes
	iterateWord1 rel pos | pos >= length rel = rel
			     | otherwise =
	    let iterateWord2 wtp1@(w1, t1) rel pos | pos >= length rel = rel
						   | otherwise =
		    let wtp2@(w2, t2) = rel !! pos
			rel' = if t1 == t2 then checkPrefixes w1 w2 rel else rel
		    in iterateWord2 wtp1 rel' (pos + 1)
		wtp = rel !! pos
		rel' = iterateWord2 wtp rel 0
            in iterateWord1 rel' (pos + 1)
    in iterateWord1 rel 0


-- | Compute the congruent closure of a relation on words with
-- given \simeq relation on letters.
-- This function should be applied to the relation until a fixpoint is reached.
congruentClosure :: EquivRel DiagSort          -- ^ the simeq relation
		 -> EquivRelTagged DiagEmbWord 
		 -> EquivRelTagged DiagEmbWord
congruentClosure simeq rel =
    let -- iterateWord1 
        iterateWord1 rel pos | pos >= length rel = rel
			     | otherwise =
	    let -- iterateWord2
	        iterateWord2 wtp1@(_, t1) rel pos | pos >= length rel = rel
						  | otherwise =
                    let -- iterateWord3
		        iterateWord3 wtp1@(w1, _) wtp2 rel pos | pos >= length rel = rel
							       | otherwise =
			    let -- iterateWord4
			        iterateWord4 wtp1@(w1, _) wtp2@(w2, _) wtp3@(w3, t3) rel pos | pos >= length rel = rel
											     | otherwise =
				    let (w4, t4) = rel !! pos
					rel' = if t3 /= t4 then rel
					          else let ct1 = findTag rel (w3 ++ w1)
							   ct2 = findTag rel (w4 ++ w2)
						       in mergeEquivClasses rel ct1 ct2
				    in iterateWord4 wtp1 wtp2 wtp3 rel' (pos + 1)

			        wtp3@(w3, _) = rel !! pos
				rel' = if inRel simeq (wordCod w1) (wordDom w3)
				          then iterateWord4 wtp1 wtp2 wtp3 rel 0
					  else rel
			    in iterateWord3 wtp1 wtp2 rel' (pos + 1)

		        wtp2@(_, t2) = rel !! pos
			rel' = if t1 /= t2 then rel
			          else iterateWord3 wtp1 wtp2 rel 0 
		    in iterateWord2 wtp1 rel' (pos + 1)

		wtp = rel !! pos
		rel' = iterateWord2 wtp rel 0
	    in iterateWord1 rel' (pos + 1)

    in iterateWord1 rel 0


-- | Compute the cong_tau relation for given diagram and sink.
cong_tau :: CASLDiag          -- ^ the diagram
	 -> [LEdge CASLMor]   -- ^ the sink
	 -> EquivRel DiagSort -- ^ the \simeq_tau relation
	 -> EquivRel DiagEmbWord
cong_tau diag sink st = 
    let -- domCodEqual: check that domains and codomains of given words are equal
        domCodEqual w1 w2 = 
	    -- we ignore the nodes form which the sorts come,
	    -- as all the sink source nodes are considered to be one node
	    -- TODO: ^ this is wrong
	    {-let (_, sdom1) = wordDom w1
		(_, scod1) = wordCod w1
		(_, sdom2) = wordDom w2
		(_, scod2) = wordCod w2
	    in sdom1 == sdom2 && scod1 == scod2-}
	       wordDom w1 == wordDom w2 && wordCod w1 == wordCod w2
	-- comp: the Comp rule works for words 1 and 2-letter long
	-- with equal domains and codomains
        comp w1@[_] w2@[_, _] = domCodEqual w1 w2
	comp w1@[_, _] w2@[_] = domCodEqual w1 w2
	comp _ _ = False
	
        -- fixCongLc: apply Cong and Lc rules until a fixpoint is reached
	-- TODO: Lc seems redundant in this case
        fixCongLc rel =
	    let rel' = (leftCancellableClosure . congruentClosure st) rel
	    in if rel == rel' then rel else fixCongLc rel'

	-- compute the relation
	embs = sinkEmbs diag sink
	words = embWords embs st
	rel = map (\w -> (w, w)) words
	rel' = mergeEquivClassesBy rel comp
	rel'' = fixCongLc rel'
    in taggedValsToEquivClasses rel''


-- | Compute the cong_0 relation for given diagram.
cong_0 :: CASLDiag
       -> EquivRel DiagSort -- ^ the \simeq relation
       -> EquivRel DiagEmbWord
cong_0 diag simeq = 
-- TODO: make the parts common with cong_tau global
    let -- domCodEqual: check that domains and codomains of given words are equal
        domCodEqual w1 w2 = 
	       wordDom w1 == wordDom w2 && wordCod w1 == wordCod w2

	-- diagRule: the Diag rule
	diagRule [(n1, s11, s12)] [(n2, s21, s22)] =
	    isMorph diag (n1, s11) (n2, s21) &&
	    isMorph diag (n1, s12) (n2, s22)
	diagRule _ _ = False

	-- comp: the Comp rule works for words 1 and 2-letter long
	-- with equal domains and codomains
        comp w1@[_] w2@[_, _] = domCodEqual w1 w2
	comp w1@[_, _] w2@[_] = domCodEqual w1 w2
	comp _ _ = False
	
	-- compute the relation
	em = embs diag
	words = embWords em simeq
	rel = map (\w -> (w, w)) words
	rel' = mergeEquivClassesBy rel diagRule
	rel'' = mergeEquivClassesBy rel' comp
    in taggedValsToEquivClasses rel''


-- | The amalgamability checking function for CASL.
ensuresAmalgamability :: CASLDiag        -- ^ the diagram to be checked
		      -> [LEdge CASLMor] -- ^ the sink
		      -> Result Amalgamates
ensuresAmalgamability diag' sink@((_, tn, _) : _) = 
    do let diag = delNode tn diag'
           s = simeq diag
	   st = simeq_tau sink
       -- 1. Check the inclusion (*). If it doesn't hold, the specification is
       -- incorrect.
       --warning DontKnow ("sink: " ++ (showPretty sink "")) nullPos -- test
       --warning DontKnow ("diag: " ++ (showPretty diag "")) nullPos -- test
       case subRelation st s of
	    Just (ns1, ns2) -> let getNodeSig _ [] = emptySign () -- this should never be the case
				   getNodeSig n ((n1, sig) : nss) = if n == n1 then sig else getNodeSig n nss
				   lns = labNodes diag'
				   sortString1 = renderText Nothing (printText (snd ns1)) ++
					     " in {" ++ renderText Nothing (printText (getNodeSig (fst ns1) lns)) ++ "}"
				   sortString2 = renderText Nothing (printText (snd ns2)) ++
					     " in {" ++ renderText Nothing (printText (getNodeSig (fst ns2) lns)) ++ "}"
	                       in do return (No ("sorts " ++ sortString1 ++ " and " ++ sortString2))
	    Nothing -> do let ct = cong_tau diag' sink st
			      c0 = cong_0 diag s
			  -- 2. Check the simple case: \cong_0 \in \cong, so if \cong_\tau \in \cong_0 the
			  -- specification is correct.
			  --warning DontKnow ("cong_tau: " ++ (showPretty ct "")) nullPos -- test
			  --warning DontKnow ("cong_0: " ++ (showPretty c0 "")) nullPos -- test
		          case subRelation ct c0 of
		               Nothing -> do return Yes
			       Just _ -> return DontKnow -- TODO

