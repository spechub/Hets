{- | 
   
    Module      :  $Header$
    Copyright   :  (c)  Martin Kühl and Till Mossakowski and Uni Bremen 2003
    Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

    Maintainer  :  hets@tzi.de
    Stability   :  provisional
    Portability :  portable

    Overload resolution

-}

module CASL.Overload where

import CASL.StaticAnalysis -- Sign = Env
import CASL.AS_Basic -- FORMULA
import Common.Result -- Result

import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Rel as Rel
import qualified Common.Id      as Id

{-

Idee: 
- global Infos aus Sign berechnen + mit durchreichen
  (connected compenents, s.u.)
- rekursiv in Sentence absteigen, bis atomare Formel erreicht wird
- atomaren Formeln mit minExpTerm behandeln

TODO: All das hier implementieren und testen :D

-}

{-----------------------------------------------------------
    Overload Resolution
-----------------------------------------------------------}
{- expand all sentences to be fully qualified, then return them if there is no
   ambiguity -}
overloadResolution :: Sign -> [Sentence] -> Result [Sentence]
overloadResolution sign sentences
    = do expandedSentences <- map (minExpSentence sign) sentences
         -- check ambiguities, generate errors for them

{-----------------------------------------------------------
    Extract Atomic Sentences from (general) Sentences
-----------------------------------------------------------}
getAtoms :: Sentence -> [Sentence]
getAtoms sentence
    = case sentence of
        -- Non-Atomic Sentences -> Descend and Extract
        Quantification _ _ sentence' _ -> getAtoms sentence'
        Conjunction sentences _        -> getAllAtoms sentences
        Disjunction sentences _        -> getAllAtoms sentences
        Implication sent1 sent2 _      -> getAllAtoms [sent1, sent2]
        Equivalence sent1 sent2 _      -> getAllAtoms [sent1, sent2]
        Negation sentence' _           -> getAtoms sentence'
        -- Atomic Sentences -> Wrap and Return
        _                              -> [sentence]
    where getAllAtoms = concat . map getAtoms

{-----------------------------------------------------------
    Minimal Expansion of a Sentence -- TODO: implement :o)
-----------------------------------------------------------}
minExpSentence :: Sign -> Sentence -> Result [[Sentence]]
minExpSentence sign sentence
    = case sentence of
        -- Atomic Sentences -> Calculate minimal Expansion 
        True_atom _                    -> [["True", "_bool"]]
        False_atom _                   -> [["False", "_bool"]]
        Predication PRED_SYMB [TERM] _ -> -- predicate application
        Definedness TERM _             -> -- see till's mail
        Existl_equation TERM TERM _    -> -- see till's mail
        Strong_equation TERM TERM _    -> -- see till's mail
        Membership TERM SORT _         -> -- like in 'forall n in Nat'?
        -- Unparsed Sentences -> Parser Error, Bail out!
        Mixfix_formula term            ->
            error $ "Parser Error: Unparsed `Mixfix_formula' received: "
                    ++ (show term)
        Unparsed_formula string _      -> 
            error $ "Parser Error: Unparsed `Unparsed_formula' received: "
                    ++ string
        -- Non-Atomic Sentences -> getAtoms Error, Bail out!
        _                              ->
            error $ "Internal Error: Unknown type of Sentence received: "
                    ++ (show sentence)

{-----------------------------------------------------------
    Minimal Expansion of a Term
-----------------------------------------------------------}
minExpTerm :: Sign -> TERM -> Result [[TERM]]
minExpTerm sign term
    = case term of
        Simple_id var
            -> minExpTerm_simple sign var
        Qual_var var sort _
            -> -- qualified term
        Application op terms _
            -> -- op application
        Sorted_term term sort _
            -> -- qualified term
               -- wie unterscheidet sich das von Qual_var???
        Cast term sort _
            -> -- cast ?
        Conditional term1 formula term2 _
            -> -- conditional ?
        Unparsed_term string _
            -> error $ "Parser Error: Unparsed `Unparsed_term' found: "
               ++ string
        _   -> error $ "Parser Error: Unparsed `Mixfix' term found: "
               ++ (show term)

{-----------------------------------------------------------
    Minimal Expansion of a Simple_id Term
-----------------------------------------------------------}
minExpTerm_simple :: Sign -> SIMPLE_ID -> Result [[TERM]]
minExpTerm_simple sign var
    = do
        -- is_const :: OpType -> Bool
        let is_const = null . opArgs            -- list of args is empty
            = 1 == Set.size                     -- True if s is the only member
                (Set.intersection sorts         -- intersect with current sorts
                    (subsortsOf s sign))        -- find subsorts
        -- vars :: Set.Set SORT
        let vars = case Map.lookup var (varMap sign) of
            Nothing    -> Set.empty
            Just vars' -> vars'
        -- ops :: Set.Set SORT
        let ops = case Map.lookup (simpleIdToId var) (opMap sign) of
            Nothing    -> Set.empty
            Just ops'  ->
                Set.fromList                    -- convert back into Set
                    $ map opRes                 -- get result of each op
                    $ Set.elems                 -- convert Set to list
                    $ Set.filter is_const ops'  -- find const ops
        -- all_sorts :: Set.Set SORT
        let all_sorts = Set.union vars ops
        -- no_lesser_sort :: (Set.Set SORT) -> SORT -> Bool
        let no_lesser_sort sorts s
        -- least_sorts :: Set.Set SORT
        let least_sorts
            = Set.filter (no_lesser_sort all_sorts) all_sorts
        -- TODO: merge var into this process somewhere
        return qualifyTerms                     -- merge into qualified Term
            $ equivalence_Classes leqF           -- divide into equiv. classes
            $ Set.toList least_sorts            -- convert to List

{-----------------------------------------------------------
    Minimal Expansion of a Qual_var Term
-----------------------------------------------------------}
minExpTerm_qual :: Sign -> VAR -> SORT -> Result [[TERM]]
minExpTerm_qual sign var sort
    = do
        -- expandedVar :: [[TERM]]
        expandedVar <- minExpTerm_simple sign var
        -- selectExpansions :: [TERM] -> [(TERM, SORT)]
        let selectExpansions c                  -- foreach c in expandedVar
            = [ ((Simple_id var), sort) |       -- choose {(var, sort)}
                sorted <- c,                    -- foreach sorted Term in c
                fits sorted ]                   -- if it fits var and sort
        -- fits :: TERM -> Bool
        let fits (Sorted_term (Simple_id v) s _)
            = (v == var) && (s <= sort)         -- if var eq and sort leq
        let fits _ = False                      -- TODO: this shouldn't happen
        return qualifyTerms                     -- merge into qualified Term
            $ map selectExpansions expandedVar  -- choose Set foreach Expansion

{-----------------------------------------------------------
    Minimal Expansion of a Sorted_term Term
-----------------------------------------------------------}
minExpTerm_sorted :: Sign -> TERM -> SORT -> Result [[TERM]]
minExpTerm_sorted sign term sort
    = do
        -- expandedTerm :: [[TERM]]
        expandedTerm <- minExpTerm sign term
        -- selectExpansions :: [TERM] -> [(TERM, SORT)]
        let selectExpansions c                  -- foreach c in expandedTerm
            = [ (term, sort) |                  -- choose {(term, sort)}
                sorted <- c,                    -- foreach sorted Term in c
                fits sorted ]                   -- if it fits term and sort
        let fits (Sorted_term t s _)
            = (t == term) && (s <= sort)        -- if term eq and sort leq
        let fits _ = False                      -- TODO this shouldn't happen
        return qualifyTerms                     -- merge into qualified Term
            $ map selectExpansions expandedTerm -- choose Set foreach Expansion

{-----------------------------------------------------------
    Minimal Expansion of an Application Term
-----------------------------------------------------------}
minExpTerm_op :: Sign -> OP_SYMB -> [TERM] -> Result [[TERM]]
minExpTerm_op sign op terms
    = do
        -- ops :: [OP_SYMB]
        let ops = Map.toList (opMap sign)
        -- expansions :: [[[Sorted_TERM]]]
        expansions <- mapM (minExpTerm sign) terms
        -- permuted_exps :: [[[Sorted_TERM]]]
        let permuted_exps = permute expansions
        -- profiles :: [[(OP_SYMB, [SORT])]]
        let profiles = map get_profile permuted_exps
        -- P :: [[[(OP_SYMB, [SORT])]]]
        let P = map (equivalence_Classes op_eq) profiles
        -- P' :: [[[(OP_SYMB, [SORT])]]]
        let P' = map (minimize sign) P
        -- kann das sein? das sieht mir aus, als wär da eine Liste zuviel drum
        -- hab ich eventuell vorher ein concat vergessen?
        return qualifyTerms $ qualifyOps P'
        -- TODO: qualifyTerms muss hier anders definiert sein
        -- evtl. muss jede minExpX eine andere Fkt am Ende aufrufen...
    where
        op_eq (op1,ts1) (op2,ts2)
            = let w1 = op_terms op1                             -- :: [TERM]
                  w2 = op_terms op2                             -- :: [TERM]
                  b1 = zipped_all (leq_SORT sign) ts1 w1        -- ::  Bool
                  b2 = zipped_all (leq_SORT sign) ts2 w2        -- ::  Bool
                  ops_equal = op1 == op2                        -- ::  Bool
                  ops_equiv = op1 leqF op2                      -- ::  Bool
                  types_equal = all ( zipWith (==) ts1 ts2 )    -- ::  Bool
                  -- TODO: leqF fehlt noch!
              in b1 && b2 && (ops_equal || (ops_equiv && types_equal))
        get_profile cs -- :: [[Sorted_TERM]] -> [(OP_SYMB, [SORT])]
            = [ (op', ts) | op' <- ops, ts <- (permute cs),
                (op_name op') == (op_name op),
                zipped_all (leq_SORT sign) ts (op_terms op') ]
        -- TODO: darf hier ein unqualifizierter OP in Sign stecken?!?
        -- wenn ja, dann muss ich op_terms anpassen!!!

{-----------------------------------------------------------
    Construct a TERM of type Sorted_term
    from each (TERM, SORT) tuple
-----------------------------------------------------------}
qualifyTerms :: [[(TERM, SORT)]] -> [[TERM]]
qualifyTerms = map (map qualify_term)
    where qualify_term term sort = Sorted_term sort term []

-- TODO: implement me for real - used by minExpTerm_op
-- minimize :: Sign -> [XX] -> [XX]
minimize :: (Ord a) => Sign -> [a] -> [a]
minimize sign as
    = concat $ map (\a -> if null (filter (<a) as then [a] else []) as

{-----------------------------------------------------------
    Divide a Set (list) into equivalence classes w.r.to eq
-----------------------------------------------------------}
equivalence_Classes :: (a -> a -> Bool) -> [a] -> [[a]]
equivalence_Classes _ [] = []
equivalence_Classes eq (x:l)
    = let (xs, ys) = partition (eq x) l
           xs'     = (x:xs)
      in xs':(equiv eq ys)
-- komplexere Implementation: siehe unten, Till's SML-version...

{-----------------------------------------------------------
    Transform a list [l1,l2, ... ln] to (in sloppy notation)
    [[x1,x2, ... ,xn] | x1<-l1, x2<-l2, ... xn<-ln]
-----------------------------------------------------------}
permute       :: [[a]] -> [[a]]
permute []    = [[]]
permute [x]   = map (\y -> [y]) x
permute (x:l) = concat (map (distribute (permute l)) x)
    where distribute perms y = map ((:) y) perms

{-----------------------------------------------------------
    Like 'all (zipWith p as bs)',
    but must return False if lengths don't match
-----------------------------------------------------------}
zipped_all                 :: (a -> b -> Bool) -> [a] -> [b] -> Bool
zipped_all _ []     []     = True
zipped_all p (a:as) (b:bs) = (p a b) && (zipped_all p as bs)
zipped_all _  _      _     = False

{-----------------------------------------------------------
    These are used by minExpTerm_op only,
    maybe souldn't be global anyway...
-----------------------------------------------------------}
op_name                         :: OP_SYMB -> OP_NAME
op_name (Op_name name)          = name
op_name (Qual_op_name name _ _) = name

op_terms                        :: OP_SYMB -> OP_TYPE
op_terms (Qual_op_name _ ts _)  = ts
op_terms (Op_name _)            = error "Critical: Unqualified Op in op_terms!"

{-----------------------------------------------------------
    Return True if s1 <= s2
-----------------------------------------------------------}
leq_SORT :: Sign -> SORT -> SORT -> Bool
leq_SORT sign s1 s2 = Set.member s2 (supersortsOf s1 sign)
-- leq_SORT = (flip Set.member) . (flip supersortsOf)

leqF :: a -> a -> Bool -- Funktionsgleichheit
leqP :: a -> a -> Bool -- Praedikatsgleichheit


{-

Die alten SML-Funktionen, die hier verwandt wurden.
Den Beschreibungen nach sind das genau die beiden, mit denen eine Menge in
Aequivalenzklassen unterteilt wird.
Wie die erste davon funktioniert, ist mir nicht offen ersichtlich,
aber vielleicht brauch ich die eigentlich auch gar nicht?

(* Compute the connected compenents of a graph which is given
   by a list of nodes and a boolean function indicating whether
   there is an egde between two nodes.
   For each node, the algorithm splits the connected components
   which have been computed so far into two categories:
   those which are connected to the node and those which are not.
   The former are all linked with @ in order to form a new connected
   component, the latter are left untouched. *)
     			 
fun compute_conn_components (edges:'a*'a->bool) (nodes:'a list):'a list list =
  let
    fun is_connected(node,nil) = false
      | is_connected(node,n::c) = 
          edges(node,n) orelse edges(n,node) orelse is_connected(node,c)
    fun split_components(node,nil,acc_comp_of_node,acc_other_comps) = 
    	(node::acc_comp_of_node)::acc_other_comps
      | split_components(node,current_comp::other_comps,acc_comp_of_node,acc_other_comps) =
        if is_connected(node,current_comp)
        then split_components(node,other_comps,current_comp@acc_comp_of_node,acc_other_comps)
        else split_components(node,other_comps,acc_comp_of_node,current_comp::acc_other_comps)
    fun add_node (node:'a,components:'a list list):'a list list =
        split_components(node,components,nil,nil)
  in
  foldr add_node (nodes,[])
  end 

(* Compute the equivalence classes of the equivalence closures of leqF and leqP resp.
   and store them in a table indexed by function and predicate names, resp.
   This is needed when checking if terms or predications are equivalent, since
   this equivalence is defined in terms of  the equivalence closures of leqF and leqP resp. *)


     			 
fun get_conn_components (env:local_env) : local_env1 =
	let
		val (srts,vars,funs,preds) = env
	in
		(env,(Symtab_id.map (compute_conn_components (leqF env)) funs ,
		      Symtab_id.map (compute_conn_components (leqP env)) preds) )
	end

-}

