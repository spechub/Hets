{- | 
   
    Module      :  $Header$
    Copyright   :  (c)  Martin Kühl and Till Mossakowski and Uni Bremen 2003
    Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

    Maintainer  :  hets@tzi.de
    Stability   :  provisional
    Portability :  portable

    Overload resolution

-}

-- does anyone ever need anything else from here??
module CASL.Overload (
    overloadResolution          -- :: Sign -> [Sentence] -> Result [Sentence]
    ) where

import CASL.StaticAna           -- Sign/Env, Sentence, OpType
import CASL.AS_Basic_CASL       -- TERM, SORT, VAR, OP_{NAME,SYMB}
import Common.Result            -- Result

import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
--import qualified Common.Lib.Rel as Rel        -- not used directly
import qualified Common.Id      as Id

import Data.List                ( partition )

{-

    Idee: 
        - global Infos aus Sign berechnen + mit durchreichen
          (connected compenents, s.u.)
        - rekursiv in Sentence absteigen, bis atomare Formel erreicht wird
        - atomaren Formeln mit minExpTerm behandeln

-}

{-----------------------------------------------------------
    Overload Resolution
-----------------------------------------------------------}
{- expand all sentences to be fully qualified, then return them if there is no
   ambiguity -}
overloadResolution :: Sign -> [Sentence] -> Result [Sentence]
overloadResolution sign
    = mapM (minExpSentence sign)

{-----------------------------------------------------------
    Extract Atomic Sentences from (general) Sentences
-----------------------------------------------------------}
--getAtoms :: Sentence -> [Sentence]
--getAtoms sentence
--    = case sentence of
--        -- Non-Atomic Sentences -> Descend and Extract
--        Quantification _ _ sentence' _ -> getAtoms sentence'
--        Conjunction sentences _        -> getAllAtoms sentences
--        Disjunction sentences _        -> getAllAtoms sentences
--        Implication sent1 sent2 _      -> getAllAtoms [sent1, sent2]
--        Equivalence sent1 sent2 _      -> getAllAtoms [sent1, sent2]
--        Negation sentence' _           -> getAtoms sentence'
--        -- Atomic Sentences -> Wrap and Return
--        _                              -> [sentence]
--    where getAllAtoms = concat . map getAtoms

{-----------------------------------------------------------
    Minimal Expansions of a Sentence
-----------------------------------------------------------}
minExpSentence :: Sign -> Sentence -> Result Sentence
minExpSentence sign sentence
    = case sentence of
        -- Trivial Atom         -> Return untouched
        True_atom _     -> return sentence                      -- :: Sentence
        False_atom _    -> return sentence                      -- :: Sentence
        -- Atomic Sentence      -> Check for Ambiguities
        Predication predicate terms pos -> do
                ts <- mapM choose_unambiguous terms             -- :: [TERM]
                return $ Predication predicate ts pos           -- :: Sentence
        -- FIXME: This is the trivial implememtation, not the full one
        Definedness term pos            -> do
                t <- choose_unambiguous term                    -- :: TERM
                return $ Definedness t pos                      -- :: Sentence
        Existl_equation term1 term2 pos -> do
                t1 <- choose_unambiguous term1                  -- :: TERM
                t2 <- choose_unambiguous term2                  -- :: TERM
                return $ Existl_equation t1 t2 pos              -- :: Sentence
        Strong_equation term1 term2 pos -> do
                t1 <- choose_unambiguous term1                  -- :: TERM
                t2 <- choose_unambiguous term2                  -- :: TERM
                return $ Strong_equation t1 t2 pos              -- :: Sentence
        Membership term sort pos        -> do
                t <- choose_unambiguous term                    -- :: TERM
                return $ Membership t sort pos                  -- :: Sentence
        -- Unparsed Sentence    -> Error in Parser, Bail out!
        Mixfix_formula term             -> error
            $ "Parser Error: Unparsed `Mixfix_formula' received: "
            ++ (show term)
        Unparsed_formula string _       -> error
            $ "Parser Error: Unparsed `Unparsed_formula' received: "
            ++ (show string)
        -- "Other" Sentence     -> Unknown Error, Bail out!
        _                               -> error
            $ "Internal Error: Unknown type of Sentence received: "
            ++ (show sentence)
    where
        choose_unambiguous      :: TERM -> Result TERM
        choose_unambiguous term  = do
            expansions  <- minExpTerm sign term                 -- :: [[TERM]]
            case expansions of
                [_]     -> return $ head $ head expansions      -- ::   TERM
                _       -> error
                    $ "Cannot disambiguate! Term: " ++ (show term)
                    ++ "\n  Possible Expansions: " ++ (show expansions)

{-----------------------------------------------------------
    Minimal Expansions of a Term
-----------------------------------------------------------}
minExpTerm :: Sign -> TERM -> Result [[TERM]]
minExpTerm sign term'
    = case term' of
        Simple_id var
            -> minExpTerm_simple sign var
        Qual_var var sort _
            -> minExpTerm_qual sign var sort
        Application op terms _
            -> minExpTerm_op sign op terms
        Sorted_term term sort _
            -> minExpTerm_sorted sign term sort
        Cast term sort _
            -> minExpTerm_cast sign term sort
        Conditional term1 formula term2 _
            -> error $ "not implemented ... yet"        -- conditional ?
        Unparsed_term string _
            -> error $ "minExpTerm: Parser Error - Unparsed `Unparsed_term' "
               ++ string
        _   -> error $ "minExpTerm: Parser Error - Unparsed `Mixfix' term "
               ++ (show term')

{-----------------------------------------------------------
    Minimal Expansions of a Simple_id Term
-----------------------------------------------------------}
minExpTerm_simple :: Sign -> Id.SIMPLE_ID -> Result [[TERM]]
minExpTerm_simple sign var = do
    vars        <- return
        $ Map.findWithDefault                   -- :: Set.Set SORT
            Set.empty var (varMap sign)
    ops'        <- return
        $ Map.findWithDefault                   -- :: Set.Set SORT
            Set.empty name (opMap sign)
    ops         <- return
        $ Set.fromList                          -- :: Set.Set SORT
        $ (map opRes)                           -- :: [SORT]
        $ Set.toList                            -- :: [SORT]
        $ (Set.filter is_const_op)              -- :: Set.Set SORT
            ops'                                -- :: Set.Set SORT
        -- maybe use Set.fold instead of List.map?
    cs          <- return
        $ Set.union vars ops                    -- :: Set.Set SORT
    least       <- return
        $ Set.filter (is_least_sort cs) cs      -- :: Set.Set SORT
    return
        $ qualifyTerms                          -- :: [[TERM]]
        $ (equivalence_Classes leqF)            -- :: [[(TERM, SORT)]]
        $ map pair_with_id                      -- :: [(TERM, SORT)]
        $ Set.toList least                      -- :: [SORT]
    where
        name                    :: Id.Id
        name                     = Id.simpleIdToId var
        is_const_op             :: OpType -> Bool
        is_const_op op           = (null . opArgs) op
        is_least_sort           :: Set.Set SORT -> SORT -> Bool
        is_least_sort ss s
            = Set.size (Set.intersection ss (subsortsOf s sign)) == 1
        pair_with_id            :: SORT -> (TERM, SORT)
        pair_with_id sort        = ((Simple_id var), sort)

{-----------------------------------------------------------
    Minimal Expansions of a Qual_var Term
-----------------------------------------------------------}
minExpTerm_qual :: Sign -> VAR -> SORT -> Result [[TERM]]
minExpTerm_qual sign var sort = do
    expandedVar <- minExpTerm_simple sign var   -- :: [[TERM]]
    return
        $ qualifyTerms                          -- :: [[TERM]]
        $ map selectExpansions expandedVar      -- :: [[(TERM, SORT)]]
    where
        fits                    :: TERM -> Bool
        fits term                = case term of
            (Sorted_term (Simple_id var') sort' _)
                -> (var == var') && (sort == sort')
            _   -> error "minExpTerm: unsorted TERM after expansion"
        selectExpansions        :: [TERM] -> [(TERM, SORT)]
        selectExpansions c
            = [ ((Simple_id var), sort) |       -- :: (TERM, SORT)
                sorted <- c,                    -- :: TERM
                fits sorted ]                   -- :: Bool

{-----------------------------------------------------------
    Minimal Expansions of a Sorted_term Term
-----------------------------------------------------------}
minExpTerm_sorted :: Sign -> TERM -> SORT -> Result [[TERM]]
minExpTerm_sorted sign term sort = do
    expandedTerm <- minExpTerm sign term        -- :: [[TERM]]
    return
        $ qualifyTerms                          -- :: [[TERM]]
        $ map selectExpansions expandedTerm     -- :: [[(TERM, SORT)]]
    where
        fits                    :: TERM -> Bool
        fits term'               = case term' of
            (Sorted_term term'' sort' _)
                -> (term == term'') && (sort == sort')
            _   -> error "minExpTerm: unsorted TERM after expansion"
        selectExpansions        :: [TERM] -> [(TERM, SORT)]
        selectExpansions c
            = [ (term, sort) |                  -- :: (TERM, SORT)
                sorted <- c,                    -- :: TERM
                fits sorted ]                   -- :: Bool

{-----------------------------------------------------------
    Minimal Expansions of a Function Application Term
-----------------------------------------------------------}
minExpTerm_op :: Sign -> OP_SYMB -> [TERM] -> Result [[TERM]]
minExpTerm_op sign op terms = do
    expansions          <- mapM
        (minExpTerm sign) terms                 -- :: [[[TERM]]]
    permuted_exps       <- return
        $ permute expansions                    -- :: [[[TERM]]]
    profiles            <- return
        $ map get_profile permuted_exps         -- :: [[(OpType, [TERM])]]
    p                   <- return
        $ concat                                -- :: [[(OpType, [TERM])]]
        $ map (equivalence_Classes op_eq)       -- :: [[[(OpType, [TERM])]]]
          profiles                              -- :: [[(OpType, [TERM])]]
    p'                  <- return
        $ map (minimize sign) p                 -- :: [[(OpType, [TERM])]]
    return
        $ qualifyTerms                          -- :: [[TERM]]
        $ qualifyOps p'                         -- :: [[(TERM, SORT)]]
    where
        name            :: OP_NAME
        name             = op_name op
        ops             :: [OpType]
        ops              = Set.toList
            $ Map.find name $ (opMap sign)
        op_name         :: OP_SYMB -> OP_NAME
        op_name op'      = case op' of
            (Op_name name')             -> name'
            (Qual_op_name name' _ _)    -> name'
        term_sort       :: TERM -> SORT
        term_sort term'  = case term' of
            (Sorted_term _ sort _ )     -> sort
            _                           -> error                -- unlikely
                "minExpTerm: unsorted TERM after expansion"
        qualifyOps      :: [[(OpType, [TERM])]] -> [[(TERM, SORT)]]
        qualifyOps       = map (map qualify_op)
        qualify_op      :: (OpType, [TERM]) -> (TERM, SORT)
        qualify_op (op', terms')
            = ( (Application                                    -- ::  TERM
                    (Qual_op_name                               -- :: OP_SYMB
                        name                                    -- :: OP_NAME
                        (toOP_TYPE op')                         -- :: OP_TYPE
                        [])                                     -- :: [Pos]
                    terms'                                      -- :: [TERM]
                    [])                                         -- :: [Pos]
              , (opRes op') )                                   -- ::  SORT
        get_profile     :: [[TERM]] -> [(OpType, [TERM])]
        get_profile cs
            = [ (op', ts) |
                op' <- ops,                                     -- :: OpType
                ts <- (permute cs),                             -- :: [TERM]
                zipped_all (leq_SORT sign)                      -- ::  Bool
                    (map term_sort ts)                          -- :: [SORT]
                    (opArgs op') ]                              -- :: [SORT]
        op_eq           :: (OpType, [TERM]) -> (OpType, [TERM]) -> Bool
        op_eq (op1,ts1) (op2,ts2)
            = let   w1 = opArgs op1                             -- :: [SORT]
                    w2 = opArgs op2                             -- :: [SORT]
                    s1 = map term_sort ts1                      -- :: [SORT]
                    s2 = map term_sort ts2                      -- :: [SORT]
                    b1 = zipped_all (leq_SORT sign) s1 w1       -- ::  Bool
                    b2 = zipped_all (leq_SORT sign) s2 w2       -- ::  Bool
                    ops_equal = (op1 == op2)                    -- ::  Bool
                    ops_equiv = op1 `leqF` op2                  -- ::  Bool
                    types_equal = and ( zipWith (==) ts1 ts2 )  -- ::  Bool
                in b1 && b2 && (ops_equal || (ops_equiv && types_equal))

{-----------------------------------------------------------
    Minimal Expansions of a Cast Term
-----------------------------------------------------------}
minExpTerm_cast :: Sign -> TERM -> SORT -> Result [[TERM]]
minExpTerm_cast sign term sort = do
    expandedTerm        <- minExpTerm sign term         -- :: [[TERM]]
    validExps           <- return
        $ filter (leq_SORT sign sort . term_sort)       -- ::  [TERM]
        $ map head expandedTerm                         -- ::  [TERM]
    return
        $ qualifyTerms                                  -- :: [[TERM]]
        $ [map (\ t -> (t, sort)) validExps]            -- :: [[(TERM, SORT)]]
    where
        term_sort       :: TERM -> SORT
        term_sort term'  = case term' of
            (Sorted_term _ sort _ )     -> sort
            _                           -> error        -- unlikely
                "minExpTerm: unsorted TERM after expansion"

{-----------------------------------------------------------
    Divide a Set (list) into equivalence classes w.r. to eq
-----------------------------------------------------------}
-- also look below for Till's SML-version of this
equivalence_Classes         :: (a -> a -> Bool) -> [a] -> [[a]]
equivalence_Classes _ []     = []
equivalence_Classes eq (x:l) = xs':(equivalence_Classes eq ys)
    where
        (xs, ys) = partition (eq x) l
        xs'      = (x:xs)

{-----------------------------------------------------------
    Transform a list [l1,l2, ... ln] to (in sloppy notation)
    [[x1,x2, ... ,xn] | x1<-l1, x2<-l2, ... xn<-ln]
-----------------------------------------------------------}
permute      :: [[a]] -> [[a]]
permute []    = [[]]
permute [x]   = map (\y -> [y]) x
permute (x:l) = concat (map (distribute (permute l)) x)
    where
        distribute perms y = map ((:) y) perms

{-----------------------------------------------------------
    Like 'and (zipWith p as bs)',
    but must return False if lengths don't match
-----------------------------------------------------------}
zipped_all                :: (a -> b -> Bool) -> [a] -> [b] -> Bool
zipped_all _ []     []     = True
zipped_all p (a:as) (b:bs) = (p a b) && (zipped_all p as bs)
zipped_all _  _      _     = False

{-----------------------------------------------------------
    Construct a TERM of type Sorted_term
    from each (TERM, SORT) tuple
-----------------------------------------------------------}
qualifyTerms :: [[(TERM, SORT)]] -> [[TERM]]
qualifyTerms  = map (map qualify_term)
    where
        qualify_term       :: (TERM, SORT) -> TERM
        qualify_term (t, s) = Sorted_term t s []

{-----------------------------------------------------------
    For each C in P (see above), let C' choose _one_
    f:s \in C for each s minimal such that f:s \in C
-----------------------------------------------------------}
minimize :: Sign -> [(OpType, [TERM])] -> [(OpType, [TERM])]
minimize sign ops_n_terms
    = concat $ map reduce ops_n_terms
    where
        results        :: Set.Set SORT
        results         = Set.fromList (map (opRes . fst) ops_n_terms)
        lesserSorts    :: SORT -> Set.Set SORT
        lesserSorts s   = Set.intersection results (subsortsOf s sign)
        leastSort      :: SORT -> Bool
        leastSort s     = Set.size (lesserSorts s) == 1
        reduce         :: (OpType, [TERM]) -> [(OpType, [TERM])]
        reduce x@(op,_) = if (leastSort (opRes op)) then [x] else []

{-----------------------------------------------------------
    Return True if s1 <= s2
-----------------------------------------------------------}
leq_SORT :: Sign -> SORT -> SORT -> Bool
leq_SORT sign s1 s2 = Set.member s2 (supersortsOf s1 sign)
-- leq_SORT = (flip Set.member) . (flip supersortsOf)


leqF :: a -> a -> Bool -- Funktionsgleichheit
leqF _ _ = True

leqP :: a -> a -> Bool -- Praedikatsgleichheit
leqP _ _ = True


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

