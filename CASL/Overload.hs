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
    = let
      expandedSentences =
          map (minExpTerm sign) sentences
      in
      return expandedSentences

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
  Minimal Expansion of a Sentence
-----------------------------------------------------------}
minExpSentence :: Sign -> Sentence -> [[Sentence]]
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
minExpTerm :: Sign -> TERM -> [[TERM]]
minExpTerm sign term
    = case term of
        Simple_id var
            -> -- var/const definition
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
            -> error $ "Parser Error: Unparsed `Unparsed_term' received: "
               ++ string
        _   -> error $ "Parser Error: Unparsed `Mixfix_whatever' received: "
               ++ (show term)

{-----------------------------------------------------------
  minExpTerm Helper Functions for Special Cases
-----------------------------------------------------------}
minExpTerm_simple :: Sign -> SIMPLE_ID -> [[TERM]]
minExpTerm_simple sign var
    = let const op = null (opArgs op)
          vars = case Map.lookup var (varMap sign) of
                   Nothing -> []
                   Just ss -> Set.elems ss
          ops = case Map.lookup (simpleIdToId var) (opMap sign) of
                  Nothing -> []
                  Just os -> map (opRes) $ Set.elems $ Set.filter (const) os
          all_sorts = (vars ++ ops)
          sorts = filter (leastSort sign all_sorts) all_sorts
          in qualifyTerm $ equivalenceClasses leqF sorts
    where
    leastSort sign sorts x = null $ filter (> x) sorts -- > defined in sign

minExpTerm_qual :: Sign -> VAR -> SORT -> [[TERM]]
minExpTerm_qual sign var sort
    = let expandedVar = minExpTerm_simple sign var
          selectExpansions c = [ (var, sort) |
                                 sorted <- c,
                                 fits sorted ]
          fits (Sorted_term (Simple_id v) s _)
               = (v == var) && (s <= sort)
          in qualifyTerm $ map selectExpansions expandedVar

minExpTerm_sorted :: Sign -> TERM -> SORT -> [[TERM]]
minExpTerm_sorted sign term sort
    = let expandedTerm = minExpTerm sign term
          selectExpansions c = [ (term, sort) |
                                 sorted <- c,
                                 fits sorted ]
          fits (Sorted_term t s _)
               = (t == term) && (s <= sort)
          in qualifyTerm $ map selectExpansions expandedTerm

minExpTerm_op :: Sign -> OP_SYMB -> [TERM] -> [[TERM]]
minExpTerm_op sign op terms
    = let expandedTerms = map minExpTerm sign terms
          expansions = permute expandedTerms
          computeProfile cs
              = map (id . permute) cs
          profiles = map computeProfile expansions

-- -- --
-- ein Problem koennten noch die Definitionen von sort' <= sort und
-- var' == var darstellen, falls ich die noch machen muss.
-- Da hilft wohl auch nur ein beherzter Blick in die fremde source ^^
-- Update: das ist quasi in Common.Lib.Rel gemacht worden :\)


-- Diese Funktionen fehlen in jedem Fall noch und sich ziemlich wichtig:

-- Ouch! This naive Implementation takes quadratic Time!!
minimize :: (Ord a) => Sign -> [a] -> [a]
minimize _ as
    = concat $ map (\a -> if null (filter (<a) as then [a] else []) as

equivalenceClasses :: (a -> a -> Bool) -> [a] -> [[a]]
equivalenceClasses _ [] = []
equivalenceClasses eq (x:l)
    = let (xs, ys) = partition (eq x) l
          xs' = (x:xs)
          in xs':(equiv eq ys)
-- komplexere Implementation: siehe unten, Till's SML-version...

{- Transform a list [l1,l2, ... ln] to
   (in sloppy notation) [[x1,x2, ... ,xn] | x1<-l1, x2<-l2, ... xn<-ln] -}
permute :: [[a]] -> [[a]]
permute [] = [[]]
permute [x] = map (\y -> [y]) x
permute (x:l)
    = concat (map (distribute (permute l)) x)
    where
    distribute perms y = map ((:) y) perms

leqF :: a -> a -> Bool -- Funktionsgleichheit
leqP :: a -> a -> Bool -- Praedikatsgleichheit

-- diverse Ordering Funktionen fuer SORT-Typen
-- sollten innerhalb der Sign definiert werden koennen, vermutlich in
-- sortRel liegend, aber dafuer muss ich Rel besser verstehen fuerchte ich...

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

---

{- 

So sehen meine Datentypen aus
(also nicht meine, sondern die, die ich hier benutze:

Sign == Env
data Env = Env { sortSet :: Set.Set SORT
	       , sortRel :: Rel.Rel SORT	 
               , opMap :: Map.Map Id (Set.Set OpType)
	       , predMap :: Map.Map Id (Set.Set PredType)
               , varMap :: Map.Map SIMPLE_ID (Set.Set SORT)
	       , sentences :: [Named FORMULA]	 
	       , envDiags :: [Diagnosis]
	       } deriving (Show, Eq)


Sentence == FORMULA
siehe AS_Basic fuer FORMULA, TERM und alle darin verwandten Typen

Result is a Monad
-- | The 'Result' monad.  
-- A failing 'Result' should include a 'FatalError' message.
-- Otherwise diagnostics should be non-fatal.
data Result a = Result { diags :: [Diagnosis]
	               , maybeResult :: (Maybe a)
		       } deriving (Show)

instance Functor Result where
    fmap f (Result errs m) = Result errs $ fmap f m
 
instance Monad Result where
  return x = Result [] $ Just x
  Result errs Nothing >>= _ = Result errs Nothing
  Result errs1 (Just x) >>= f = Result (errs1++errs2) y
     where Result errs2 y = f x
  fail s = fatal_error s nullPos

-}
