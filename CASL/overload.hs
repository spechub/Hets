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

import CASL.StaticAnalysis -- Sign, Sentence = FORMULA
import CASL.AS_Basic -- FORMULA
import Common.Result -- Result

{-

Idee: 
- global Infos aus Sign berechnen + mit durchreichen
  (connected compenents, s.u.)
- rekursiv in Sentence absteigen, bis atomare Formel erreicht wird
- atomaren Formeln mit MinExpTerm behandeln

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
  Minimal Expansion of a Sentence
-----------------------------------------------------------}
{- descend recursively into sentences if sentence is non-atomic
   expand atomic sentence otherwise
   TODO: how to construct the complete, qualified sentence from
   the results? -}
minExpTerm :: Sign -> Sentence -> [[Sentence]]
minExpTerm sign sentence
    = case sentence of
        Quantification _ _ sentence' _ -> minExpTerm sign sentence'
        Conjunction sentences _        -> minExpTermAll sentences
        Disjunction sentences _        -> minExpTermAll sentences
        Implication sent1 sent2 _      -> minExpTermAll [sent1, sent2]
        Equivalence sent1 sent2 _      -> minExpTermAll [sent1, sent2]
        Negation sentence' _           -> minExpTerm sign sentence'
        True_atom _                    -> -- [["True", "_bool"]]
        False_atom _                   -> -- [["False", "_bool"]]
        Predication PRED_SYMB [TERM] _ -> -- predicate application
        Definedness TERM _             -> -- see till's mail
        Existl_equation TERM TERM _    -> -- ?
        Strong_equation TERM TERM _    -> -- ?
        Membership TERM SORT _         -> -- ?
        Mixfix_formula _               -> -- parser error - bail out?
        Unparsed_formula _ _           -> -- parser error - bail out?
    where
    minExpTermAll = map (minExpTerm sign)

{-----------------------------------------------------------
  Minimal Expansion of a Term
-----------------------------------------------------------}
minExpTerm_ :: Sign -> TERM -> [[TERM]]
minExpTerm_ sign term
    = case term of
        Simple_id var           -> minExpTerm_simple sign var
        Qual_var var sort _     -> minExpTerm_qual sign var sort
        Sorted_term term sort _ -> minExpTerm_sorted sign term sort
        Application op terms _  -> minExpTerm_op sign op terms
        -- wie unterscheidet sich das von Qual_var???
        _                       -> -- parser error - bail out?
{- restliche, fehlende Faelle sind:
   Cast term sort _
   Conditional term1 formula term2 _
   Unparsed_term string _
   mehrere Mixfix-Teile bei denen ich mir nicht sicher bin, was sie
   sein sollen und was ich mit ihnen anfangen koennen soll... -}

-- -- -- Die Hilfsfunktionen fuer minExpTerm, je nach Typ des Terms

{-----------------------------------------------------------
  minExpTerm Helper Functions for Special Cases
-----------------------------------------------------------}
minExpTerm_simple sign var =
let 
    my_consts = [ (var, sort) | (var', sort) <- (varMap sign), var' == var ]
    my_funcs = [ (var, sort) | (var', sort) <- (opMap sign), var' == var ]
    my_subset = (minimize sign) (my_consts ++ my_funcs)
    in equiv leqF my_subset
minExpTerm_qual sign var sort =
    let
    met_var = minExpTerm_simple sign var
    make_met = \c -> [ (var, sort) |
                       (var', sort') <- c, sort' <= sort, var' == var ]
    in map make_met met_var
minExpTerm_sorted sign term sort =
    let
    met_var = minExpTerm sign term -- ist das der einzige Unterschied?
    make_met = \c -> [ (term, sort) |
                       (term', sort') <- c, sort' <= sort, term' == term ]
    in map make_met met_var
minExpTerm_op sign op terms = [[]]
-- the lean mean difficulty machine :\)
-- das gilt, nehme ich an, auch als Fall fuer Praedikat-Applikation?
-- dafuer sehe ich naemlich ansonsten keinen anderen...
-- -- --
-- ein Problem koennten noch die Definitionen von sort' <= sort und
-- var' == var darstellen, falls ich die noch machen muss.
-- Da hilft wohl auch nur ein beherzter Blick in die fremde source ^^


-- Diese Funktionen fehlen in jedem Fall noch und sich ziemlich wichtig:
minimize :: Sign -> [TERM] -> [TERM] -- minimiert

equiv :: (a -> a -> Bool) -> [a] -> [[a]] -- Aequivalenzklassen
-- naive Implementation:
equiv _ [] = []
equiv eq (x:xs) = let
                  (xs', ys) = partition (eq x) xs
                  in xs':(equiv eq ys)
-- komplexere Implementation: siehe unten, Till's SML-version

{- Transform a list [l1,l2, ... ln] to
   (in sloppy notation) [[x1,x2, ... ,xn] | x1<-l1, x2<-l2, ... xn<-ln] -}
permute :: [[a]] -> [[a]]
permute [] = [[]]
permute [x] = map (\y -> [y]) x
permute (x:l) =
    concat (map (distribute (permute l)) x)
    where
    distribute perms y = map ((:) y) perms

leqF :: a -> a -> Bool -- Funktionsgleichheit
leqP :: a -> a -> Bool -- Praedikatsgleichheit

-- diverse Ordering Funktionen fuer SORT-Typen

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
