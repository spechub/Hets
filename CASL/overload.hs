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
TODO: All das hier implementieren und testen :D
-}

-- overloadResolution :: Sign -> [Sentence] -> [Sentence] -- Result [Sentence]
-- overloadResolution sign sents =
--     [ minExpTerm sign atom | atom <- (concat $ map getAtoms sents) ]
-- -- TODO: das hier in Result  verpacken und natuerlich vorher auf
-- -- Fehler pruefen
-- -- ... und natuerlich voerher sinnvollerweise implementieren :)

-- -- Nimmt Formulae auseinander und gibt eine Liste der
-- -- zugrundeliegenden atomaren Formulae zurueck.
-- -- Idee: nimmt eine zusammengesetzte Formel auseinander und durchsucht
-- -- die erhaltenen Formeln weiter nach Atomen.
-- -- Nicht-zusammengesetzte Formeln sind atomar und werden (in eine
-- -- Liste verpackt) zurueckgegeben.
-- getAtoms :: Sentence -> [Sentence]
-- getAtoms sentence =
--     case sentence of
--         Quantification _ _ sent' _ -> getAtoms sent'
--         Conjunction sents _        -> concat $ map getAtoms sents
--         Disjunction sents _        -> concat $ map getAtoms sents
--         Implication s1 s2 _        -> concat [getAtoms s1, getAtoms s2]
--         Equivalence s1 s2 _        -> concat [getAtoms s1, getAtoms s2]
--         Negation sent' _           -> getAtoms sent'
--         _                          -> [sentence]
-- -- na, ob das wohl soweit stimmt... ?

-- -- das hier ist die, die eine Formel erwartet - ich muss noch pruefen,
-- -- ob sich das lohnt oder ob ich nicht die Terme selbst direkt
-- -- weiterreichen sollte ... andererseite hab ich das Gefuehl, dass
-- -- dann einige Sachen fehlen wuerden...
-- minExpTerm :: Sign -> Sentence -> [[Sentence]]
-- -- Ergebnistyp: Aequivalanzklassen von irgendwas...
-- minExpTerm sign sentence =
--     case sentence of
-- 	True_atom [Pos] -> 
-- 	False_atom [Pos] -> 
-- 	Predication PRED_SYMB [TERM] [Pos] -> 
-- 	Definedness TERM [Pos] -> 
-- 	Existl_equation TERM TERM [Pos] -> 
-- 	Strong_equation TERM TERM [Pos] -> 
-- 	Membership TERM SORT [Pos] -> 
-- 	Mixfix_formula TERM  -> 
--         Unparsed_formula String [Pos] -> 
--         _ -> 
-- -- so ... und was fang ich jetzt damit an? -- Tja, das ist hier die Frage

-- -- die hier, alternativ, nimmt einen Term und zerlegt/erweitert
-- -- diesen. Das sollte bewirken, dass ich direkt ueber den fuer den
-- -- algo relevanten Typen eine Fallunterscheidung machen kann und somit
-- -- eine rekursionsebene spare, wenn ich terme direkt runterwerfe. In
-- -- jedem fall brauche ich diese funktion, als haupt-finktion oder als
-- -- helfer, damit ich die unterschiedlichen Terme einfach unterscheiden
-- -- kann.
-- -- wobei mir gerade auffaellt, dass ich die fallunterscheidung auch
-- -- direkt als pattern-matching gemacht haben koennte, also:
-- -- TODO: case .. of umschreiben als pattern-matching
-- minExpTerm_ :: Sign -> TERM -> [[TERM]]
-- minExpTerm_ sign term =
--     case term of
--               Simple_id var ->
--                   let
--                   consts = [ (var,sort) | 
--                              (var',sort) <- (varMap sign), 
--                              var' == var
--                            ]
--                   funcs = [ (var,sort) |
--                             (var',sort) <- (opMap sign),
--                             var' == var
--                           ]
--                   in equiv leqn_f $ minimize $ consts ++ funcs
--               Qual_var var sort _ ->
--                   let
--                   met_t = minExpTerm_ sign var
--                   met_ts c = [ (t,s) | (t,s') <- c, s' <= s ]
--                   met_ts' = map met_ts met_t
--                   in met_ts'
--               Sorted_term term sort _ ->
--                   let
--                   met_t = minExpTerm_ sign var
--                   met_ts c = [ (t,s) | (t,s') <- c, s' <= s ]
--                   met_ts' = map met_ts met_t
--                   in met_ts'
--                   -- oder ist da ein Unterschied, den ich beachten muss?
--               Application op terms _ -> [[]]
--               -- das gilt, nehme ich an, auch als Fall fuer
--               -- Praedikat-Applikation? dafuer sehe ich naemlich
--               -- ansonsten keinen anderen...
--               Cast term sort _ -> [[]]
--               Conditional term formula term _ -> [[]]
--               -- da muss ich dann wohl wieder die formel in atome zerlegen?
--               Unparsed_term str _ -> [[]] 
--               -- na was fuer den Fall wohl richtig sein soll...
--               _ -> [[]]
--               -- Das muss dann wohl ein Mixfix sein ...
--               -- was auch immer zum Henker das sein mag.
--               -- naja, find ich schon noch raus... ^^


{-
Idee: 
- global Infos aus Sign berechnen + mit durchreichen
  (connected compenents, s.u.)
- rekursiv in Sentence absteigen, bis atomare Formel erreicht wird
- atomaren Formeln mit MinExpTerm behandeln

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

Sign == Env and looks like this:
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

Result is a Monad and looks like this:
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
