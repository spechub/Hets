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

-- -- -- die Hauptfunktion, macht aus Formeln ... Formeln :\)

-- overloadResolution :: Sign -> [Sentence] -> Result [Sentence]
-- overloadResolution sign sents =
--     return [ minExpTerm sign atom | atom <- (concat $ map getAtoms sents) ]
-- -- TODO: den Rest implementieren und dann hier auf Fehler testen

-- -- Nimmt Formulae auseinander und gibt eine Liste der
-- -- zugrundeliegenden atomaren Formulae zurueck. 
-- -- ... oder eher der zugrundeliegenden atomaren Terme?
-- -- Idee: nimmt eine zusammengesetzte Formel auseinander und durchsucht
-- -- die erhaltenen Formeln weiter nach Atomen.
-- -- Nicht-zusammengesetzte Formeln sind atomar und werden (in eine
-- -- Liste verpackt) zurueckgegeben.
-- getAtoms :: Sentence -> [Sentence]
-- getAtoms (Quantification _ _ sentence _) = getAtoms sentence
-- getAtoms (Conjunction sentences _) = getAllAtoms sentences
-- getAtoms (Disjunction sentences _) = getAllAtoms sentences
-- getAtoms (Implication sent1 sent2 _) = getAllAtoms [sent1, sent2]
-- getAtoms (Equivalence sent1 sent2 _) = getAllAtoms [sent1, sent2]
-- getAtoms (Negation sentence _) = getAtoms sentence
-- -- entweder: es gibt sentences zurueck
-- getAtoms sentence = [sentence]
-- -- oder: es gibt terme zurueck
-- -- getAtoms (Predication _ terms _) = terms
-- -- getAtoms (Definedness term _) = [term]
-- -- getAtoms (Existl_equation term1 term2 _) = [term1, term2]
-- -- getAtoms (Strong_equation term1 term2 _) = [term1, term2]
-- -- getAtoms (Membership term _ _) = [term]
-- -- getAtoms (Mixfix_formula term) = term
-- -- getAtoms Unparsed_formula _ _) = [] -- da solltsn Fehler gebn
-- -- -- es fehlen noch: True_atom und False_atom ... was mach ich mit denen?
--     where
--     getAllAtoms = concat . (map getAtoms)

-- -- das hier ist die, die eine Formel erwartet - ich muss noch pruefen,
-- -- ob sich das lohnt oder ob ich nicht die Terme selbst direkt
-- -- weiterreichen sollte ... andererseite hab ich das Gefuehl, dass
-- -- dann einige Sachen fehlen wuerden...
-- minExpTerm :: Sign -> Sentence -> [[Sentence]]
-- -- Ergebnistyp: Aequivalanzklassen von irgendwas...
-- minExpTerm sign sentence =
--     case sentence of
--                   True_atom [Pos] -> [["true", "_bool"]]
--  	          False_atom [Pos] -> [["false", "_bool"]]
--  	          Predication PRED_SYMB [TERM] [Pos] -> 
--  	          Definedness TERM [Pos] -> 
--  	          Existl_equation TERM TERM [Pos] -> 
--  	          Strong_equation TERM TERM [Pos] -> 
--  	          Membership TERM SORT [Pos] -> 
--  	          Mixfix_formula TERM  -> 
--                   Unparsed_formula String [Pos] -> 
--                   _ -> 
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
-- minExpTerm_ sign (Simple_id var) = minExpTerm_simple sign var
-- minExpTerm_ sign (Qual_var var sort _) = minExpTerm_qual sign var sort
-- minExpTerm_ sign (Sorted_term term sort _) = minExpTerm_sorted sign term sort
-- -- wie unterscheidet sich das von Qual_var???
-- minExpTerm_ sign (Application op terms _) = minExpTerm_op sign op terms
-- -- bei den restlichen bin ich nicht sicher, wie sie mit den
-- -- dokumentierten Faellen vereinbar sind bzw. ihnen entsprechen, und
-- -- also auch nicht, was ich damit machen soll.
-- -- -- meine Tastatur is zu hart und mein kleiner Finger tut weh :\( --
-- -- das da oben im Smiley ist kein Tippfehler, die Klammer verwirrt
-- -- Emacs ^_^
-- minExpTerm_ sign _ = [[]]
-- -- restliche, fehlende Faelle sind:
-- -- Cast term sort _
-- -- Conditional term1 formula term2 _
-- -- Unparsed_term string _
-- -- mehrere Mixfix-Teile bei denen ich mir nicht sicher bin, was sie
-- -- sein sollen und was ich mit ihnen anfangen koennen soll...

-- -- -- Die Hilfsfunktionen fuer minExpTerm, je nach Typ des Terms

-- minExpTerm_simple sign var =
--     let 
--     my_consts = [ (var, sort) | (var', sort) <- (varMap sign), var' == var ]
--     my_funcs = [ (var, sort) | (var', sort) <- (opMap sign), var' == var ]
--     my_subset = (minimize sign) (my_consts ++ my_funcs)
--     in equiv leqF my_subset
-- minExpTerm_qual sign var sort =
--     let
--     met_var = minExpTerm_simple sign var
--     make_met = \c -> [ (var, sort) |
--                        (var', sort') <- c, sort' <= sort, var' == var ]
--     in map make_met met_var
-- minExpTerm_sorted sign term sort =
--     let
--     met_var = minExpTerm sign term -- ist das der einzige Unterschied?
--     make_met = \c -> [ (term, sort) |
--                        (term', sort') <- c, sort' <= sort, term' == term ]
--     in map make_met met_var
-- minExpTerm_op sign op terms = [[]]
-- -- the lean mean difficulty machine :\)
-- -- das gilt, nehme ich an, auch als Fall fuer Praedikat-Applikation?
-- -- dafuer sehe ich naemlich ansonsten keinen anderen...
-- -- -- --
-- -- ein Problem koennten noch die Definitionen von sort' <= sort und
-- -- var' == var darstellen, falls ich die noch machen muss.
-- -- Da hilft wohl auch nur ein beherzter Blick in die fremde source ^^


-- -- Diese Funktionen fehlen in jedem Fall noch und sich ziemlich wichtig:
-- minimize :: Sign -> [TERM] -> [TERM] -- minimiert
-- equiv :: (a -> a -> Bool) -> [a] -> [[a]] -- Aequivalenzklassen
-- leqF :: a -> a -> Bool -- Funktionsgleichheit
-- leqP :: a -> a -> Bool -- Praedikatsgleichheit

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
