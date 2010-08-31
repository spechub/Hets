{- |

    Module      :  $Header$
    Description :  Check for truth in one-point model
    Copyright   :  (c) Mingyi Liu and Till Mossakowski and Uni Bremen 2004
    License     :  GPLv2 or higher, see LICENSE.txt

    Maintainer  :  xinga@informatik.uni-bremen.de
    Stability   :  provisional
    Portability :  portable

Check for truth in one-point model
   with all predicates true, all functions total

-}

module CASL.CCC.OnePoint where

import CASL.AS_Basic_CASL
import CASL.Morphism(Morphism, imageOfMorphism)
import CASL.Sign(Sign(sortSet, predMap), supersortsOf, toPredType)

import qualified Data.Map as Map
import qualified Data.Set as Set

{-
We use a three valued logic to evaluate a formula in a one-point expansion
of an unknown arbitrary model. This means that for new sorts and new predicates,
every equation and predicate application holds, but for the old sorts and
predicates, we do not know anything. The three valued logic is represented
with Maybe Bool. It has the following meaning:

         Nothing      * = unknown
         Just True    True
         Jast False   False

The connectives are as follows:

and t f *
t   t f *
f   f f f
*   * f *

or  t f *
t   t t t
f   t f *
*   t * *

implies t f *
t       t f *
f       t t t
*       t * *

equivalent t f *
t          t f *
f          f t *
*          * * *

not t f *
    f t *

(this is just Kleene's strong three-valued logic)
-}

evaluateOnePoint :: Morphism f e m -> [FORMULA f] -> Maybe Bool
evaluateOnePoint m fs =
     let p = map (evaluateOnePointFORMULA (imageOfMorphism m)) fs
     in if elem (Just False) p then  Just False
        else if elem Nothing p then  Nothing
                               else  Just True

{-
evaluateOnePoint :: Morphism f e m-> [FORMULA f] -> Maybe Bool
evaluateOnePoint m fs = do
     p <- mapM (evaluateOnePointFORMULA (imageOfMorphism m)) fs
     return (all id p)
-}


evaluateOnePointFORMULA :: Sign f e -> FORMULA f -> Maybe Bool
evaluateOnePointFORMULA sig (Quantification _ _ f _) =
                      evaluateOnePointFORMULA sig f

evaluateOnePointFORMULA sig (Conjunction fs _) =
     let p = map (evaluateOnePointFORMULA sig) fs
     in if elem (Just False) p then Just False
        else if elem Nothing p then Nothing
                               else Just True

evaluateOnePointFORMULA sig (Disjunction fs _) =
      let p = map (evaluateOnePointFORMULA sig) fs
      in if elem (Just True) p then Just True
         else if elem Nothing p then Nothing
                                else Just False

evaluateOnePointFORMULA sig (Implication f1 f2 _ _) =
        let p1 = evaluateOnePointFORMULA sig f1
            p2 = evaluateOnePointFORMULA sig f2
        in if p1 == Just False || p2 == Just True then Just True
           else if p1 == Just True && p2 == Just False then Just False
                                                       else Nothing

evaluateOnePointFORMULA sig (Equivalence f1 f2 _) =
         let p1 = evaluateOnePointFORMULA sig f1
             p2 = evaluateOnePointFORMULA sig f2
         in if p1 == Nothing || p2 == Nothing then Nothing
            else if p1 == p2 then Just True
                             else Just False

evaluateOnePointFORMULA sig (Negation f _)=
      case evaluateOnePointFORMULA sig f of
       Just True -> Just False
       Just False ->Just True
       _ -> Nothing

evaluateOnePointFORMULA _ (True_atom _) = Just True

evaluateOnePointFORMULA _ (False_atom _) = Just False

evaluateOnePointFORMULA sig (Predication pred_symb _ _) =
     case pred_symb of
       Pred_name _ ->  Nothing
       Qual_pred_name pname ptype _ ->
                case Map.lookup pname (predMap sig) of
                  Nothing -> Just True
                  Just ptypes ->
                    if toPredType ptype `Set.member` ptypes then Nothing
                    else Just True

evaluateOnePointFORMULA sig (Definedness (Sorted_term _ sort _) _) =
      if Set.member sort (sortSet sig) then Nothing else Just True

evaluateOnePointFORMULA sig (Existl_equation (Sorted_term _ sort1 _)
    (Sorted_term _ sort2 _) _) =
        if not (Set.member sort1 (sortSet sig))
             && not (Set.member sort2 (sortSet sig)) then Just True
        else Nothing

evaluateOnePointFORMULA sig (Strong_equation (Sorted_term _ sort1 _)
    (Sorted_term _ sort2 _) _) =
        if not (Set.member sort1 (sortSet sig))
             && not (Set.member sort2 (sortSet sig)) then Just True
        else Nothing

-- todo: auch pruefen, ob Sorte von t in sortSet sig
evaluateOnePointFORMULA sig (Membership (Sorted_term _ sort1 _) sort2 _)=
        if not (Set.member sort1 (sortSet sig))
             && not (Set.member sort2 (sortSet sig)) then Just True
        else Nothing

evaluateOnePointFORMULA _ (Mixfix_formula _) = error "Fehler Mixfix_formula"

evaluateOnePointFORMULA _ (Unparsed_formula _ _)= error
                                                  "Fehler Unparsed_formula"

{-
         compute recover_Sort_gen_ax constr, get (srts,ops,maps)
         check whether all srts are "new" (not in the image of the morphism)
         check whether for all s in srts, there is a term,
           using variables of sorts outside srts
           using operation symbols from ops
         Algorithm:
         construct a list L of "inhabited" sorts
         initially, the list L is empty
         iteration step:
           for each operation symbol in ops, such that
              all argument sorts (opArgs)
                 are either in the list L or are outside srts
              add the results sort (opRes) to the list L of inhabited sorts
         start with initial list, and iterate until iteration is stable
         check whether srts is a sublist of the list resulting from the
         iteration
-}

evaluateOnePointFORMULA sig (Sort_gen_ax constrs _) =
      let (srts,ops,_) = recover_Sort_gen_ax constrs
          sorts = sortSet sig
          argsAndres = concatMap (\ os -> case os of
                                          Op_name _->[]
                                          Qual_op_name _ ot _->
                                            case ot of
                                             Op_type _ args res _->[(args,res)]
                                  ) ops
          iterateInhabited l =
                    if l == newL then newL else iterateInhabited newL
                             where newL = foldr (\ (as,rs) l'->
                                                   if all (\s->elem s l') as
                                                       && notElem rs l'
                                                   then rs:l'
                                                   else l') l argsAndres
    --      inhabited = iterateInhabited []
          inhabited = iterateInhabited $ Set.toList sorts
      in if any (\ s -> Set.member s sorts) srts then Nothing
         else if all (\ s -> elem s inhabited) srts then Just True
              else Nothing

evaluateOnePointFORMULA _ (ExtFORMULA _)=error "Fehler ExtFORMULA"

evaluateOnePointFORMULA _ _=error "Fehler" -- or Just False

-- | Test whether a signature morphism adds new supersorts
addsNewSupersorts :: Morphism f e m -> Bool
addsNewSupersorts m =
    any (\ s -> not $ Set.isSubsetOf (Set.insert s $ supersortsOf s sig) sorts)
       $ Set.toList sorts
       where sig = imageOfMorphism m
             sorts = sortSet sig
{-
check: is there a sort not in the image of the morphism, that is
simultaneously s supersort of a sort that  is in the image.

e.g.
go through all sorts in the image
for each such sort s, comupte supersortsOf s
test whether a supersort is not in the image
if there is such a sort (i.e. supersort not in the image), then return True
otherwise, return False
-}
