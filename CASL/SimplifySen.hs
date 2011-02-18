{- |
Module      :  $Header$
Description : simplification of formulas and terms for output after analysis
Copyright   :  (c) Heng Jiang, C. Maeder, Uni Bremen 2004-2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Simplification of formulas and terms for output after analysis

-}

module CASL.SimplifySen
  ( simplifyCASLSen
  , simplifyCASLTerm
  , simplifySen
  , simplifyTerm
  , rmTypesT
  ) where

import Common.AS_Annotation
import Common.Id
import Common.Result
import Common.DocUtils
import Common.Lib.State
import CASL.Sign
import CASL.AS_Basic_CASL
import CASL.Overload
import CASL.StaticAna

{- | simplifies formula\/term informations for 'show theory' of
   HETS-graph representation.  -}
simplifyCASLSen :: Sign () e -> FORMULA () -> FORMULA ()
simplifyCASLSen = simplifySen dummyMin dummy

simplifyCASLTerm :: Sign () e -> TERM () -> TERM ()
simplifyCASLTerm = simplifyTerm dummyMin dummy

simplifySen :: (GetRange f, Pretty f, TermExtension f)
  => (Min f e) -- ^ extension type analysis
    -> (Sign f e -> f -> f) -- ^ simplifySen for ExtFORMULA
    -> Sign f e -> FORMULA f -> FORMULA f
simplifySen minF simpF sign formula =
    case formula of
    Quantification q vars f pos ->
            -- add 'vars' to signature
           let sign' = execState (mapM_ addVars vars) sign
           in Quantification q vars (simplifySen minF simpF sign' f) pos
    Conjunction fs pos -> Conjunction (map simplifySenCall fs) pos
    Disjunction fs pos -> Disjunction (map simplifySenCall fs) pos
    Implication f1 f2 bool pos ->
        Implication (simplifySenCall f1) (simplifySenCall f2) bool pos
    Equivalence f1 f2 pos ->
        Equivalence (simplifySenCall f1) (simplifySenCall f2) pos
    Negation f pos ->  Negation (simplifySenCall f) pos
    True_atom x -> True_atom x
    False_atom x -> False_atom x
    f@(Predication _ _ _) -> anaFormulaCall f
    Definedness t pos -> Definedness (simplifyTermC t) pos
    f@(Existl_equation _ _ _) -> anaFormulaCall f
    f@(Strong_equation _ _ _) -> anaFormulaCall f
    Membership t sort pos -> Membership (simplifyTermC t) sort pos
    ExtFORMULA f -> ExtFORMULA $ simpF sign f
    QuantOp o ty f ->
        let sign' = execState (addOp (emptyAnno ()) (toOpType ty) o) sign
        in QuantOp o ty $ simplifySen minF simpF sign' f
    QuantPred p ty f ->
        let sign' = execState (addPred (emptyAnno ()) (toPredType ty) p) sign
        in QuantPred p ty $ simplifySen minF simpF sign' f
    f@(Sort_gen_ax _ _) -> f
    _ -> error "simplifySen"
    where
        simplifySenCall = simplifySen minF simpF sign
        simplifyTermC = simplifyTerm minF simpF sign
        anaFormulaCall = anaFormula minF simpF sign

-- | remove a sort annotation
rmSort :: TERM f -> TERM f
rmSort term = case term of
         Sorted_term t _ _ -> t
         _ -> term

{- |
   simplifies the term and removes its type-information as far as the signature
   allows
-}
rmTypesT :: (GetRange f, Pretty f, TermExtension f)
  => Min f e -> (Sign f e -> f -> f) -> Sign f e -> TERM f -> TERM f
rmTypesT minF simpF sign term =
    let simTerm = simplifyTerm minF simpF sign term
        minTerm = rmSort simTerm
    in case maybeResult $ oneExpTerm minF sign minTerm of
       Just _ -> minTerm
       _ -> simTerm

{- |
   simplify the TERM and keep its typing information if it had one
-}
simplifyTerm :: (GetRange f, Pretty f, TermExtension f)
  => Min f e -> (Sign f e -> f -> f) -> Sign f e -> TERM f -> TERM f
simplifyTerm minF simpF sign term =
    let simplifyTermC = simplifyTerm minF simpF sign
        minT = maybeResult . oneExpTerm minF sign
    in case term of
       Qual_var v _ _ ->
           let minTerm = Application (Op_name $ simpleIdToId v) [] nullRange
           in case minT minTerm of
              Just _ -> minTerm
              Nothing -> term
       Sorted_term t sort pos ->
           simplifyTermWithSort minF simpF sign sort pos t
       Conditional term1 formula term2 pos ->
           let t1 = simplifyTermC term1
               t2 = simplifyTermC term2
               f = simplifySen minF simpF sign formula
               minCond = Conditional (rmSort t1) f (rmSort t2) pos
           in case minT minCond of
              Just _ -> minCond
              Nothing -> Conditional t1 f t2 pos
       Cast t sort pos -> Cast (rmTypesT minF simpF sign t) sort pos
       Application opSymb@(Op_name _) ts pos ->
           -- assume arguments of unqualified appls are simplified already
           let minOp = Application opSymb (map rmSort ts) pos
           in case minT minOp of
              Just _ -> minOp
              Nothing -> term
       Application q@(Qual_op_name ide ty ps) tl pos ->
           let args = zipWith (\ t s -> simplifyTermWithSort minF simpF sign
                               s ps t) tl $ args_OP_TYPE ty
               opSymb = Op_name ide
               minArgs = map rmSort args
               minOp = Application opSymb minArgs pos
               simT = simplifyTermWithSort minF simpF sign
                         (res_OP_TYPE ty) ps
                         $ Application opSymb args pos
           in case minT minOp of
              Just _ -> minOp
              Nothing -> if null args then case minT simT of
                 Just _ -> simT
                 _ -> Application q [] pos
                 else simT
       _ -> term

{- |
   simplify the TERM with given sort and attach sort if necessary
-}
simplifyTermWithSort :: (GetRange f, Pretty f, TermExtension f)
  => Min f e -> (Sign f e -> f -> f) -> Sign f e -> SORT -> Range -> TERM f
    -> TERM f
simplifyTermWithSort minF simpF sign gSort poss term =
    let simplifyTermCS = simplifyTermWithSort minF simpF sign gSort poss
        simplifyTermC = simplifyTerm minF simpF sign
        minT = maybeResult . oneExpTerm minF sign
    in case term of
       Qual_var v _ _ ->
           let minTerm = Application (Op_name $ simpleIdToId v) [] nullRange
               simT = Sorted_term minTerm gSort poss
           in case minT simT of
                  Just _ -> simT
                  _ -> term
       Sorted_term t sort pos ->
           let simT = simplifyTermCS t
           in case minT simT of
                   Just _ -> simT
                   Nothing -> Sorted_term (rmSort $
                               simplifyTermWithSort minF simpF sign sort pos t)
                              sort pos
       Conditional term1 formula term2 pos ->
           let t1 = simplifyTermCS term1
               t2 = simplifyTermCS term2
               f = simplifySen minF simpF sign formula
               minCond = Conditional (rmSort t1) f (rmSort t2) pos
           in case minT minCond of
              Just _ -> minCond
              Nothing -> Sorted_term minCond gSort poss
       Cast t sort pos -> Cast (rmTypesT minF simpF sign t) sort pos
       Application opSymb@(Op_name _) ts pos ->
           -- assume arguments of unqualified appls are simplified already
           let minOp = Application opSymb (map rmSort ts) pos
           in case minT minOp of
              Just _ -> minOp
              Nothing -> case minT term of
                  Just _ -> term
                  Nothing -> Sorted_term term gSort poss
       Application (Qual_op_name _ ty _) _ _ ->
           let simT = simplifyTermC term in
           if gSort == res_OP_TYPE ty then
              simT else
           let minOp = Sorted_term (rmSort simT) gSort poss
           in case minT minOp of
              Just _ -> minOp
              Nothing -> Sorted_term simT gSort poss
       _ -> term

{- |
    analyzes the formula if it is the minimal expansions.
-}
anaFormula :: (GetRange f, Pretty f, TermExtension f)
  => Min f e -> (Sign f e -> f -> f) -> Sign f e -> FORMULA f -> FORMULA f
anaFormula minF simpF sign form1 =
    let minForm = maybeResult . minExpFORMULA minF sign
        simplifyTermC = simplifyTerm minF simpF sign
        simpForm = case form1 of
            Existl_equation t1 t2 pos -> Existl_equation
              (simplifyTermC t1) (simplifyTermC t2) pos
            Strong_equation t1 t2 pos -> Strong_equation
              (simplifyTermC t1) (simplifyTermC t2) pos
            _ -> error "anaFormula1"
        rmForm = case simpForm of
            Existl_equation t1 t2 pos -> Existl_equation
              (rmSort t1) (rmSort t2) pos
            Strong_equation t1 t2 pos -> Strong_equation
              (rmSort t1) (rmSort t2) pos
            _ -> error "anaFormula2"
     in case form1 of
        Predication predSymb@(Pred_name _) tl pos ->
           let minPred = Predication predSymb (map rmSort tl) pos
           in case minForm minPred of
              Just _ -> minPred
              Nothing -> form1
        Predication (Qual_pred_name pName (Pred_type sl ps) _) tl pos ->
           let args = zipWith (\ t s -> simplifyTermWithSort
                               minF simpF sign s ps t) tl sl
               predSymb = Pred_name pName
               minPred = Predication predSymb (map rmSort args) pos
           in case minForm minPred of
              Just _ -> minPred
              Nothing -> Predication predSymb args pos
        _ -> case minForm rmForm of
             Just _ -> rmForm
             _ -> simpForm
