{- |
Module      :  $Header$
Copyright   :  (c) T.Mossakowski, C.Maeder and Uni Bremen 2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

Parsing lists of lists being MILO (MId-Level Ontology) .kif files
-}

module CASL.Kif2CASL where

import Common.Id
import Common.AS_Annotation
import Common.ToId
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Map as Map
import qualified Text.PrettyPrint.HughesPJ as Doc
import CASL.Kif
import CASL.AS_Basic_CASL
import CASL.Fold
import CASL.Sign
import CASL.Logic_CASL

-- | the universal sort
universe :: SORT
universe = toId "U"

-- | translation of formulas
kif2CASLFormula :: ListOfList -> CASLFORMULA
kif2CASLFormula (List (Literal KToken "and" : phis)) =
  Conjunction (map kif2CASLFormula phis) nullRange
kif2CASLFormula (List (Literal KToken "or" : phis)) =
  Disjunction (map kif2CASLFormula phis) nullRange
kif2CASLFormula (List [Literal KToken "=>", phi1, phi2]) =
  Implication (kif2CASLFormula phi1) (kif2CASLFormula phi2) True nullRange
kif2CASLFormula (List [Literal KToken "<=>", phi1, phi2]) =
  Equivalence (kif2CASLFormula phi1) (kif2CASLFormula phi2) nullRange
kif2CASLFormula (List [Literal KToken "True"]) =
  True_atom nullRange
kif2CASLFormula (List [Literal KToken "False"]) =
  False_atom nullRange
kif2CASLFormula (List [Literal KToken "exists", List vl, phi]) =
  Quantification Existential (kif2CASLvardeclList vl) (kif2CASLFormula phi) nullRange
kif2CASLFormula (List [Literal KToken "forall", List vl, phi]) =
  Quantification Universal (kif2CASLvardeclList vl) (kif2CASLFormula phi) nullRange
kif2CASLFormula (List (Literal KToken p:rest)) =
  Predication (Qual_pred_name (toId p)
               (Pred_type (map (const universe) rest) nullRange) nullRange)
                  (map kif2CASLTerm rest) nullRange
-- also translate 2nd order applications to 1st order, using holds predicate
kif2CASLFormula (List l) =
  Predication (Qual_pred_name (toId "holds")
               (Pred_type (map (const universe) l) nullRange) nullRange)
                  (map kif2CASLTerm l) nullRange
kif2CASLFormula x = error ("kif2CASLFormula : cannot translate" ++
                       show (ppListOfList x))

kif2CASLTerm :: ListOfList -> TERM ()
kif2CASLTerm ll = case ll of
    Literal QWord v -> Qual_var (toSimpleId $ tail v) universe nullRange
    Literal _ s -> Application (Op_name $ toId s) [] nullRange
    List (Literal _ f : args) ->
        Application (Op_name $ toId f) (map kif2CASLTerm args) nullRange
    _ -> error $ "kif2CASLTerm : cannot translate " ++ show (ppListOfList ll)

-- | translation of variable declaration lists
kif2CASLvardeclList :: [ListOfList] -> [VAR_DECL]
kif2CASLvardeclList = map kif2CASLvardecl

-- | translation of variable declarations
kif2CASLvardecl :: ListOfList -> VAR_DECL
kif2CASLvardecl l = case l of
    Literal _ v -> Var_decl [toSimpleId $ tail v] universe nullRange
    _ -> error $ "kif2CASLvardecl " ++ show (ppListOfList l)

-- | first pass of translation, just collecting the formulas
kif2CASLpass1 :: [ListOfList] -> [Annoted CASLFORMULA]
kif2CASLpass1 [] = []
kif2CASLpass1 (phi:rest) =
  (emptyAnno phi') { r_annos = annos } : kif2CASLpass1 rest'
  where phi' = kif2CASLFormula phi
        (annos,rest') = skipComments [] rest

-- | chech for comment
isKifComment (List (Literal KToken "documentation":_)) = True
isKifComment _ = False

-- | convert comment to annotation
toAnno :: ListOfList -> Annotation
toAnno (List (_:l)) =
  Unparsed_anno Comment_start
    (Group_anno [show $ Doc.vcat $ map ppListOfList l]) nullRange
toAnno _ = error "Kif2CASL.toAnno: wrong format of comment"

-- | skip the first comments; they belong to the whole file
skipComments :: [Annotation] -> [ListOfList] -> ([Annotation], [ListOfList])
skipComments acc [] = (reverse acc,[])
skipComments acc l@(x:rest) =
  if isKifComment x
   then skipComments (toAnno x:acc) rest
   else (reverse acc,l)

-- | collect all predicate symbols used in a formula
collectPreds :: CASLFORMULA -> Set.Set PRED_ITEM
collectPreds = foldFormula
    (constRecord (error "Kif2CASL.collectPreds") Set.unions Set.empty)
    { foldPredication = \ _ p l _ -> Set.singleton p }

collectVars :: CASLFORMULA -> Set.Set Token
collectVars = foldFormula
    (constRecord (error "Kif2CASL.collectVars") Set.unions Set.empty)
    { foldQual_var = \ _ v _ _ -> Set.singleton v }

collectConsts :: CASLFORMULA -> Set.Set Id
collectConsts = foldFormula
    (constRecord (error "Kif2CASL.collectConsts") Set.unions Set.empty)
    { foldApplication = \ _ o l _ -> if null l then
          Set.singleton $ case o of
            Op_name i -> i
            Qual_op_name i _ _ -> i else Set.unions l }

-- | main translation function
kif2CASL :: [ListOfList] -> BASIC_SPEC () () ()
kif2CASL l = Basic_spec [empty_anno sorts, ops, preds, vars, axs]
  where (ans,rest) = skipComments [] l
        phis = kif2CASLpass1 rest
        axs = Axiom_items phis nullRange
        preds = Sig_items $ Pred_items preddecls nullRange
        preddecls = Set.toList $ Set.unions $ map (collectPreds . item) phis
        pMap = foldl insertPred Map.empty preds
        sig = (emptySign ()) { sortSet = Set.singleton universe
                             , predMap = pMap}

insertPred :: Map.Map Id (Set.Set PredType) -> PRED_SYMB
               -> Map.Map Id (Set.Set PredType)
insertPred m (Qual_pred_name p (Pred_type t _) _) =
  Map.insertWith Set.union p (Set.singleton (PredType t)) m
