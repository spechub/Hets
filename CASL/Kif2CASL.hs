{- |
Module      :  $Header$
Description :  Parser for SUMO (suggested upper merged ontology) .kif files
Copyright   :  (c) T.Mossakowski, C.Maeder and Uni Bremen 2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Parser for SUMO (suggested upper merged ontology) .kif files
-}

module CASL.Kif2CASL where

import Common.Id
import Common.AS_Annotation
import Common.ToId
import qualified Data.List as List
import qualified Data.Set as Set
import qualified Text.PrettyPrint.HughesPJ as Doc
import CASL.Kif
import CASL.AS_Basic_CASL
import CASL.Fold
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
kif2CASLFormula (List [Literal KToken "not", phi]) =
  Negation (kif2CASLFormula phi) nullRange
kif2CASLFormula (List [Literal KToken "True"]) =
  True_atom nullRange
kif2CASLFormula (List [Literal KToken "False"]) =
  False_atom nullRange
kif2CASLFormula (List [Literal KToken "exists", List vl, phi]) =
  Quantification Existential (kif2CASLvardeclList vl) (kif2CASLFormula phi) nullRange
kif2CASLFormula (List [Literal KToken "forall", List vl, phi]) =
  Quantification Universal (kif2CASLvardeclList vl) (kif2CASLFormula phi) nullRange
kif2CASLFormula (List [Literal KToken "equal",t1,t2]) =
  Strong_equation (kif2CASLTerm t1) (kif2CASLTerm t2) nullRange
kif2CASLFormula (List (Literal KToken p:rest)) =
  Predication (Pred_name (toId p))
                  (map kif2CASLTerm rest) nullRange
-- also translate 2nd order applications to 1st order, using holds predicate
kif2CASLFormula (List l) =
  Predication (Pred_name (toId "holds"))
                  (map kif2CASLTerm l) nullRange
-- a variable in place of a formula; coerce from Booleans
kif2CASLFormula (Literal QWord v) =
  Strong_equation (Simple_id (toVar v))
                  trueTerm
                  nullRange
kif2CASLFormula x = error ("kif2CASLFormula : cannot translate" ++
                       show (ppListOfList x))

trueTerm :: TERM ()
trueTerm = Application (Op_name $ toId "True") [] nullRange

falseTerm :: TERM ()
falseTerm = Application (Op_name $ toId "False") [] nullRange

toVar :: String -> Token
toVar v = toSimpleId $ 'v' : tail v

kif2CASLTerm :: ListOfList -> TERM ()
kif2CASLTerm ll = case ll of
    Literal QWord v -> Simple_id $ toVar v
    Literal _ s -> Application (Op_name $ toId s) [] nullRange
    -- a formula in place of a term; coerce to Booleans
    List (Literal l f : args) ->
      if f `elem` ["forall","exists"] -- ,"and","or","=>","<=>","not"]
       then Conditional trueTerm 
                (kif2CASLFormula (List (Literal l f : args))) falseTerm nullRange
        else Application (Op_name $ toId f) (map kif2CASLTerm args) nullRange
    _ -> error $ "kif2CASLTerm : cannot translate " ++ show (ppListOfList ll)

-- | translation of variable declaration lists
kif2CASLvardeclList :: [ListOfList] -> [VAR_DECL]
kif2CASLvardeclList = map kif2CASLvardecl

-- | translation of variable declarations
kif2CASLvardecl :: ListOfList -> VAR_DECL
kif2CASLvardecl l = case l of
    Literal _ v -> Var_decl [toVar v] universe nullRange
    _ -> error $ "kif2CASLvardecl " ++ show (ppListOfList l)

-- | first pass of translation, just collecting the formulas
kif2CASLpass1 :: [ListOfList] -> [Annoted CASLFORMULA]
kif2CASLpass1 [] = []
kif2CASLpass1 (phi:rest) =
  (emptyAnno phi') { r_annos = annos } : kif2CASLpass1 rest'
  where phi' = kif2CASLFormula phi
        (annos,rest') = skipComments [] rest

-- | chech for comment
isKifComment :: ListOfList -> Bool
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

data Predsym = Predsym Int PRED_NAME
                deriving (Eq, Ord, Show)

sameArity :: Predsym -> Predsym -> Bool
sameArity (Predsym m _) (Predsym n _) = m==n

getName :: Predsym -> PRED_NAME
getName (Predsym _ p) = p

-- | collect all predicate symbols used in a formula
collectPreds :: CASLFORMULA -> Set.Set Predsym
collectPreds = foldFormula
    (constRecord (error "Kif2CASL.collectPreds") Set.unions Set.empty)
    { foldPredication = \ _ p args _ -> Set.insert 
               (Predsym (length args) 
                        (case p of
                          Pred_name pn -> pn
                          Qual_pred_name pn _ _ -> pn))
               (Set.unions args) }

collectVars :: CASLFORMULA -> Set.Set Token
collectVars = foldFormula
    (constRecord (error "Kif2CASL.collectVars") Set.unions Set.empty)
    { foldSimpleId = \ _ v -> Set.singleton v }

data Opsym = Opsym Int OP_NAME
                deriving (Eq, Ord, Show)

sameOpArity :: Opsym -> Opsym -> Bool
sameOpArity (Opsym m _) (Opsym n _) = m==n

getOpName :: Opsym -> OP_NAME
getOpName (Opsym _ p) = p

collectOps :: CASLFORMULA -> Set.Set Opsym
collectOps = foldFormula
    (constRecord (error "Kif2CASL.collectConsts") Set.unions Set.empty)
    { foldApplication = \ _ o l _ -> 
          Set.insert (Opsym (length l) (case o of
            Op_name i -> i
            Qual_op_name i _ _ -> i) )
            (Set.unions l) }

nonEmpty :: Annoted (BASIC_ITEMS () () ()) -> Bool
nonEmpty bi = case item bi of
  Sig_items (Sort_items l _) -> not (null l)
  Sig_items (Op_items l _) -> not (null l)
  Sig_items (Pred_items l _) -> not (null l)
  Var_items l _ -> not (null l)
  Axiom_items l _ -> not (null l)
  _ -> True

-- | main translation function
kif2CASL :: [ListOfList] -> BASIC_SPEC () () ()
kif2CASL l = Basic_spec $ filter nonEmpty 
                           [(emptyAnno sorts) { l_annos = ans }, 
                            emptyAnno ops, emptyAnno preds, 
                            emptyAnno vars, emptyAnno axs]
  where (ans,rest) = skipComments [] l
        phis = kif2CASLpass1 rest
        axs = Axiom_items phis nullRange
        preds = Sig_items $ Pred_items preddecls nullRange
        predsyms = Set.toList $ Set.unions $ map (collectPreds . item) phis
        preddecls = map (emptyAnno . mkPreddecl) (List.groupBy sameArity predsyms)
        mkPreddecl [] = error "kif2CASL: this cannot happen"
        mkPreddecl psyms@(Predsym arity _:_) = 
           Pred_decl (map getName psyms) 
                     (Pred_type (replicate arity universe) nullRange)
                     nullRange
        sorts = Sig_items $ Sort_items [emptyAnno sortdecl] nullRange
        sortdecl = Sort_decl [universe] nullRange
        ops = Sig_items $ Op_items opdecls nullRange
        opsyms = Set.toList $ Set.unions $ map (collectOps . item) phis
        opdecls = map (emptyAnno . mkOpdecl) (List.groupBy sameOpArity opsyms)
        mkOpdecl [] = error "kif2CASL: this cannot happen"
        mkOpdecl opsms@(Opsym arity _ : _) = 
           Op_decl (map getOpName opsms) 
             (Op_type Total (replicate arity universe) universe nullRange)
                   [] nullRange
        usedVars = Set.toList $ Set.unions $ map (collectVars . item) phis
        vars = Var_items (if null usedVars then []
                           else [Var_decl usedVars universe nullRange])
                         nullRange

