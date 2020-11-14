{-# LANGUAGE DeriveGeneric #-}
{- |
Module      :  ./CASL/Kif2CASL.hs
Description :  Parser for SUMO (suggested upper merged ontology) .kif files
Copyright   :  (c) T.Mossakowski, C.Maeder and Uni Bremen 2006
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Parser for SUMO (suggested upper merged ontology) .kif files
-}

module CASL.Kif2CASL where

import Common.AS_Annotation
import Common.Id
import Common.Lexer
import Common.Parsec
import Common.ProofUtils
import Common.Token

import qualified Data.List as List
import qualified Data.HashSet as Set
import qualified Data.HashMap.Strict as Map

import qualified Text.PrettyPrint.HughesPJ as Doc
import Text.ParserCombinators.Parsec

import CASL.Kif
import CASL.AS_Basic_CASL
import CASL.Fold

import GHC.Generics (Generic)
import Data.Hashable

-- | the universal sort
universe :: SORT
universe = toId "U" nullRange

llRange :: RangedLL -> Range
llRange (RangedLL p _ q) = Range [fromSourcePos p, fromSourcePos q]

-- | translation of formulas
kif2CASLFormula :: RangedLL -> CASLFORMULA
kif2CASLFormula rl@(RangedLL _ x _) = let r = llRange rl in case x of
  List (pr@(RangedLL _ (Literal KToken p) _) : phis) -> case (p, phis) of
    ("and", _) -> Junction Con (map kif2CASLFormula phis) r
    ("or", _) -> Junction Dis (map kif2CASLFormula phis) r
    ("=>", [phi1, phi2]) ->
      Relation (kif2CASLFormula phi1) Implication (kif2CASLFormula phi2) r
    ("<=>", [phi1, phi2]) ->
      Relation (kif2CASLFormula phi1) Equivalence (kif2CASLFormula phi2) r
    ("not", [phi]) -> Negation (kif2CASLFormula phi) r
    ("True", []) -> Atom True r
    ("False", []) -> Atom False r
    ("exists", [RangedLL _ (List vl) _, phi]) ->
      Quantification Existential (kif2CASLvardeclList vl) (kif2CASLFormula phi)
      r
    ("forall", [RangedLL _ (List vl) _, phi]) ->
      Quantification Universal (kif2CASLvardeclList vl) (kif2CASLFormula phi)
      r
    ("equal", [t1, t2]) ->
      Equation (kif2CASLTerm t1) Strong (kif2CASLTerm t2) r
    _ -> Predication (Pred_name (toId p $ llRange pr))
      (map kif2CASLTerm phis) r
-- also translate 2nd order applications to 1st order, using holds predicate
  List l -> Predication (Pred_name (toId "holds" r))
                  (map kif2CASLTerm l) r
-- a variable in place of a formula; coerce from Booleans
  Literal k v | elem k [QWord, AtWord] ->
    Equation (Mixfix_token $ toVar v r) Strong trueTerm r
  _ -> error $ "kif2CASLFormula : cannot translate " ++ show x

trueTerm :: TERM ()
trueTerm = varOrConst $ mkSimpleId "True"

falseTerm :: TERM ()
falseTerm = varOrConst $ mkSimpleId "False"

toVar :: String -> Range -> Token
toVar v = toSId $ 'v' : tail v

toId :: String -> Range -> Id
toId s = simpleIdToId . toSId s

-- | convert a string to a legal CASL identifier
toSId :: String -> Range -> Token
toSId s = Token $ case parse (reserved (casl_reserved_words
                                        ++ formula_words) scanAnyWords >> eof)
             "Kif2CASL.toId" s of
    Left _ -> 'a' : concatMap ( \ c -> '_' : Map.findWithDefault [c] c
                              (Map.insert '_' "U" charMap)) s
    Right _ -> s

kif2CASLTerm :: RangedLL -> TERM ()
kif2CASLTerm rl@(RangedLL _ x _) = let r = llRange rl in case x of
    Literal k v | elem k [QWord, AtWord] -> Mixfix_token $ toVar v r
    Literal _ s -> varOrConst $ toSId s r
    -- a formula in place of a term; coerce to Booleans
    List (rf@(RangedLL _ (Literal _ f) _) : args) ->
      if f `elem` ["forall", "exists"] -- ,"and","or","=>","<=>","not"]
       then Conditional trueTerm
         (kif2CASLFormula rl) falseTerm r
        else Application (Op_name $ toId f $ llRange rf)
                 (map kif2CASLTerm args) r
    _ -> error $ "kif2CASLTerm : cannot translate " ++ show (ppRangedLL rl)

-- | translation of variable declaration lists
kif2CASLvardeclList :: [RangedLL] -> [VAR_DECL]
kif2CASLvardeclList = map kif2CASLvardecl

-- | translation of variable declarations
kif2CASLvardecl :: RangedLL -> VAR_DECL
kif2CASLvardecl rl@(RangedLL _ l _) = let r = llRange rl in case l of
    Literal _ v -> Var_decl [toVar v r] universe r
    _ -> error $ "kif2CASLvardecl " ++ show (ppListOfList l)

-- | first pass of translation, just collecting the formulas
kif2CASLpass1 :: [RangedLL] -> [Annoted CASLFORMULA]
kif2CASLpass1 [] = []
kif2CASLpass1 (phi : rest) =
  (emptyAnno phi') { r_annos = annos } : kif2CASLpass1 rest'
  where phi' = kif2CASLFormula phi
        (annos, rest') = skipComments [] rest

-- | check for comment
isKifComment :: ListOfList -> Bool
isKifComment (List (RangedLL _ (Literal KToken "documentation") _ : _)) = True
isKifComment _ = False

-- | convert comment to annotation
toAnno :: ListOfList -> Annotation
toAnno (List (_ : l)) =
  Unparsed_anno Comment_start
    (Group_anno [show $ Doc.vcat $ map ppRangedLL l]) nullRange
toAnno _ = error "Kif2CASL.toAnno: wrong format of comment"

-- | skip the first comments; they belong to the whole file
skipComments :: [Annotation] -> [RangedLL] -> ([Annotation], [RangedLL])
skipComments acc [] = (reverse acc, [])
skipComments acc l@(RangedLL _ x _ : rest) =
  if isKifComment x
   then skipComments (toAnno x : acc) rest
   else (reverse acc, l)

data Predsym = Predsym Int PRED_NAME
                deriving (Eq, Ord, Show, Generic)

instance Hashable Predsym

sameArity :: Predsym -> Predsym -> Bool
sameArity (Predsym m _) (Predsym n _) = m == n

getName :: Predsym -> PRED_NAME
getName (Predsym _ p) = p

-- | collect all predicate symbols used in a formula
collectPreds :: CASLFORMULA -> Set.HashSet Predsym
collectPreds = foldFormula
    (constRecord (error "Kif2CASL.collectPreds") Set.unions Set.empty)
    { foldPredication = \ _ p args _ -> Set.insert
               (Predsym (length args)
                        (case p of
                          Pred_name pn -> pn
                          Qual_pred_name pn _ _ -> pn))
               (Set.unions args) }

collectVars :: CASLFORMULA -> Set.HashSet Token
collectVars = foldFormula
    (constRecord (error "Kif2CASL.collectVars") Set.unions Set.empty)
    { foldMixfix_token = const Set.singleton
    , foldQuantification = \ _ _ vs rs _ ->
        Set.difference rs . Set.fromList
          $ concatMap (\ (Var_decl v _ _) -> v) vs
    }

data Opsym = Opsym Int OP_NAME
                deriving (Eq, Ord, Show, Generic)

instance Hashable Opsym

sameOpArity :: Opsym -> Opsym -> Bool
sameOpArity (Opsym m _) (Opsym n _) = m == n

getOpName :: Opsym -> OP_NAME
getOpName (Opsym _ p) = p

collectOps :: CASLFORMULA -> Set.HashSet Opsym
collectOps = foldFormula
    (constRecord (error "Kif2CASL.collectConsts") Set.unions Set.empty)
    { foldApplication = \ _ o l _ ->
          Set.insert (Opsym (length l) (case o of
            Op_name i -> i
            Qual_op_name i _ _ -> i) )
            (Set.unions l) }

nonEmpty :: Annoted (BASIC_ITEMS () () ()) -> Bool
nonEmpty bi = case item bi of
  Sig_items (Sort_items _ l _) -> not (null l)
  Sig_items (Op_items l _) -> not (null l)
  Sig_items (Pred_items l _) -> not (null l)
  Var_items l _ -> not (null l)
  Axiom_items l _ -> not (null l)
  _ -> True

-- | main translation function
kif2CASL :: [RangedLL] -> BASIC_SPEC () () ()
kif2CASL l = Basic_spec $ filter nonEmpty
                           [(emptyAnno sorts) { l_annos = ans },
                            emptyAnno ops, emptyAnno preds,
                            emptyAnno vars, emptyAnno axs]
  where (ans, rest) = skipComments [] l
        phis = kif2CASLpass1 rest
        axs = Axiom_items phis nullRange
        preds = Sig_items $ Pred_items preddecls nullRange
        predsyms = Set.toList $ Set.unions $ map (collectPreds . item) phis
        preddecls = map (emptyAnno . mkPreddecl)
          $ List.groupBy sameArity predsyms
        mkPreddecl [] = error "kif2CASL: this cannot happen"
        mkPreddecl psyms@(Predsym arity _ : _) =
            Pred_decl (map getName psyms)
              (Pred_type (replicate arity universe) nullRange)
              nullRange
        sorts =
            Sig_items $ Sort_items NonEmptySorts [emptyAnno sortdecl] nullRange
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
