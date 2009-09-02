{- |
Module      :  $Header$
Description :  Hets-to-OMDoc conversion
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  ewaryst.schulz@dfki.de
Stability   :  provisional
Portability :  non-portable(Logic)

CASL implementation of the interface functions export_signToOmdoc,
export_morphismToOmdoc, export_senToOmdoc from class Logic. The actual
instantiation can be found in module CASL.Logic_CASL.
-}

module CASL.OMDoc
    ( exportSignToOmdoc
    , exportMorphismToOmdoc
    , exportSenToOmdoc
    , omdocMetaTheory
    ) where

import OMDoc.DataTypes

import Common.AS_Annotation
import Common.Id
import Common.LibName
import Common.Result

import Common.DocUtils

import CASL.AS_Basic_CASL
import CASL.ATC_CASL ()
import CASL.Sign
import CASL.Morphism
import CASL.Fold
import CASL.Quantification

import Data.Map as Map
import Data.Set as Set

-- | the identifier of a specification, combining the specid and the libid
data SPEC_ID = SPEC_ID Id Id | NOSPEC deriving Show

omdocMetaTheory :: Maybe OMCD
omdocMetaTheory = Just $ CD "casl" $ Just "http://cds.omdoc.org/logics/casl.omdoc"


exportSignToOmdoc ::  (Show f, Pretty e) => SIMPLE_ID -> LIB_ID -> Sign f e ->
                      [TCElement]
exportSignToOmdoc sid lid sign =
    [TCComment $ "Signature of Spec: " ++ (show spid)]
 ++ Set.toList (Set.map (sortSignToOmdoc spid sign) (sortSet sign))
 ++ Map.elems (mapWithKey (funSignToOmdoc spid sign) (opMap sign))
 ++ Map.elems (mapWithKey (predSignToOmdoc spid sign) (predMap sign))
     where spid = (SPEC_ID (simpleIdToId sid) (libIdToId lid))


exportMorphismToOmdoc :: Morphism f e m -> TCElement
--exportMorphismToOmdoc morphism = []
--exportMorphismToOmdoc _ = error "not implemented yet"
exportMorphismToOmdoc (Morphism _ _ sortmap opmap predmap _) =
    TCMorphism $ Map.elems (mapWithKey (makeSortMapEntry NOSPEC) sortmap)
              ++ Map.elems (mapWithKey (makeOpMapEntry NOSPEC) opmap)
              ++ Map.elems (mapWithKey (makePredMapEntry NOSPEC) predmap)


exportSenToOmdoc :: (GetRange f, Pretty f) => SIMPLE_ID -> LIB_ID -> Sign f e
                 -> Named(FORMULA f) -> TCElement
exportSenToOmdoc sid lid sign f =
    let spid  = (SPEC_ID (simpleIdToId sid) (libIdToId lid))
        sname = (senAttr f)
        sen   = sentence f
    in
      case sen of
        -- CLEANUP: Remove the comment later
        Sort_gen_ax cs b -> makeADTsFromConstraints spid sign cs b
        _ -> TCAxiomOrTheorem True sname $ foldFormula
             (omdocRec spid
              sign (\_ -> error "CASL extension not supported."))
             sen


sfail :: String -> Range -> a
sfail s r = error $ show (Diag Error ("unexpected " ++ s) r)


-------------------------- ADT --------------------------

makeADTsFromConstraints :: SPEC_ID -> Sign f e -> [Constraint] -> Bool
                         -> TCElement
makeADTsFromConstraints spid _ cs b =
    TCADT $ Prelude.map (makeADTSortDef spid b) cs

makeADTSortDef :: SPEC_ID -> Bool -> Constraint -> OmdADT
makeADTSortDef spid b (Constraint s l _) =
    ADTSortDef (idToName spid s) b $
    Prelude.map (makeADTConstructor spid . fst) l

makeADTConstructor :: SPEC_ID -> OP_SYMB -> OmdADT
makeADTConstructor spid (Qual_op_name n (Op_type _ args _ _) _) =
    ADTConstr (idToName spid n) $ Prelude.map (makeADTArgument spid) args

makeADTConstructor _ (Op_name (Id _ _ r)) = sfail "No_qual_op" r

-- No support for selectors
makeADTArgument :: SPEC_ID -> SORT -> OmdADT
makeADTArgument spid s = ADTArg (sortToOmdoc spid s) Nothing


-------------------------- Theory constitutive --------------------------

sortSignToOmdoc :: SPEC_ID -> Sign a e -> SORT -> TCElement
sortSignToOmdoc spid _ s
    | isLocalId spid s = TCSymbol (idToName spid s)
                         (Just const_sort)
                         Typ
    -- CLEANUP: Have to be filtered completely
    | otherwise = TCComment $ "nonlocal symbol: " ++ (show s)


-- assuming here the the set of pred types contains only one Element!
predSignToOmdoc :: SPEC_ID -> Sign a e -> Id -> (Set.Set PredType) ->
                   TCElement
predSignToOmdoc spid _ p ptypes
    | isLocalId spid p =
        TCSymbol
        (idToName spid p)
        (Just $ makePredType spid $ Set.findMin ptypes)
        Obj
    -- CLEANUP: Have to be filtered completely
    | otherwise = TCComment $ "nonlocal predicate: " ++ (show p)


-- assuming here the the set of op types contains only one Element!
funSignToOmdoc :: SPEC_ID -> Sign a e -> Id -> (Set.Set OpType) -> TCElement
funSignToOmdoc spid _ f ftypes
    | isLocalId spid f =
        TCSymbol
        (idToName spid f)
        (Just $ makeObjectType spid $ Set.findMin ftypes)
        Obj
    -- CLEANUP: Have to be filtered completely
    | otherwise = TCComment $ "nonlocal function: " ++ (show f)


-------------------------- types --------------------------

-- | Given an operator or predicate signature we construct the according type
makeType :: SPEC_ID -> OpKind -> [SORT] -> Maybe SORT -> OMElement
makeType spid _ [] (Just r) = (sortToOmdoc spid r)
makeType spid total domain range =
    (OMA $ funtypeconstr : (Prelude.map (sortToOmdoc spid) args))
         where
           funtypeconstr = case total of
                             Total -> case range of
                                        Nothing -> const_predtype
                                        _ -> const_funtype
                             Partial -> const_partialfuntype
           args = case range of Nothing -> domain
                                Just r -> domain ++ [r]
{-
-- | Given an operator or predicate signature we construct the according
-- type by currying and using bool as rangetype for predicates

    foldr (addType spid)
              (OMA [typeconstr, (sortToOmdoc spid s), rangeelem])
              rest
        where
          typeconstr = case total of Total -> const_funtype
                                     Partial -> const_partialfuntype
          s = last domain
          rest = init domain
          rangeelem = case range of Nothing -> (const_bool)
                                    Just r -> (sortToOmdoc spid r)


addType :: SPEC_ID -> SORT -> OMElement -> OMElement
addType spid s elm = OMA [const_funtype, (sortToOmdoc spid s), elm]

-}

makePredType :: SPEC_ID -> PredType -> OMElement
makePredType spid (PredType predargs) =
    makeType spid Total predargs Nothing

makeObjectType :: SPEC_ID -> OpType -> OMElement
makeObjectType spid (OpType opkind opargs oprange) =
    makeType spid opkind opargs (Just oprange)

-------------------------- Names --------------------------

-- | the qualified name of an identifier consisting of
--   the name, the spec and the lib
data NameTriple = NameTriple { getName :: String,
                               getSpecName :: String,
                               getLibName :: String } deriving Show


-- gn_Over has still to be outcoded

idToName :: SPEC_ID -> Id -> String
idToName spid = getName . (idToNameTriple spid)

idToNameTriple :: SPEC_ID -> Id -> NameTriple
-- spid-structure
idToNameTriple spid s
    | isQualName s = NameTriple (show $ unQualName s)
                     (show $ getNodeId s) (show $ getLibId s)
    | otherwise = case spid of
                    (SPEC_ID sid lid) ->
                        NameTriple (show s) (show sid) (show lid)
                    NOSPEC -> error $ "unqualified morphism entry" ++ show s

isLocalId :: SPEC_ID -> Id -> Bool
-- spid-structure
isLocalId (SPEC_ID s l) i@(Id _ [_, s1, l1] _)
    | isQualName i = (s == s1) && (l == l1)
    | otherwise = True
isLocalId _ _ = True


-------------------------- OpenMath --------------------------

-- | probably outsource this to a generic module
makeOMS :: NameTriple -> OMElement
makeOMS (NameTriple i s l) =
-- special handling for library entries !??
    OMS (CD s $ if l == "library" || l == "" then Nothing else Just l)
            $ OMName i

idToOmdoc :: SPEC_ID -> Id -> OMElement
idToOmdoc spid s = makeOMS $ idToNameTriple spid s

sortToOmdoc :: SPEC_ID -> Id -> OMElement
sortToOmdoc = idToOmdoc

funToOmdoc :: SPEC_ID -> OP_SYMB -> OMElement
funToOmdoc spid (Qual_op_name i _ _) = idToOmdoc spid i
funToOmdoc spid (Op_name i) = idToOmdoc spid i

predToOmdoc :: SPEC_ID -> PRED_SYMB -> OMElement
predToOmdoc spid (Qual_pred_name i _ _) = idToOmdoc spid i
predToOmdoc spid (Pred_name i) = idToOmdoc spid i

-- | the object e1 and its type e2
makeAttribution :: OMElement -> OMElement -> OMElement
makeAttribution e1 e2 = OMATTT e1 $ OMAttr const_type e2

varToOmdoc :: Token -> OMElement
varToOmdoc v = OMV $ OMName $ tokStr v

-- | typed vars can only be typed by a single sort
varDeclToOMDoc :: SPEC_ID -> (VAR, SORT) -> OMElement
varDeclToOMDoc spid (v, s) = makeAttribution (varToOmdoc v) $
                             sortToOmdoc spid s

-- cdbase entries missing for predefined content dictionaries

const_casl :: String -> OMElement
const_casl n = OMS (CD "casl" Nothing) $ OMName n

const_true, const_false, const_sort, const_funtype, const_partialfuntype
 , const_and, const_or, const_implies, const_implied, const_equivalent
 , const_forall, const_exists, const_eq, const_eeq, const_existsunique
 , const_def, const_in, const_if, const_cast, const_type, const_not
 , const_predtype :: OMElement

const_true = const_casl "true"
const_false = const_casl "false"

const_funtype = const_casl "funtype"
const_partialfuntype = const_casl "partialfuntype"
const_predtype = const_casl "predtype"
const_type = const_casl "type"

const_not = const_casl "not"
const_and = const_casl "and"
const_or = const_casl "or"
const_implies = const_casl "implies"
const_implied = const_casl "implied"
const_equivalent = const_casl "equivalent"

const_forall = const_casl "forall"
const_exists = const_casl "exists"

const_eq = const_casl "eq"
const_eeq = const_casl "eeq"
const_existsunique = const_casl "existsunique"
const_def = const_casl "def"
const_in = const_casl "in"
const_if = const_casl "if"
const_cast = const_casl "cast"
const_sort = const_casl "sort"

omdocRec :: GetRange f => SPEC_ID -> Sign f e -> (f -> OMElement)
         -> Record f OMElement OMElement
omdocRec spid _ mf = Record
    { foldQuantification = \ _ q vs f _ ->
      let s = case q of
                Universal -> const_forall
                Existential -> const_exists
                Unique_existential -> const_existsunique
          vl = Prelude.map (varDeclToOMDoc spid) $ flatVAR_DECLs vs
      in OMBIND s vl f
    , foldConjunction = \ _ fs _ -> OMA $ const_and : fs
    , foldDisjunction = \ _ fs _ -> OMA $ const_or : fs
    , foldImplication = \ _ f1 f2 b _ ->
        if b then (OMA [const_implies , f1, f2])
        else (OMA [const_implied , f1, f2])
    , foldEquivalence = \ _ f1 f2 _ ->
                        (OMA [const_equivalent , f1, f2])
    , foldNegation = \ _ f _ -> (OMA [const_not , f])
    , foldTrue_atom = \ _ _ -> const_true
    , foldFalse_atom = \ _ _ -> const_false
    , foldPredication = \ _ p ts _ -> OMA $ (predToOmdoc spid p) : ts
    , foldDefinedness = \ _ t _ -> OMA [const_def, t]
    , foldExistl_equation = \ _ t1 t2 _ -> (OMA [const_eeq , t1, t2])
    , foldStrong_equation = \ _ t1 t2 _ -> (OMA [const_eq , t1, t2])
    , foldMembership = \ _ t s _ ->
                       (OMA [const_in , t, sortToOmdoc spid s])
    , foldMixfix_formula = \ t _ -> sfail "Mixfix_formula" $ getRange t
    , foldQuantOp = \ _ o _ _ -> sfail ("QuantOp " ++ show o) $ getRange o
    , foldQuantPred = \ _ p _ _ -> sfail ("QuantPred " ++ show p) $ getRange p
    , foldSort_gen_ax = \ t _ _ -> sfail
                        "Sort generating axioms should be filtered out before!"
                        $ getRange t
    , foldExtFORMULA = \ _ f -> mf f
    , foldQual_var = \ _ v _ _ -> varToOmdoc v
    , foldApplication = \ _ o ts _ -> OMA $ (funToOmdoc spid o) : ts
    , foldSorted_term = \ _ r _ _ -> r
    , foldCast = \ _ t s _ ->
                 (OMA [const_cast , t, sortToOmdoc spid s])
    , foldConditional = \ _ e f t _ -> (OMA [const_if , e , t, f])
    , foldMixfix_qual_pred = \ _ p -> sfail "Mixfix_qual_pred" $ getRange p
    , foldMixfix_term = \ (Mixfix_term ts) _ ->
        sfail "Mixfix_term" $ getRange ts
    , foldMixfix_token = \ _ t -> sfail "Mixfix_token" $ tokPos t
    , foldMixfix_sorted_term = \ _ _ r -> sfail "Mixfix_sorted_term" r
    , foldMixfix_cast = \ _ _ r -> sfail "Mixfix_cast" r
    , foldMixfix_parenthesized = \ _ _ r -> sfail "Mixfix_parenthesized" r
    , foldMixfix_bracketed = \ _ _ r -> sfail "Mixfix_bracketed" r
    , foldMixfix_braced = \ _ _ r -> sfail "Mixfix_braced" r }


-------------------------- Morphisms --------------------------


makeSortMapEntry :: SPEC_ID -> SORT -> SORT -> (OMName, OMElement)
makeSortMapEntry spid s1 s2 = (OMName $ idToName spid s1, sortToOmdoc spid s2)

makeOpMapEntry :: SPEC_ID -> (Id, OpType) -> (Id, OpKind) ->
                  (OMName, OMElement)
makeOpMapEntry spid (o1, _) (o2, _) =
    (OMName $ idToName spid o1, idToOmdoc spid o2)

makePredMapEntry :: SPEC_ID -> (Id, PredType) -> Id -> (OMName, OMElement)
makePredMapEntry spid (p1, _) p2 =
    (OMName $ idToName spid p1, idToOmdoc spid p2)


--------------------------------------------------------------------


