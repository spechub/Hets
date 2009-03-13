{- |
Module      :  $Header$
Description :  Hets-to-OMDoc conversion
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  ewaryst.schulz@dfki.de
Stability   :  provisional
Portability :  non-portable(Logic)

CASL implementation of the interface functions export_signToOmdoc, export_morphismToOmdoc, export_senToOmdoc from class Logic. The actual instantiation can be found in module CASL.Logic_CASL.
-}

module CASL.OMDoc
    ( exportSignToOmdoc
    , exportMorphismToOmdoc
    , exportSenToOmdoc
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
import CASL.ToDoc

import Data.Map as Map
import Data.Set as Set

-- | the identifier of a specification, combining the specid and the libid
data SPEC_ID = SPEC_ID Id Id deriving Show

exportSignToOmdoc ::  (Show f, Pretty e) => SIMPLE_ID -> LIB_ID -> Sign f e -> [TCElement]
exportSignToOmdoc sid lid sign =
    [TCComment $ "Signature of Spec: " ++ (show spid)]
 ++ Set.toList (Set.map (sortSignToOmdoc spid sign) (sortSet sign))
 ++ Map.elems (mapWithKey (funSignToOmdoc spid sign) (opMap sign))
 ++ Map.elems (mapWithKey (predSignToOmdoc spid sign) (predMap sign))
     where spid = (SPEC_ID (simpleIdToId sid) (libIdToId lid))

exportMorphismToOmdoc :: SIMPLE_ID -> LIB_ID -> Morphism f e ()
                      -> [TCElement]
--exportMorphismToOmdoc sid lid morphism = []
exportMorphismToOmdoc _ _ _ = []


exportSenToOmdoc :: Pretty f => SIMPLE_ID -> LIB_ID -> Sign f e -> Named(FORMULA f)
                 -> [TCElement]
exportSenToOmdoc sid lid sign f =
    let spid  = (SPEC_ID (simpleIdToId sid) (libIdToId lid))
        sname = (senAttr f)
        sen   = sentence f
    in
      case sen of
        -- CLEANUP: Remove the comment later
        Sort_gen_ax cs b -> [TCComment $ show $ printTheoryFormula f,
                             buildADTsFromConstraints spid sign cs b]
        _ -> [TCAxiomOrTheorem True sname $ foldFormula
              (omdocRec spid
               sign (\_ -> error "CASL extension not supported."))
              sen]

sfail :: String -> Range -> a
sfail s r = error $ show (Diag Error ("unexpected " ++ s) r)


-------------------------- ADT --------------------------

buildADTsFromConstraints :: SPEC_ID -> Sign f e -> [Constraint] -> Bool
                         -> TCElement
buildADTsFromConstraints spid _ cs b = 
    TCADT $ Prelude.map (buildADTSortDef spid b) cs

buildADTSortDef :: SPEC_ID -> Bool -> Constraint -> OmdADT
buildADTSortDef spid b (Constraint s l _) = 
    ADTSortDef (idToName spid s) b $
    Prelude.map (buildADTConstructor spid . fst) l

buildADTConstructor :: SPEC_ID -> OP_SYMB -> OmdADT
buildADTConstructor spid (Qual_op_name n (Op_type _ args _ _) _) =
    ADTConstr (idToName spid n) $ Prelude.map (buildADTArgument spid) args

buildADTConstructor _ (Op_name (Id _ _ r)) = sfail "No_qual_op" r

-- No support for selectors
buildADTArgument :: SPEC_ID -> SORT -> OmdADT
buildADTArgument spid s = ADTArg (sortToOmdoc spid s) Nothing


-------------------------- Theory constitutive --------------------------

sortSignToOmdoc :: SPEC_ID -> Sign a e -> SORT -> TCElement
sortSignToOmdoc spid _ s
    | isLocalId spid s = TCSymbol (idToName spid s) Nothing Typ
    -- CLEANUP: Have to be filtered completely
    | otherwise = TCComment $ "nonlocal symbol: " ++ (show s)


-- assuming here the the set of pred types contains only one Element!
predSignToOmdoc :: SPEC_ID -> Sign a e -> Id -> (Set.Set PredType) -> TCElement
predSignToOmdoc spid _ p ptypes
    | isLocalId spid p =
        TCSymbol
        (idToName spid p)
        (Just (buildType spid Total (predArgs $ Set.findMin ptypes) Nothing))
        Obj
    -- CLEANUP: Have to be filtered completely
    | otherwise = TCComment $ "nonlocal predicate: " ++ (show p)


-- assuming here the the set of op types contains only one Element!
funSignToOmdoc :: SPEC_ID -> Sign a e -> Id -> (Set.Set OpType) -> TCElement
funSignToOmdoc spid _ f ftypes
    | isLocalId spid f =
        TCSymbol
        (idToName spid f)
        (Just $ buildObjectType spid $ Set.findMin ftypes)
        Obj
    -- CLEANUP: Have to be filtered completely
    | otherwise = TCComment $ "nonlocal function: " ++ (show f)


-------------------------- types --------------------------

-- | Given an operator or predicate signature we construct the according
-- type by currying and using bool as rangetype for predicates
buildType :: SPEC_ID -> OpKind -> [SORT] -> Maybe SORT -> OMElement
buildType spid _ [] (Just r) = (sortToOmdoc spid r)
buildType spid total domain range =
    foldr (addType spid)
              (OMA [typeconstr, (sortToOmdoc spid s), rangeelem])
              rest
        where
          typeconstr = case total of Total -> st_const "funtype"
                                     Partial -> casl_const "partialfuntype"
          s = last domain
          rest = init domain
          rangeelem = case range of Nothing -> (tv_const "bool")
                                    Just r -> (sortToOmdoc spid r)

buildObjectType :: SPEC_ID -> OpType -> OMElement
buildObjectType spid (OpType opkind opargs oprange) =
    buildType spid opkind opargs (Just oprange)

addType :: SPEC_ID -> SORT -> OMElement -> OMElement
addType spid s elm = OMA [(st_const "funtype"), (sortToOmdoc spid s), elm]


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
idToNameTriple (SPEC_ID sid lid) s
    | isQualName s = NameTriple (show $ unQualName s)
                     (show $ getNodeId s) (show $ getLibId s)
    | otherwise = NameTriple (show s) (show sid) (show lid)


isLocalId :: SPEC_ID -> Id -> Bool
isLocalId (SPEC_ID s l) i@(Id _ [_, s1, l1] _)
    | isQualName i = (s == s1) && (l == l1)
    | otherwise = True
isLocalId _ _ = True


-------------------------- OpenMath --------------------------

-- | probably outsource this to a generic module
buildOMS :: NameTriple -> OMElement
buildOMS (NameTriple i s l) = OMS (CD s $ Just l) $ OMName i

idToOmdoc :: SPEC_ID -> Id -> OMElement
idToOmdoc spid s = buildOMS $ idToNameTriple spid s

sortToOmdoc :: SPEC_ID -> Id -> OMElement
sortToOmdoc = idToOmdoc

funToOmdoc :: SPEC_ID -> OP_SYMB -> OMElement
funToOmdoc spid (Qual_op_name i _ _) = idToOmdoc spid i
funToOmdoc spid (Op_name i) = idToOmdoc spid i

predToOmdoc :: SPEC_ID -> PRED_SYMB -> OMElement
predToOmdoc spid (Qual_pred_name i _ _) = idToOmdoc spid i
predToOmdoc spid (Pred_name i) = idToOmdoc spid i

-- | type attributes for terms can only consist of a single sort
sortToOmdocAttribute :: SPEC_ID -> SORT -> OMAttribute
sortToOmdocAttribute spid s = OMAttr (st_const "type") $ sortToOmdoc spid s

varToOmdoc :: Token -> OMElement
varToOmdoc v = OMV $ OMName $ tokStr v

-- | typed vars can only be typed by a single sort
varDeclToOMDoc :: SPEC_ID -> (VAR, SORT) -> OMElement
varDeclToOMDoc spid (v, s) = OMATTT (varToOmdoc v) (sortToOmdocAttribute spid s)


-- | Predefined truthval constants: false, true
tv_const :: String -> OMElement
tv_const n = OMS (CD "truthval" Nothing) $ OMName n

-- | Predefined simpletypes constants: funtype, type
st_const :: String -> OMElement
st_const n = OMS (CD "simpletypes" Nothing) $ OMName n

-- | Predefined pl0 constants: not, and, or, implies, implied, equivalent
pl0_const :: String -> OMElement
pl0_const n = OMS (CD "pl0" Nothing) $ OMName n

-- | Predefined pl1 constants: forall, exists
pl1_const :: String -> OMElement
pl1_const n = OMS (CD "pl1" Nothing) $ OMName n

-- | Predefined casl constants: eq, eeq, existsunique, defined, in, if, cast
casl_const :: String -> OMElement
casl_const n = OMS (CD "casl" Nothing) $ OMName n



omdocRec :: SPEC_ID -> Sign f e -> (f -> OMElement)
         -> Record f OMElement OMElement
omdocRec spid _ mf = Record
    { foldQuantification = \ _ q vs f _ ->
      let s = case q of
                Universal -> pl1_const "forall"
                Existential -> pl1_const "exists"
                Unique_existential -> casl_const "existsunique"
          vl = Prelude.map (varDeclToOMDoc spid) $ flatVAR_DECLs vs
      in OMBIND s vl f
    , foldConjunction = \ _ fs _ -> OMA $ (pl0_const "and") : fs
    , foldDisjunction = \ _ fs _ -> OMA $ (pl0_const "or") : fs
    , foldImplication = \ _ f1 f2 b _ ->
        if b then (OMA [(pl0_const "implies") , f1, f2])
        else (OMA [(pl0_const "implied") , f1, f2])
    , foldEquivalence = \ _ f1 f2 _ ->
                        (OMA [(pl0_const "equivalent") , f1, f2])
    , foldNegation = \ _ f _ -> (OMA [(pl0_const "not") , f])
    , foldTrue_atom = \ _ _ -> tv_const "true"
    , foldFalse_atom = \ _ _ -> tv_const "false"
    , foldPredication = \ _ p ts _ -> OMA $ (predToOmdoc spid p) : ts
    , foldDefinedness = \ _ t _ -> OMA [(casl_const "def"), t]
    , foldExistl_equation = \ _ t1 t2 _ -> (OMA [(casl_const "eeq") , t1, t2])
    , foldStrong_equation = \ _ t1 t2 _ -> (OMA [(casl_const "eq") , t1, t2])
    , foldMembership = \ _ t s _ ->
                       (OMA [(casl_const "in") , t, sortToOmdoc spid s])
    , foldMixfix_formula = \ t _ -> sfail "Mixfix_formula" $ getRange t
    , foldSort_gen_ax = \ t _ _ -> sfail
                        "Sort generating axioms should be filtered out before!"
                        $ getRange t
    , foldExtFORMULA = \ _ f -> mf f
    , foldQual_var = \ _ v _ _ -> varToOmdoc v
    , foldApplication = \ _ o ts _ -> OMA $ (funToOmdoc spid o) : ts
    , foldSorted_term = \ _ r _ _ -> r
    , foldCast = \ _ t s _ ->
                 (OMA [(casl_const "cast") , t, sortToOmdoc spid s])
    , foldConditional = \ _ e f t _ -> (OMA [(casl_const "if") , e , t, f])
    , foldMixfix_qual_pred = \ _ p -> sfail "Mixfix_qual_pred" $ getRange p
    , foldMixfix_term = \ (Mixfix_term ts) _ ->
        sfail "Mixfix_term" $ getRange ts
    , foldMixfix_token = \ _ t -> sfail "Mixfix_token" $ tokPos t
    , foldMixfix_sorted_term = \ _ _ r -> sfail "Mixfix_sorted_term" r
    , foldMixfix_cast = \ _ _ r -> sfail "Mixfix_cast" r
    , foldMixfix_parenthesized = \ _ _ r -> sfail "Mixfix_parenthesized" r
    , foldMixfix_bracketed = \ _ _ r -> sfail "Mixfix_bracketed" r
    , foldMixfix_braced = \ _ _ r -> sfail "Mixfix_braced" r }



