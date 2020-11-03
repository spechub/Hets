{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  ./Comorphisms/Hybrid2CASL.hs
Copyright   :  nevrenato@gmail.com
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

Comorphism HybridCASL to CASL.
-}

module Comorphisms.Hybrid2CASL
  ( Hybrid2CASL (..)
  ) where

import Logic.Logic
import Logic.Comorphism

import Common.ProofTree
import Common.AS_Annotation
import Common.Result
import qualified Common.Lib.Rel as Rel
import qualified Common.Lib.MapSet as MapSet
import Common.Id

import qualified Data.Set as Set
import qualified Data.HashMap.Strict as Map

import Hybrid.Logic_Hybrid
import Hybrid.AS_Hybrid
import Hybrid.HybridSign

import CASL.Logic_CASL
import CASL.AS_Basic_CASL
import CASL.Morphism
import CASL.Sign
import CASL.Sublogic as SL

import Data.Hashable


data Hybrid2CASL = Hybrid2CASL deriving Show

-- Just to make things easier to understand
type HForm = HybridFORMULA
type CForm = CASLFORMULA
type CSign = CASLSign


instance Language Hybrid2CASL where
   language_name Hybrid2CASL = "Hybrid2CASL"

instance Comorphism Hybrid2CASL
        Hybrid ()
        H_BASIC_SPEC HForm SYMB_ITEMS SYMB_MAP_ITEMS
        HSign
        HybridMor
        Symbol RawSymbol ()
        CASL
        CASL_Sublogics
        CASLBasicSpec CForm SYMB_ITEMS SYMB_MAP_ITEMS
        CSign
        CASLMor
        Symbol RawSymbol ProofTree where

        sourceLogic Hybrid2CASL = Hybrid
        sourceSublogic Hybrid2CASL = ()
        targetLogic Hybrid2CASL = CASL
        mapSublogic Hybrid2CASL _ = Just SL.caslTop
                { SL.cons_features = SL.emptyMapConsFeature
                , SL.sub_features = SL.NoSub
                }
        map_theory Hybrid2CASL = transTheory
        has_model_expansion Hybrid2CASL = True
        is_weakly_amalgamable Hybrid2CASL = True
        is_model_transportable Hybrid2CASL = True
        isInclusionComorphism Hybrid2CASL = True

{- Translates the given theory in an HybridCASL form to an equivalent
theory in CASL form
Question : Why some sentences are in the sig and other sentences are
in the 2nd argument ? (this is scary)
fs'' is needed for special sentences, refering about datatypes
for which hybridization has nothing to do -}
transTheory :: (HSign, [Named HForm]) -> Result (CSign, [Named CForm])
transTheory (s, fs) = let
    newSig = transSig s
    fs' = fmap (mapNamed trans) fs
    fs'' = dataTrans (fs ++ sentences s)
    newSens = fs' ++ sentences newSig ++ fs''
    rigidP = applRig (rigidPreds $ extendedInfo s) "RigidPred" gnPCons
    rigidO = applRig (rigidOps $ extendedInfo s) "RigidOp" gnOCons
  in return (newSig, rigidP ++ rigidO ++ newSens)

-- Special formulas not covered by normal hybridization
dataTrans :: [Named HForm] -> [Named CForm]
dataTrans = foldr f []
        where
        f a b = case sentence a of
            Sort_gen_ax a' b' -> a { sentence = Sort_gen_ax a' b' } : b
            _ -> b

transSig :: HSign -> CSign
transSig hs = let
  workflow = transSens hs . addWrldArg hs
  workflow' = addRels hs . addWorlds hs
  in workflow . workflow' $ newSign hs

{- Creates a new CASL signature based on the hybrid Sig
Also adds the world sort. -}
newSign :: HSign -> CSign
newSign hs = (emptySign ())
  { sortRel = Rel.insertKey worldSort $ sortRel hs
  , emptySortSet = emptySortSet hs
  , assocOps = assocOps hs
  , varMap = varMap hs
  , declaredSymbols = declaredSymbols hs
  , envDiags = envDiags hs
  , annoMap = annoMap hs
  , globAnnos = globAnnos hs
  , opMap = addOpMapSet (rigidOps $ extendedInfo hs) (opMap hs)
  , predMap = addMapSet (rigidPreds $ extendedInfo hs) (predMap hs)
  }

{- | Adds the World constants, based
on the nominals in HSign -}
addWorlds :: HSign -> CSign -> CSign
addWorlds hs cs =
        let getWorld = OpType Total [] worldSort
            s = extendedInfo hs
            kl = Map.keys $ nomies s
            workflow = stringToId . ("Wrl_" ++) . tokStr
            il = fmap workflow kl
            ins = foldr (\ k m -> MapSet.insert k getWorld m) (opMap cs) il
            in cs { opMap = ins }

{- | Adds the Accessibility relation, based
ono the modalities found in HSign -}
addRels :: HSign -> CSign -> CSign
addRels hs cs =
        let accRelT = PredType [worldSort, worldSort]
            s = extendedInfo hs
            kl = Map.keys $ modies s
            il = fmap (stringToId . ("Acc_" ++) . tokStr) kl
            ins = foldl (\ m k -> MapSet.insert k accRelT m) (predMap cs) il
            in cs { predMap = ins }

{- | Adds one argument of type World to all preds and ops
definitions in an hybrid signature and passes them to a caslsig -}
addWrldArg :: HSign -> CSign -> CSign
addWrldArg hs cs = let
    f (OpType a b c) = OpType a (worldSort : b) c
    g (PredType a) = PredType (worldSort : a)
    ops = addOpMapSet (rigidOps $ extendedInfo hs) (opMap hs)
    preds = addMapSet (rigidPreds $ extendedInfo hs) (predMap hs)
    ks = Set.elems $ MapSet.keysSet ops
    ks' = Set.elems $ MapSet.keysSet preds
  in cs
    { opMap = foldr (MapSet.update (Set.map f)) (opMap cs) ks
    , predMap = foldr (MapSet.update (Set.map g)) (predMap cs) ks'
    }

{- Translates all hybridformulas in a hybridSig to caslformulas
Ones are in the declaration of nominals and modalities (however
for nows that is forbidden to happen)
The others come from the casl sig -}
transSens :: HSign -> CSign -> CSign
transSens hs cs = let
    mods = Map.elems (modies $ extendedInfo hs)
    noms = Map.elems (nomies $ extendedInfo hs)
    fs = concat $ mods ++ noms
    workflow = makeNamed "" . trans . item
    fs' = fmap workflow fs
    fs'' = fmap (mapNamed trans) (sentences hs)
  in cs { sentences = fs' ++ fs'' }

-- Translates an HybridCASL formula to CASL formula
trans :: HForm -> CForm
trans = let w = mkSimpleId "world"
            vars = mkVarDecl w worldSort
        in mkForall [vars] . trForm (QtM w) []

{- | Formula translator
The 2nd argument is used to store the reserved words -}
trForm :: Mode -> [String] -> HForm -> CForm
trForm w s b = case b of
    ExtFORMULA f -> alpha w s f
    Junction j fs r -> Junction j (fmap (trForm w s) fs) r
    Relation f r f' q -> Relation (trForm w s f) r (trForm w s f') q
    Negation f _ -> mkNeg $ trForm w s f
    Predication p l _ -> mkPredication (mkPName p) $ trTerms w s l
    Quantification q l f r -> Quantification q l (trForm w s f) r
    Definedness t _ -> Definedness (trTerm w s t) nullRange
    Atom a r -> Atom a r
    _ -> error "Hybrid2CASL.trForm"

-- | Alpha function, translates pure Hybrid Formulas
alpha :: Mode -> [String] -> H_FORMULA -> CForm
alpha w s b = case b of
    Here n _ -> mkStEq (mkArg (Right n) s) $ case w of
         QtM wm -> mkVarTerm wm worldSort
         _ -> mkArg (Left w) s
    BoxOrDiamond True m f _ -> trBox w m s f
    BoxOrDiamond False m f _ -> trForm w s $ toBox m f
    At (Simple_nom n) f _ -> trForm (AtM n) s f
    Univ n f _ -> trForall w n s f
    Exist n f _ -> mkNeg $ trForall w n s (mkNeg f)
  where
    toBox m f = mkNeg . ExtFORMULA $ BoxOrDiamond True m (mkNeg f) nullRange

-- | Function that takes care of formulas of box type
trBox :: Mode -> MODALITY -> [String] -> HForm -> CForm
trBox m (Simple_mod m') s f = quant $ mkImpl prd $ trForm (QtM v) ss f
  where
    quant = mkForall [var]
    var = mkVarDecl v worldSort
    v = mkSimpleId $ head ss
    ss = newVarName s
    prd = mkPredication predN $ predA m
    predN = qp m' t
    predA w = [mkArg (Left w) s, mkArg (Left (QtM v)) s]
    qp x = mkQualPred (stringToId . ("Acc_" ++) $ show x)
    t = Pred_type [worldSort, worldSort] nullRange
trBox _ _ _ _ = trueForm

-- translation function for the quantification of nominals case
trForall :: Mode -> NOMINAL -> [String] -> HForm -> CForm
trForall w (Simple_nom a) s f = mkForall [mkVarDecl a worldSort]
  $ trForm w (show a : s) f

-- Function that translates a list of hybrid terms to casl terms
trTerms :: Mode -> [String] -> [TERM H_FORMULA] -> [TERM ()]
trTerms m s l = mkArg (Left m) s : fmap (trTerm m s) l

-- Function that translates hybrid term to casl term
trTerm :: Mode -> [String] -> TERM H_FORMULA -> TERM ()
trTerm m s t = case t of
  Qual_var v s' x -> Qual_var v s' x
  Application o l r -> Application (mkOName o) (trTerms m s l) r
  Sorted_term t' s' r -> Sorted_term (trTerm m s t') s' r
  _ -> error "Hybrid2CASL.trTerm"


-- **** Auxiliar functions and datatype ****

-- The world sort type
worldSort :: SORT
worldSort = stringToId "World"

mkPName :: PRED_SYMB -> PRED_SYMB
mkPName ~(Qual_pred_name n t _) = mkQualPred n (f t)
        where f (Pred_type l r) = Pred_type (worldSort : l) r

mkOName :: OP_SYMB -> OP_SYMB
mkOName ~(Qual_op_name n t _) = mkQualOp n (f t)
        where f (Op_type o l s r) = Op_type o (worldSort : l) s r

{- Function that will decide how to create a new argument
That argument can be a variable or a nominal (constant) -}
mkArg :: Either Mode NOMINAL -> [String] -> TERM ()
mkArg a l = case a of
                Left (QtM w) -> vt w
                Left (AtM w) -> ch tokStr w
                Right (Simple_nom n) -> ch show n
              where
                vt x = mkVarTerm x worldSort
                ap x = mkAppl (qo x t) []
                ch f x = if f x `elem` l then vt x else ap x
                qo x = mkQualOp $ stringToId . ("Wrl_" ++) $ show x
                t = Op_type Total [] worldSort nullRange


-- Create a new variable name new in the formula
newVarName :: [String] -> [String]
newVarName xs = ("world" ++) (show $ length xs) : xs

{- | Auxiliar datatype to determine wich is the argument of alpha
Quantified Mode or At mode -}
data Mode = QtM VAR | AtM SIMPLE_ID

-- **** End of auxiliar functions and datatypes section ****************

-- ----- Generation of constraints associated with rigid designators

toName :: (Functor f) => String -> f a -> f (Named a)
toName s = fmap $ makeNamed s

{- Adds the constraints associated with the rigidity
of predicates or operations. -}
applRig :: (Ord k, Hashable k) => MapSet.MapSet k a ->
           String ->
           (k -> a -> CForm) ->
           [Named CForm]
applRig m s f = toName s $ glueDs ks f m
        where ks = Set.elems $ MapSet.keysSet m

{- Given a list of designators, generates the rigidity constraints
associated, and concats them into a single list -}
glueDs :: (Ord k, Hashable k) => [k] ->
          (k -> a -> CForm) ->
          MapSet.MapSet k a ->
          [CForm]
glueDs ks f m = concat $ foldr (\ a b -> g a : b) [] ks
       where g k = glueDe k (MapSet.lookup k m) f

{- Given a single designator, genereates the rigidity constraints
associated, and joins them into a single list -}
glueDe :: k -> Set.Set a -> (k -> a -> CForm) -> [CForm]
glueDe n s f = foldr (\ a b -> f n a : b) [] $ Set.elems s

{- Generates a rigid constraint from a single pred name and type
We add the extra world argument in mkPredType so that it coincides
with the later translated predicate definition -}
gnPCons :: PRED_NAME -> PredType -> CForm
gnPCons n (PredType ts) = mkForall decls $ mkForall wA $ mkImpl f1 f2
        where f1 = mkPredication predName $ terms w1
              f2 = mkPredication predName $ terms w2
              decls = fromSort ts
              terms x = fromDecls $ x : decls
              predName = mkQualPred n $ mkPredType ts
              mkPredType x = Pred_type (worldSort : x) nullRange

gnOCons :: OP_NAME -> OpType -> CForm
gnOCons n (OpType o ts t) = mkForall decls $ mkForall wA f
          where f = mkStEq (mkAppl opName $ terms w1) t2
                t2 = mkAppl opName $ terms w2
                decls = fromSort ts
                terms x = fromDecls $ x : decls
                opName = mkQualOp n $ mkOpType o (worldSort : ts) t
                mkOpType x y z = Op_type x y z nullRange


{- The next functions are auxiliar. They are need for generating the
proper variables/terms for the quantifiers,predications and operations. -}
w1 :: VAR_DECL
w1 = mkVarDecl (mkSimpleId "w") worldSort
w2 :: VAR_DECL
w2 = mkVarDecl (mkSimpleId "w'") worldSort
{- mkVarDecl doesn't support arrays as arg
mkForall doesn't support single elements as arg -}
wA :: [VAR_DECL]
wA = [Var_decl [mkSimpleId "w", mkSimpleId "w'"] worldSort nullRange]

-- Auxiliar function 1
fromSort :: [SORT] -> [VAR_DECL]
fromSort = snd . foldr f (0 :: Int, [])
        where
              f so (i, xs) = (i + 1, mkVarDecl (str i) so : xs)
              str i = mkSimpleId $ 'x' : show i

-- Auxiliar function 2
fromDecls :: [VAR_DECL] -> [TERM f]
fromDecls = concatMap fromDecl

-- Auxiliar function 3
fromDecl :: VAR_DECL -> [TERM f]
fromDecl (Var_decl vs s _ ) = map (`mkVarTerm` s) vs
