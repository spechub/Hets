module UML.Morphism
  ( Morphism (..)               -- datatype for Morphisms
  , pretty                      -- pretty printing
  , idMor                       -- identity morphism
  , isLegalMorphism             -- check if morhpism is ok
  , composeMor                  -- composition
  , inclusionMap                -- inclusion map
  , mapSentence                 -- map of sentences
--  , mapSentenceH                -- map of sentences, without Result type
--  , applyMap                    -- application function for maps
--  , applyMorphism               -- application function for morphism
--  , morphismUnion
  ) where

import           Common.Doc      hiding (Label)
import           Common.DocUtils
import           Common.Result
import qualified Data.Map        as Map
import           Data.Maybe
import           UML.Sign
import           UML.UML

import           Control.Monad   (unless)

data Morphism = Morphism
  { source         :: Sign
  , target         :: Sign
  , classMap       :: ClassMap,
    attributeMap   :: AttributeMap,
    operationMap   :: OperationMap,
    compositionMap :: CompositionMap,
    associationMap :: AssociationMap
  } deriving (Eq, Ord, Show)
type Mapping s = Map.Map s s
type ClassMap = Mapping ClassEntity
type AttributeMap = Mapping (Class, String, Type)
type OperationMap = Mapping (Class, String, [(String, Type)], Type)
type CompositionMap = Mapping ((String, ClassEntity), String, (String, Type))
type AssociationMap = Mapping (String, [(String, Type)])

instance Pretty Morphism where
    pretty _ = text ""

idMor :: Sign -> Morphism
idMor sign = inclusionMap sign sign

inclusionMap :: Sign -> Sign -> Morphism
inclusionMap sign1 sign2 = Morphism {source = sign1
  , target = sign2
  , classMap = Map.fromList [(c, c) | c <- fst $ signClassHier sign2],
    attributeMap = Map.fromList [(c, c) | c <- signAttribute sign2],
    operationMap = Map.fromList [(c, c) | c <- signOperations sign2],
    compositionMap = Map.fromList [(c, c) | c <- signCompositions sign2],
    associationMap = Map.fromList [(c, c) | c <- signAssociations sign2]
}


isLegalMorphism :: Morphism -> Result ()
isLegalMorphism mor = let
                            cmap = classMap mor
                            sign = source mor
                        in unless ( (isValidMorph cmap (associationMap mor) isValidAssoMorph (signAssociations  sign))
                        &&  (isValidMorph cmap (compositionMap mor) isValidCompMorph (signCompositions  sign))
                        &&  (isValidMorph cmap (attributeMap mor) isValidAttrMorph (signAttribute sign))
                        &&  (isValidMorph cmap (operationMap mor) isValidOperMorph (signOperations sign))) $ fail "illegal UML class diagram morphism"


isValidMorph :: Ord s => ClassMap -> (Mapping s) -> (ClassMap -> s -> s -> Bool) -> [s] -> Bool
isValidMorph cmap smap f slist = all (apply (f cmap)) [(x, fromJust $ Map.lookup x smap) | x <- slist, not (Map.lookup x smap == Nothing)]
                                    where apply f (x, y) = f x y

isValidAttrMorph :: ClassMap -> (Class, String, Type) -> (Class, String, Type) -> Bool
isValidAttrMorph cmap (c, s, t) (c', s', t') = ((Map.lookup (CL c) cmap) == Just (CL c')) && (typesMatch cmap (t, t'))


typesMatch :: ClassMap -> (Type, Type) -> Bool
typesMatch cmap (t, t') = (typeOrdered t == typeOrdered t') && (typeUnique t == typeUnique t') && (case (umltype t, umltype t')  of
                        (CE ce, CE ce') -> (Map.lookup ce cmap) == Just ce'
                        (x, y) -> x == y)

isValidOperMorph :: ClassMap -> (Class, String, [(String, Type)], Type) -> (Class, String, [(String, Type)], Type) -> Bool
isValidOperMorph cmap (c, s, paras, t) (c', s', paras', t') =  ((Map.lookup (CL c) cmap) == Just (CL c')) && (typesMatch cmap (t, t')) && ((length paras) == (length paras')) && (all (typesMatch cmap) $ zip (map snd paras) (map snd paras'))

isValidAssoMorph :: ClassMap -> (String, [(String, Type)]) -> (String, [(String, Type)]) -> Bool
isValidAssoMorph cmap (s, ends) (s', ends') = ((length ends) == (length ends')) && (all (typesMatch cmap) $ zip (map snd ends) (map snd ends'))

isValidCompMorph :: ClassMap -> ((String, ClassEntity), String, (String, Type)) -> ((String, ClassEntity), String, (String, Type)) -> Bool
isValidCompMorph cmap ((_, c), _, (_, t)) ((_, c'), _, (_, t')) = ((Map.lookup c cmap) == Just c') && (typesMatch cmap (t, t'))

composeMor :: Morphism -> Morphism -> Result Morphism
composeMor m1 m2 = return Morphism {
        source = source m1,
        target = target m2,
        classMap = Map.fromList [(a, d) | (a, b) <- (Map.toList $ classMap m1), (c, d) <- (Map.toList $ classMap m2), b == c],
        attributeMap = Map.fromList [(a, d) | (a, b) <- (Map.toList $ attributeMap m1), (c, d) <- (Map.toList $ attributeMap m2), b == c],
        operationMap = Map.fromList [(a, d) | (a, b) <- (Map.toList $ operationMap m1), (c, d) <- (Map.toList $ operationMap m2), b == c],
        compositionMap = Map.fromList [(a, d) | (a, b) <- (Map.toList $ compositionMap m1), (c, d) <- (Map.toList $ compositionMap m2), b == c],
        associationMap = Map.fromList [(a, d) | (a, b) <- (Map.toList $ associationMap m1), (c, d) <- (Map.toList $ associationMap m2), b == c]
}

mapSentence :: Morphism -> Sen -> Result Sen
mapSentence mor (NLeqF n f) = return $ NLeqF n (mapSen_fe mor f)
mapSentence mor (FLeqN f n) = return $ FLeqN (mapSen_fe mor f) n


mapSen_fe :: Morphism -> FunExpr -> FunExpr
mapSen_fe mor (NumComp mfc mfe) = (NumComp (comp2mfcomp ((sn2, ori2), n2, (tn2, tar2))) mfe)
                                    where
                                            ((sn1, ori1), n1, (tn1, tar1)) = (lookupByMF (comp2mfcomp) (Map.toList (compositionMap mor)) mfc)
                                            ((sn2, ori2), n2, (tn2, tar2)) = fromJust $ Map.lookup ((sn1, ori1), n1, (tn1, tar1)) (compositionMap mor)
                                            mfe2 = case sn1 of
                                                    mfe -> showClassEntityName ori2
                                                    _ -> umlTypeString $ umltype tar2
mapSen_fe mor (NumAss mfa mfe) = NumAss (asso2mfasso (n', ends')) mfe'
                                    where
                                            (n, ends) = lookupByMF asso2mfasso (Map.toList (associationMap mor)) mfa
                                            (n', ends') = fromJust $ Map.lookup (n, ends) (associationMap mor)
                                            mfe' = head [en' | ((en, et), (en', et')) <- (zip ends ends'), en == mfe]
mapSen_fe mor (NumAttr mfa) = NumAttr $ attr2mfattr $  fromJust $ Map.lookup (lookupByMF attr2mfattr (Map.toList (attributeMap mor)) mfa) (attributeMap mor)



lookupByMF :: (Eq b, Show b) => (a -> b) -> [(a, a)] -> b -> a
lookupByMF tran [] mf = error $ "invalid classifier: " ++ (show mf)
lookupByMF tranAB ((el, _) : lis) mf = case tranAB el of
                                mf -> el
                                _ -> lookupByMF tranAB lis mf


{-lookupCEbyName :: [ClassEntity] -> String -> ClassEntity
lookupCEbyName [] s = error $ "invalid classifier: " ++ s
lookupCEbyName (ce:lis) s = case (showClassEntityName ce) of
                                s -> ce
                                _ -> lookupCEbyName lis s

lookupCompbyName :: [Association] -> MFCOMPOSITION -> Association
lookupCompb1yName [] mf = error $ "invalid classifier: " ++ (show mf)
lookupCompbyName (ass:lis) (MFComposition n e1 t1 e2 t2) =
    case (e1 == (showClassEntityName $ endTarget origin)) && (n == (assoName ass)) of
        True -> ass
        _ -> lookupCEbyName lis (MFComposition n e1 t1 e2 t2)
        where (origin, target) = compositionEnds ass

lookupAssobyMF :: [Association] -> MFASSOCIATION -> Association
lookupAssobyMF [] mf = error $ "invalid classifier: " ++ (show mf)
lookupAssobyMF (ass:lis)  mfa = case asso2mfasso ass of
                                    mfa -> ass
                                    _ -> lookupAssobyMF lis mfa

lookupAttrbyMF :: [Attribute] -> MFATTRIBUTE -> Attribute
lookupAttrbyMF [] mf = error $ "invalid classifier: " ++ (show mf)
lookupAttrbyMF
-- | Application funtion for morphisms
--applyMorphism :: Morphism -> Id -> Id
--applyMorphism mor idt = Map.findWithDefault idt idt $ propMap mor -}

