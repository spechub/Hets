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

import UML.UML 
import qualified Data.Map as Map
import UML.Sign
import Common.Doc
import Common.DocUtils
import Common.Result
import Data.Maybe

data Morphism = Morphism
  { source :: Sign
  , target :: Sign
  , classMap :: ClassMap,
    attributeMap :: AttributeMap,
    operationMap :: OperationMap,
    compositionMap :: CompositionMap,
    associationMap :: AssociationMap
  } deriving (Eq, Ord, Show)

type ClassMap = Map.Map ClassEntity ClassEntity
type AttributeMap = Map.Map (Class,String,Type) (Class,String,Type)
type OperationMap = Map.Map (Class,String,[(String,Type)],Type) (Class,String,[(String,Type)],Type)
type CompositionMap = Map.Map (ClassEntity,String,Type) (ClassEntity,String,Type)
type AssociationMap = Map.Map (String,[(String,Type)]) (String,[(String,Type)])

instance Pretty Morphism where
    pretty _ = text ""

idMor :: Sign -> Morphism
idMor sign = inclusionMap sign sign

inclusionMap :: Sign -> Sign -> Morphism
inclusionMap sign1 sign2 = Morphism{source = sign1
  , target = sign2
  , classMap = Map.fromList [(c,c) | c <- fst $ signClassHier sign2],
    attributeMap = Map.fromList [(c,c) | c <- signAttribute sign2],
    operationMap = Map.fromList [(c,c) | c <- signOperations sign2],
    compositionMap = Map.fromList [(c,c) | c <- signCompositions sign2],
    associationMap = Map.fromList [(c,c) | c <- signAssociations sign2]
}

isLegalMorphism :: Morphism -> Result ()
isLegalMorphism pmor = Left ""
    {-let psource = allItems $ source pmor
        ptarget = allItems $ target pmor
        pdom = Map.keysSet $ propMap pmor
        pcodom = Set.map (applyMorphism pmor) psource
        --attrCond = all (isValidAttrMorph (classMap pmor) (attributeMap pmor)) (signAttribute $ source pmor)
    in unless (Set.isSubsetOf pcodom ptarget && Set.isSubsetOf pdom psource) $
    fail "illegal CommonLogic morphism"-}

isValidAttrMorph :: ClassMap -> AttributeMap -> (Class,String,Type) -> Bool 
isValidAttrMorph cmap amap (c,s,t) = case Map.lookup (c,s,t) amap of
                                        Nothing -> True
                                        Just (c',s',t') -> ((Map.lookup c cmap) == c') && (typeOrdered t == typeOrdered t') && (typeUnique t == typeUnique t')

composeMor :: Morphism -> Morphism -> Morphism
composeMor m1 m2 = Morphism{
        source = source m1,
        target = target m2,
        classMap = Map.fromList [(a,d)| (a,b) <- (Map.toList $ classMap m1), (c,d) <- (Map.toList $ classMap m2), b==c], 
        attributeMap = Map.fromList [(a,d)| (a,b) <- (Map.toList $ attributeMap m1), (c,d) <- (Map.toList $ attributeMap m2), b==c], 
        operationMap = Map.fromList [(a,d)| (a,b) <- (Map.toList $ operationMap m1), (c,d) <- (Map.toList $ operationMap m2), b==c], 
        compositionMap = Map.fromList [(a,d)| (a,b) <- (Map.toList $ compositionMap m1), (c,d) <- (Map.toList $ compositionMap m2), b==c], 
        associationMap = Map.fromList [(a,d)| (a,b) <- (Map.toList $ associationMap m1), (c,d) <- (Map.toList $ associationMap m2), b==c] 
}

mapSentence :: Morphism -> MultForm -> Result MultForm
mapSentence mor (NLeqF n f) = NLeqF n (mapSen_fe f)
mapSentence mor (FLeqN f n) = FLeqN (mapSen_fe f) n 


mapSen_fe :: Morphism -> FunExpr -> FunExpr
mapSen_fe mor (NumComp mfc mfe) = (NumComp (comp2mfcomp (ori2,n2,tar2)) mfe2) 
                                    where     
                                            (ori1, n1, tar1) = (lookupByMF (comp2mfcomp) (Map.toList (compositionMap mor)) mfc)
                                            (ori2, n2, tar2) = fromJust $ Map.lookup (ori1, n1, tar1) (compositionMap mor)
                                            mfe2 = case endName ori1 of 
                                                    mfe -> showClassEntityName ori2
                                                    _ -> umlTypeString $ umltype tar2                            
mapSen_fe mor (NumAss mfa mfe) = NumAss (asso2mfasso (n',ends')) mfe'
                                    where 
                                            (n,ends) = lookupByMF asso2mfasso (Map.toList (associationMap mor)) mfa
                                              (n',ends') = fromJust $ Map.lookup (n,ends) (associationMap mor)
                                              mfe' = head [en'| ((en,et),(en',et')) <- (zip ends ends'), en==mfe] 
mapSen_fe mor (NumAttr mfa) = NumAttr $ attr2mfattr $  fromJust $ Map.lookup (lookupByMF attr2mfattr (Map.toList (attributeMap mor)) mfa) (attributeMap mor)



lookupByMF :: (Eq b) => (Show b) => (a -> b) -> [(a,a)] -> b -> a
lookupByMF tran [] mf = error $ "invalid classifier: " ++ (show mf)
lookupByMF tranAB ((el,_):lis) mf = case tranAB el of 
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
        where (origin,target) = compositionEnds ass

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

