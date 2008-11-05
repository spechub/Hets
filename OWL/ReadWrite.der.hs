{-# OPTIONS -w #-}
{- |
Module      :  $Header$
Copyright   :  (c) Heng Jiang, C. Maeder, Uni Bremen 2004-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (ATerms)

Automatically derived and manual ShATermConvertible instances
-}

module OWL.ReadWrite () where

import qualified Data.Map as Map
import OWL.AS
import Common.Utils
import Common.ATerm.Lib
import Data.Typeable
import Data.Char
import Data.List
import Control.Monad

instance ShATermConvertible QName where
  toShATermAux = toShATermAux_QName
  fromShATermAux = fromShATermAux_QName

toShATermAux_QName :: ATermTable -> QName -> IO (ATermTable, Int)
toShATermAux_QName att0 (QN aa ab _) = do
        (att1, aa') <- toShATerm' att0 (aa ++ ":" ++ ab)
        return $ addATerm (ShAAppl (aa ++ ":" ++ ab) [aa'] []) att1

fromShATermAux_QName :: Int -> ATermTable -> (ATermTable, QName)
fromShATermAux_QName ix att = (att,
      case getShATerm ix att of
       ShAAppl idName _ _ ->
         if null idName || idName == "\"\"" then
              QN "" "_" ""
          else
           let idName' = read idName::String
               idName'' = if head idName' == '<' then
                               take ((length idName') -2) $ tail idName'
                             else idName'
               (pre, loc) = span (/= ':') idName''
           in if null loc then    -- no : in ID, only localName
                 QN "" pre ""
                 else
                  if (not $ isAlpha $ head pre)
                     then QN "" idName'' ""
                     else
                      if (take 4 pre == "http" ||
                          take 4 pre == "file")
                          then let (ns, loc2) = span (/= '#') idName''
                               in if length loc2 > 1 then
                                     QN "" (tail loc2) ns
                                     else QN "" ns ""
                          else  QN pre (tail loc) ""
       u -> fromShATermError "OWL.QName" u)

instance ShATermConvertible OntologyFile where
    toShATermAux att0 (OntologyFile a b) = do
        (att1, a') <- toShATermFromNamespace att0 a
        (att2, b') <- toShATerm' att1 b
        return $ addATerm (ShAAppl "OntologyFile" [a', b'] []) att2
    fromShATermAux ix att0 =
        case getShATerm ix att0 of
          ShAAppl "OntologyFile" [a,b] _ ->
              case fromShATermToNamespace a att0 of { (att1, a') ->
              case fromShATerm' b att1 of { (att2, b') ->
                 (att2, OntologyFile a' b') }}
          u -> fromShATermError "OntologyFile" u

toShATermFromNamespace :: ATermTable -> Namespace -> IO (ATermTable, Int)
toShATermFromNamespace att nsMap = do
    (att2, inds) <- foldM (\ (att0, l) t -> do
                    (att1, i) <- toShATermFromNS att0 t
                    return (att1, i : l)) (att, []) $ Map.toList nsMap
    return $ addATerm (ShAList (reverse inds) []) att2

toShATermFromNS :: ATermTable -> (String, String) -> IO (ATermTable, Int)
toShATermFromNS att0 (pre,u) = do
    (att1, pre') <- toShATerm' att0 pre
    (att2, uri') <- toShATerm' att1 u
    return $ addATerm (ShAAppl "NS" [pre', uri'] []) att2

fromShATermToNamespace :: Int -> ATermTable -> (ATermTable, Namespace)
fromShATermToNamespace ix att0 =
    case getShATerm ix att0 of
      ShAAppl "Namespace" [ind] _ ->
          case getShATerm ind att0 of
            ShAList ns _ ->
                case mapAccumL fromShATermToNS att0 ns of
                  (att1, ps) -> (att1, Map.fromList ps)
            u -> fromShATermError "OWL.NamespaceList" u
      u -> fromShATermError "OWL.Namespace" u

fromShATermToNS :: ATermTable -> Int -> (ATermTable, (String, String))
fromShATermToNS att0 ix =
    case getShATerm ix att0 of
      ShAAppl "NS" [name, u] _ ->
         case fromShATerm' name att0 of { (att1, name') ->
         case fromShATerm' u att1 of { (att2, uri') ->
             (att2, (name', take (length uri' -2) (tail uri')))}}
      u -> fromShATermError "OWL.NS" u

instance ShATermConvertible Constant where
    toShATermAux att0 (Constant a (Typed b)) = do
        (att1, a') <- toShATerm' att0 (a ++ "^^")
        (att2, b') <- toShATerm' att1 b
        return $ addATerm (ShAAppl "TypedConstant" [a', b'] []) att2
    toShATermAux att0 (Constant a (Untyped b)) = do
        (att1, a') <- toShATerm' att0 (a ++ "@" ++ b)
        return $ addATerm (ShAAppl "UntypedConstant" [a'] []) att1
 {- I wonder why TypedConstant has two arguments when writing
    but only one when reading -}
    fromShATermAux ix att0 =
        case getShATerm ix att0 of
            ShAAppl "TypedConstant" [a] _ ->
                    case fromShATerm' a att0 of { (att1, a') ->
                      let (b, c) = span (/='^') a'
                      in (att1, Constant b $ Typed $ mkQName $ drop 2 c) }
            ShAAppl "UntypedConstant" [a] _ ->
                    case fromShATerm' a att0 of { (att1, a') ->
                      let (b, c) = span (/='@') a'
                      in  (att1, Constant b $ Untyped $ drop 1 c ) }
            u -> fromShATermError "Constant" u

instance ShATermConvertible Entity where
    toShATermAux att0 (Entity ty euri) = do
       (att1, t) <- toShATerm' att0 euri
       return $ addATerm (ShAAppl (show ty) [t] []) att1
    fromShATermAux ix att0 = case getShATerm ix att0 of
       u@(ShAAppl tys [a] _) -> case readMaybe tys of
         Nothing -> fromShATermError "Entity" u
         Just ty -> case fromShATerm' a att0 of
           (att1, a') -> (att1, Entity ty a')
       u -> fromShATermError "Entity" u

instance ShATermConvertible Description where
  toShATermAux att0 xv = case xv of
    OWLClass a -> do
        (att1, a') <- toShATerm' att0 a
        return $ addATerm (ShAAppl "OWLClass" [a'] []) att1
    ObjectJunction ty a -> do
        (att1, a') <- toShATerm' att0 a
        return $ addATerm (ShAAppl ("Object" ++ show ty) [a'] []) att1
    ObjectComplementOf a -> do
        (att1, a') <- toShATerm' att0 a
        return $ addATerm (ShAAppl "ObjectComplementOf" [a'] []) att1
    ObjectOneOf a -> do
        (att1, a') <- toShATerm' att0 a
        return $ addATerm (ShAAppl "ObjectOneOf" [a'] []) att1
    ObjectValuesFrom ty a b -> do
        (att1, a') <- toShATerm' att0 a
        (att2, b') <- toShATerm' att1 b
        return $ addATerm (ShAAppl ("Object" ++ show ty) [a',b'] []) att2
    ObjectExistsSelf a -> do
        (att1, a') <- toShATerm' att0 a
        return $ addATerm (ShAAppl "ObjectExistsSelf" [a'] []) att1
    ObjectHasValue a b -> do
        (att1, a') <- toShATerm' att0 a
        (att2, b') <- toShATerm' att1 b
        return $ addATerm (ShAAppl "ObjectHasValue" [a',b'] []) att2
    ObjectCardinality (Cardinality ty a b c) -> do
        (att1, a') <- toShATerm' att0 a
        (att2, b') <- toShATerm' att1 b
        (att3, c') <- toShATerm' att2 c
        return $ addATerm (ShAAppl ("Object" ++ show ty) [a',b', c'] []) att3
    DataValuesFrom ty a b c -> do
        (att1, a') <- toShATerm' att0 a
        (att2, b') <- toShATerm' att1 b
        (att3, c') <- toShATerm' att2 c
        return $ addATerm (ShAAppl ("Data" ++ show ty) [a',b',c'] []) att3
    DataHasValue a b -> do
        (att1, a') <- toShATerm' att0 a
        (att2, b') <- toShATerm' att1 b
        return $ addATerm (ShAAppl "DataHasValue" [a',b'] []) att2
    DataCardinality (Cardinality ty a b c) -> do
        (att1, a') <- toShATerm' att0 a
        (att2, b') <- toShATerm' att1 b
        (att3, c') <- toShATerm' att2 c
        return $ addATerm (ShAAppl ("Data" ++ show ty) [a',b',c'] []) att3
  fromShATermAux ix att0 = case getShATerm ix att0 of
    ShAAppl "OWLClass" [a] _ ->
        case fromShATerm' a att0 of { (att1, a') ->
        (att1, OWLClass a') }
    ShAAppl "ObjectUnionOf" [a] _ ->
        case fromShATerm' a att0 of { (att1, a') ->
        (att1, ObjectJunction UnionOf a') }
    ShAAppl "ObjectIntersectionOf" [a] _ ->
        case fromShATerm' a att0 of { (att1, a') ->
        (att1, ObjectJunction IntersectionOf a') }
    ShAAppl "ObjectComplementOf" [a] _ ->
        case fromShATerm' a att0 of { (att1, a') ->
        (att1, ObjectComplementOf a') }
    ShAAppl "ObjectOneOf" [a] _ ->
        case fromShATerm' a att0 of { (att1, a') ->
        (att1, ObjectOneOf a') }
    ShAAppl "ObjectAllValuesFrom" [a,b] _ ->
        case fromShATerm' a att0 of { (att1, a') ->
        case fromShATerm' b att1 of { (att2, b') ->
        (att2, ObjectValuesFrom AllValuesFrom a' b') }}
    ShAAppl "ObjectSomeValuesFrom" [a,b] _ ->
       case fromShATerm' a att0 of { (att1, a') ->
        case fromShATerm' b att1 of { (att2, b') ->
        (att2, ObjectValuesFrom SomeValuesFrom a' b') }}
    ShAAppl "ObjectExistsSelf" [a] _ ->
        case fromShATerm' a att0 of { (att1, a') ->
        (att1, ObjectExistsSelf a') }
    ShAAppl "ObjectHasValue" [a,b] _ ->
        case fromShATerm' a att0 of { (att1, a') ->
        case fromShATerm' b att1 of { (att2, b') ->
        (att2, ObjectHasValue a' b') }}
    ShAAppl "ObjectMinCardinality" [a,b,c] _ ->
        case fromShATerm' a att0 of { (att1, a') ->
        case fromShATerm' b att1 of { (att2, b') ->
        case fromShATerm' c att2 of { (att3, c') ->
        (att3, ObjectCardinality $ Cardinality MinCardinality a' b' c') }}}
    ShAAppl "ObjectMaxCardinality" [a,b,c] _ ->
        case fromShATerm' a att0 of { (att1, a') ->
        case fromShATerm' b att1 of { (att2, b') ->
        case fromShATerm' c att2 of { (att3, c') ->
        (att3, ObjectCardinality $ Cardinality MaxCardinality a' b' c') }}}
    ShAAppl "ObjectExactCardinality" [a,b,c] _ ->
        case fromShATerm' a att0 of { (att1, a') ->
        case fromShATerm' b att1 of { (att2, b') ->
        case fromShATerm' c att2 of { (att3, c') ->
        (att3, ObjectCardinality $ Cardinality ExactCardinality a' b' c') }}}
    ShAAppl "DataAllValuesFrom" [a,b,c] _ ->
        case fromShATerm' a att0 of { (att1, a') ->
        case fromShATerm' b att1 of { (att2, b') ->
        case fromShATerm' c att2 of { (att3, c') ->
        (att3, DataValuesFrom AllValuesFrom a' b' c') }}}
    ShAAppl "DataSomeValuesFrom" [a,b,c] _ ->
        case fromShATerm' a att0 of { (att1, a') ->
        case fromShATerm' b att1 of { (att2, b') ->
        case fromShATerm' c att2 of { (att3, c') ->
        (att3, DataValuesFrom SomeValuesFrom a' b' c') }}}
    ShAAppl "DataHasValue" [a,b] _ ->
        case fromShATerm' a att0 of { (att1, a') ->
        case fromShATerm' b att1 of { (att2, b') ->
        (att2, DataHasValue a' b') }}
    ShAAppl "DataMinCardinality" [a,b,c] _ ->
        case fromShATerm' a att0 of { (att1, a') ->
        case fromShATerm' b att1 of { (att2, b') ->
        case fromShATerm' c att2 of { (att3, c') ->
        (att3, DataCardinality $ Cardinality MinCardinality a' b' c') }}}
    ShAAppl "DataMaxCardinality" [a,b,c] _ ->
        case fromShATerm' a att0 of { (att1, a') ->
        case fromShATerm' b att1 of { (att2, b') ->
        case fromShATerm' c att2 of { (att3, c') ->
        (att3, DataCardinality $ Cardinality MaxCardinality a' b' c') }}}
    ShAAppl "DataExactCardinality" [a,b,c] _ ->
        case fromShATerm' a att0 of { (att1, a') ->
        case fromShATerm' b att1 of { (att2, b') ->
        case fromShATerm' c att2 of { (att3, c') ->
        (att3, DataCardinality $ Cardinality ExactCardinality a' b' c') }}}
    u -> fromShATermError "Description" u

instance ShATermConvertible Axiom where
    toShATermAux att0 xv = case xv of
      EntityAnno a -> do
        (att1, a') <- toShATerm' att0 a
        return $ addATerm (ShAAppl "EntityAnno" [a'] []) att1
      PlainAxiom a f -> do
         (att1, a') <- toShATerm' att0 a
         toATC_Axiom a' att1 f
    fromShATermAux ix att0 = case getShATerm ix att0 of
      ShAAppl "EntityAnno" [a] _ ->
        case fromShATerm' a att0 of { (att1, a') ->
        (att1, EntityAnno a') }
      _ -> fromATC_Axiom ix att0

negPrefix :: PositiveOrNegative -> String
negPrefix ty = case ty of
    Positive -> ""
    Negative -> show ty

toATC_Axiom :: Int -> ATermTable -> PlainAxiom -> IO (ATermTable, Int)
toATC_Axiom a' att1 xv = case xv of
    SubClassOf b c -> do
        (att2, b') <- toShATerm' att1 b
        (att3, c') <- toShATerm' att2 c
        return $ addATerm (ShAAppl "SubClassOf" [a',b',c'] []) att3
    EquivOrDisjointClasses ty b -> do
        (att2, b') <- toShATerm' att1 b
        return $ addATerm (ShAAppl (show ty ++ "Classes") [a',b'] []) att2
    DisjointUnion b c -> do
        (att2, b') <- toShATerm' att1 b
        (att3, c') <- toShATerm' att2 c
        return $ addATerm (ShAAppl "DisjointUnion" [a',b',c'] []) att3
    SubObjectPropertyOf b c -> do
        (att2, b') <- toShATerm' att1 b
        (att3, c') <- toShATerm' att2 c
        return $ addATerm (ShAAppl "SubObjectPropertyOf" [a',b',
                                                          c'] []) att3
    EquivOrDisjointObjectProperties ty b -> do
        (att2, b') <- toShATerm' att1 b
        return $ addATerm (ShAAppl (show ty ++ "ObjectProperties")
                           [a', b'] []) att2
    ObjectPropertyDomainOrRange ty b c -> do
        (att2, b') <- toShATerm' att1 b
        (att3, c') <- toShATerm' att2 c
        return $ addATerm (ShAAppl ("ObjectProperty" ++ drop 3 (show ty))
                           [a', b', c'] []) att3
    InverseObjectProperties b c -> do
        (att2, b') <- toShATerm' att1 b
        (att3, c') <- toShATerm' att2 c
        return $ addATerm (ShAAppl "InverseObjectProperties" [a',b',
                                                              c'] []) att3
    ObjectPropertyCharacter ch b -> do
        (att2, b') <- toShATerm' att1 b
        return $ addATerm (ShAAppl (show ch ++ "ObjectProperty")
                           [a', b'] []) att2
    SubDataPropertyOf b c -> do
        (att2, b') <- toShATerm' att1 b
        (att3, c') <- toShATerm' att2 c
        return $ addATerm (ShAAppl "SubDataPropertyOf" [a',b',c'] []) att3
    EquivOrDisjointDataProperties ty b -> do
        (att2, b') <- toShATerm' att1 b
        return $ addATerm (ShAAppl (show ty ++ "DataProperties")
                           [a', b'] []) att2
    DataPropertyDomainOrRange (DataDomain c) b -> do
        (att2, b') <- toShATerm' att1 b
        (att3, c') <- toShATerm' att2 c
        return $ addATerm (ShAAppl "DataPropertyDomain" [a',b',c'] []) att3
    DataPropertyDomainOrRange (DataRange c) b -> do
        (att2, b') <- toShATerm' att1 b
        (att3, c') <- toShATerm' att2 c
        return $ addATerm (ShAAppl "DataPropertyRange" [a',b',c'] []) att3
    FunctionalDataProperty b -> do
        (att2, b') <- toShATerm' att1 b
        return $ addATerm (ShAAppl "FunctionalDataProperty" [a',
                                                             b'] []) att2
    SameOrDifferentIndividual ty b -> do
        (att2, b') <- toShATerm' att1 b
        return $ addATerm (ShAAppl (show ty ++ "Individual") [a',b'] []) att2
    ClassAssertion b c -> do
        (att2, b') <- toShATerm' att1 b
        (att3, c') <- toShATerm' att2 c
        return $ addATerm (ShAAppl "ClassAssertion" [a',b',c'] []) att3
    ObjectPropertyAssertion (Assertion b ty c d) -> do
        (att2, b') <- toShATerm' att1 b
        (att3, c') <- toShATerm' att2 c
        (att4, d') <- toShATerm' att3 d
        return $ addATerm (ShAAppl (negPrefix ty ++ "ObjectPropertyAssertion")
                           [a', b', c', d'] []) att4
    DataPropertyAssertion (Assertion b ty c d) -> do
        (att2, b') <- toShATerm' att1 b
        (att3, c') <- toShATerm' att2 c
        (att4, d') <- toShATerm' att3 d
        return $ addATerm (ShAAppl (negPrefix ty ++ "DataPropertyAssertion")
                           [a', b', c', d'] []) att4
    Declaration b -> do
        (att2, b') <- toShATerm' att1 b
        return $ addATerm (ShAAppl "Declaration" [a',b'] []) att2

fromATC_Axiom :: Int -> ATermTable -> (ATermTable, Axiom)
fromATC_Axiom ix att0 = case getShATerm ix att0 of
    ShAAppl "SubClassOf" [a,b,c] _ ->
        case fromShATerm' a att0 of { (att1, a') ->
        case fromShATerm' b att1 of { (att2, b') ->
        case fromShATerm' c att2 of { (att3, c') ->
        (att3, PlainAxiom a' $ SubClassOf b' c') }}}
    ShAAppl "EquivalentClasses" [a,b] _ ->
        case fromShATerm' a att0 of { (att1, a') ->
        case fromShATerm' b att1 of { (att2, b') ->
        (att2, PlainAxiom a' $ EquivOrDisjointClasses Equivalent b') }}
    ShAAppl "DisjointClasses" [a,b] _ ->
        case fromShATerm' a att0 of { (att1, a') ->
        case fromShATerm' b att1 of { (att2, b') ->
        (att2, PlainAxiom a' $ EquivOrDisjointClasses Disjoint b') }}
    ShAAppl "DisjointUnion" [a,b,c] _ ->
        case fromShATerm' a att0 of { (att1, a') ->
        case fromShATerm' b att1 of { (att2, b') ->
        case fromShATerm' c att2 of { (att3, c') ->
        (att3, PlainAxiom a' $ DisjointUnion b' c') }}}
    ShAAppl "SubObjectPropertyOf" [a,b,c] _ ->
        case fromShATerm' a att0 of { (att1, a') ->
        case fromShATerm' b att1 of { (att2, b') ->
        case fromShATerm' c att2 of { (att3, c') ->
        (att3, PlainAxiom a' $ SubObjectPropertyOf b' c') }}}
    ShAAppl "EquivalentObjectProperties" [a,b] _ ->
        case fromShATerm' a att0 of { (att1, a') ->
        case fromShATerm' b att1 of { (att2, b') ->
        (att2, PlainAxiom a' $ EquivOrDisjointObjectProperties Equivalent b') }}
    ShAAppl "DisjointObjectProperties" [a,b] _ ->
        case fromShATerm' a att0 of { (att1, a') ->
        case fromShATerm' b att1 of { (att2, b') ->
        (att2, PlainAxiom a' $ EquivOrDisjointObjectProperties Disjoint b') }}
    ShAAppl "ObjectPropertyDomain" [a,b,c] _ ->
        case fromShATerm' a att0 of { (att1, a') ->
        case fromShATerm' b att1 of { (att2, b') ->
        case fromShATerm' c att2 of { (att3, c') ->
        (att3, PlainAxiom a' $ ObjectPropertyDomainOrRange ObjDomain b' c') }}}
    ShAAppl "ObjectPropertyRange" [a,b,c] _ ->
        case fromShATerm' a att0 of { (att1, a') ->
        case fromShATerm' b att1 of { (att2, b') ->
        case fromShATerm' c att2 of { (att3, c') ->
        (att3, PlainAxiom a' $ ObjectPropertyDomainOrRange ObjRange b' c') }}}
    ShAAppl "InverseObjectProperties" [a,b,c] _ ->
        case fromShATerm' a att0 of { (att1, a') ->
        case fromShATerm' b att1 of { (att2, b') ->
        case fromShATerm' c att2 of { (att3, c') ->
        (att3, PlainAxiom a' $ InverseObjectProperties b' c') }}}
    ShAAppl "FunctionalObjectProperty" [a,b] _ ->
        case fromShATerm' a att0 of { (att1, a') ->
        case fromShATerm' b att1 of { (att2, b') ->
        (att2, PlainAxiom a' $ ObjectPropertyCharacter Functional b') }}
    ShAAppl "InverseFunctionalObjectProperty" [a,b] _ ->
        case fromShATerm' a att0 of { (att1, a') ->
        case fromShATerm' b att1 of { (att2, b') ->
        (att2, PlainAxiom a' $ ObjectPropertyCharacter InverseFunctional b') }}
    ShAAppl "ReflexiveObjectProperty" [a,b] _ ->
        case fromShATerm' a att0 of { (att1, a') ->
        case fromShATerm' b att1 of { (att2, b') ->
        (att2, PlainAxiom a' $ ObjectPropertyCharacter Reflexive b') }}
    ShAAppl "IrreflexiveObjectProperty" [a,b] _ ->
        case fromShATerm' a att0 of { (att1, a') ->
        case fromShATerm' b att1 of { (att2, b') ->
        (att2, PlainAxiom a' $ ObjectPropertyCharacter Irreflexive b') }}
    ShAAppl "SymmetricObjectProperty" [a,b] _ ->
        case fromShATerm' a att0 of { (att1, a') ->
        case fromShATerm' b att1 of { (att2, b') ->
        (att2, PlainAxiom a' $ ObjectPropertyCharacter Symmetric b') }}
    -- a- or anti- symmetric?
    ShAAppl "AntisymmetricObjectProperty" [a,b] _ ->
        case fromShATerm' a att0 of { (att1, a') ->
        case fromShATerm' b att1 of { (att2, b') ->
        (att2, PlainAxiom a' $ ObjectPropertyCharacter Antisymmetric b') }}
    ShAAppl "TransitiveObjectProperty" [a,b] _ ->
        case fromShATerm' a att0 of { (att1, a') ->
        case fromShATerm' b att1 of { (att2, b') ->
        (att2, PlainAxiom a' $ ObjectPropertyCharacter Transitive b') }}
    ShAAppl "SubDataPropertyOf" [a,b,c] _ ->
        case fromShATerm' a att0 of { (att1, a') ->
        case fromShATerm' b att1 of { (att2, b') ->
        case fromShATerm' c att2 of { (att3, c') ->
        (att3, PlainAxiom a' $ SubDataPropertyOf b' c') }}}
    ShAAppl "EquivalentDataProperties" [a,b] _ ->
        case fromShATerm' a att0 of { (att1, a') ->
        case fromShATerm' b att1 of { (att2, b') ->
        (att2, PlainAxiom a' $ EquivOrDisjointDataProperties Equivalent b') }}
    ShAAppl "DisjointDataProperties" [a,b] _ ->
        case fromShATerm' a att0 of { (att1, a') ->
        case fromShATerm' b att1 of { (att2, b') ->
        (att2, PlainAxiom a' $ EquivOrDisjointDataProperties Disjoint b') }}
    ShAAppl "DataPropertyDomain" [a,b,c] _ ->
        case fromShATerm' a att0 of { (att1, a') ->
        case fromShATerm' b att1 of { (att2, b') ->
        case fromShATerm' c att2 of { (att3, c') ->
        (att3, PlainAxiom a' $ DataPropertyDomainOrRange (DataDomain c') b') }}}
    ShAAppl "DataPropertyRange" [a,b,c] _ ->
        case fromShATerm' a att0 of { (att1, a') ->
        case fromShATerm' b att1 of { (att2, b') ->
        case fromShATerm' c att2 of { (att3, c') ->
        (att3, PlainAxiom a' $ DataPropertyDomainOrRange (DataRange c') b') }}}
    ShAAppl "FunctionalDataProperty" [a,b] _ ->
        case fromShATerm' a att0 of { (att1, a') ->
        case fromShATerm' b att1 of { (att2, b') ->
        (att2, PlainAxiom a' $ FunctionalDataProperty b') }}
    ShAAppl "SameIndividual" [a,b] _ ->
        case fromShATerm' a att0 of { (att1, a') ->
        case fromShATerm' b att1 of { (att2, b') ->
        (att2, PlainAxiom a' $ SameOrDifferentIndividual Same b') }}
    ShAAppl "DifferentIndividuals" [a,b] _ ->
        case fromShATerm' a att0 of { (att1, a') ->
        case fromShATerm' b att1 of { (att2, b') ->
        (att2, PlainAxiom a' $  SameOrDifferentIndividual Different b') }}
    ShAAppl "ClassAssertion" [a,b,c] _ ->
        case fromShATerm' a att0 of { (att1, a') ->
        case fromShATerm' b att1 of { (att2, b') ->
        case fromShATerm' c att2 of { (att3, c') ->
        (att3, PlainAxiom a' $ ClassAssertion b' c') }}}
    ShAAppl "ObjectPropertyAssertion" [a,b,c,d] _ ->
        case fromShATerm' a att0 of { (att1, a') ->
        case fromShATerm' b att1 of { (att2, b') ->
        case fromShATerm' c att2 of { (att3, c') ->
        case fromShATerm' d att3 of { (att4, d') ->
        (att4, PlainAxiom a' $ ObjectPropertyAssertion
        $ Assertion b' Positive c' d') }}}}
    ShAAppl "NegativeObjectPropertyAssertion" [a,b,c,d] _ ->
        case fromShATerm' a att0 of { (att1, a') ->
        case fromShATerm' b att1 of { (att2, b') ->
        case fromShATerm' c att2 of { (att3, c') ->
        case fromShATerm' d att3 of { (att4, d') ->
        (att4, PlainAxiom a' $ ObjectPropertyAssertion
        $ Assertion b' Negative c' d') }}}}
    ShAAppl "DataPropertyAssertion" [a,b,c,d] _ ->
        case fromShATerm' a att0 of { (att1, a') ->
        case fromShATerm' b att1 of { (att2, b') ->
        case fromShATerm' c att2 of { (att3, c') ->
        case fromShATerm' d att3 of { (att4, d') ->
        (att4, PlainAxiom a' $ DataPropertyAssertion
        $ Assertion b' Positive c' d') }}}}
    ShAAppl "NegativeDataPropertyAssertion" [a,b,c,d] _ ->
        case fromShATerm' a att0 of { (att1, a') ->
        case fromShATerm' b att1 of { (att2, b') ->
        case fromShATerm' c att2 of { (att3, c') ->
        case fromShATerm' d att3 of { (att4, d') ->
        (att4, PlainAxiom a' $ DataPropertyAssertion
        $ Assertion b' Negative c' d') }}}}
    ShAAppl "Declaration" [a,b] _ ->
        case fromShATerm' a att0 of { (att1, a') ->
        case fromShATerm' b att1 of { (att2, b') ->
        (att2, PlainAxiom a' $ Declaration b') }}
    u -> fromShATermError "Axiom" u

{-! for Ontology derive : ShATermConvertible !-}
{-! for Annotation derive : ShATermConvertible !-}
{-! for ObjectPropertyExpression derive : ShATermConvertible !-}
{-! for DatatypeFacet derive : ShATermConvertible !-}
{-! for DataRange derive : ShATermConvertible !-}
{-! for EntityAnnotation derive : ShATermConvertible !-}
{-! for SubObjectPropertyExpression derive : ShATermConvertible !-}
