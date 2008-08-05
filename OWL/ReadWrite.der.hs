{-# OPTIONS -w #-}
{- |
Module      :  $Header$
Copyright   :  (c) Heng Jiang, C. Maeder, Uni Bremen 2004-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Automatic derivation of instances via DrIFT-rule Typeable, ShATermConvertible
 the type in OWL.OWL11.FFS
manual instance for 'OntologyFile'
-}

module OWL.ReadWrite where

import qualified Data.Map as Map
import OWL.AS
import Common.QName ()
import Common.ATerm.Lib
import Data.Typeable
import Data.Char
import Data.List
import Control.Monad
import Text.XML.HXT.DOM.QualifiedName (mkName)

{- this is an overlapping instance that is now resolved in the
Ontology instance -}

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
    toShATermAux att0 (TypedConstant (a, b)) = do
        (att1, a') <- toShATerm' att0 (a ++ "^^")
        (att2, b') <- toShATerm' att1 b
        return $ addATerm (ShAAppl "TypedConstant" [a', b'] []) att2
    toShATermAux att0 (UntypedConstant (a, b)) = do
        (att1, a') <- toShATerm' att0 (a ++ "@" ++ b)
        return $ addATerm (ShAAppl "UntypedConstant" [a'] []) att1
    fromShATermAux ix att0 =
        case getShATerm ix att0 of
            ShAAppl "TypedConstant" [a] _ ->
                    case fromShATerm' a att0 of { (att1, a') ->
                      let (b, c) = span (/='^') a'
                          c' = mkName $ (if null c then "" else tail $ tail c)
                      in (att1, TypedConstant (b, c')) }
            ShAAppl "UntypedConstant" [a] _ ->
                    case fromShATerm' a att0 of { (att1, a') ->
                      let (b, c) = span (/='@') a'
                      in  (att1, UntypedConstant (b, if null c then "" else tail c)) }
            u -> fromShATermError "Constant" u

{-! for OntologyFile derive : Typeable!-}
{-! for Ontology derive : Typeable !-}
{-! for Annotation derive : Typeable !-}
{-! for Entity derive : Typeable !-}
{-! for Constant derive : Typeable !-}
{-! for ObjectPropertyExpression derive : Typeable !-}
{-! for DatatypeFacet derive : Typeable !-}
{-! for DataRange derive : Typeable !-}
{-! for EntityAnnotation derive : Typeable !-}
{-! for Description derive : Typeable !-}
{-! for SubObjectPropertyExpression derive : Typeable !-}
{-! for Axiom derive : Typeable !-}

{-! for Ontology derive : ShATermConvertible !-}
{-! for Annotation derive : ShATermConvertible !-}
{-! for Entity derive : ShATermConvertible !-}
{-! for ObjectPropertyExpression derive : ShATermConvertible !-}
{-! for DatatypeFacet derive : ShATermConvertible !-}
{-! for DataRange derive : ShATermConvertible !-}
{-! for EntityAnnotation derive : ShATermConvertible !-}
{-! for Description derive : ShATermConvertible !-}
{-! for SubObjectPropertyExpression derive : ShATermConvertible !-}
{-! for Axiom derive : ShATermConvertible !-}
