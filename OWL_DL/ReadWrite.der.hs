{- |
Module      :  $Header$
Copyright   :  (c) Heng Jiang, C. Maeder, Uni Bremen 2004-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

Automatic derivation of instances via DrIFT-rule Typeable, ShATermConvertible
  for the type(s): 'Message' 'Ontology' 'Directive' 'Annotation' 'DataLiteral' 'Fact' 'Individual' 'Value' 'Axiom' 'Func' 'Modality' 'Description' 'Restriction' 'Drcomponent' 'Ircomponent' 'Cardinality' 'DataRange'

manual instance for 'Ontology'
-}
{- todo:
    - implement test programms to check if
      input and output ATerms are equivalent.
-}
module OWL_DL.ReadWrite where

import qualified Common.Lib.Map as Map
import OWL_DL.AS
import Common.ATerm.Lib
import Common.DynamicUtils
import Data.Char
import Data.List
import Control.Monad

{- this is an overlapping instance that is now resolved in the
Ontology instance -}
{-
instance ShATermConvertible Namespace where
    -- von Map koennen viele namespace ATerm aufgabaut werden, die nach
    -- dem toShATerm noch zusammensetzen muessen... -> unschoen!
    toShATermAux = toShATermFromNamespace
    fromShATermAux = fromShATermToNamespace
-}

instance ShATermConvertible Ontology where
    toShATermAux att0 (Ontology a b c) = do
        (att1, a') <- toShATerm' att0 a
        (att2, b') <- toShATerm' att1 b
        (att3, c') <- toShATermFromNamespace att2 c
        return $ addATerm (ShAAppl "Ontology" [a',b',c'] []) att3
    fromShATermAux ix att0 =
        case getShATerm ix att0 of
            ShAAppl "Ontology" [a,b,c] _ ->
                    case fromShATerm' a att0 of { (att1, a') ->
                    case fromShATerm' b att1 of { (att2, b') ->
                    case fromShATermToNamespace c att2 of { (att3, c') ->
                    (att3, Ontology a' b' c') }}}
            u -> fromShATermError "Ontology" u

toShATermFromNamespace :: ATermTable -> Namespace -> IO (ATermTable, Int)
toShATermFromNamespace att nsMap = do
    (att2, inds) <- foldM (\ (att0, l) t -> do
                    (att1, i) <- toShATermFromNS att0 t
                    return (att1, i : l)) (att, []) $ Map.toList nsMap
    return $ addATerm (ShAList (reverse inds) []) att2

toShATermFromNS :: ATermTable -> (String, String) -> IO (ATermTable, Int)
toShATermFromNS att0 (pre,uri) = do
    (att1, pre') <- toShATerm' att0 pre
    (att2, uri') <- toShATerm' att1 uri
    return $ addATerm (ShAAppl "NS" [pre', uri'] []) att2

fromShATermToNamespace :: Int -> ATermTable -> (ATermTable, Namespace)
fromShATermToNamespace ix att0 =
    case getShATerm ix att0 of
      ShAAppl "Namespace" [ind] _ ->
          case getShATerm ind att0 of
            ShAList ns _ ->
                case mapAccumL fromShATermToNS att0 ns of
                  (att1, ps) -> (att1, Map.fromList ps)
            u -> fromShATermError "OWL_DL.NamespaceList" u
      u -> fromShATermError "OWL_DL.Namespace" u

fromShATermToNS :: ATermTable -> Int -> (ATermTable, (String, String))
fromShATermToNS att0 ix =
    case getShATerm ix att0 of
      ShAAppl "NS" [name, uri] _ ->
         case fromShATerm' name att0 of { (att1, name') ->
         case fromShATerm' uri att1 of { (att2, uri') ->
             (att2, (name', uri'))}}
      u -> fromShATermError "OWL_DL.NS" u

instance ShATermConvertible QName where
    toShATermAux att0 (QN aa ab _) = do
        (att1, aa') <- toShATerm' att0 (aa ++ ":" ++ ab)
        return $ addATerm (ShAAppl (aa ++ ":" ++ ab) [aa'] []) att1
    fromShATermAux ix att = (att,
        case getShATerm ix att of
         ShAAppl idName _ _ ->
           let idName' = read idName::String
               (pre, loc) = span (/= ':') idName'
           in if null loc then    -- no : in ID, only localName
                 QN "" pre ""
                 else
                  if (not $ isAlpha $ head pre)
                     then QN "" idName' ""
                     else
                      if (take 4 pre == "http" ||
                          take 4 pre == "file")
                          then let (ns, loc2) = span (/= '#') idName'
                               in if length loc2 > 1 then
                                     QN "" (tail loc2) ns
                                     else QN "" ns ""
                          else  QN pre (tail loc) ""
         u -> fromShATermError "OWL_DL.QName" u)

{-! for QName derive : Typeable !-}
{-! for Message derive : Typeable !-}
{-! for Ontology derive : Typeable !-}
{-! for Directive derive : Typeable !-}
{-! for Annotation derive : Typeable !-}
{-! for DataLiteral derive : Typeable !-}
{-! for Fact derive : Typeable !-}
{-! for Individual derive : Typeable !-}
{-! for Value derive : Typeable !-}
{-! for Axiom derive : Typeable !-}
{-! for Func derive : Typeable !-}
{-! for Modality derive : Typeable !-}
{-! for Description derive : Typeable !-}
{-! for Restriction derive : Typeable !-}
{-! for Drcomponent derive : Typeable !-}
{-! for Ircomponent derive : Typeable !-}
{-! for Cardinality derive : Typeable !-}
{-! for DataRange derive : Typeable !-}

{-! for Message derive : ShATermConvertible !-}
{-! for Directive derive : ShATermConvertible !-}
{-! for Annotation derive : ShATermConvertible !-}
{-! for DataLiteral derive : ShATermConvertible !-}
{-! for Fact derive : ShATermConvertible !-}
{-! for Individual derive : ShATermConvertible !-}
{-! for Value derive : ShATermConvertible !-}
{-! for Axiom derive : ShATermConvertible !-}
{-! for Func derive : ShATermConvertible !-}
{-! for Modality derive : ShATermConvertible !-}
{-! for Description derive : ShATermConvertible !-}
{-! for Restriction derive : ShATermConvertible !-}
{-! for Drcomponent derive : ShATermConvertible !-}
{-! for Ircomponent derive : ShATermConvertible !-}
{-! for Cardinality derive : ShATermConvertible !-}
{-! for DataRange derive : ShATermConvertible !-}
