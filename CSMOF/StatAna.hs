{- |
Module      :  ./CSMOF/StatAna.hs
Description :  Static CSMOF analysis
Copyright   :  (c) Daniel Calegari Universidad de la Republica, Uruguay 2013
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  dcalegar@fing.edu.uy
Stability   :  provisional
Portability :  portable
-}

module CSMOF.StatAna where

import CSMOF.As
import CSMOF.Sign

import Common.Result
import Common.GlobalAnnotations
import Common.ExtSign
import Common.AS_Annotation

import qualified Common.Lib.Rel as Rel
import qualified Data.Set as Set
import qualified Data.HashMap.Strict as Map


basicAna :: (Metamodel, Sign, GlobalAnnos) -> Result (Metamodel, ExtSign Sign (), [Named Sen])
basicAna (meta, _, _) = return (meta, mkExtSign (buildSignature meta), buildSentences meta)


data TypeInfo = TypeInfo { typesI :: Set.Set TypeClass
                         , typRelI :: Rel.Rel TypeClass
                         , absTypes :: Set.Set TypeClass }

data PropInfo = PropInfo { rolInfo :: Set.Set Role
                         , propInfo :: Set.Set PropertyT }


buildSignature :: Metamodel -> Sign
buildSignature m =
  let typesInfo = buildSignatureInfo m
  in Sign { types = typesI (fst typesInfo)
          , typeRel = typRelI (fst typesInfo)
          , abstractClasses = absTypes (fst typesInfo)
          , roles = rolInfo (snd typesInfo)
          , properties = propInfo (snd typesInfo)
          , instances = buildInstances m
          , links = buildLinks m
          }

emptyPropType :: (TypeInfo, PropInfo)
emptyPropType = (TypeInfo Set.empty Rel.empty Set.empty, PropInfo Set.empty Set.empty)


buildSignatureInfo :: Metamodel -> (TypeInfo, PropInfo)
buildSignatureInfo = foldr buildInfo emptyPropType . element

buildInfo :: NamedElement -> (TypeInfo, PropInfo) -> (TypeInfo, PropInfo)
buildInfo (NamedElement el _ (TType (Type _ (DDataType _)))) (ti, pin) =
  (TypeInfo (Set.insert (TypeClass el DataTypeKind) (typesI ti)) (typRelI ti) (absTypes ti), pin)
buildInfo (NamedElement el _ (TType (Type _ (DClass (Class _ abst supC _))))) (ti, pin) =
  let classT = TypeClass el ClassKind
      rels = addSuperClasses classT supC (typRelI ti)
  in if abst then
     (TypeInfo (Set.insert classT (typesI ti)) rels
               (Set.insert classT (absTypes ti)), pin)
     else (TypeInfo (Set.insert classT (typesI ti)) rels (absTypes ti), pin)
buildInfo (NamedElement el _ (TTypedElement (TypedElement _ ty (Property _ _ opp cla)))) (ti, pin) =
  let role = Set.insert (targetRole prop) (Set.insert (sourceRole prop) (rolInfo pin))
      prop = createProperty el ty cla opp
  in
   (ti, PropInfo role (Set.insert prop (propInfo pin)))


addSuperClasses :: TypeClass -> [Class] -> Rel.Rel TypeClass -> Rel.Rel TypeClass
addSuperClasses tc = flip $ foldr (Rel.insertPair tc . toTypeClass)

toTypeClass :: Class -> TypeClass
toTypeClass c = TypeClass (namedElementName (typeSuper (classSuperType c))) ClassKind


buildInstances :: Metamodel -> Map.HashMap String TypeClass
buildInstances m =
  let models = model m
  in case models of
       [] -> Map.empty
       -- There is assumed that there is only one model to process, the thers are discarded
       mo : _ -> foldr createInstanceFromObject Map.empty (object mo)

createInstanceFromObject :: Object -> Map.HashMap String TypeClass -> Map.HashMap String TypeClass
createInstanceFromObject ob mapp =
  let targetClassType =
        case typeSubClasses (objectType ob) of
          DDataType _ -> DataTypeKind
          DClass _ -> ClassKind
  in Map.insert (objectName ob) (TypeClass (namedElementName (typeSuper (objectType ob))) targetClassType) mapp


buildLinks :: Metamodel -> Set.Set LinkT
buildLinks m =
  let models = model m
  in case models of
       [] -> Set.empty
       -- There is assumed that there is only one model to process, the thers are discarded
       mo : _ -> foldr createLinksFromLinks Set.empty (link mo)

createLinksFromLinks :: Link -> Set.Set LinkT -> Set.Set LinkT
createLinksFromLinks li linkk =
  let nam = namedElementName (typedElementSuper (propertySuper (linkType li)))
      ty = typedElementType (propertySuper (linkType li))
      cla = propertyClass (linkType li)
      opp = opposite (linkType li)
  in
   Set.insert (LinkT (objectName (source li)) (objectName (target li)) (createProperty nam ty cla opp)) linkk


createProperty :: String -> Type -> Class -> Maybe Property -> PropertyT
createProperty el ty cla opp =
  let sourceClassName = namedElementName (typeSuper (classSuperType cla))
      targetClassName = namedElementName (typeSuper ty)
      targetClassType =
        case typeSubClasses ty of
          DDataType _ -> DataTypeKind
          DClass _ -> ClassKind
  in
   case opp of
     Nothing -> PropertyT "_"
                (TypeClass sourceClassName ClassKind)
                el
                (TypeClass targetClassName targetClassType)
     Just p -> PropertyT (namedElementName (typedElementSuper (propertySuper p)))
                (TypeClass sourceClassName ClassKind)
                el
                (TypeClass targetClassName targetClassType)


buildSentences :: Metamodel -> [Named Sen]
buildSentences = foldr buildSen [] . element


buildSen :: NamedElement -> [Named Sen] -> [Named Sen]
buildSen (NamedElement _ _ (TType _)) lis = lis
buildSen (NamedElement el _ (TTypedElement (TypedElement _ _
                                                      (Property _ (MultiplicityElement low upp _) _ cla)))) lis =
  let clas = TypeClass (namedElementName (typeSuper (classSuperType cla))) ClassKind
  in
   if low == upp
   then makeNamed "" (Sen (MultConstr clas el) low EQUAL) : lis
   else if upp /= -1 then makeNamed "" (Sen (MultConstr clas el) upp LEQ) :
          if low > 0 then
             makeNamed "" (Sen (MultConstr clas el) low GEQ) : lis
          else lis
        else if low > 0 then
               makeNamed "" (Sen (MultConstr clas el) low GEQ) : lis
             else lis
