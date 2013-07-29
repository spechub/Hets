{- |
Module      :  $Header$
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

import Common.GlobalAnnotations
import Common.Result
import Common.GlobalAnnotations
import Common.ExtSign
import Common.AS_Annotation

import qualified Common.Lib.Rel as Rel
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Maybe


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
          , properties  = propInfo (snd typesInfo)
          , instances = buildInstances m
          , links = buildLinks m
          }

emptyPropType :: (TypeInfo, PropInfo)
emptyPropType = ((TypeInfo Set.empty Rel.empty Set.empty),(PropInfo Set.empty Set.empty))


buildSignatureInfo :: Metamodel -> (TypeInfo, PropInfo)
buildSignatureInfo m = foldr (buildInfo) emptyPropType (element m)

buildInfo :: NamedElement -> (TypeInfo, PropInfo) -> (TypeInfo, PropInfo)
buildInfo (NamedElement el ow (TType (Type sup (DDataType d)))) (ti,pi) = 
  (TypeInfo (Set.insert (TypeClass el DataTypeKind) (typesI ti)) (typRelI ti) (absTypes ti), pi)
buildInfo (NamedElement el ow (TType (Type sup (DClass (Class su abs supC attr))))) (ti,pi) = 
  let classT = TypeClass el ClassKind
      rels = addSuperClasses classT supC (typRelI ti)
  in case abs of
      True -> (TypeInfo (Set.insert classT (typesI ti)) rels (Set.insert classT (absTypes ti)), pi)
      False -> (TypeInfo (Set.insert classT (typesI ti)) rels (absTypes ti), pi)
buildInfo (NamedElement el ow (TTypedElement (TypedElement ne ty (Property te me opp cla)))) (ti,pi) = 
  let sourceClassName = namedElementName (typeSuper (classSuperType cla))
      targetClassName = namedElementName (typeSuper ty)
      roles = Set.insert (targetRole prop) (Set.insert (sourceRole prop) (rolInfo pi))
      prop = createProperty el ty cla opp
  in
   (ti, PropInfo roles (Set.insert prop (propInfo pi)))


addSuperClasses :: TypeClass -> [Class] -> Rel.Rel TypeClass -> Rel.Rel TypeClass
addSuperClasses tc setC rels = foldr ((Rel.insertPair tc) . toTypeClass) rels setC

toTypeClass :: Class -> TypeClass
toTypeClass c = TypeClass (namedElementName (typeSuper (classSuperType c))) ClassKind


buildInstances :: Metamodel -> Map.Map String TypeClass
buildInstances m = foldr (createInstanceFromObject) Map.empty (object (head (model m)))

createInstanceFromObject :: Object -> Map.Map String TypeClass -> Map.Map String TypeClass
createInstanceFromObject ob map = 
	let targetClassType = 
              case typeSubClasses (objectType ob) of
                DDataType d -> DataTypeKind
                DClass c -> ClassKind
	in Map.insert (objectName ob) (TypeClass (namedElementName (typeSuper (objectType ob))) targetClassType) map


buildLinks :: Metamodel -> Set.Set LinkT
buildLinks m =  foldr (createLinksFromLinks) Set.empty (link (head (model m)))

createLinksFromLinks :: Link -> Set.Set LinkT -> Set.Set LinkT
createLinksFromLinks li links = 
  let name = namedElementName (typedElementSuper (propertySuper (linkType li)))
      ty = typedElementType (propertySuper (linkType li))
      cla = propertyClass (linkType li)
      opp = opposite (linkType li)
  in 
   Set.insert (LinkT (objectName (source li)) (objectName (target li)) (createProperty name ty cla opp)) links


createProperty :: String -> Type -> Class -> Maybe Property -> PropertyT
createProperty el ty cla opp =
  let sourceClassName = namedElementName (typeSuper (classSuperType cla))
      targetClassName = namedElementName (typeSuper ty)
      targetClassType = 
        case typeSubClasses ty of
          DDataType d -> DataTypeKind
          DClass c -> ClassKind
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
buildSentences meta = foldr (buildSen) [] (element meta)

buildSen :: NamedElement -> [Named Sen] -> [Named Sen]
buildSen (NamedElement el ow (TType x)) lis = lis
buildSen (NamedElement el ow (TTypedElement (TypedElement ne ty 
                                                      (Property te (MultiplicityElement low upp mes) opp cla)))) lis = 
  let clas = TypeClass (namedElementName (typeSuper (classSuperType cla))) ClassKind
  in 
   if low == upp 
   then (makeNamed "" (Sen (MultConstr clas el) low EQUAL)) : lis
   else if not (upp == -1) then
          if low > 0 then
            (makeNamed "" (Sen (MultConstr clas el) upp LEQ)) : ((makeNamed "" (Sen (MultConstr clas el) low GEQ)) : lis)
          else (makeNamed "" (Sen (MultConstr clas el) upp LEQ)) : lis
        else lis

