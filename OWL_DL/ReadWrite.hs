{- |
Module      :  $Header$
Copyright   :  (c) Heng Jiang, Uni Bremen 2004-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  jiang@tzi.de
Stability   :  provisional
Portability :  portable

This module is equivalent to OWL_DL.ATC_OWL_DL.hs which is missing, therefore.
-}

{- todo:
    - implement test programm calls to check if
      input and output ATerms are equivalent.

-}
module OWL_DL.ReadWrite where

import Text.XML.HXT.DOM.XmlTreeTypes
import qualified Common.Lib.Map as Map
import OWL_DL.AS
import Common.ATerm.Lib
import Common.DynamicUtils
import Data.Char

_tc_QNameTc :: TyCon
_tc_QNameTc = mkTyCon "QName"
instance Typeable QName where
    typeOf _ = mkTyConApp _tc_QNameTc []

_tc_MessageTc :: TyCon
_tc_MessageTc = mkTyCon "Message"
instance Typeable Message where
    typeOf _ = mkTyConApp _tc_MessageTc []

_tc_OntologyTc :: TyCon
_tc_OntologyTc = mkTyCon "Ontology"
instance Typeable Ontology where
    typeOf _ = mkTyConApp _tc_OntologyTc []

_tc_DirectiveTc :: TyCon
_tc_DirectiveTc = mkTyCon "Directive"
instance Typeable Directive where
    typeOf _ = mkTyConApp _tc_DirectiveTc []

_tc_AnnotationTc :: TyCon
_tc_AnnotationTc = mkTyCon "Annotation"
instance Typeable Annotation where
    typeOf _ = mkTyConApp _tc_AnnotationTc []

_tc_DataLiteralTc :: TyCon
_tc_DataLiteralTc = mkTyCon "DataLiteral"
instance Typeable DataLiteral where
    typeOf _ = mkTyConApp _tc_DataLiteralTc []

_tc_FactTc :: TyCon
_tc_FactTc = mkTyCon "Fact"
instance Typeable Fact where
    typeOf _ = mkTyConApp _tc_FactTc []

_tc_IndividualTc :: TyCon
_tc_IndividualTc = mkTyCon "Individual"
instance Typeable Individual where
    typeOf _ = mkTyConApp _tc_IndividualTc []

_tc_ValueTc :: TyCon
_tc_ValueTc = mkTyCon "Value"
instance Typeable Value where
    typeOf _ = mkTyConApp _tc_ValueTc []

_tc_AxiomTc :: TyCon
_tc_AxiomTc = mkTyCon "Axiom"
instance Typeable Axiom where
    typeOf _ = mkTyConApp _tc_AxiomTc []

_tc_FuncTc :: TyCon
_tc_FuncTc = mkTyCon "Func"
instance Typeable Func where
    typeOf _ = mkTyConApp _tc_FuncTc []

_tc_ModalityTc :: TyCon
_tc_ModalityTc = mkTyCon "Modality"
instance Typeable Modality where
    typeOf _ = mkTyConApp _tc_ModalityTc []

_tc_DescriptionTc :: TyCon
_tc_DescriptionTc = mkTyCon "Description"
instance Typeable Description where
    typeOf _ = mkTyConApp _tc_DescriptionTc []

_tc_RestrictionTc :: TyCon
_tc_RestrictionTc = mkTyCon "Restriction"
instance Typeable Restriction where
    typeOf _ = mkTyConApp _tc_RestrictionTc []

_tc_DrcomponentTc :: TyCon
_tc_DrcomponentTc = mkTyCon "Drcomponent"
instance Typeable Drcomponent where
    typeOf _ = mkTyConApp _tc_DrcomponentTc []

_tc_IrcomponentTc :: TyCon
_tc_IrcomponentTc = mkTyCon "Ircomponent"
instance Typeable Ircomponent where
    typeOf _ = mkTyConApp _tc_IrcomponentTc []

_tc_CardinalityTc :: TyCon
_tc_CardinalityTc = mkTyCon "Cardinality"
instance Typeable Cardinality where
    typeOf _ = mkTyConApp _tc_CardinalityTc []

_tc_DataRangeTc :: TyCon
_tc_DataRangeTc = mkTyCon "DataRange"
instance Typeable DataRange where
    typeOf _ = mkTyConApp _tc_DataRangeTc []

instance ShATermConvertible Message where
    toShATerm att0 (Message aa) =
        case toShATerm att0 aa of { (att1,aa') ->
        addATerm (ShAAppl "Message" [ aa' ] []) att1 }
    fromShATerm att =
        case getATerm att of
            ShAAppl "Message" [ aa ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    Message aa' }
            u -> fromShATermError "OWL_DL.Message" u

instance ShATermConvertible Ontology where
    toShATerm att0 (Ontology aa ab ac) =
        case toShATerm att0 aa of { (att1,aa') ->
        case toShATerm att1 ab of { (att2,ab') ->
        case toShATerm att2 ac of { (att3,ac') ->
        addATerm (ShAAppl "Ontology" [ aa',ab',ac'] []) att3 }}}
    fromShATerm att =
        case getATerm att of
            ShAAppl "Ontology" [ aa,ab,ac ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    case fromShATerm $ getATermByIndex1 ab att of { ab' ->
                    case fromShATerm $ getATermByIndex1 ac att of { ac' ->
                    Ontology aa' ab' ac' }}}
            u -> fromShATermError "OWL_DL.Ontology" u

instance ShATermConvertible Namespace where
    -- von Map koennen viele namespace ATerm aufgabaut werden, die nach
    -- dem toShATerm noch zusammensetzen muessen... -> unschoen!
    toShATerm att nsMap =
        toShATerm' att [] (Map.toList nsMap)
      where toShATerm' att0 nsList [] =
              case addATerm (ShAList nsList []) att0 of { (att1, nl) ->
                  addATerm (ShAAppl "Namespace" [nl] []) att1}
            toShATerm' att0 nsList ((pre,uri):rest) =
              case toShATerm att0 pre of { (att1, pre') ->
              case toShATerm att1 uri of { (att2, uri') ->
              case addATerm (ShAAppl "NS" [pre', uri'] []) att2 of {
               (att3, ns) -> toShATerm' att3 (ns:nsList) rest }}}
    fromShATerm att = case getATerm att of
             ShAAppl "Namespace" [ind] _ ->
               case getATerm $ getATermByIndex1 ind att of
                 ShAList ns1 _ ->
                   mkMap ns1 (Map.empty)
                 u -> fromShATermError "OWL_DL.Namespace" u
             u -> fromShATermError "OWL_DL.Namespace" u
     where
      mkMap :: [Int] -> Namespace -> Namespace
      mkMap [] mp = mp
      mkMap (h:r) mp = case getATerm $ getATermByIndex1 h att of
                 ShAAppl "NS" [name, uri] _ ->
                     case fromShATerm $ getATermByIndex1 name att of { name' ->
                     case fromShATerm $ getATermByIndex1 uri att of { uri' ->
                           mkMap r (Map.insert name' uri' mp)}}
                 u -> fromShATermError "OWL_DL.mkMap.Namespace" u

instance ShATermConvertible QName where
    toShATerm att0 (QN aa ab _) =
        case toShATerm att0 (aa ++ ":" ++ ab) of {(att1, aa') ->
           addATerm (ShAAppl (aa ++ ":" ++ ab) [aa'] []) att1}
    fromShATerm att =
        case getATerm att of
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
         u -> fromShATermError "OWL_DL.QName" u

instance ShATermConvertible Directive where
    toShATerm att0 (Anno aa) =
        case toShATerm att0 aa of { (att1,aa') ->
        addATerm (ShAAppl "Anno" [ aa' ] []) att1 }
    toShATerm att0 (Ax aa) =
        case toShATerm att0 aa of { (att1,aa') ->
        addATerm (ShAAppl "Ax" [ aa' ] []) att1 }
    toShATerm att0 (Fc aa) =
        case toShATerm att0 aa of { (att1,aa') ->
        addATerm (ShAAppl "Fc" [ aa' ] []) att1 }
    fromShATerm att =
        case getATerm att of
            ShAAppl "Anno" [ aa ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    Anno aa' }
            ShAAppl "Ax" [ aa ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    Ax aa' }
            ShAAppl "Fc" [ aa ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    Fc aa' }
            u -> fromShATermError "OWL_DL.Directive" u

instance ShATermConvertible Annotation where
    toShATerm att0 (OntoAnnotation aa ab) =
        case toShATerm att0 aa of { (att1,aa') ->
        case toShATerm att1 ab of { (att2,ab') ->
        addATerm (ShAAppl "OntoAnnotation" [ aa',ab' ] []) att2 }}
    toShATerm att0 (URIAnnotation aa ab) =
        case toShATerm att0 aa of { (att1,aa') ->
        case toShATerm att1 ab of { (att2,ab') ->
        addATerm (ShAAppl "URIAnnotation" [ aa',ab' ] []) att2 }}
    toShATerm att0 (DLAnnotation aa ab) =
        case toShATerm att0 aa of { (att1,aa') ->
        case toShATerm att1 ab of { (att2,ab') ->
        addATerm (ShAAppl "DLAnnotation" [ aa',ab' ] []) att2 }}
    toShATerm att0 (IndivAnnotation aa ab) =
        case toShATerm att0 aa of { (att1,aa') ->
        case toShATerm att1 ab of { (att2,ab') ->
        addATerm (ShAAppl "IndivAnnotation" [ aa',ab' ] []) att2 }}
    fromShATerm att =
        case getATerm att of
            ShAAppl "OntoAnnotation" [ aa,ab ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    case fromShATerm $ getATermByIndex1 ab att of { ab' ->
                    OntoAnnotation aa' ab' }}
            ShAAppl "URIAnnotation" [ aa,ab ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    case fromShATerm $ getATermByIndex1 ab att of { ab' ->
                    URIAnnotation aa' ab' }}
            ShAAppl "DLAnnotation" [ aa,ab ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    case fromShATerm $ getATermByIndex1 ab att of { ab' ->
                    DLAnnotation aa' ab' }}
            ShAAppl "IndivAnnotation" [ aa,ab ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    case fromShATerm $ getATermByIndex1 ab att of { ab' ->
                    IndivAnnotation aa' ab' }}
            u -> fromShATermError "OWL_DL.Annotation" u

instance ShATermConvertible DataLiteral where
    toShATerm att0 (TypedL aa) =
        case toShATerm att0 aa of { (att1,aa') ->
        addATerm (ShAAppl "TypedL" [ aa' ] []) att1 }
    toShATerm att0 (PlainL aa) =
        case toShATerm att0 aa of { (att1,aa') ->
        addATerm (ShAAppl "PlainL" [ aa' ] []) att1 }
    toShATerm att0 (Plain aa) =
        case toShATerm att0 aa of { (att1,aa') ->
        addATerm (ShAAppl "Plain" [ aa' ] []) att1 }
    toShATerm att0 (RDFSL aa) =
        case toShATerm att0 aa of { (att1,aa') ->
        addATerm (ShAAppl "RDFSL" [ aa' ] []) att1 }
    fromShATerm att =
        case getATerm att of
            ShAAppl "TypedL" [ aa ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    TypedL aa' }
            ShAAppl "PlainL" [ aa ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    PlainL aa' }
            ShAAppl "Plain" [ aa ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    Plain aa' }
            ShAAppl "RDFSL" [ aa ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    RDFSL aa' }
            u -> fromShATermError "OWL_DL.DataLiteral" u

instance ShATermConvertible Fact where
    toShATerm att0 (Indiv aa) =
        case toShATerm att0 aa of { (att1,aa') ->
        addATerm (ShAAppl "Indiv" [ aa' ] []) att1 }
    toShATerm att0 (SameIndividual aa ab ac) =
        case toShATerm att0 aa of { (att1,aa') ->
        case toShATerm att1 ab of { (att2,ab') ->
        case toShATerm att2 ac of { (att3,ac') ->
        addATerm (ShAAppl "SameIndividual" [ aa',ab',ac' ] []) att3 }}}
    toShATerm att0 (DifferentIndividuals aa ab ac) =
        case toShATerm att0 aa of { (att1,aa') ->
        case toShATerm att1 ab of { (att2,ab') ->
        case toShATerm att2 ac of { (att3,ac') ->
        addATerm (ShAAppl "DifferentIndividuals" [ aa',ab',ac' ] []) att3 }}}
    fromShATerm att =
        case getATerm att of
            ShAAppl "Indiv" [ aa ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    Indiv aa' }
            ShAAppl "SameIndividual" [ aa,ab,ac ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    case fromShATerm $ getATermByIndex1 ab att of { ab' ->
                    case fromShATerm $ getATermByIndex1 ac att of { ac' ->
                    SameIndividual aa' ab' ac' }}}
            ShAAppl "DifferentIndividuals" [ aa,ab,ac ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    case fromShATerm $ getATermByIndex1 ab att of { ab' ->
                    case fromShATerm $ getATermByIndex1 ac att of { ac' ->
                    DifferentIndividuals aa' ab' ac' }}}
            u -> fromShATermError "OWL_DL.Fact" u

instance ShATermConvertible Individual where
    toShATerm att0 (Individual aa ab ac ad) =
        case toShATerm att0 aa of { (att1,aa') ->
        case toShATerm att1 ab of { (att2,ab') ->
        case toShATerm att2 ac of { (att3,ac') ->
        case toShATerm att3 ad of { (att4,ad') ->
        addATerm (ShAAppl "Individual" [ aa',ab',ac',ad' ] []) att4 }}}}
    fromShATerm att =
        case getATerm att of
            ShAAppl "Individual" [ aa,ab,ac,ad ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    case fromShATerm $ getATermByIndex1 ab att of { ab' ->
                    case fromShATerm $ getATermByIndex1 ac att of { ac' ->
                    case fromShATerm $ getATermByIndex1 ad att of { ad' ->
                    Individual aa' ab' ac' ad' }}}}
            u -> fromShATermError "OWL_DL.Individual" u

instance ShATermConvertible Value where
    toShATerm att0 (ValueID aa ab) =
        case toShATerm att0 aa of { (att1,aa') ->
        case toShATerm att1 ab of { (att2,ab') ->
        addATerm (ShAAppl "ValueID" [ aa',ab' ] []) att2 }}
    toShATerm att0 (ValueIndiv aa ab) =
        case toShATerm att0 aa of { (att1,aa') ->
        case toShATerm att1 ab of { (att2,ab') ->
        addATerm (ShAAppl "ValueIndiv" [ aa',ab' ] []) att2 }}
    toShATerm att0 (ValueDL aa ab) =
        case toShATerm att0 aa of { (att1,aa') ->
        case toShATerm att1 ab of { (att2,ab') ->
        addATerm (ShAAppl "ValueDL" [ aa',ab' ] []) att2 }}
    fromShATerm att =
        case getATerm att of
            ShAAppl "ValueID" [ aa,ab ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    case fromShATerm $ getATermByIndex1 ab att of { ab' ->
                    ValueID aa' ab' }}
            ShAAppl "ValueIndiv" [ aa,ab ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    case fromShATerm $ getATermByIndex1 ab att of { ab' ->
                    ValueIndiv aa' ab' }}
            ShAAppl "ValueDL" [ aa,ab ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    case fromShATerm $ getATermByIndex1 ab att of { ab' ->
                    ValueDL aa' ab' }}
            u -> fromShATermError "OWL_DL.Value" u

instance ShATermConvertible Axiom where
    toShATerm att0 Thing =
        addATerm (ShAAppl "Thing" [] []) att0
    toShATerm att0 AxNothing =
        addATerm (ShAAppl "Nothing" [] []) att0
    toShATerm att0 (Class aa ab ac ad ae) =
        case toShATerm att0 aa of { (att1,aa') ->
        case toShATerm att1 ab of { (att2,ab') ->
        case toShATerm att2 ac of { (att3,ac') ->
        case toShATerm att3 ad of { (att4,ad') ->
        case toShATerm att4 ae of { (att5,ae') ->
        addATerm (ShAAppl "Class" [ aa',ab',ac',ad',ae' ] []) att5 }}}}}
    toShATerm att0 (EnumeratedClass aa ab ac ad) =
        case toShATerm att0 aa of { (att1,aa') ->
        case toShATerm att1 ab of { (att2,ab') ->
        case toShATerm att2 ac of { (att3,ac') ->
        case toShATerm att3 ad of { (att4,ad') ->
        addATerm (ShAAppl "EnumeratedClass" [ aa',ab',ac',ad' ] []) att4 }}}}
    toShATerm att0 (DisjointClasses aa ab ac) =
        case toShATerm att0 aa of { (att1,aa') ->
        case toShATerm att1 ab of { (att2,ab') ->
        case toShATerm att2 ac of { (att3,ac') ->
        addATerm (ShAAppl "DisjointClasses" [ aa',ab',ac' ] []) att3 }}}
    toShATerm att0 (EquivalentClasses aa ab) =
        case toShATerm att0 aa of { (att1,aa') ->
        case toShATerm att1 ab of { (att2,ab') ->
        addATerm (ShAAppl "EquivalentClasses" [ aa',ab' ] []) att2 }}
    toShATerm att0 (SubClassOf aa ab) =
        case toShATerm att0 aa of { (att1,aa') ->
        case toShATerm att1 ab of { (att2,ab') ->
        addATerm (ShAAppl "SubClassOf" [ aa',ab' ] []) att2 }}
    toShATerm att0 (Datatype aa ab ac) =
        case toShATerm att0 aa of { (att1,aa') ->
        case toShATerm att1 ab of { (att2,ab') ->
        case toShATerm att2 ac of { (att3,ac') ->
        addATerm (ShAAppl "Datatype" [ aa',ab',ac' ] []) att3 }}}
    toShATerm att0 (DatatypeProperty aa ab ac ad ae af ag) =
        case toShATerm att0 aa of { (att1,aa') ->
        case toShATerm att1 ab of { (att2,ab') ->
        case toShATerm att2 ac of { (att3,ac') ->
        case toShATerm att3 ad of { (att4,ad') ->
        case toShATerm att4 ae of { (att5,ae') ->
        case toShATerm att5 af of { (att6,af') ->
        case toShATerm att6 ag of { (att7,ag') ->
        addATerm (ShAAppl "DatatypeProperty" [ aa',ab',ac',ad',ae',af',ag' ] []) att7 }}}}}}}
    toShATerm att0 (ObjectProperty aa ab ac ad ae af ag ah ai) =
        case toShATerm att0 aa of { (att1,aa') ->
        case toShATerm att1 ab of { (att2,ab') ->
        case toShATerm att2 ac of { (att3,ac') ->
        case toShATerm att3 ad of { (att4,ad') ->
        case toShATerm att4 ae of { (att5,ae') ->
        case toShATerm att5 af of { (att6,af') ->
        case toShATerm att6 ag of { (att7,ag') ->
        case toShATerm att7 ah of { (att8,ah') ->
        case toShATerm att8 ai of { (att9,ai') ->
        addATerm (ShAAppl "ObjectProperty" [ aa',ab',ac',ad',ae',af',ag',ah',ai' ] []) att9 }}}}}}}}}
    toShATerm att0 (AnnotationProperty aa ab) =
        case toShATerm att0 aa of { (att1,aa') ->
        case toShATerm att1 ab of { (att2,ab') ->
        addATerm (ShAAppl "AnnotationProperty" [ aa',ab' ] []) att2 }}
    toShATerm att0 (OntologyProperty aa ab) =
        case toShATerm att0 aa of { (att1,aa') ->
        case toShATerm att1 ab of { (att2,ab') ->
        addATerm (ShAAppl "OntologyProperty" [ aa',ab' ] []) att2 }}
    toShATerm att0 (DEquivalentProperties aa ab ac) =
        case toShATerm att0 aa of { (att1,aa') ->
        case toShATerm att1 ab of { (att2,ab') ->
        case toShATerm att2 ac of { (att3,ac') ->
        addATerm (ShAAppl "DEquivalentProperties" [ aa',ab',ac' ] []) att3 }}}
    toShATerm att0 (DSubPropertyOf aa ab) =
        case toShATerm att0 aa of { (att1,aa') ->
        case toShATerm att1 ab of { (att2,ab') ->
        addATerm (ShAAppl "DSubPropertyOf" [ aa',ab' ] []) att2 }}
    toShATerm att0 (IEquivalentProperties aa ab ac) =
        case toShATerm att0 aa of { (att1,aa') ->
        case toShATerm att1 ab of { (att2,ab') ->
        case toShATerm att2 ac of { (att3,ac') ->
        addATerm (ShAAppl "IEquivalentProperties" [ aa',ab',ac' ] []) att3 }}}
    toShATerm att0 (ISubPropertyOf aa ab) =
        case toShATerm att0 aa of { (att1,aa') ->
        case toShATerm att1 ab of { (att2,ab') ->
        addATerm (ShAAppl "ISubPropertyOf" [ aa',ab' ] []) att2 }}
    fromShATerm att =
        case getATerm att of
            ShAAppl "Thing" [ ] _ ->
                    Thing
            ShAAppl "Nothing" [ ] _ ->
                    AxNothing
            ShAAppl "Class" [ aa,ab,ac,ad,ae ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    case fromShATerm $ getATermByIndex1 ab att of { ab' ->
                    case fromShATerm $ getATermByIndex1 ac att of { ac' ->
                    case fromShATerm $ getATermByIndex1 ad att of { ad' ->
                    case fromShATerm $ getATermByIndex1 ae att of { ae' ->
                    Class aa' ab' ac' ad' ae' }}}}}
            ShAAppl "EnumeratedClass" [ aa,ab,ac,ad ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    case fromShATerm $ getATermByIndex1 ab att of { ab' ->
                    case fromShATerm $ getATermByIndex1 ac att of { ac' ->
                    case fromShATerm $ getATermByIndex1 ad att of { ad' ->
                    EnumeratedClass aa' ab' ac' ad' }}}}
            ShAAppl "DisjointClasses" [ aa,ab,ac ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    case fromShATerm $ getATermByIndex1 ab att of { ab' ->
                    case fromShATerm $ getATermByIndex1 ac att of { ac' ->
                    DisjointClasses aa' ab' ac' }}}
            ShAAppl "EquivalentClasses" [ aa,ab ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    case fromShATerm $ getATermByIndex1 ab att of { ab' ->
                    EquivalentClasses aa' ab' }}
            ShAAppl "SubClassOf" [ aa,ab ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    case fromShATerm $ getATermByIndex1 ab att of { ab' ->
                    SubClassOf aa' ab' }}
            ShAAppl "Datatype" [ aa,ab,ac ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    case fromShATerm $ getATermByIndex1 ab att of { ab' ->
                    case fromShATerm $ getATermByIndex1 ac att of { ac' ->
                    Datatype aa' ab' ac' }}}
            ShAAppl "DatatypeProperty" [ aa,ab,ac,ad,ae,af,ag ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    case fromShATerm $ getATermByIndex1 ab att of { ab' ->
                    case fromShATerm $ getATermByIndex1 ac att of { ac' ->
                    case fromShATerm $ getATermByIndex1 ad att of { ad' ->
                    case fromShATerm $ getATermByIndex1 ae att of { ae' ->
                    case fromShATerm $ getATermByIndex1 af att of { af' ->
                    case fromShATerm $ getATermByIndex1 ag att of { ag' ->
                    DatatypeProperty aa' ab' ac' ad' ae' af' ag' }}}}}}}
            ShAAppl "ObjectProperty" [ aa,ab,ac,ad,ae,af,ag,ah,ai ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    case fromShATerm $ getATermByIndex1 ab att of { ab' ->
                    case fromShATerm $ getATermByIndex1 ac att of { ac' ->
                    case fromShATerm $ getATermByIndex1 ad att of { ad' ->
                    case fromShATerm $ getATermByIndex1 ae att of { ae' ->
                    case fromShATerm $ getATermByIndex1 af att of { af' ->
                    case fromShATerm $ getATermByIndex1 ag att of { ag' ->
                    case fromShATerm $ getATermByIndex1 ah att of { ah' ->
                    case fromShATerm $ getATermByIndex1 ai att of { ai' ->
                    ObjectProperty aa' ab' ac' ad' ae' af' ag' ah' ai' }}}}}}}}}
            ShAAppl "AnnotationProperty" [ aa,ab ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    case fromShATerm $ getATermByIndex1 ab att of { ab' ->
                    AnnotationProperty aa' ab' }}
            ShAAppl "OntologyProperty" [ aa,ab ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    case fromShATerm $ getATermByIndex1 ab att of { ab' ->
                    OntologyProperty aa' ab' }}
            ShAAppl "DEquivalentProperties" [ aa,ab,ac ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    case fromShATerm $ getATermByIndex1 ab att of { ab' ->
                    case fromShATerm $ getATermByIndex1 ac att of { ac' ->
                    DEquivalentProperties aa' ab' ac' }}}
            ShAAppl "DSubPropertyOf" [ aa,ab ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    case fromShATerm $ getATermByIndex1 ab att of { ab' ->
                    DSubPropertyOf aa' ab' }}
            ShAAppl "IEquivalentProperties" [ aa,ab,ac ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    case fromShATerm $ getATermByIndex1 ab att of { ab' ->
                    case fromShATerm $ getATermByIndex1 ac att of { ac' ->
                    IEquivalentProperties aa' ab' ac' }}}
            ShAAppl "ISubPropertyOf" [ aa,ab ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    case fromShATerm $ getATermByIndex1 ab att of { ab' ->
                    ISubPropertyOf aa' ab' }}
            u -> fromShATermError "OWL_DL.Axiom" u

instance ShATermConvertible Func where
    toShATerm att0 Functional =
        addATerm (ShAAppl "Functional" [] []) att0
    toShATerm att0 InverseFunctional =
        addATerm (ShAAppl "InverseFunctional" [] []) att0
    toShATerm att0 Functional_InverseFunctional =
        addATerm (ShAAppl "Functional_InverseFunctional" [] []) att0
    toShATerm att0 Transitive =
        addATerm (ShAAppl "Transitive" [] []) att0
    fromShATerm att =
        case getATerm att of
            ShAAppl "Functional" [ ] _ ->
                    Functional
            ShAAppl "InverseFunctional" [ ] _ ->
                    InverseFunctional
            ShAAppl "Functional_InverseFunctional" [ ] _ ->
                    Functional_InverseFunctional
            ShAAppl "Transitive" [ ] _ ->
                    Transitive
            u -> fromShATermError "OWL_DL.Func" u

instance ShATermConvertible Modality where
    toShATerm att0 Complete =
        addATerm (ShAAppl "Complete" [] []) att0
    toShATerm att0 Partial =
        addATerm (ShAAppl "Partial" [] []) att0
    fromShATerm att =
        case getATerm att of
            ShAAppl "Complete" [ ] _ ->
                    Complete
            ShAAppl "Partial" [ ] _ ->
                    Partial
            u -> fromShATermError "OWL_DL.Modality" u

instance ShATermConvertible Description where
    toShATerm att0 (DC aa) =
        case toShATerm att0 aa of { (att1,aa') ->
        addATerm (ShAAppl "DC" [ aa' ] []) att1 }
    toShATerm att0 (DR aa) =
        case toShATerm att0 aa of { (att1,aa') ->
        addATerm (ShAAppl "DR" [ aa' ] []) att1 }
    toShATerm att0 (UnionOf aa) =
        case toShATerm att0 aa of { (att1,aa') ->
        addATerm (ShAAppl "UnionOf" [ aa' ] []) att1 }
    toShATerm att0 (IntersectionOf aa) =
        case toShATerm att0 aa of { (att1,aa') ->
        addATerm (ShAAppl "IntersectionOf" [ aa' ] []) att1 }
    toShATerm att0 (ComplementOf aa) =
        case toShATerm att0 aa of { (att1,aa') ->
        addATerm (ShAAppl "ComplementOf" [ aa' ] []) att1 }
    toShATerm att0 (OneOfDes aa) =
        case toShATerm att0 aa of { (att1,aa') ->
        addATerm (ShAAppl "OneOfDes" [ aa' ] []) att1 }
    fromShATerm att =
        case getATerm att of
            ShAAppl "DC" [ aa ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    DC aa' }
            ShAAppl "DR" [ aa ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    DR aa' }
            ShAAppl "UnionOf" [ aa ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    UnionOf aa' }
            ShAAppl "IntersectionOf" [ aa ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    IntersectionOf aa' }
            ShAAppl "ComplementOf" [ aa ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    ComplementOf aa' }
            ShAAppl "OneOfDes" [ aa ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    OneOfDes aa' }
            u -> fromShATermError "OWL_DL.Description" u

instance ShATermConvertible Restriction where
    toShATerm att0 (DataRestriction aa ab ac) =
        case toShATerm att0 aa of { (att1,aa') ->
        case toShATerm att1 ab of { (att2,ab') ->
        case toShATerm att2 ac of { (att3,ac') ->
        addATerm (ShAAppl "DataRestriction" [ aa',ab',ac' ] []) att3 }}}
    toShATerm att0 (IndivRestriction aa ab ac) =
        case toShATerm att0 aa of { (att1,aa') ->
        case toShATerm att1 ab of { (att2,ab') ->
        case toShATerm att2 ac of { (att3,ac') ->
        addATerm (ShAAppl "IndivRestriction" [ aa',ab',ac' ] []) att3 }}}
    fromShATerm att =
        case getATerm att of
            ShAAppl "DataRestriction" [ aa,ab,ac ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    case fromShATerm $ getATermByIndex1 ab att of { ab' ->
                    case fromShATerm $ getATermByIndex1 ac att of { ac' ->
                    DataRestriction aa' ab' ac' }}}
            ShAAppl "IndivRestriction" [ aa,ab,ac ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    case fromShATerm $ getATermByIndex1 ab att of { ab' ->
                    case fromShATerm $ getATermByIndex1 ac att of { ac' ->
                    IndivRestriction aa' ab' ac' }}}
            u -> fromShATermError "OWL_DL.Restriction" u

instance ShATermConvertible Drcomponent where
    toShATerm att0 (DRCAllValuesFrom aa) =
        case toShATerm att0 aa of { (att1,aa') ->
        addATerm (ShAAppl "DRCAllValuesFrom" [ aa' ] []) att1 }
    toShATerm att0 (DRCSomeValuesFrom aa) =
        case toShATerm att0 aa of { (att1,aa') ->
        addATerm (ShAAppl "DRCSomeValuesFrom" [ aa' ] []) att1 }
    toShATerm att0 (DRCValue aa) =
        case toShATerm att0 aa of { (att1,aa') ->
        addATerm (ShAAppl "DRCValue" [ aa' ] []) att1 }
    toShATerm att0 (DRCCardinality aa) =
        case toShATerm att0 aa of { (att1,aa') ->
        addATerm (ShAAppl "DRCCardinality" [ aa' ] []) att1 }
    fromShATerm att =
        case getATerm att of
            ShAAppl "DRCAllValuesFrom" [ aa ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    DRCAllValuesFrom aa' }
            ShAAppl "DRCSomeValuesFrom" [ aa ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    DRCSomeValuesFrom aa' }
            ShAAppl "DRCValue" [ aa ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    DRCValue aa' }
            ShAAppl "DRCCardinality" [ aa ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    DRCCardinality aa' }
            u -> fromShATermError "OWL_DL.Drcomponent" u

instance ShATermConvertible Ircomponent where
    toShATerm att0 (IRCAllValuesFrom aa) =
        case toShATerm att0 aa of { (att1,aa') ->
        addATerm (ShAAppl "IRCAllValuesFrom" [ aa' ] []) att1 }
    toShATerm att0 (IRCSomeValuesFrom aa) =
        case toShATerm att0 aa of { (att1,aa') ->
        addATerm (ShAAppl "IRCSomeValuesFrom" [ aa' ] []) att1 }
    toShATerm att0 (IRCValue aa) =
        case toShATerm att0 aa of { (att1,aa') ->
        addATerm (ShAAppl "IRCValue" [ aa' ] []) att1 }
    toShATerm att0 (IRCCardinality aa) =
        case toShATerm att0 aa of { (att1,aa') ->
        addATerm (ShAAppl "IRCCardinality" [ aa' ] []) att1 }
    fromShATerm att =
        case getATerm att of
            ShAAppl "IRCAllValuesFrom" [ aa ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    IRCAllValuesFrom aa' }
            ShAAppl "IRCSomeValuesFrom" [ aa ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    IRCSomeValuesFrom aa' }
            ShAAppl "IRCValue" [ aa ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    IRCValue aa' }
            ShAAppl "IRCCardinality" [ aa ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    IRCCardinality aa' }
            u -> fromShATermError "OWL_DL.Ircomponent" u

instance ShATermConvertible Cardinality where
    toShATerm att0 (MinCardinality aa) =
        case toShATerm att0 aa of { (att1,aa') ->
        addATerm (ShAAppl "MinCardinality" [ aa' ] []) att1 }
    toShATerm att0 (MaxCardinality aa) =
        case toShATerm att0 aa of { (att1,aa') ->
        addATerm (ShAAppl "MaxCardinality" [ aa' ] []) att1 }
    toShATerm att0 (Cardinality aa) =
        case toShATerm att0 aa of { (att1,aa') ->
        addATerm (ShAAppl "Cardinality" [ aa' ] []) att1 }
    fromShATerm att =
        case getATerm att of
            ShAAppl "MinCardinality" [ aa ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    MinCardinality aa' }
            ShAAppl "MaxCardinality" [ aa ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    MaxCardinality aa' }
            ShAAppl "Cardinality" [ aa ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    Cardinality aa' }
            u -> fromShATermError "OWL_DL.Cardinality" u

instance ShATermConvertible DataRange where
    toShATerm att0 (DID aa) =
        case toShATerm att0 aa of { (att1,aa') ->
        addATerm (ShAAppl "DID" [ aa' ] []) att1 }
    toShATerm att0 (OneOfData aa) =
        case toShATerm att0 aa of { (att1,aa') ->
        addATerm (ShAAppl "OneOfData" [ aa' ] []) att1 }
    toShATerm att0 (RLit aa) =
        case toShATerm att0 aa of { (att1,aa') ->
        addATerm (ShAAppl "RLit" [ aa' ] []) att1 }
    fromShATerm att =
        case getATerm att of
            ShAAppl "DID" [ aa ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    DID aa' }
            ShAAppl "OneOfData" [ aa ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    OneOfData aa' }
            ShAAppl "RLit" [ aa ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    RLit aa' }
            u -> fromShATermError "OWL_DL.DataRange" u
