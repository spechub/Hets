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
import Char

instance ShATermConvertible Message where
    toShATerm att0 (Message aa) =
        case toShATerm att0 aa of {  (att1,aa') ->
        addATerm (ShAAppl "Message" [ aa' ] []) att1 }
    fromShATerm att =
        case aterm of
            (ShAAppl "Message" [ aa ] _) ->
                    case fromShATerm (getATermByIndex1 aa att) of {  aa' ->
                    (Message aa') }
            u -> fromShATermError "Message" u
        where
            aterm = getATerm att

instance ShATermConvertible Ontology where
    toShATerm att0 (Ontology aa ab ac) =
        case toShATerm att0 aa of {  (att1,aa') ->
        case toShATerm att1 ab of {  (att2,ab') ->
        case toShATerm att2 ac of {  (att3,ac') ->
        addATerm (ShAAppl "Ontology" [ aa',ab',ac'] []) att3 }}}
    fromShATerm att =
        case aterm of
            (ShAAppl "Ontology" [ aa,ab,ac ] _) ->
                    case fromShATerm (getATermByIndex1 aa att) of {  aa' ->
                    case fromShATerm (getATermByIndex1 ab att) of {  ab' ->
                    case fromShATerm (getATermByIndex1 ac att) of {  ac' ->
                    (Ontology aa' ab' ac') }}}
            u -> fromShATermError "Ontology" u
        where
            aterm = getATerm att

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
{-
    toShATerm att0 (Map.Tip) = addATerm (ShAAppl "Namespace" [ShAList [] []] []) att0
    toShATerm att0 (Map.Bin _ k x l r) =
        case toShATerm' att0 l of { (att1, l') ->
        case toShATerm' att1 r of { (att2, r') ->
        case toShATerm att2 k of { (att3, k') ->
        case toShATerm att3 x of { (att4, x') ->
        case addATerm (ShAAppl "NS" [k', x'] []) att4 of { (att5, ns) ->
        case addATerm (ShAList ([ns]++l'++r') []) att5 of { (att6, li) ->
            addATerm (ShAAppl "Namespace" [li] []) att6 }}}}}}
     where toShATerm' :: ATermTable                     
                      -> Map.Map String String -> (ATermTable, [Int])
           toShATerm' att00 (Map.Tip) = (att00, [])
           toShATerm' att00 (Map.Bin _ k1, x1, l1, r1) =
               case toShATerm' att00 l1 of { (att11, l1') ->
               case toShATerm' att11 r1 of { (att12, r1') ->
               case toShATerm att12 k1 of { (att13, k1') ->
               case toShATerm att13 x1 of { (att14, x1') ->
               case addATerm (ShAAppl "NS" [k1', x1'] []) att14 of 
                                            {(att15, ns) ->
                                             (att15, ns:(l1'++r1'))}}}}}
-}                                                          
    fromShATerm att = case aterm of
             ShAAppl "Namespace" [ind] _ ->
               case getATerm $ getATermByIndex1 ind att of 
                 ShAList ns1 _ -> 
                   mkMap ns1 (Map.empty)
                 u -> fromShATermError "Namespace" u
             u -> fromShATermError "Namespace" u
     where     
      mkMap :: [Int] -> Namespace -> Namespace
      mkMap [] mp = mp 
      mkMap (h:r) mp = case getATerm $ getATermByIndex1 h att of
                 ShAAppl "NS" [name, uri] _ ->
                     case fromShATerm (getATermByIndex1 name att) of { name' ->
                     case fromShATerm (getATermByIndex1 uri att) of { uri' -> 
                           mkMap r (Map.insert name' uri' mp)}}
                 u -> fromShATermError "Namespace" u
      aterm = getATerm att

instance ShATermConvertible QName where
    toShATerm att0 (QN aa ab _) =
        case toShATerm att0 (aa ++ ":" ++ ab) of {(att1, aa') ->
           addATerm (ShAAppl (aa ++ ":" ++ ab) [aa'] []) att1}    

    fromShATerm att =
        case aterm of
         (ShAAppl idName _ _) ->
           let idName' = read idName::String
               (pre, loc) = span (not . (==':')) idName'
           in if null loc then    -- no : in ID, only localName
                 QN "" pre ""
                 else 
                  if (not $ isAlpha $ head pre) 
                     then QN "" idName' ""
                     else 
                      if (take 4 pre  == "http" ||
                          take 4 pre == "file")
                          then let (ns, loc2) = span (not . (=='#')) idName'
                               in if length loc2 > 1 then
                                     QN "" (tail loc2) ns
                                     else QN "" ns ""  
                          else  QN pre (tail loc) ""
         u -> fromShATermError "QName" u
        where  aterm = getATerm att

instance ShATermConvertible Directive where
    toShATerm att0 (Anno aa) =
        case toShATerm att0 aa of {  (att1,aa') ->
        addATerm (ShAAppl "Anno" [ aa' ] []) att1 }
    toShATerm att0 (Ax aa) =
        case toShATerm att0 aa of {  (att1,aa') ->
        addATerm (ShAAppl "Ax" [ aa' ] []) att1 }
    toShATerm att0 (Fc aa) =
        case toShATerm att0 aa of {  (att1,aa') ->
        addATerm (ShAAppl "Fc" [ aa' ] []) att1 }
    fromShATerm att =
        case aterm of
            (ShAAppl "Anno" [ aa ] _) ->
                    case fromShATerm (getATermByIndex1 aa att) of {  aa' ->
                    (Anno aa') }
            (ShAAppl "Ax" [ aa ] _) ->
                    case fromShATerm (getATermByIndex1 aa att) of {  aa' ->
                    (Ax aa') }
            (ShAAppl "Fc" [ aa ] _) ->
                    case fromShATerm (getATermByIndex1 aa att) of {  aa' ->
                    (Fc aa') }
            u -> fromShATermError "Directive" u
        where
            aterm = getATerm att

instance ShATermConvertible Annotation where
    toShATerm att0 (OntoAnnotation aa ab) =
        case toShATerm att0 aa of {  (att1,aa') ->
        case toShATerm att1 ab of {  (att2,ab') ->
        addATerm (ShAAppl "OntoAnnotation" [ aa',ab' ] []) att2 }}
    toShATerm att0 (URIAnnotation aa ab) =
        case toShATerm att0 aa of {  (att1,aa') ->
        case toShATerm att1 ab of {  (att2,ab') ->
        addATerm (ShAAppl "URIAnnotation" [ aa',ab' ] []) att2 }}
    toShATerm att0 (DLAnnotation aa ab) =
        case toShATerm att0 aa of {  (att1,aa') ->
        case toShATerm att1 ab of {  (att2,ab') ->
        addATerm (ShAAppl "DLAnnotation" [ aa',ab' ] []) att2 }}
    toShATerm att0 (IndivAnnotation aa ab) =
        case toShATerm att0 aa of {  (att1,aa') ->
        case toShATerm att1 ab of {  (att2,ab') ->
        addATerm (ShAAppl "IndivAnnotation" [ aa',ab' ] []) att2 }}
    fromShATerm att =
        case aterm of
            (ShAAppl "OntoAnnotation" [ aa,ab ] _) ->
                    case fromShATerm (getATermByIndex1 aa att) of {  aa' ->
                    case fromShATerm (getATermByIndex1 ab att) of {  ab' ->
                    (OntoAnnotation aa' ab') }}
            (ShAAppl "URIAnnotation" [ aa,ab ] _) ->
                    case fromShATerm (getATermByIndex1 aa att) of {  aa' ->
                    case fromShATerm (getATermByIndex1 ab att) of {  ab' ->
                    (URIAnnotation aa' ab') }}
            (ShAAppl "DLAnnotation" [ aa,ab ] _) ->
                    case fromShATerm (getATermByIndex1 aa att) of {  aa' ->
                    case fromShATerm (getATermByIndex1 ab att) of {  ab' ->
                    (DLAnnotation aa' ab') }}
            (ShAAppl "IndivAnnotation" [ aa,ab ] _) ->
                    case fromShATerm (getATermByIndex1 aa att) of {  aa' ->
                    case fromShATerm (getATermByIndex1 ab att) of {  ab' ->
                    (IndivAnnotation aa' ab') }}
            u -> fromShATermError "Annotation" u
        where
            aterm = getATerm att

instance ShATermConvertible DataLiteral where
    toShATerm att0 (TypedL aa) =
        case toShATerm att0 aa of {  (att1,aa') ->
        addATerm (ShAAppl "TypedL" [ aa' ] []) att1 }
    toShATerm att0 (PlainL aa) =
        case toShATerm att0 aa of {  (att1,aa') ->
        addATerm (ShAAppl "PlainL" [ aa' ] []) att1 }
    toShATerm att0 (Plain aa) =
        case toShATerm att0 aa of {  (att1,aa') ->
        addATerm (ShAAppl "Plain" [ aa' ] []) att1 }
    toShATerm att0 (RDFSL aa) =
        case toShATerm att0 aa of {  (att1,aa') ->
        addATerm (ShAAppl "RDFSL" [ aa' ] []) att1 }
    fromShATerm att =
        case aterm of
            (ShAAppl "TypedL" [ aa ] _) ->
                    case fromShATerm (getATermByIndex1 aa att) of {  aa' ->
                    (TypedL aa') }
            (ShAAppl "PlainL" [ aa ] _) ->
                    case fromShATerm (getATermByIndex1 aa att) of {  aa' ->
                    (PlainL aa') }
            (ShAAppl "Plain" [ aa ] _) ->
                    case fromShATerm (getATermByIndex1 aa att) of {  aa' ->
                    (Plain aa') }
            (ShAAppl "RDFSL" [ aa ] _) ->
                    case fromShATerm (getATermByIndex1 aa att) of {  aa' ->
                    (RDFSL aa') }
            u -> fromShATermError "DataLiteral" u
        where
            aterm = getATerm att

instance ShATermConvertible Fact where
    toShATerm att0 (Indiv aa) =
        case toShATerm att0 aa of {  (att1,aa') ->
        addATerm (ShAAppl "Indiv" [ aa' ] []) att1 }
    toShATerm att0 (SameIndividual aa ab ac) =
        case toShATerm att0 aa of {  (att1,aa') ->
        case toShATerm att1 ab of {  (att2,ab') ->
        case toShATerm att2 ac of {  (att3,ac') ->
        addATerm (ShAAppl "SameIndividual" [ aa',ab',ac' ] []) att3 }}}
    toShATerm att0 (DifferentIndividuals aa ab ac) =
        case toShATerm att0 aa of {  (att1,aa') ->
        case toShATerm att1 ab of {  (att2,ab') ->
        case toShATerm att2 ac of {  (att3,ac') ->
        addATerm (ShAAppl "DifferentIndividuals" [ aa',ab',ac' ] []) att3 }}}
    fromShATerm att =
        case aterm of
            (ShAAppl "Indiv" [ aa ] _) ->
                    case fromShATerm (getATermByIndex1 aa att) of {  aa' ->
                    (Indiv aa') }
            (ShAAppl "SameIndividual" [ aa,ab,ac ] _) ->
                    case fromShATerm (getATermByIndex1 aa att) of {  aa' ->
                    case fromShATerm (getATermByIndex1 ab att) of {  ab' ->
                    case fromShATerm (getATermByIndex1 ac att) of {  ac' ->
                    (SameIndividual aa' ab' ac') }}}
            (ShAAppl "DifferentIndividuals" [ aa,ab,ac ] _) ->
                    case fromShATerm (getATermByIndex1 aa att) of {  aa' ->
                    case fromShATerm (getATermByIndex1 ab att) of {  ab' ->
                    case fromShATerm (getATermByIndex1 ac att) of {  ac' ->
                    (DifferentIndividuals aa' ab' ac') }}}
            u -> fromShATermError "Fact" u
        where
            aterm = getATerm att

instance ShATermConvertible Individual where
    toShATerm att0 (Individual aa ab ac ad) =
        case toShATerm att0 aa of {  (att1,aa') ->
        case toShATerm att1 ab of {  (att2,ab') ->
        case toShATerm att2 ac of {  (att3,ac') ->
        case toShATerm att3 ad of {  (att4,ad') ->
        addATerm (ShAAppl "Individual" [ aa',ab',ac',ad' ] []) att4 }}}}
    fromShATerm att =
        case aterm of
            (ShAAppl "Individual" [ aa,ab,ac,ad ] _) ->
                    case fromShATerm (getATermByIndex1 aa att) of {  aa' ->
                    case fromShATerm (getATermByIndex1 ab att) of {  ab' ->
                    case fromShATerm (getATermByIndex1 ac att) of {  ac' ->
                    case fromShATerm (getATermByIndex1 ad att) of {  ad' ->
                    (Individual aa' ab' ac' ad') }}}}
            u -> fromShATermError "Individual" u
        where
            aterm = getATerm att

instance ShATermConvertible Value where
    toShATerm att0 (ValueID aa ab) =
        case toShATerm att0 aa of {  (att1,aa') ->
        case toShATerm att1 ab of {  (att2,ab') ->
        addATerm (ShAAppl "ValueID" [ aa',ab' ] []) att2 }}
    toShATerm att0 (ValueIndiv aa ab) =
        case toShATerm att0 aa of {  (att1,aa') ->
        case toShATerm att1 ab of {  (att2,ab') ->
        addATerm (ShAAppl "ValueIndiv" [ aa',ab' ] []) att2 }}
    toShATerm att0 (ValueDL aa ab) =
        case toShATerm att0 aa of {  (att1,aa') ->
        case toShATerm att1 ab of {  (att2,ab') ->
        addATerm (ShAAppl "ValueDL" [ aa',ab' ] []) att2 }}
    fromShATerm att =
        case aterm of
            (ShAAppl "ValueID" [ aa,ab ] _) ->
                    case fromShATerm (getATermByIndex1 aa att) of {  aa' ->
                    case fromShATerm (getATermByIndex1 ab att) of {  ab' ->
                    (ValueID aa' ab') }}
            (ShAAppl "ValueIndiv" [ aa,ab ] _) ->
                    case fromShATerm (getATermByIndex1 aa att) of {  aa' ->
                    case fromShATerm (getATermByIndex1 ab att) of {  ab' ->
                    (ValueIndiv aa' ab') }}
            (ShAAppl "ValueDL" [ aa,ab ] _) ->
                    case fromShATerm (getATermByIndex1 aa att) of {  aa' ->
                    case fromShATerm (getATermByIndex1 ab att) of {  ab' ->
                    (ValueDL aa' ab') }}
            u -> fromShATermError "Value" u
        where
            aterm = getATerm att

instance ShATermConvertible Axiom where
    toShATerm att0 Thing =
        addATerm (ShAAppl "Thing" [] []) att0
    toShATerm att0 OWL_DL.AS.Nothing =
        addATerm (ShAAppl "Nothing" [] []) att0
    toShATerm att0 (Class aa ab ac ad ae) =
        case toShATerm att0 aa of {  (att1,aa') ->
        case toShATerm att1 ab of {  (att2,ab') ->
        case toShATerm att2 ac of {  (att3,ac') ->
        case toShATerm att3 ad of {  (att4,ad') ->
        case toShATerm att4 ae of {  (att5,ae') ->
        addATerm (ShAAppl "Class" [ aa',ab',ac',ad',ae' ] []) att5 }}}}}
    toShATerm att0 (EnumeratedClass aa ab ac ad) =
        case toShATerm att0 aa of {  (att1,aa') ->
        case toShATerm att1 ab of {  (att2,ab') ->
        case toShATerm att2 ac of {  (att3,ac') ->
        case toShATerm att3 ad of {  (att4,ad') ->
        addATerm (ShAAppl "EnumeratedClass" [ aa',ab',ac',ad' ] []) att4 }}}}
    toShATerm att0 (DisjointClasses aa ab ac) =
        case toShATerm att0 aa of {  (att1,aa') ->
        case toShATerm att1 ab of {  (att2,ab') ->
        case toShATerm att2 ac of {  (att3,ac') ->
        addATerm (ShAAppl "DisjointClasses" [ aa',ab',ac' ] []) att3 }}}
    toShATerm att0 (EquivalentClasses aa ab) =
        case toShATerm att0 aa of {  (att1,aa') ->
        case toShATerm att1 ab of {  (att2,ab') ->
        addATerm (ShAAppl "EquivalentClasses" [ aa',ab' ] []) att2 }}
    toShATerm att0 (SubClassOf aa ab) =
        case toShATerm att0 aa of {  (att1,aa') ->
        case toShATerm att1 ab of {  (att2,ab') ->
        addATerm (ShAAppl "SubClassOf" [ aa',ab' ] []) att2 }}
    toShATerm att0 (Datatype aa ab ac) =
        case toShATerm att0 aa of {  (att1,aa') ->
        case toShATerm att1 ab of {  (att2,ab') ->
        case toShATerm att2 ac of {  (att3,ac') ->
        addATerm (ShAAppl "Datatype" [ aa',ab',ac' ] []) att3 }}}
    toShATerm att0 (DatatypeProperty aa ab ac ad ae af ag) =
        case toShATerm att0 aa of {  (att1,aa') ->
        case toShATerm att1 ab of {  (att2,ab') ->
        case toShATerm att2 ac of {  (att3,ac') ->
        case toShATerm att3 ad of {  (att4,ad') ->
        case toShATerm att4 ae of {  (att5,ae') ->
        case toShATerm att5 af of {  (att6,af') ->
        case toShATerm att6 ag of {  (att7,ag') ->
        addATerm (ShAAppl "DatatypeProperty" [ aa',ab',ac',ad',ae',af',ag' ] []) att7 }}}}}}}
    toShATerm att0 (ObjectProperty aa ab ac ad ae af ag ah ai) =
        case toShATerm att0 aa of {  (att1,aa') ->
        case toShATerm att1 ab of {  (att2,ab') ->
        case toShATerm att2 ac of {  (att3,ac') ->
        case toShATerm att3 ad of {  (att4,ad') ->
        case toShATerm att4 ae of {  (att5,ae') ->
        case toShATerm att5 af of {  (att6,af') ->
        case toShATerm att6 ag of {  (att7,ag') ->
        case toShATerm att7 ah of {  (att8,ah') ->
        case toShATerm att8 ai of {  (att9,ai') ->
        addATerm (ShAAppl "ObjectProperty" [ aa',ab',ac',ad',ae',af',ag',ah',ai' ] []) att9 }}}}}}}}}
    toShATerm att0 (AnnotationProperty aa ab) =
        case toShATerm att0 aa of {  (att1,aa') ->
        case toShATerm att1 ab of {  (att2,ab') ->
        addATerm (ShAAppl "AnnotationProperty" [ aa',ab' ] []) att2 }}
    toShATerm att0 (OntologyProperty aa ab) =
        case toShATerm att0 aa of {  (att1,aa') ->
        case toShATerm att1 ab of {  (att2,ab') ->
        addATerm (ShAAppl "OntologyProperty" [ aa',ab' ] []) att2 }}
    toShATerm att0 (DEquivalentProperties aa ab ac) =
        case toShATerm att0 aa of {  (att1,aa') ->
        case toShATerm att1 ab of {  (att2,ab') ->
        case toShATerm att2 ac of {  (att3,ac') ->
        addATerm (ShAAppl "DEquivalentProperties" [ aa',ab',ac' ] []) att3 }}}
    toShATerm att0 (DSubPropertyOf aa ab) =
        case toShATerm att0 aa of {  (att1,aa') ->
        case toShATerm att1 ab of {  (att2,ab') ->
        addATerm (ShAAppl "DSubPropertyOf" [ aa',ab' ] []) att2 }}
    toShATerm att0 (IEquivalentProperties aa ab ac) =
        case toShATerm att0 aa of {  (att1,aa') ->
        case toShATerm att1 ab of {  (att2,ab') ->
        case toShATerm att2 ac of {  (att3,ac') ->
        addATerm (ShAAppl "IEquivalentProperties" [ aa',ab',ac' ] []) att3 }}}
    toShATerm att0 (ISubPropertyOf aa ab) =
        case toShATerm att0 aa of {  (att1,aa') ->
        case toShATerm att1 ab of {  (att2,ab') ->
        addATerm (ShAAppl "ISubPropertyOf" [ aa',ab' ] []) att2 }}
    fromShATerm att =
        case aterm of
            (ShAAppl "Thing" [ ] _) ->
                    Thing
            (ShAAppl "Nothing" [ ] _) ->
                    OWL_DL.AS.Nothing
            (ShAAppl "Class" [ aa,ab,ac,ad,ae ] _) ->
                    case fromShATerm (getATermByIndex1 aa att) of {  aa' ->
                    case fromShATerm (getATermByIndex1 ab att) of {  ab' ->
                    case fromShATerm (getATermByIndex1 ac att) of {  ac' ->
                    case fromShATerm (getATermByIndex1 ad att) of {  ad' ->
                    case fromShATerm (getATermByIndex1 ae att) of {  ae' ->
                    (Class aa' ab' ac' ad' ae') }}}}}
            (ShAAppl "EnumeratedClass" [ aa,ab,ac,ad ] _) ->
                    case fromShATerm (getATermByIndex1 aa att) of {  aa' ->
                    case fromShATerm (getATermByIndex1 ab att) of {  ab' ->
                    case fromShATerm (getATermByIndex1 ac att) of {  ac' ->
                    case fromShATerm (getATermByIndex1 ad att) of {  ad' ->
                    (EnumeratedClass aa' ab' ac' ad') }}}}
            (ShAAppl "DisjointClasses" [ aa,ab,ac ] _) ->
                    case fromShATerm (getATermByIndex1 aa att) of {  aa' ->
                    case fromShATerm (getATermByIndex1 ab att) of {  ab' ->
                    case fromShATerm (getATermByIndex1 ac att) of {  ac' ->
                    (DisjointClasses aa' ab' ac') }}}
            (ShAAppl "EquivalentClasses" [ aa,ab ] _) ->
                    case fromShATerm (getATermByIndex1 aa att) of {  aa' ->
                    case fromShATerm (getATermByIndex1 ab att) of {  ab' ->
                    (EquivalentClasses aa' ab') }}
            (ShAAppl "SubClassOf" [ aa,ab ] _) ->
                    case fromShATerm (getATermByIndex1 aa att) of {  aa' ->
                    case fromShATerm (getATermByIndex1 ab att) of {  ab' ->
                    (SubClassOf aa' ab') }}
            (ShAAppl "Datatype" [ aa,ab,ac ] _) ->
                    case fromShATerm (getATermByIndex1 aa att) of {  aa' ->
                    case fromShATerm (getATermByIndex1 ab att) of {  ab' ->
                    case fromShATerm (getATermByIndex1 ac att) of {  ac' ->
                    (Datatype aa' ab' ac') }}}
            (ShAAppl "DatatypeProperty" [ aa,ab,ac,ad,ae,af,ag ] _) ->
                    case fromShATerm (getATermByIndex1 aa att) of {  aa' ->
                    case fromShATerm (getATermByIndex1 ab att) of {  ab' ->
                    case fromShATerm (getATermByIndex1 ac att) of {  ac' ->
                    case fromShATerm (getATermByIndex1 ad att) of {  ad' ->
                    case fromShATerm (getATermByIndex1 ae att) of {  ae' ->
                    case fromShATerm (getATermByIndex1 af att) of {  af' ->
                    case fromShATerm (getATermByIndex1 ag att) of {  ag' ->
                    (DatatypeProperty aa' ab' ac' ad' ae' af' ag') }}}}}}}
            (ShAAppl "ObjectProperty" [ aa,ab,ac,ad,ae,af,ag,ah,ai ] _) ->
                    case fromShATerm (getATermByIndex1 aa att) of {  aa' ->
                    case fromShATerm (getATermByIndex1 ab att) of {  ab' ->
                    case fromShATerm (getATermByIndex1 ac att) of {  ac' ->
                    case fromShATerm (getATermByIndex1 ad att) of {  ad' ->
                    case fromShATerm (getATermByIndex1 ae att) of {  ae' ->
                    case fromShATerm (getATermByIndex1 af att) of {  af' ->
                    case fromShATerm (getATermByIndex1 ag att) of {  ag' ->
                    case fromShATerm (getATermByIndex1 ah att) of {  ah' ->
                    case fromShATerm (getATermByIndex1 ai att) of {  ai' ->
                    (ObjectProperty aa' ab' ac' ad' ae' af' ag' ah' ai') }}}}}}}}}
            (ShAAppl "AnnotationProperty" [ aa,ab ] _) ->
                    case fromShATerm (getATermByIndex1 aa att) of {  aa' ->
                    case fromShATerm (getATermByIndex1 ab att) of {  ab' ->
                    (AnnotationProperty aa' ab') }}
            (ShAAppl "OntologyProperty" [ aa,ab ] _) ->
                    case fromShATerm (getATermByIndex1 aa att) of {  aa' ->
                    case fromShATerm (getATermByIndex1 ab att) of {  ab' ->
                    (OntologyProperty aa' ab') }}
            (ShAAppl "DEquivalentProperties" [ aa,ab,ac ] _) ->
                    case fromShATerm (getATermByIndex1 aa att) of {  aa' ->
                    case fromShATerm (getATermByIndex1 ab att) of {  ab' ->
                    case fromShATerm (getATermByIndex1 ac att) of {  ac' ->
                    (DEquivalentProperties aa' ab' ac') }}}
            (ShAAppl "DSubPropertyOf" [ aa,ab ] _) ->
                    case fromShATerm (getATermByIndex1 aa att) of {  aa' ->
                    case fromShATerm (getATermByIndex1 ab att) of {  ab' ->
                    (DSubPropertyOf aa' ab') }}
            (ShAAppl "IEquivalentProperties" [ aa,ab,ac ] _) ->
                    case fromShATerm (getATermByIndex1 aa att) of {  aa' ->
                    case fromShATerm (getATermByIndex1 ab att) of {  ab' ->
                    case fromShATerm (getATermByIndex1 ac att) of {  ac' ->
                    (IEquivalentProperties aa' ab' ac') }}}
            (ShAAppl "ISubPropertyOf" [ aa,ab ] _) ->
                    case fromShATerm (getATermByIndex1 aa att) of {  aa' ->
                    case fromShATerm (getATermByIndex1 ab att) of {  ab' ->
                    (ISubPropertyOf aa' ab') }}
            u -> fromShATermError "Axiom" u
        where
            aterm = getATerm att

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
        case aterm of
            (ShAAppl "Functional" [ ] _) ->
                    Functional
            (ShAAppl "InverseFunctional" [ ] _) ->
                    InverseFunctional
            (ShAAppl "Functional_InverseFunctional" [ ] _) ->
                    Functional_InverseFunctional
            (ShAAppl "Transitive" [ ] _) ->
                    Transitive
            u -> fromShATermError "Func" u
        where
            aterm = getATerm att

instance ShATermConvertible Modality where
    toShATerm att0 Complete =
        addATerm (ShAAppl "Complete" [] []) att0
    toShATerm att0 Partial =
        addATerm (ShAAppl "Partial" [] []) att0
    fromShATerm att =
        case aterm of
            (ShAAppl "Complete" [ ] _) ->
                    Complete
            (ShAAppl "Partial" [ ] _) ->
                    Partial
            u -> fromShATermError "Modality" u
        where
            aterm = getATerm att

instance ShATermConvertible Description where
    toShATerm att0 (DC aa) =
        case toShATerm att0 aa of {  (att1,aa') ->
        addATerm (ShAAppl "DC" [ aa' ] []) att1 }
    toShATerm att0 (DR aa) =
        case toShATerm att0 aa of {  (att1,aa') ->
        addATerm (ShAAppl "DR" [ aa' ] []) att1 }
    toShATerm att0 (UnionOf aa) =
        case toShATerm att0 aa of {  (att1,aa') ->
        addATerm (ShAAppl "UnionOf" [ aa' ] []) att1 }
    toShATerm att0 (IntersectionOf aa) =
        case toShATerm att0 aa of {  (att1,aa') ->
        addATerm (ShAAppl "IntersectionOf" [ aa' ] []) att1 }
    toShATerm att0 (ComplementOf aa) =
        case toShATerm att0 aa of {  (att1,aa') ->
        addATerm (ShAAppl "ComplementOf" [ aa' ] []) att1 }
    toShATerm att0 (OneOfDes aa) =
        case toShATerm att0 aa of {  (att1,aa') ->
        addATerm (ShAAppl "OneOfDes" [ aa' ] []) att1 }
    fromShATerm att =
        case aterm of
            (ShAAppl "DC" [ aa ] _) ->
                    case fromShATerm (getATermByIndex1 aa att) of {  aa' ->
                    (DC aa') }
            (ShAAppl "DR" [ aa ] _) ->
                    case fromShATerm (getATermByIndex1 aa att) of {  aa' ->
                    (DR aa') }
            (ShAAppl "UnionOf" [ aa ] _) ->
                    case fromShATerm (getATermByIndex1 aa att) of {  aa' ->
                    (UnionOf aa') }
            (ShAAppl "IntersectionOf" [ aa ] _) ->
                    case fromShATerm (getATermByIndex1 aa att) of {  aa' ->
                    (IntersectionOf aa') }
            (ShAAppl "ComplementOf" [ aa ] _) ->
                    case fromShATerm (getATermByIndex1 aa att) of {  aa' ->
                    (ComplementOf aa') }
            (ShAAppl "OneOfDes" [ aa ] _) ->
                    case fromShATerm (getATermByIndex1 aa att) of {  aa' ->
                    (OneOfDes aa') }
            u -> fromShATermError "Description" u
        where
            aterm = getATerm att

instance ShATermConvertible Restriction where
    toShATerm att0 (DataRestriction aa ab ac) =
        case toShATerm att0 aa of {  (att1,aa') ->
        case toShATerm att1 ab of {  (att2,ab') ->
        case toShATerm att2 ac of {  (att3,ac') ->
        addATerm (ShAAppl "DataRestriction" [ aa',ab',ac' ] []) att3 }}}
    toShATerm att0 (IndivRestriction aa ab ac) =
        case toShATerm att0 aa of {  (att1,aa') ->
        case toShATerm att1 ab of {  (att2,ab') ->
        case toShATerm att2 ac of {  (att3,ac') ->
        addATerm (ShAAppl "IndivRestriction" [ aa',ab',ac' ] []) att3 }}}
    fromShATerm att =
        case aterm of
            (ShAAppl "DataRestriction" [ aa,ab,ac ] _) ->
                    case fromShATerm (getATermByIndex1 aa att) of {  aa' ->
                    case fromShATerm (getATermByIndex1 ab att) of {  ab' ->
                    case fromShATerm (getATermByIndex1 ac att) of {  ac' ->
                    (DataRestriction aa' ab' ac') }}}
            (ShAAppl "IndivRestriction" [ aa,ab,ac ] _) ->
                    case fromShATerm (getATermByIndex1 aa att) of {  aa' ->
                    case fromShATerm (getATermByIndex1 ab att) of {  ab' ->
                    case fromShATerm (getATermByIndex1 ac att) of {  ac' ->
                    (IndivRestriction aa' ab' ac') }}}
            u -> fromShATermError "Restriction" u
        where
            aterm = getATerm att

instance ShATermConvertible Drcomponent where
    toShATerm att0 (DRCAllValuesFrom aa) =
        case toShATerm att0 aa of {  (att1,aa') ->
        addATerm (ShAAppl "DRCAllValuesFrom" [ aa' ] []) att1 }
    toShATerm att0 (DRCSomeValuesFrom aa) =
        case toShATerm att0 aa of {  (att1,aa') ->
        addATerm (ShAAppl "DRCSomeValuesFrom" [ aa' ] []) att1 }
    toShATerm att0 (DRCValue aa) =
        case toShATerm att0 aa of {  (att1,aa') ->
        addATerm (ShAAppl "DRCValue" [ aa' ] []) att1 }
    toShATerm att0 (DRCCardinality aa) =
        case toShATerm att0 aa of {  (att1,aa') ->
        addATerm (ShAAppl "DRCCardinality" [ aa' ] []) att1 }
    fromShATerm att =
        case aterm of
            (ShAAppl "DRCAllValuesFrom" [ aa ] _) ->
                    case fromShATerm (getATermByIndex1 aa att) of {  aa' ->
                    (DRCAllValuesFrom aa') }
            (ShAAppl "DRCSomeValuesFrom" [ aa ] _) ->
                    case fromShATerm (getATermByIndex1 aa att) of {  aa' ->
                    (DRCSomeValuesFrom aa') }
            (ShAAppl "DRCValue" [ aa ] _) ->
                    case fromShATerm (getATermByIndex1 aa att) of {  aa' ->
                    (DRCValue aa') }
            (ShAAppl "DRCCardinality" [ aa ] _) ->
                    case fromShATerm (getATermByIndex1 aa att) of {  aa' ->
                    (DRCCardinality aa') }
            u -> fromShATermError "Drcomponent" u
        where
            aterm = getATerm att

instance ShATermConvertible Ircomponent where
    toShATerm att0 (IRCAllValuesFrom aa) =
        case toShATerm att0 aa of {  (att1,aa') ->
        addATerm (ShAAppl "IRCAllValuesFrom" [ aa' ] []) att1 }
    toShATerm att0 (IRCSomeValuesFrom aa) =
        case toShATerm att0 aa of {  (att1,aa') ->
        addATerm (ShAAppl "IRCSomeValuesFrom" [ aa' ] []) att1 }
    toShATerm att0 (IRCValue aa) =
        case toShATerm att0 aa of {  (att1,aa') ->
        addATerm (ShAAppl "IRCValue" [ aa' ] []) att1 }
    toShATerm att0 (IRCCardinality aa) =
        case toShATerm att0 aa of {  (att1,aa') ->
        addATerm (ShAAppl "IRCCardinality" [ aa' ] []) att1 }
    fromShATerm att =
        case aterm of
            (ShAAppl "IRCAllValuesFrom" [ aa ] _) ->
                    case fromShATerm (getATermByIndex1 aa att) of {  aa' ->
                    (IRCAllValuesFrom aa') }
            (ShAAppl "IRCSomeValuesFrom" [ aa ] _) ->
                    case fromShATerm (getATermByIndex1 aa att) of {  aa' ->
                    (IRCSomeValuesFrom aa') }
            (ShAAppl "IRCValue" [ aa ] _) ->
                    case fromShATerm (getATermByIndex1 aa att) of {  aa' ->
                    (IRCValue aa') }
            (ShAAppl "IRCCardinality" [ aa ] _) ->
                    case fromShATerm (getATermByIndex1 aa att) of {  aa' ->
                    (IRCCardinality aa') }
            u -> fromShATermError "Ircomponent" u
        where
            aterm = getATerm att

instance ShATermConvertible Cardinality where
    toShATerm att0 (MinCardinality aa) =
        case toShATerm att0 aa of {  (att1,aa') ->
        addATerm (ShAAppl "MinCardinality" [ aa' ] []) att1 }
    toShATerm att0 (MaxCardinality aa) =
        case toShATerm att0 aa of {  (att1,aa') ->
        addATerm (ShAAppl "MaxCardinality" [ aa' ] []) att1 }
    toShATerm att0 (Cardinality aa) =
        case toShATerm att0 aa of {  (att1,aa') ->
        addATerm (ShAAppl "Cardinality" [ aa' ] []) att1 }
    fromShATerm att =
        case aterm of
            (ShAAppl "MinCardinality" [ aa ] _) ->
                    case fromShATerm (getATermByIndex1 aa att) of {  aa' ->
                    (MinCardinality aa') }
            (ShAAppl "MaxCardinality" [ aa ] _) ->
                    case fromShATerm (getATermByIndex1 aa att) of {  aa' ->
                    (MaxCardinality aa') }
            (ShAAppl "Cardinality" [ aa ] _) ->
                    case fromShATerm (getATermByIndex1 aa att) of {  aa' ->
                    (Cardinality aa') }
            u -> fromShATermError "Cardinality" u
        where
            aterm = getATerm att

instance ShATermConvertible DataRange where
    toShATerm att0 (DID aa) =
        case toShATerm att0 aa of {  (att1,aa') ->
        addATerm (ShAAppl "DID" [ aa' ] []) att1 }
    toShATerm att0 (OneOfData aa) =
        case toShATerm att0 aa of {  (att1,aa') ->
        addATerm (ShAAppl "OneOfData" [ aa' ] []) att1 }
    toShATerm att0 (RLit aa) =
        case toShATerm att0 aa of {  (att1,aa') ->
        addATerm (ShAAppl "RLit" [ aa' ] []) att1 }
    fromShATerm att =
        case aterm of
            (ShAAppl "DID" [ aa ] _) ->
                    case fromShATerm (getATermByIndex1 aa att) of {  aa' ->
                    (DID aa') }
            (ShAAppl "OneOfData" [ aa ] _) ->
                    case fromShATerm (getATermByIndex1 aa att) of {  aa' ->
                    (OneOfData aa') }
            (ShAAppl "RLit" [ aa ] _) ->
                    case fromShATerm (getATermByIndex1 aa att) of {  aa' ->
                    (RLit aa') }
            u -> fromShATermError "DataRange" u
        where
            aterm = getATerm att


