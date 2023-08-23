{- |
Module      :  ./CSMOF/Print.hs
Description :  pretty printing for CSMOF
Copyright   :  (c) Daniel Calegari Universidad de la Republica, Uruguay 2013
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  dcalegar@fing.edu.uy
Stability   :  provisional
Portability :  portable
-}


module CSMOF.Print where

import CSMOF.As

import Common.Doc
import Common.DocUtils


instance Pretty Metamodel where
  pretty (Metamodel nam ele mode) =
    text "metamodel" <+> text nam <+> lbrace
    $++$ space <+> space <+> foldr (($++$) . pretty) empty ele
    $+$ rbrace
    $++$ foldr (($+$) . pretty) empty mode

instance Show Metamodel where
  show m = show $ pretty m


instance Pretty NamedElement where
  pretty (NamedElement _ _ nes) = pretty nes

instance Show NamedElement where
  show m = show $ pretty m


instance Pretty TypeOrTypedElement where
  pretty (TType typ) = pretty typ
  pretty (TTypedElement _) = empty   -- Do not show properties at top level but inside classes

instance Show TypeOrTypedElement where
  show m = show $ pretty m


instance Pretty Type where
  pretty (Type _ sub) = pretty sub

instance Show Type where
  show m = show $ pretty m


instance Pretty DataTypeOrClass where
  pretty (DDataType dat) = pretty dat
  pretty (DClass cla) = pretty cla

instance Show DataTypeOrClass where
  show m = show $ pretty m


instance Pretty Datatype where
  pretty (Datatype sup) =
      text "datatype" <+> text (namedElementName (typeSuper sup))

instance Show Datatype where
  show m = show $ pretty m


instance Pretty Class where
  pretty (Class sup isa supC own) =
    text (if isa then "abstract class" else "class")
    <+> text (namedElementName (typeSuper sup))
    <+> (case supC of
           [] -> lbrace
           _ : _ -> text "extends"
                    <+> foldr ( (<+>) . text . namedElementName . typeSuper . classSuperType) empty supC
                    <+> lbrace)
    $+$ space <+> space <+> foldr (($+$) . pretty) empty own
    $+$ rbrace

instance Show Class where
  show m = show $ pretty m


instance Pretty TypedElement where
  pretty (TypedElement _ _ sub) = pretty sub

instance Show TypedElement where
  show m = show $ pretty m


instance Pretty Property where
  pretty (Property sup mul opp _) =
    text "property" <+> text (namedElementName (typedElementSuper sup))
    <> pretty mul
    <+> colon <+> text (namedElementName (typeSuper (typedElementType sup)))
    <+> (case opp of
           Just n -> text "oppositeOf" <+> text (namedElementName (typedElementSuper (propertySuper n)))
           Nothing -> empty)

instance Show Property where
  show m = show $ pretty m


instance Pretty MultiplicityElement where
  pretty (MultiplicityElement low upp _) =
    lbrack <> pretty low <> comma
    <> (if upp == -1
        then text "*"
        else pretty upp)
    <> rbrack

instance Show MultiplicityElement where
  show m = show $ pretty m


-- Model part of CSMOF


instance Pretty Model where
  pretty (Model mon obj lin mode) =
    text "model" <+> text mon
    <+> text "conformsTo" <+> text (metamodelName mode) <+> lbrace
    $++$ space <+> space <+> foldr (($+$) . pretty) empty obj
    $++$ space <+> space <+> foldr (($+$) . pretty) empty lin
    $+$ rbrace

instance Show Model where
  show m = show $ pretty m


instance Pretty Object where
  pretty (Object on ot _) =
    text "object " <> text on
    <+> colon <+> text (namedElementName (typeSuper ot))

instance Show Object where
  show m = show $ pretty m


instance Pretty Link where
  pretty (Link lt sou tar _) =
    text "link" <+> text (namedElementName (typedElementSuper (propertySuper lt)))
    <> lparen <> text (objectName sou) <> comma <> text (objectName tar) <> rparen $+$ empty

instance Show Link where
  show m = show $ pretty m
