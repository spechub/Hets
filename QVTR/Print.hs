{- |
Module      :  $Header$
Description :  pretty printing for QVTR
Copyright   :  (c) Daniel Calegari Universidad de la Republica, Uruguay 2013
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  dcalegar@fing.edu.uy
Stability   :  provisional
Portability :  portable
-}


module QVTR.Print where

import QVTR.As
import CSMOF.Print ()

import Common.Doc
import Common.DocUtils

                            
instance Pretty Transformation where
  pretty (Transformation nam (souNam,souMet,souAS) (tarNam,tarMet,tarAS) keS rels) = 
    pretty souAS
    $++$ pretty tarAS
    $++$ text "transformation" <+> text nam <> lparen 
      <> text souNam <> colon <> text souMet <> comma 
      <+> text tarNam <> colon <> text tarMet <> rparen
    $+$ lbrace
    $++$ foldr (($+$). pretty) empty keS
    $++$ foldr (($+$) . pretty) empty rels
    $+$ rbrace

instance Show Transformation where
  show m = show $ pretty m


instance Pretty Key where
  pretty (Key met typN pro) =
    text "key" <+> text met <> colon <> colon <> text typN 
    <+> lbrace <> foldr ((<+>) . pretty) empty pro <> rbrace <> semi

instance Show Key where
  show m = show $ pretty m


instance Pretty PropKey where
  pretty (SimpleProp nam) = text nam
  pretty (OppositeProp typ nam) = text "opposite" <> lparen <> text typ <> dot <> text nam <> rparen

instance Show PropKey where
  show m = show $ pretty m


instance Pretty Relation where
  pretty (Relation to reln vars primD souD tarD whenC whereC) = 
    (if to then text "top relation" else text "relation") <+> text reln <+> lbrace
    $++$ foldr (($+$) . (<> semi) . pretty) empty vars
    $++$ foldr (($+$) . pretty) empty primD
    $++$ pretty souD
    $++$ pretty tarD
    $++$ pretty whenC
    $++$ pretty whereC
    
instance Show Relation where
  show m = show $ pretty m


instance Pretty PrimitiveDomain where
  pretty (PrimitiveDomain nam typ) = text "primitive domain" <+> text nam <> colon <> text typ <> semi

instance Show PrimitiveDomain where
  show m = show $ pretty m


instance Pretty RelVar where
  pretty (RelVar typ nam) = text nam <> colon <> text typ

instance Show RelVar where
  show m = show $ pretty m


instance Pretty Domain where
  pretty (Domain meta var typ pat) = 
    text "domain" <+> text meta <+> text var <+> colon <+> text typ <+> lbrace
    $+$ pretty pat
    $+$ rbrace

instance Show Domain where
  show m = show $ pretty m


instance Pretty Pattern where
  pretty (Pattern els rels preds) =
    foldr ((<+>) . pretty) empty els
    $+$ foldr ((<+>) . printVar) empty rels
    $+$ text preds

printVar :: (String,RelInvok) -> Doc
printVar (nam,relI) = text nam <+> equals <+> pretty relI

instance Show Pattern where
  show m = show $ pretty m


instance Pretty WhenWhere where
  pretty (When inv ocl) =
    text "when" <+> lbrace
    $+$ foldr (($+$) . pretty) empty inv
    $+$ foldr (($+$) . text) empty ocl
    $+$ rbrace
  pretty (Where inv ocl) =
    text "where" <+> lbrace
    $+$ foldr (($+$) . pretty) empty inv
    $+$ foldr (($+$) . text) empty ocl
    $+$ rbrace

instance Show WhenWhere where
  show m = show $ pretty m


instance Pretty RelInvok where
  pretty (RelInvok nam par) = text nam <> lparen <> foldr ((<+>) . pretty) empty par <> rparen

instance Show RelInvok where
  show m = show $ pretty m

