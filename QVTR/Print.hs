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
    $++$ foldr (($+$) . pretty) empty keS
    $++$ foldr (($++$) . pretty) empty rels
    $+$ rbrace

instance Show Transformation where
  show m = show $ pretty m


instance Pretty Key where
  pretty (Key met typN pro) =
    text "key" <+> text met <> colon <> colon <> text typN 
    <+> lbrace <> foldr ((<+>) . pretty) empty pro <> rbrace

instance Show Key where
  show m = show $ pretty m


instance Pretty PropKey where
  pretty (SimpleProp nam) = text nam
  pretty (OppositeProp typ nam) = text "opposite" <> lparen <> text typ <> dot <> text nam <> rparen

instance Show PropKey where
  show m = show $ pretty m


instance Pretty Relation where
  pretty (Relation to reln vars primD souD tarD whenC whereC) = 
    space <+>
    (if to then text "top relation" else text "relation") <+> text reln <+> lbrace
    $++$ space <+> space <+> foldr (($+$) . pretty) empty vars
    $++$ space <+> space <+> foldr (($+$) . pretty) empty primD
    $++$ space <+> space <+> pretty souD
    $++$ space <+> space <+> pretty tarD
    $++$ space <+> space <+> pretty whenC
    $++$ space <+> space <+> pretty whereC
    
instance Show Relation where
  show m = show $ pretty m


instance Pretty PrimitiveDomain where
  pretty (PrimitiveDomain nam typ) = text "primitive domain" <+> text nam <> colon <> text typ

instance Show PrimitiveDomain where
  show m = show $ pretty m


instance Pretty RelVar where
  pretty (RelVar typ nam) = text nam <> colon <> text typ

instance Show RelVar where
  show m = show $ pretty m


instance Pretty Domain where
  pretty (Domain dom tem) = 
    text "domain" <+> text dom
    $+$ space <+> space <+> pretty tem

instance Show Domain where
  show m = show $ pretty m


instance Pretty ObjectTemplate where
  pretty (ObjectTemplate var met typ temL) =
    text var <+> colon <+> text met <> colon <> colon <> text typ <+> lbrace
    $+$ space <+> space <+> foldr (($+$) . pretty) empty temL
    $+$ rbrace

instance Show ObjectTemplate where
  show m = show $ pretty m


instance Pretty PropertyTemplate where
  pretty (PropertyTemplate nam expr tem) =
    text nam <+> text "="
    <+> (case expr of 
           Nothing -> case tem of
                        Nothing -> empty
                        Just t -> pretty t
           Just e -> text e
        )

instance Show PropertyTemplate where
  show m = show $ pretty m


instance Pretty WhenWhere where
  pretty (When inv ocl) =
    text "when" <+> lbrace
    $+$ space <+> space <+> foldr (($+$) . pretty) empty inv
    $+$ space <+> space <+> foldr (($+$) . text) empty ocl
    $+$ rbrace
  pretty (Where inv ocl) =
    text "where" <+> lbrace
    $+$ space <+> space <+> foldr (($+$) . pretty) empty inv
    $+$ space <+> space <+> foldr (($+$) . text) empty ocl
    $+$ rbrace

instance Show WhenWhere where
  show m = show $ pretty m


instance Pretty RelInvok where
  pretty (RelInvok nam par) = text nam <> lparen <> foldr ((<+>) . pretty) empty par <> rparen

instance Show RelInvok where
  show m = show $ pretty m

