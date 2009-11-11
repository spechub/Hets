{- |
Module      :  $Header$
Description :  extracted annotated items for xml output from basic specs
Copyright   :  (c) Christian Maeder and Ewaryst Schulz and DFKI GmbH 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  non-portable (imports Common.Item)

get item representation of 'BasicSpec'
-}

module HasCASL.ToItem (bsToItem) where

import Common.AS_Annotation
import Common.Doc
import Common.DocUtils
import Common.Id
import Common.Item

import HasCASL.As
import HasCASL.PrintAs

bsToItem :: BasicSpec -> Item
bsToItem (BasicSpec bs) =
    mkItem "BasicSpec" nullRange $ map (fmap biToItem) bs

biToItem :: BasicItem -> Item
biToItem bi = case bi of
  SigItems si -> siToItem si
  ProgItems pes rg -> mkItem "ProgItems" rg $ map (fmap peToItem) pes
  ClassItems inst cs rg -> mkItem (case inst of
      Instance -> "ClassInstanceItems"
      Plain -> "ClassItems") rg $ map (fmap ciToItem) cs
  GenVarItems gvs rg ->
      mkItem "GenVarItems" rg $ map (emptyAnno . gvdToItem) gvs
  FreeDatatype ds rg -> mkItem "FreeDatatype" rg $ map (fmap dtdToItem) ds
  GenItems sis rg -> mkItem "GenItems" rg $ map (fmap siToItem) sis
  AxiomItems gvs ts rg -> mkItem "AxiomItems" rg $
    map (emptyAnno . gvdToItem) gvs ++ map (fmap trmToItem) ts
  Internal bs rg -> mkItem "Internal" rg $ map (fmap biToItem) bs

siToItem :: SigItems -> Item
siToItem si = case si of
  TypeItems inst ts rg -> mkItem (case inst of
    Instance -> "TypeInstanceItem"
    Plain -> "TypeItem") rg $ map (fmap tiToItem) ts
  OpItems b os rg -> mkItem (show b ++ "Items") rg $ map (fmap oiToItem) os

tiToItem :: TypeItem -> Item
tiToItem ti = case ti of
  TypeDecl tps k rg -> mkItem "TypeDecl" rg
    $ map (emptyAnno . tpToItem) tps ++ [emptyAnno (kToItem k)]
  SubtypeDecl tps ty rg -> mkItem "SubtypeDecl" rg
    $ map (emptyAnno . tpToItem) tps ++ [emptyAnno (tyToItem ty)]
  IsoDecl tps rg -> mkItem "IsoDecl" rg $ map (emptyAnno . tpToItem) tps
  SubtypeDefn tp v ty trm rg -> mkItem "SubtypeDefn" rg
     $ map emptyAnno [tpToItem tp, vToItem v, tyToItem ty]
     ++ [fmap trmToItem trm]
  AliasType tp mk sc rg -> mkItem "AliasType" rg $ map emptyAnno
    $ tpToItem tp : (case mk of
      Nothing -> []
      Just k -> [kToItem k]) ++ [scToItem sc]
  Datatype dtd -> dtdToItem dtd

tpToItem :: TypePattern -> Item
tpToItem tp = mkItem ("TypePattern", pretty tp) (getRange tp) []

kToItem :: Kind -> Item
kToItem k = mkItem ("Kind", pretty k) nullRange []

tyToItem :: Type -> Item
tyToItem ty = mkItem ("Type", pretty ty) (getRange ty) []

vToItem :: Vars -> Item
vToItem vs = mkItem ("Vars", pretty vs) nullRange []

scToItem :: TypeScheme -> Item
scToItem sc = mkItem ("TypeScheme" , pretty sc) (getRange sc) []

oiToItem :: OpItem -> Item
oiToItem oi = case oi of
  OpDecl is sc as rg -> mkItem "OpDecl" rg
    $ map (emptyAnno . polyIdToItem) is
      ++ [emptyAnno $ scToItem sc] ++ map (emptyAnno . attrToItem) as
  OpDefn o vs sc trm rg -> mkItem "OpDefn" rg
    $ map emptyAnno
    $ polyIdToItem o : [headToItem vs | not $ null vs ]
    ++ [scToItem sc, trmToItem trm]

polyIdToItem :: PolyId -> Item
polyIdToItem i@(PolyId _ _ rg) = mkItem ("OpId", pretty i) rg []

attrToItem :: OpAttr -> Item
attrToItem a = mkItem ("OpAttr", pretty a) (getRange a) []

headToItem :: [[VarDecl]] -> Item
headToItem vs = mkItem ("OpHead", fcat $ printHead vs) nullRange []

peToItem :: ProgEq -> Item
peToItem pe@(ProgEq _ _ rg) = mkItem ("ProgEq", pretty pe) rg []

ciToItem :: ClassItem -> Item
ciToItem (ClassItem cd bs rg) =
  mkItem "ClassItem" rg $ emptyAnno (cdToItem cd) : map (fmap biToItem) bs

cdToItem :: ClassDecl -> Item
cdToItem (ClassDecl cs k rg) =
  mkItem "ClassDecl" rg $ map (emptyAnno . classToItem) cs
  ++ [emptyAnno $ kToItem k]

classToItem :: Id -> Item
classToItem i = mkItem ("Class", pretty i) (getRangeSpan i) []

gvdToItem :: GenVarDecl -> Item
gvdToItem gvd = mkItem ("GenVarDecl", pretty gvd) nullRange []

dtdToItem :: DatatypeDecl -> Item
dtdToItem (DatatypeDecl tp k as ds rg) =
  mkItem "DatatypeDecl" rg $ emptyAnno (tpToItem tp) :
  emptyAnno (kToItem k) : map (fmap altToItem) as
  ++ map (emptyAnno . classToItem) ds

altToItem :: Alternative -> Item
altToItem a = case a of
  Constructor _ _ _ r -> mkItem ("Constructor", pretty a) r []
  Subtype _ r -> mkItem ("SubtypeAlternative", pretty a) r []

trmToItem :: Term -> Item
trmToItem t = mkItem ("Term", pretty t) (getRange t) []
