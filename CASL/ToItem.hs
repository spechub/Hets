{- |
Module      :  $Header$
Description :  extracted annotated items as strings from BASIC_SPEC
Copyright   :  (c) Christian Maeder and Ewaryst Schulz  and DFKI GmbH 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  experimental
Portability :  portable

get item representation of 'BASIC_SPEC'
-}

module CASL.ToItem (bsToItem) where

import Common.Doc
import Common.DocUtils
import Common.Id
import Common.Item
import Common.AS_Annotation

import CASL.AS_Basic_CASL
import CASL.ToDoc()


instance ItemTypeable SortsKind where
    toIT NonEmptySorts = Nonempty
    toIT PossiblyEmptySorts = Possiblyempty


data (Pretty b, Pretty s, Pretty f) =>
    TransState b s f = TS { fB :: (b -> Doc)
                          , fS :: (s -> Doc)
                          , fF :: (f -> Doc) }

bsToItem :: (Pretty b, Pretty s, Pretty f) => BASIC_SPEC b s f -> Item
bsToItem = basicSpecToItem $ TS pretty pretty pretty

basicSpecToItem :: (Pretty b, Pretty s, Pretty f) => 
                   TransState b s f -> BASIC_SPEC b s f -> Item
basicSpecToItem st (Basic_spec l) =
    rootItem { items = map (fmap $ basicItem2I st) l }

-- only to copy from it later
basicItemToItem :: (Pretty b, Pretty s, Pretty f) => 
                   TransState b s f -> BASIC_ITEMS b s f -> Item
basicItemToItem _ sis = liftIT2I $ Abstract $ show $ pretty sis
----

basicItem2I :: (Pretty b, Pretty s, Pretty f) => 
               TransState b s f -> BASIC_ITEMS b s f -> Item
basicItem2I st (Sig_items s) = sigItem2I st s
basicItem2I st (Free_datatype sk l rg) =
    Item Freedatatype rg $ (liftIT2AI $ toIT sk) : [] -- map (fmap $ dtdecl2I st) l

basicItem2I st (Sort_gen _ rg) = Item Sortgen rg []
basicItem2I st (Var_items _ rg) = Item Varitems rg []
basicItem2I st (Local_var_axioms _ _ rg) = Item Localvaraxioms rg []
basicItem2I st (Axiom_items _ rg) = Item Axiomitems rg []
basicItem2I st (Ext_BASIC_ITEMS _) = Item Extbasicitems nullRange []

sigItem2I :: (Pretty b, Pretty s, Pretty f) => 
               TransState b s f -> SIG_ITEMS s f -> Item

sigItem2I _ _ = liftIT2I Sigitem

{-
basicItemToItem :: TransState b s f -> BASIC_ITEMS b s f -> Item
basicItemToItem st sis = let
  rans = if null $ r_annos sis then [] else [sis { item = "", l_annos = [] }]
  in case item sis of
    Sig_items s -> sigItemToItem s sis
    Free_datatype sk l _ ->
      sis { item = show $ keyword freeS <+> keyword (typeString sk l)
          , r_annos = [] }
      : addSemi (map dtdeclToItem l)
      ++ rans
    Sort_gen l _ -> case l of
         [Annoted (Datatype_items sk l' _) _ las ras] ->
           let alas = l_annos sis ++ las
               aras = ras ++ r_annos sis
           in sis
           { item = show $ keyword generatedS <+> keyword (typeString sk l')
           , l_annos = alas, r_annos = [] }
           : addSemi (map dtdeclToItem l')
           ++ if null aras then [] else
                  [sis { item = "", l_annos = [], r_annos = aras} ]
         _ -> sis { item = show $ keyword generatedS <+> text "{"
                  , r_annos = [] }
              : concatMap (sigItemToItem fS fF) l
              ++ [sis { item = "}", l_annos = [] }]
    Var_items l _ -> [sis
      { item = show $ topSigKey (varS ++ pluralS l)
        <+> fsep (punctuate semi $ map printVarDecl l) }]
    Local_var_axioms l f _ -> sis
      { item = show $ fsep $ forallDoc : punctuate semi (map printVarDecl l)
      , r_annos = [] }
      : map (formToItem fF) f
      ++ rans
    Axiom_items f _ ->
      if null $ l_annos sis then [] else [sis { item = "", r_annos = [] }]
      ++ map (formToItem fF) f
      ++ rans
    Ext_BASIC_ITEMS b -> [sis { item = show $ fB b }]

formToItem :: TransState b s f -> Annoted (FORMULA f) -> Annoted String
formToItem s f = f { item = show . addBullet . printFormula (fF s) $ item f }

sigItemToItem :: (s -> Doc) -> (f -> Doc) -> Annoted (SIG_ITEMS s f)
                   -> [Annoted String]
sigItemToItem fS fF sis = let
  ras = if null $ r_annos sis then [] else [sis { item = "", l_annos = [] }]
  in case item sis of
    Sort_items sk l _ -> sis
      {item = show $ topSigKey $ (case sk of
        NonEmptySorts -> sortS
        PossiblyEmptySorts -> esortS) ++ pluralS l
      , r_annos = [] }
      : map (sortItemToItem fF) l
      ++ ras
    Op_items l _  ->
      sis { item = show $ topSigKey $ opS ++ pluralS l
          , r_annos = [] }
      : addSemi (map (opItemToItem fF) l)
      ++ ras
    Pred_items l _ ->
      sis { item = show $ topSigKey $ predS ++ pluralS l
          , r_annos = [] }
      : addSemi (map (predItemToItem fF) l)
      ++ ras
    Datatype_items sk l _ ->
      sis { item = show $ topSigKey $ typeString sk l
          , r_annos = [] }
      : addSemi (map dtdeclToItem l)
      ++ ras
    Ext_SIG_ITEMS s -> [sis { item = show $ fS s }]

addSemi :: [Annoted String] -> [Annoted String]
addSemi l = case reverse l of
  [] -> []
  lt : rt -> reverse $ lt : map (\ a -> a { item = item a ++ ";" }) rt

dtdeclToItem :: Annoted DATATYPE_DECL -> Annoted String
dtdeclToItem dt = dt { item = showDoc (item dt) ""}

sortItemToItem :: (f -> Doc) -> Annoted (SORT_ITEM f) -> Annoted String
sortItemToItem mf si = case item si of
    Subsort_defn s v sup af r -> let nf = emptyAnno $ item af in si
      { item = show $ printSortItem mf (Subsort_defn s v sup nf r)
      , l_annos = l_annos si ++ l_annos af
      , r_annos = r_annos af ++ r_annos si }
    s -> si { item = show $ printSortItem mf s }

opItemToItem :: (f -> Doc) -> Annoted (OP_ITEM f) -> Annoted String
opItemToItem mf p = case item p of
    Op_defn i h t r -> let nt = emptyAnno $ item t in p
      { item = show $ printOpItem mf (Op_defn i h nt r)
      , l_annos = l_annos p ++ l_annos t
      , r_annos = r_annos t ++ r_annos p }
    o -> p { item = show $ printOpItem mf o }

predItemToItem :: (f -> Doc) -> Annoted (PRED_ITEM f) -> Annoted String
predItemToItem mf p = case item p of
    Pred_defn i h f r -> let nf = emptyAnno $ item f in p
      { item = show $ printPredItem mf (Pred_defn i h nf r)
      , l_annos = l_annos p ++ l_annos f
      , r_annos = r_annos f ++ r_annos p }
    pd -> p { item = show $ printPredItem mf pd }

-}