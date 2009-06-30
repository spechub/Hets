{- |
Module      :  $Header$
Description :  extracted annotated items as strings from BASIC_SPEC
Copyright   :  (c) Christian Maeder and Uni Bremen 2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

get annotated strings of 'BASIC_SPEC'
-}

module CASL.ToAnnStrList where

import Common.Id
import Common.Keywords
import Common.Doc
import Common.DocUtils
import Common.AS_Annotation

import CASL.AS_Basic_CASL
import CASL.ToDoc

basicSpec2annStrList :: (b -> Doc) -> (s -> Doc) -> (f -> Doc)
                     -> BASIC_SPEC b s f -> [Annoted String]
basicSpec2annStrList fB fS fF (Basic_spec l) = case l of
    [] -> []
    _ -> concatMap (basicItem2annStrList fB fS fF) l

basicItem2annStrList :: (b -> Doc) -> (s -> Doc) -> (f -> Doc)
                 -> Annoted (BASIC_ITEMS b s f) -> [Annoted String]
basicItem2annStrList fB fS fF sis = case item sis of
    Sig_items s -> sigItem2annStrList fS fF sis { item = s }
    Free_datatype sk l _ ->
      sis { item = show $ keyword freeS <+> keyword (typeString sk l)
          , r_annos = [] }
      : map dtdecl2annStrList l
      ++ if null $ r_annos sis then [] else [sis { item = "", l_annos = [] }]
    Sort_gen l _ -> case l of
         [Annoted (Datatype_items sk l' _) _ las ras] ->
           let alas = l_annos sis ++ las
               aras = ras ++ r_annos sis
           in sis
           { item = show $ keyword generatedS <+> keyword (typeString sk l')
           , l_annos = alas, r_annos = [] }
           : map dtdecl2annStrList l'
           ++ if null aras then [] else
                  [sis { item = "", l_annos = [], r_annos = aras} ]
         _ -> sis { item = show $ keyword generatedS <+> text "{"
                  , r_annos = [] }
              : concatMap (sigItem2annStrList fS fF) l
              ++ [sis { item = "}", l_annos = [] }]
    Var_items l _ -> [sis
      { item = show $ topSigKey (varS ++ pluralS l)
        <+> fsep (punctuate semi $ map printVarDecl l) }]
    Local_var_axioms l f _ -> sis
      { item = show $ fsep $ forallDoc : punctuate semi (map printVarDecl l)
      , r_annos = [] }
      : map (form2annStrList fF) f
      ++ if null $ r_annos sis then [] else [sis { item = "", l_annos = [] }]
    Axiom_items f _ ->
      if null $ l_annos sis then [] else [sis { item = "", r_annos = [] }]
      ++ map (form2annStrList fF) f
      ++ if null $ r_annos sis then [] else [sis { item = "", l_annos = [] }]
    Ext_BASIC_ITEMS b -> [sis { item = show $ fB b }]

form2annStrList :: (f -> Doc) -> Annoted (FORMULA f) -> Annoted String
form2annStrList fF f =
  f { item = show $ addBullet (printFormula fF $ item f) <> semi }

sigItem2annStrList :: (s -> Doc) -> (f -> Doc) -> Annoted (SIG_ITEMS s f)
                   -> [Annoted String]
sigItem2annStrList fS fF sis = case item sis of
    Sort_items sk l _ -> sis
      {item = show $ topSigKey $ (case sk of
        NonEmptySorts -> sortS
        PossiblyEmptySorts -> esortS) ++ pluralS l
      , r_annos = [] }
      : map (sortItem2annStrList fF) l
      ++ if null $ r_annos sis then [] else [sis { item = "", l_annos = [] }]
    Op_items l _  ->
      sis { item = show $ topSigKey $ opS ++ pluralS l
          , r_annos = [] }
      : map (opItem2annStrList fF) l
      ++ if null $ r_annos sis then [] else [sis { item = "", l_annos = [] }]
    Pred_items l _ ->
      sis { item = show $ topSigKey $ predS ++ pluralS l
          , r_annos = [] }
      : map (predItem2annStrList fF) l
      ++ if null $ r_annos sis then [] else [sis { item = "", l_annos = [] }]
    Datatype_items sk l _ ->
      sis { item = show $ topSigKey $ typeString sk l
          , r_annos = [] }
      : map dtdecl2annStrList l
      ++ if null $ r_annos sis then [] else [sis { item = "", l_annos = [] }]
    Ext_SIG_ITEMS s -> [sis { item = show $ fS s }]

dtdecl2annStrList :: Annoted DATATYPE_DECL -> Annoted String
dtdecl2annStrList dt = dt { item = showDoc (item dt) "" }

sortItem2annStrList :: (f -> Doc) -> Annoted (SORT_ITEM f) -> Annoted String
sortItem2annStrList mf si = case item si of
    Subsort_defn s v sup af r -> let nf = emptyAnno $ item af in si
      { item = show $ printSortItem mf (Subsort_defn s v sup nf r) <> semi
      , l_annos = l_annos si ++ l_annos af
      , r_annos = r_annos af ++ r_annos si }
    s -> si { item = show $ printSortItem mf s <> semi }

opItem2annStrList :: (f -> Doc) -> Annoted (OP_ITEM f) -> Annoted String
opItem2annStrList mf p = case item p of
    Op_defn i h t r -> let nt = emptyAnno $ item t in p
      { item = show $ printOpItem mf (Op_defn i h nt r) <> semi
      , l_annos = l_annos p ++ l_annos t
      , r_annos = r_annos t ++ r_annos p }
    o -> p { item = show $ printOpItem mf o <> semi }

predItem2annStrList :: (f -> Doc) -> Annoted (PRED_ITEM f) -> Annoted String
predItem2annStrList mf p = case item p of
    Pred_defn i h f r -> let nf = emptyAnno $ item f in p
      { item = show $ printPredItem mf (Pred_defn i h nf r) <> semi
      , l_annos = l_annos p ++ l_annos f
      , r_annos = r_annos f ++ r_annos p }
    pd -> p { item = show $ printPredItem mf pd <> semi }
