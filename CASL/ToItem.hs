{- |
Module      :  $Header$
Description :  extracted annotated items as strings from BASIC_SPEC
Copyright   :  (c) Christian Maeder and Ewaryst Schulz  and DFKI GmbH 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  experimental
Portability :  non-portable

get item representation of 'BASIC_SPEC'
-}

module CASL.ToItem (bsToItem) where

import Control.Monad.State

import Common.Doc
import Common.DocUtils
import Common.Id
import Common.Item
--import Common.AS_Annotation

import CASL.AS_Basic_CASL
import CASL.ToDoc()

-- utils
mapF :: Functor f => (a -> b) -> [f a] -> [f b]
mapF f = map $ fmap f



instance ItemTypeable SortsKind where
    toIT NonEmptySorts = Nonempty
    toIT PossiblyEmptySorts = Possiblyempty


-- TS = TransState
data TS b s f = TS { fB :: (b -> Doc)
                   , fS :: (s -> Doc)
                   , fF :: (f -> Doc) }


-- this function is only to unify the types of the state and the basic spec
-- in the call of toitem and runState in bsToItem
getTransState :: (Pretty b, Pretty s, Pretty f) => BASIC_SPEC b s f ->
                 TS b s f
getTransState _ = TS pretty pretty pretty

bsToItem :: (Pretty b, Pretty s, Pretty f) => (BASIC_SPEC b s f) -> Item
bsToItem bs = fst $ runState (toitem bs) $ getTransState bs

instance ItemConvertible (BASIC_SPEC b s f) (State (TS b s f)) where
    toitem (Basic_spec l) = 
        do{ l' <-  listfromAList l
          ; return rootItem{ items = l' } }

instance ItemConvertible (BASIC_ITEMS b s f) (State (TS b s f)) where
    toitem bi =
        case bi of
          Sig_items s -> toitem s
          _ -> return $ abstract "basicitem"

instance ItemConvertible (SIG_ITEMS s f) (State (TS b s f)) where
    toitem si = return $ liftIT2I $ Simple Sig




{-

bsToItem2 :: (Pretty b, Pretty s, Pretty f) => BASIC_SPEC b s f -> Item
bsToItem2 = basicSpecToItem $ TS pretty pretty pretty


basicSpecToItem :: TS b s f ->
                   BASIC_SPEC b s f -> Item
basicSpecToItem st (Basic_spec l) =
    rootItem { items = mapF (basicItem2I st) l }


basicItem2I :: TS b s f ->
               BASIC_ITEMS b s f -> Item

basicItem2I st (Sig_items s) = sigItem2I st s
basicItem2I st (Free_datatype sk l rg) =
    Item (IT Datatype Free) rg [] $ (liftIT2AI sk) : [] -- mapF (dtdecl2I st) l
basicItem2I st (Sort_gen _ rg) = Item (IT SortK Gen) rg [] []
basicItem2I st (Var_items _ rg) = Item (IT Var Items) rg [] []
basicItem2I st (Local_var_axioms _ _ rg) = Item Localvaraxioms rg [] []
basicItem2I st (Axiom_items _ rg) = Item Axiomitems rg [] []
basicItem2I st (Ext_BASIC_ITEMS _) = Item (IT Basic Ext) nullRange [] []


sigItem2I :: TS b s f ->
             SIG_ITEMS s f -> Item

sigItem2I st (Sort_items sk sis rg) =
    Item (IT SortK Items) rg [] $ mapF (sortItem2I st) sis
sigItem2I _ _ = liftIT2I (Simple Sig)


sortItem2I :: TS b s f ->
              SORT_ITEM f -> Item

sortItem2I st (Sort_decl l rg) = liftIT2I (Simple SortK)
sortItem2I st (Subsort_decl l t rg) = liftIT2I (Simple SortK)
sortItem2I st (Subsort_defn s v s' f rg) = liftIT2I (Simple SortK)
sortItem2I st (Iso_decl l rg) = liftIT2I (Simple SortK)
-}

{-

data SORT_ITEM f = Sort_decl [SORT] Range
                 -- pos: commas
               | Subsort_decl [SORT] SORT Range
                 -- pos: commas, <
               | Subsort_defn SORT VAR SORT (Annoted (FORMULA f)) Range
                 -- pos: "=", "{", ":", ".", "}"
                 -- the left anno list stored in Annoted Formula is
                 -- parsed after the equal sign
               | Iso_decl [SORT] Range
                 -- pos: "="s
                 deriving Show

Sort_items SortsKind [Annoted (SORT_ITEM f)] Range
                 -- pos: sort, semi colons
               | Op_items [Annoted (OP_ITEM f)] Range
                 -- pos: op, semi colons
               | Pred_items [Annoted (PRED_ITEM f)] Range
                 -- pos: pred, semi colons
               | Datatype_items SortsKind [Annoted DATATYPE_DECL] Range
                 -- type, semi colons
               | Ext_SIG_ITEMS s

formToItem :: TS b s f -> Annoted (FORMULA f) -> Annoted String
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