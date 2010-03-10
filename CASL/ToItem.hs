{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
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

import Control.Monad.Reader

import Common.Doc
import Common.DocUtils
import Common.Id
import Common.Item

import CASL.AS_Basic_CASL
import CASL.ToDoc

--------------------- TS = TransState
data TS b s f = TS { fB :: b -> Doc
                   , fS :: s -> Doc
                   , fF :: f -> Doc }

-- LITC = LocalITContext
-- This datastructure is used to pass an additional ItemType argument to
-- the toitem method when one needs an instance for which this method
-- should behave differently in different contexts depending on this argument.
-- Typically the ItemType is used as ItemType of the Item to be created.

data LITC a = LITC ItemType a

--------------------- lifting to Local Contexts
withLIT :: ItemTypeable a => a -> b -> LITC b
withLIT = LITC . toIT

listWithLIT :: ItemTypeable a => a -> [b] -> [LITC b]
listWithLIT = map . withLIT

-- analogous for annotated objects, don't needed yet
--annWithLIT :: ItemTypeable a => a -> Annoted b -> Annoted (LITC b)
--annWithLIT it = fmap (withLIT it)

--annlistWithLIT :: ItemTypeable a => a -> [Annoted b] -> [Annoted (LITC b)]
--annlistWithLIT it = map (annWithLIT it)


-- this function is only to unify the types of the state and the basic spec
-- in the call of toitem and runState in bsToItem
getTransState :: (Pretty b, Pretty s, Pretty f)
    => BASIC_SPEC b s f -> TS b s f
getTransState _ = TS pretty pretty pretty

--------------------- The Main function of this module
bsToItem :: (Pretty b, Pretty s, Pretty f, GetRange b, GetRange s, GetRange f)
    => BASIC_SPEC b s f -> Item
bsToItem bs = runReader (toitem bs) $ getTransState bs

instance (GetRange b, GetRange s, GetRange f)
    => ItemConvertible (BASIC_SPEC b s f) (Reader (TS b s f)) where
    toitem (Basic_spec l) = do
        l' <-  listFromAL l
        return rootItem { items = l' }

instance (GetRange b, GetRange s, GetRange f)
    => ItemConvertible (BASIC_ITEMS b s f) (Reader (TS b s f)) where
    toitem bi = let rg = getRangeSpan bi in
        case bi of
          Sig_items s -> toitem s
          Var_items l _ -> mkItemM "Var_items" rg $ listFromL l
          Axiom_items al _ -> mkItemM "Axiom_items" rg $ listFromAL al
          Local_var_axioms vl fl _ ->
              mkItemMM "Local_var_axioms" rg
                           [fromL "VAR_DECLS" vl, fromAL "FORMULAS" fl]
          Sort_gen asis _ -> mkItemM "Sort_gen" rg $ listFromAL asis
          Free_datatype sk adtds _ ->
              mkItemM ("Free_datatype", "SortsKind", show sk) rg
                          $ listFromAL adtds
          Ext_BASIC_ITEMS b -> do
              st <- ask
              fromPrinter (fB st) "Ext_BASIC_ITEMS" b

instance (GetRange s, GetRange f)
    => ItemConvertible (SIG_ITEMS s f) (Reader (TS b s f)) where
    toitem si = let rg = getRangeSpan si in
        case si of
          Sort_items sk sis _ ->
              mkItemM ("Sort_items", "SortsKind", show sk) rg
                $ listFromAL sis
          Op_items aois _ -> mkItemM "Op_items" rg $ listFromAL aois
          Pred_items apis _ -> mkItemM "Pred_items" rg $ listFromAL apis
          Datatype_items sk adds _ ->
              mkItemM ("Datatype_items", "SortsKind", show sk) rg
                $ listFromAL adds
          Ext_SIG_ITEMS s -> do
              st <- ask
              fromPrinter (fS st) "Ext_SIG_ITEMS" s


instance GetRange f => ItemConvertible (SORT_ITEM f) (Reader (TS b s f)) where
    toitem si = let rg = getRangeSpan si in
        case si of
          Sort_decl l _ -> mkItemM "Sort_decl" rg $ listFromL
                            $ listWithLIT "SORT" l
          Subsort_decl sl s _ -> mkItemMM "Subsort_decl" rg
                                  [ fromL "SORTS" $ listWithLIT "SORT" sl
                                  , fromC $ withLIT "SORT" s]
          Subsort_defn s v s' f _ ->
              mkItemMM "Subsort_defn" rg
                [ fromC $ withLIT "SORT" s, fromC $ withLIT "VAR" v
                , fromC $ withLIT "SORT" s', fromAC f]
          Iso_decl l _ -> mkItemM "Iso_decl" rg $ listFromL
                           $ listWithLIT "SORT" l


instance GetRange f => ItemConvertible (OP_ITEM f) (Reader (TS b s f)) where
    toitem oi = let rg = getRangeSpan oi in
        case oi of
          Op_decl onl ot oal _ ->
              mkItemMM "Op_decl" rg
                [ fromL "OP_NAMES" $ listWithLIT "OP_NAME" onl, fromC ot
                , fromL "OP_ATTRIBS" oal]
          Op_defn on oh at _ ->
              mkItemMM "Op_defn" rg [ fromC $ withLIT "OP_NAME" on, fromC oh
                                    , fromAC at]


instance GetRange f => ItemConvertible (PRED_ITEM f) (Reader (TS b s f)) where
    toitem p = let rg = getRangeSpan p in
        case p of
          Pred_decl pnl pt _ ->
              mkItemMM "Pred_decl" rg
                [fromL "PRED_NAMES" $ listWithLIT "PRED_NAME" pnl, fromC pt]
          Pred_defn pn ph af _ ->
              mkItemMM "Pred_defn" rg [ fromC $ withLIT "PRED_NAME" pn, fromC ph
                                      , fromAC af]


-------------------- not further expanded --------------------

fromPrinterWithRg :: (Monad m, GetRange a) =>
                     (a -> Doc) -> String -> a -> m Item
fromPrinterWithRg = fromPrinterWithRange getRangeSpan

fromPrinterWithRange
    :: Monad m => (a -> Range) -> (a -> Doc) -> String -> a -> m Item
fromPrinterWithRange r p n o = mkItemMM (n, p o) (r o) []

fromPrinter :: Monad m => (a -> Doc) -> String -> a -> m Item
fromPrinter p n o = mkItemMM (n, p o) nullRange []

litFromPrinterWithRg :: (Monad m, GetRange a) =>
                        (a -> Doc) -> LITC a -> m Item
litFromPrinterWithRg p (LITC (IT l attrs _) o) =
    mkItemMM (IT l attrs $ Just $ p o) (getRangeSpan o) []


instance ItemConvertible OP_TYPE (Reader (TS b s f)) where
    toitem = fromPrinterWithRg pretty "OP_TYPE"

instance ItemConvertible OP_HEAD (Reader (TS b s f)) where
    toitem = fromPrinterWithRg pretty "OP_HEAD"

instance ItemConvertible (OP_ATTR f) (Reader (TS b s f)) where
    toitem a = do
        st <- ask
        fromPrinter (printAttr (fF st)) "OP_ATTR" a

instance ItemConvertible PRED_TYPE (Reader (TS b s f)) where
    toitem = fromPrinterWithRg pretty "PRED_TYPE"

instance ItemConvertible PRED_HEAD (Reader (TS b s f)) where
    toitem = fromPrinterWithRg printPredHead "PRED_HEAD"

instance ItemConvertible DATATYPE_DECL (Reader (TS b s f)) where
    toitem = fromPrinterWithRg pretty "DATATYPE_DECL"

instance ItemConvertible VAR_DECL (Reader (TS b s f)) where
    toitem = fromPrinterWithRg pretty "VAR_DECL"

instance GetRange f => ItemConvertible (FORMULA f) (Reader (TS b s f)) where
    toitem f = do
      st <- ask
      fromPrinterWithRange getRangeSpan
               (printFormula (fF st)) "FORMULA" f

instance GetRange f => ItemConvertible (TERM f) (Reader (TS b s f)) where
    toitem f = do
      st <- ask
      fromPrinterWithRange getRangeSpan
               (printTerm (fF st)) "TERM" f

instance ItemConvertible (LITC Id) (Reader (TS b s f)) where
    toitem = litFromPrinterWithRg pretty

instance ItemConvertible (LITC Token) (Reader (TS b s f)) where
    toitem = litFromPrinterWithRg pretty
