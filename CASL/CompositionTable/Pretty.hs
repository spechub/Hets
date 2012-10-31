{- |
Module      :  $Header$
Description :  pretty output for composition tables
Copyright   :  (c) Christian Maeder DFKI 2012
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

-}

module CASL.CompositionTable.Pretty where

import CASL.CompositionTable.CompositionTable
import CASL.CompositionTable.Keywords
import Common.Doc

ctxt :: String -> Doc
ctxt = text . (':' :)

table2Doc :: Table -> Doc
table2Doc (Table (Table_Attrs name br brs)
           (Compositiontable cs) ct (Reflectiontable rs)
           (Models ms)) =
   parens $ text defCalculusS <+> doubleQuotes (text name)
   $+$ ctxt identityRelationS <+> baserel br
   $+$ (if null brs then empty else
        ctxt baseRelationsS <+> parens
             (hsep $ map baserel brs))
   $+$ conversetable ct
   $+$ (if null cs then empty else
        colon <> (text compositionOperationS $+$
                  parens (vcat $ map cmptabentry cs)))
   $+$ (if null rs then empty else
            text ";; reflectiontable" <+>
             parens (vcat $ map reftabentry rs))
   $+$ (if null ms then empty else
            text ";; models" <+>
             parens (vcat $ map model ms))

baserel :: Baserel -> Doc
baserel (Baserel br) = text br

cmptabentry :: Cmptabentry -> Doc
cmptabentry (Cmptabentry (Cmptabentry_Attrs a1 a2) l) = parens
  $ baserel a1 <+> baserel a2 <+> parens (hsep $ map baserel l)

conversetable :: Conversetable -> Doc
conversetable ct = case ct of
  Conversetable l -> if null l then empty else
        colon <> (text converseOperationS $+$
             parens (vcat $ map contabentry l))
  Conversetable_Ternary l1 l2 l3 ->
    vcat [ contab3 inverseOperationS l1
         , contab3 shortcutOperationS l2
         , contab3 homingOperationS l3 ]

contab3 :: String -> [Contabentry_Ternary] -> Doc
contab3 t l = if null l then empty else
   colon <> (text t $+$ parens (vcat $ map contabentry3 l))

contabentry3 :: Contabentry_Ternary -> Doc
contabentry3 (Contabentry_Ternary a l) =
  parens $ baserel a <+> case l of
           [b] -> baserel b
           _ -> parens $ hsep $ map baserel l

contabentry :: Contabentry -> Doc
contabentry (Contabentry a bs) = parens $ baserel a <+> case bs of
  [b] -> baserel b
  _ -> parens $ hsep $ map baserel bs

reftabentry :: Reftabentry -> Doc
reftabentry (Reftabentry a b) = parens $ baserel a <+> baserel b

model :: Model -> Doc
model (Model a b) = parens $ text a <+> text b
