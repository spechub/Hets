{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances, DeriveDataTypeable #-}
{- |
Module      :  ./GenHyb/GenInsts
Description :  Instance of class Logic for rigid CASL


Instance of class Logic for rigid logic.
-}

module GenHyb.GenInsts where

import Logic.Logic
import Common.Id
import Common.Doc
import Common.DocUtils
import qualified Data.Set as Set
import qualified Data.Map as Map
import GenHyb.GenTypes

import ATerm.Lib
import ATC.Id
import ATC.AS_Annotation

-- for HSign

instance (Pretty sig) => Pretty (HSign sig) where
    pretty = printSign

printSign :: (Pretty sig) => HSign sig -> Doc
printSign hsig = 
 let bsig = baseSig hsig in 
    pretty bsig {- (bsig {CSign.sortRel = Rel.difference (Rel.transReduce $ CSign.sortRel bsig)
                             . Rel.transReduce $ Rel.fromSet $ Set.map (\x->(x,x)) $ PARSign.rigidSorts $ CSign.extendedInfo bsig,
                  CSign.opMap = CSign.diffOpMapSet (CSign.opMap bsig) $ PARSign.rigidOps $ CSign.extendedInfo bsig,
                  CSign.predMap = CSign.diffMapSet (CSign.predMap bsig) $ PARSign.rigidPreds $ CSign.extendedInfo bsig}) -}
    -- this ensures that the rigid symbols are not displayed as non-rigid
    $+$
    let nomss = Set.toList $ noms hsig in
    case nomss of 
     [] -> empty
     _ -> hsep [text ("nominal" ++ (case nomss of 
                              [_] -> ""
                              _ -> "s")), sepByCommas $ map pretty nomss]
    $+$
    (foldl (\aDoc (i,n) -> aDoc $+$ 
                            hsep [text ( case Map.toList $ mods hsig of 
                                           [_] -> "modality"
                                           _ -> "modalities"
                                       ),
                                  pretty i, 
                                  text ":", 
                                  pretty n]) empty $ Map.toList $ mods hsig)

instance (ShATermConvertible sig) => ShATermConvertible (HSign sig) where
  toShATermAux att0 xv = case xv of
    HSign a b c -> do
      (att1, a') <- toShATerm' att0 a
      (att2, b') <- toShATerm' att1 b
      (att3, c') <- toShATerm' att2 c
      return $ addATerm (ShAAppl "HSign" [a', b', c'] []) att3
  fromShATermAux ix att0 = case getShATerm ix att0 of
    ShAAppl "HSign" [a, b, c] _ ->
      case fromShATerm' a att0 of
      { (att1, a') ->
      case fromShATerm' b att1 of
      { (att2, b') ->
      case fromShATerm' c att2 of
      { (att3, c') ->
      (att3, HSign a' b' c') }}}
    u -> fromShATermError "HSign" u

-- for HMorphism

instance (Pretty sig, Pretty mor) => Pretty (HMorphism sig mor) where
    pretty = printMorphism

printMorphism :: (Pretty sig, Pretty mor) => HMorphism sig mor -> Doc
printMorphism hmor = error "printmorphism nyi"

instance (ShATermConvertible sig, ShATermConvertible mor) 
   => ShATermConvertible (HMorphism sig mor) where
  toShATermAux att0 xv = case xv of
    HMorphism a b c d e -> do
      (att1, a') <- toShATerm' att0 a
      (att2, b') <- toShATerm' att1 b
      (att3, c') <- toShATerm' att2 c
      (att4, d') <- toShATerm' att3 d
      (att5, e') <- toShATerm' att4 e
      return $ addATerm (ShAAppl "HMorphism" [a', b', c', d',
                                              e'] []) att5
  fromShATermAux ix att0 = case getShATerm ix att0 of
    ShAAppl "HMorphism" [a, b, c, d, e] _ ->
      case fromShATerm' a att0 of
      { (att1, a') ->
      case fromShATerm' b att1 of
      { (att2, b') ->
      case fromShATerm' c att2 of
      { (att3, c') ->
      case fromShATerm' d att3 of
      { (att4, d') ->
      case fromShATerm' e att4 of
      { (att5, e') ->
      (att5, HMorphism a' b' c' d' e') }}}}}
    u -> fromShATermError "HMorphism" u

-- for HFORMULA

instance (Pretty sen, Pretty raw_sym, Show symb_items) => Pretty (HFORMULA sen symb_items raw_sym)
 where
   pretty = printFormula

printFormula :: (Pretty sen, Pretty raw_sym, Show symb_items) => HFORMULA sen symb_items raw_sym -> Doc
printFormula aFrm = case aFrm of
   Base_formula pfrm _ -> pretty pfrm
   Nominal _s _ nom _ -> pretty nom -- TODO: add the optional qualification  
   AtState nom frm _ -> prettyAt <+> pretty nom <+> colon <+> printFormula frm 
   BoxFormula md frm _ -> lbrack <+> pretty md <+> rbrack <+> printFormula frm
   DiamondFormula md frm _ -> text "<" <+> pretty md <+> text ">" <+> printFormula frm
   Negation frm _ -> notDoc <+> printFormula frm
   Conjunction xs _ -> sepByArbitrary andDoc $ 
                        map printFormula xs
   Disjunction xs _ -> sepByArbitrary orDoc $ 
                         map printFormula xs
   Implication x y _ -> printFormula x <+> 
                          implies <+> printFormula y
   Equivalence x y _ -> printFormula x <+> 
                          equiv <+> printFormula y
   --QuantRigidVars q vdecls frm _ -> printQuant q <+> CPrint.printVarDecls vdecls <+> bullet <+> printFormula frm
   QuantVarsParse _ _ _ _ -> error $ "formula not yet analyzed" --  ++ show aFrm
   QuantVars q rsyms frm _ -> printQuant q <+> pretty rsyms <+> bullet <+> printFormula frm -- TODO: this is now bad because we get brackets around the rsyms
   QuantNominals q nomVars frm _ -> printQuant q <+> keyword nomS <+> sepByCommas (map pretty nomVars) <+> bullet <+> printFormula frm

instance (GetRange sen, GetRange raw_sym, GetRange symb_items) => GetRange (HFORMULA sen symb_items raw_sym)
 where
  getRange _ = nullRange
  rangeSpan x = case x of
    Base_formula a b -> joinRanges [rangeSpan a, rangeSpan b]
    Negation a b -> joinRanges [rangeSpan a, rangeSpan b]
    Conjunction a b -> joinRanges [rangeSpan a, rangeSpan b]
    Disjunction a b -> joinRanges [rangeSpan a, rangeSpan b]
    Implication a b c -> joinRanges [rangeSpan a, rangeSpan b,
                                     rangeSpan c]
    Equivalence a b c -> joinRanges [rangeSpan a, rangeSpan b,
                                     rangeSpan c]
    Nominal s a b c -> joinRanges [rangeSpan s, rangeSpan a, rangeSpan b, rangeSpan c]
    AtState a b c -> joinRanges [rangeSpan a, rangeSpan b, rangeSpan c]
    BoxFormula a b c -> joinRanges [rangeSpan a, rangeSpan b,
                                    rangeSpan c]
    DiamondFormula a b c -> joinRanges [rangeSpan a, rangeSpan b,
                                        rangeSpan c]
    QuantVarsParse a b c d -> joinRanges [rangeSpan a, rangeSpan b,
                                          rangeSpan c, rangeSpan d]
    QuantVars a b c d -> joinRanges [rangeSpan a, rangeSpan b,
                                          rangeSpan c, rangeSpan d]
    QuantNominals a b c d -> joinRanges [rangeSpan a, rangeSpan b,
                                         rangeSpan c, rangeSpan d]

printQuant :: HQUANT -> Doc -- TODO: add the optional string
printQuant (HUniversal _) = forallH 
printQuant (HExistential _) = existsH

instance GetRange HQUANT where
  getRange = const nullRange
  rangeSpan x = case x of
    HUniversal _ -> []
    HExistential _ -> []

instance ShATermConvertible HQUANT where
  toShATermAux att0 xv = case xv of
    HUniversal _ -> return $ addATerm (ShAAppl "HUniversal" [] []) att0
    HExistential _ -> return $ addATerm (ShAAppl "HExistential" [] []) att0
  fromShATermAux ix att0 = case getShATerm ix att0 of
    ShAAppl "HUniversal" [] _ -> (att0, HUniversal "")
    ShAAppl "HExistential" [] _ -> (att0, HExistential "")
    u -> fromShATermError "HQUANT" u

instance (ShATermConvertible sen, ShATermConvertible raw_sym, ShATermConvertible symb_items) =>
         ShATermConvertible (HFORMULA sen symb_items raw_sym) where
  toShATermAux att0 xv = case xv of
    Base_formula a b -> do
      (att1, a') <- toShATerm' att0 a
      (att2, b') <- toShATerm' att1 b
      return $ addATerm (ShAAppl "Base_formula" [a', b'] []) att2
    Negation a b -> do
      (att1, a') <- toShATerm' att0 a
      (att2, b') <- toShATerm' att1 b
      return $ addATerm (ShAAppl "Negation" [a', b'] []) att2
    Conjunction a b -> do
      (att1, a') <- toShATerm' att0 a
      (att2, b') <- toShATerm' att1 b
      return $ addATerm (ShAAppl "Conjunction" [a', b'] []) att2
    Disjunction a b -> do
      (att1, a') <- toShATerm' att0 a
      (att2, b') <- toShATerm' att1 b
      return $ addATerm (ShAAppl "Disjunction" [a', b'] []) att2
    Implication a b c -> do
      (att1, a') <- toShATerm' att0 a
      (att2, b') <- toShATerm' att1 b
      (att3, c') <- toShATerm' att2 c
      return $ addATerm (ShAAppl "Implication" [a', b', c'] []) att3
    Equivalence a b c -> do
      (att1, a') <- toShATerm' att0 a
      (att2, b') <- toShATerm' att1 b
      (att3, c') <- toShATerm' att2 c
      return $ addATerm (ShAAppl "Equivalence" [a', b', c'] []) att3
    Nominal s a b c -> do
      (att', s') <- toShATerm' att0 s
      (att1, a') <- toShATerm' att' a
      (att2, b') <- toShATerm' att1 b
      (att3, c') <- toShATerm' att2 c
      return $ addATerm (ShAAppl "Nominal" [s', a', b', c'] []) att3
    AtState a b c -> do
      (att1, a') <- toShATerm' att0 a
      (att2, b') <- toShATerm' att1 b
      (att3, c') <- toShATerm' att2 c
      return $ addATerm (ShAAppl "AtState" [a', b', c'] []) att3
    BoxFormula a b c -> do
      (att1, a') <- toShATerm' att0 a
      (att2, b') <- toShATerm' att1 b
      (att3, c') <- toShATerm' att2 c
      return $ addATerm (ShAAppl "BoxFormula" [a', b', c'] []) att3
    DiamondFormula a b c -> do
      (att1, a') <- toShATerm' att0 a
      (att2, b') <- toShATerm' att1 b
      (att3, c') <- toShATerm' att2 c
      return $ addATerm (ShAAppl "DiamondFormula" [a', b', c'] []) att3
    QuantVarsParse a b c d -> do
      (att1, a') <- toShATerm' att0 a
      (att2, b') <- toShATerm' att1 b
      (att3, c') <- toShATerm' att2 c
      (att4, d') <- toShATerm' att3 d
      return $ addATerm (ShAAppl "QuantVarsParse" [a', b', c',
                                                   d'] []) att4
    QuantVars a b c d -> do
      (att1, a') <- toShATerm' att0 a
      (att2, b') <- toShATerm' att1 b
      (att3, c') <- toShATerm' att2 c
      (att4, d') <- toShATerm' att3 d
      return $ addATerm (ShAAppl "QuantVars" [a', b', c',
                                                   d'] []) att4
    QuantNominals a b c d -> do
      (att1, a') <- toShATerm' att0 a
      (att2, b') <- toShATerm' att1 b
      (att3, c') <- toShATerm' att2 c
      (att4, d') <- toShATerm' att3 d
      return $ addATerm (ShAAppl "QuantNominals" [a', b', c',
                                                  d'] []) att4
  fromShATermAux ix att0 = case getShATerm ix att0 of
    ShAAppl "Base_formula" [a, b] _ ->
      case fromShATerm' a att0 of
      { (att1, a') ->
      case fromShATerm' b att1 of
      { (att2, b') ->
      (att2, Base_formula a' b') }}
    ShAAppl "Negation" [a, b] _ ->
      case fromShATerm' a att0 of
      { (att1, a') ->
      case fromShATerm' b att1 of
      { (att2, b') ->
      (att2, Negation a' b') }}
    ShAAppl "Conjunction" [a, b] _ ->
      case fromShATerm' a att0 of
      { (att1, a') ->
      case fromShATerm' b att1 of
      { (att2, b') ->
      (att2, Conjunction a' b') }}
    ShAAppl "Disjunction" [a, b] _ ->
      case fromShATerm' a att0 of
      { (att1, a') ->
      case fromShATerm' b att1 of
      { (att2, b') ->
      (att2, Disjunction a' b') }}
    ShAAppl "Implication" [a, b, c] _ ->
      case fromShATerm' a att0 of
      { (att1, a') ->
      case fromShATerm' b att1 of
      { (att2, b') ->
      case fromShATerm' c att2 of
      { (att3, c') ->
      (att3, Implication a' b' c') }}}
    ShAAppl "Equivalence" [a, b, c] _ ->
      case fromShATerm' a att0 of
      { (att1, a') ->
      case fromShATerm' b att1 of
      { (att2, b') ->
      case fromShATerm' c att2 of
      { (att3, c') ->
      (att3, Equivalence a' b' c') }}}
    ShAAppl "Nominal" [s, a, b, c] _ ->
      case fromShATerm' s att0 of
      { (att', s') -> 
      case fromShATerm' a att' of
      { (att1, a') ->
      case fromShATerm' b att1 of
      { (att2, b') ->
      case fromShATerm' c att2 of
      { (att3, c') ->
      (att3, Nominal s' a' b' c') }}}}
    ShAAppl "AtState" [a, b, c] _ ->
      case fromShATerm' a att0 of
      { (att1, a') ->
      case fromShATerm' b att1 of
      { (att2, b') ->
      case fromShATerm' c att2 of
      { (att3, c') ->
      (att3, AtState a' b' c') }}}
    ShAAppl "BoxFormula" [a, b, c] _ ->
      case fromShATerm' a att0 of
      { (att1, a') ->
      case fromShATerm' b att1 of
      { (att2, b') ->
      case fromShATerm' c att2 of
      { (att3, c') ->
      (att3, BoxFormula a' b' c') }}}
    ShAAppl "DiamondFormula" [a, b, c] _ ->
      case fromShATerm' a att0 of
      { (att1, a') ->
      case fromShATerm' b att1 of
      { (att2, b') ->
      case fromShATerm' c att2 of
      { (att3, c') ->
      (att3, DiamondFormula a' b' c') }}}
    ShAAppl "QuantVarsParse" [a, b, c, d] _ ->
      case fromShATerm' a att0 of
      { (att1, a') ->
      case fromShATerm' b att1 of
      { (att2, b') ->
      case fromShATerm' c att2 of
      { (att3, c') ->
      case fromShATerm' d att3 of
      { (att4, d') ->
      (att4, QuantVarsParse a' b' c' d') }}}}
    ShAAppl "QuantVars" [a, b, c, d] _ ->
      case fromShATerm' a att0 of
      { (att1, a') ->
      case fromShATerm' b att1 of
      { (att2, b') ->
      case fromShATerm' c att2 of
      { (att3, c') ->
      case fromShATerm' d att3 of
      { (att4, d') ->
      (att4, QuantVars a' b' c' d') }}}}
    ShAAppl "QuantNominals" [a, b, c, d] _ ->
      case fromShATerm' a att0 of
      { (att1, a') ->
      case fromShATerm' b att1 of
      { (att2, b') ->
      case fromShATerm' c att2 of
      { (att3, c') ->
      case fromShATerm' d att3 of
      { (att4, d') ->
      (att4, QuantNominals a' b' c' d') }}}}
    u -> fromShATermError "HFORMULA" u


sepByArbitrary :: Doc -> [Doc] -> Doc -- move to Common.Doc
sepByArbitrary d = fsep . prepPunctuate (d <> space)

forallH, existsH :: Doc
forallH = text "forallH"
existsH = text "existsH"

-- for H_BASIC_SPEC

instance Pretty NOM_ITEM where
  pretty = printNomItem

instance Pretty MOD_ITEM where
  pretty = printModItem

printNomItem :: NOM_ITEM -> Doc
printNomItem (Nom_item xs _) = 
  keyword (nomS ++ case xs of
     [_] -> ""
     _ -> "s") <+> ppWithCommas xs
    
printModItem :: MOD_ITEM -> Doc
printModItem (Mod_item xs i _) = undefined
  keyword (modS ++ case xs of
     [_] -> ""
     _ -> "s") <+> ppWithCommas xs <+> colon <+> pretty i

instance (ShATermConvertible sen, ShATermConvertible raw_sym, ShATermConvertible symb_items) 
         => ShATermConvertible (H_BASIC_ITEMS sen symb_items raw_sym) where
  toShATermAux att0 xv = case xv of
    Nom_decl a -> do
      (att1, a') <- toShATerm' att0 a
      return $ addATerm (ShAAppl "Nom_decl" [a'] []) att1
    Mod_decl a -> do
      (att1, a') <- toShATerm' att0 a
      return $ addATerm (ShAAppl "Mod_decl" [a'] []) att1
    Axiom_items a -> do
      (att1, a') <- toShATerm' att0 a
      return $ addATerm (ShAAppl "Axiom_items" [a'] []) att1
  fromShATermAux ix att0 = case getShATerm ix att0 of
    ShAAppl "Nom_decl" [a] _ ->
      case fromShATerm' a att0 of
      { (att1, a') ->
      (att1, Nom_decl a') }
    ShAAppl "Mod_decl" [a] _ ->
      case fromShATerm' a att0 of
      { (att1, a') ->
      (att1, Mod_decl a') }
    ShAAppl "Axiom_items" [a] _ ->
      case fromShATerm' a att0 of
      { (att1, a') ->
      (att1, Axiom_items a') }
    u -> fromShATermError "H_BASIC_ITEMS" u

instance ShATermConvertible MOD_ITEM where
  toShATermAux att0 xv = case xv of
    Mod_item a b c -> do
      (att1, a') <- toShATerm' att0 a
      (att2, b') <- toShATerm' att1 b
      (att3, c') <- toShATerm' att2 c
      return $ addATerm (ShAAppl "Mod_item" [a', b', c'] []) att3
  fromShATermAux ix att0 = case getShATerm ix att0 of
    ShAAppl "Mod_item" [a, b, c] _ ->
      case fromShATerm' a att0 of
      { (att1, a') ->
      case fromShATerm' b att1 of
      { (att2, b') ->
      case fromShATerm' c att2 of
      { (att3, c') ->
      (att3, Mod_item a' b' c') }}}
    u -> fromShATermError "MOD_ITEM" u

instance ShATermConvertible NOM_ITEM where
  toShATermAux att0 xv = case xv of
    Nom_item a b -> do
      (att1, a') <- toShATerm' att0 a
      (att2, b') <- toShATerm' att1 b
      return $ addATerm (ShAAppl "Nom_item" [a', b'] []) att2
  fromShATermAux ix att0 = case getShATerm ix att0 of
    ShAAppl "Nom_item" [a, b] _ ->
      case fromShATerm' a att0 of
      { (att1, a') ->
      case fromShATerm' b att1 of
      { (att2, b') ->
      (att2, Nom_item a' b') }}
    u -> fromShATermError "NOM_ITEM" u

instance (ShATermConvertible sen, ShATermConvertible symb_items, ShATermConvertible raw_sym) => 
          ShATermConvertible (H_BASIC_SPEC sen symb_items raw_sym) where
  toShATermAux att0 xv = case xv of
    Basic_spec a -> do
      (att1, a') <- toShATerm' att0 a
      return $ addATerm (ShAAppl "Basic_spec" [a'] []) att1
  fromShATermAux ix att0 = case getShATerm ix att0 of
    ShAAppl "Basic_spec" [a] _ ->
      case fromShATerm' a att0 of
      { (att1, a') ->
      (att1, Basic_spec a') }
    u -> fromShATermError "H_BASIC_SPEC" u

instance (GetRange sen, GetRange symb_items, GetRange raw_sym) => GetRange (H_BASIC_SPEC sen symb_items raw_sym)
 where 
  getRange _ = nullRange
  rangeSpan (Basic_spec bis) = joinRanges [rangeSpan bis]

instance (GetRange sen, GetRange symb_items, GetRange raw_sym) => GetRange (H_BASIC_ITEMS sen symb_items raw_sym) where
 getRange _ = nullRange
 rangeSpan (Nom_decl (Nom_item toks r)) = joinRanges [rangeSpan toks, rangeSpan r]
 rangeSpan (Mod_decl (Mod_item toks i r)) = joinRanges [rangeSpan toks, rangeSpan i, rangeSpan r]
 rangeSpan (Axiom_items fms) = joinRanges [rangeSpan fms]

instance (Pretty sen, Pretty raw_sym, Show symb_items) => Pretty (H_BASIC_ITEMS sen symb_items raw_sym) where
 pretty = printBasicItems

instance (Pretty sen, Pretty raw_sym, Show symb_items) => Pretty (H_BASIC_SPEC sen symb_items raw_sym) where
 pretty = printBasicSpec

printBasicSpec :: (Pretty sen, Pretty raw_sym, Show symb_items) =>  H_BASIC_SPEC sen symb_items raw_sym -> Doc
printBasicSpec (Basic_spec xs) = vcat $ map pretty xs

printBasicItems :: (Pretty sen, Pretty raw_sym, Show symb_items) => H_BASIC_ITEMS sen symb_items raw_sym -> Doc
printBasicItems (Axiom_items xs) = vcat $ map (addBullet . pretty) xs
printBasicItems (Nom_decl x) = pretty x
printBasicItems (Mod_decl x) = pretty x

instance Monoid (H_BASIC_SPEC sen symb_items raw_sym) where
    mempty = Basic_spec []
    mappend (Basic_spec l1) (Basic_spec l2) = Basic_spec $ l1 ++ l2

-- for H_symb_items

instance (Pretty sym, Pretty symb_items) => Pretty (H_SYMB_ITEMS sym symb_items)
 where pretty (BaseSymbItems s) = pretty s
       pretty (HSymbItems _ syms _) = pretty syms

instance (GetRange sym, GetRange symb_items) => GetRange (H_SYMB_ITEMS sym symb_items) where
    getRange (BaseSymbItems s) = getRange s
    getRange (HSymbItems _ syms _) = getRange syms
    rangeSpan (BaseSymbItems s) = rangeSpan s
    rangeSpan (HSymbItems _ syms _) = rangeSpan syms

instance ShATermConvertible H_SYMB_KIND where
  toShATermAux att0 xv = case xv of
    NomKind -> return $ addATerm (ShAAppl "NomKind" [] []) att0
    ModKind -> return $ addATerm (ShAAppl "MKind" [] []) att0
  fromShATermAux ix att0 = case getShATerm ix att0 of
    ShAAppl "NomKind" [] _ -> (att0, NomKind)
    ShAAppl "ModKind" [] _ -> (att0, ModKind)
    u -> fromShATermError "H_SYMB_KIND" u

instance (ShATermConvertible sym, ShATermConvertible symb_items) => ShATermConvertible (H_SYMB_ITEMS sym symb_items) where
  toShATermAux att0 xv = case xv of
    BaseSymbItems a -> do
      (att1, a') <- toShATerm' att0 a
      return $ addATerm (ShAAppl "BaseSymbItems" [a'] []) att1
    HSymbItems a b c -> do
      (att1, a') <- toShATerm' att0 a
      (att2, b') <- toShATerm' att1 b
      (att3, c') <- toShATerm' att2 c
      return $ addATerm (ShAAppl "HSymbItems" [a', b', c'] []) att3
  fromShATermAux ix att0 = case getShATerm ix att0 of
    ShAAppl "BaseSymbItems" [a] _ ->
      case fromShATerm' a att0 of
       (att1, a') ->
         (att1, BaseSymbItems a')
    ShAAppl "HSymbItems" [a, b, c] _ ->
      case fromShATerm' a att0 of
      { (att1, a') ->
      case fromShATerm' b att1 of
      { (att2, b') ->
      case fromShATerm' c att2 of
      { (att3, c') ->
      (att3, HSymbItems a' b' c') }}}
    u -> fromShATermError "H_SYMB_ITEMS" u


-- for HSymbol

instance Pretty sym => Pretty (HSymbol sym) where
 pretty (BaseSymb s) = pretty s
 pretty (HSymb i _) = pretty i

instance GetRange sym => GetRange (HSymbol sym) where
    getRange (BaseSymb s) = getRange s
    getRange (HSymb i _ ) = getRange i
    rangeSpan (BaseSymb s) = rangeSpan s
    rangeSpan (HSymb i _ ) = rangeSpan i

instance ShATermConvertible HKind where
  toShATermAux att0 xv = case xv of
    Nom -> return $ addATerm (ShAAppl "Nom" [] []) att0
    Mod a -> do
      (att1, a') <- toShATerm' att0 a
      return $ addATerm (ShAAppl "Mod" [a'] []) att1
  fromShATermAux ix att0 = case getShATerm ix att0 of
    ShAAppl "Nom" [] _ -> (att0, Nom)
    ShAAppl "Mod" [a] _ ->
      case fromShATerm' a att0 of
      { (att1, a') ->
      (att1, Mod a') }
    u -> fromShATermError "HKind" u

instance (ShATermConvertible sym) => ShATermConvertible (HSymbol sym) where
  toShATermAux att0 xv = case xv of
    BaseSymb a -> do
      (att1, a') <- toShATerm' att0 a
      return $ addATerm (ShAAppl "BaseSymb" [a'] []) att1
    HSymb a b -> do
      (att1, a') <- toShATerm' att0 a
      (att2, b') <- toShATerm' att1 b
      return $ addATerm (ShAAppl "HSymb" [a', b'] []) att2
  fromShATermAux ix att0 = case getShATerm ix att0 of
    ShAAppl "BaseSymb" [a] _ ->
      case fromShATerm' a att0 of
      { (att1, a') ->
      (att1, BaseSymb a') }
    ShAAppl "HSymb" [a, b] _ ->
      case fromShATerm' a att0 of
      { (att1, a') ->
      case fromShATerm' b att1 of
      { (att2, b') ->
      (att2, HSymb a' b') }}
    u -> fromShATermError "HSymbol" u

-- for HRawSymbol


instance (Pretty raw_sym, Pretty sym) => Pretty (HRawSymbol sym raw_sym) where
 pretty (BaseRawSymbol rs) = pretty rs
 pretty (ASymbol x) = pretty x
 pretty (AKindedSymb _ x) = pretty x

instance (GetRange sym, GetRange raw_sym) => GetRange (HRawSymbol sym raw_sym) where
    getRange (BaseRawSymbol rs) = getRange rs
    getRange (ASymbol x) = getRange x
    getRange (AKindedSymb _ x) = getRange x
    rangeSpan (BaseRawSymbol rs) = rangeSpan rs
    rangeSpan (ASymbol x) = rangeSpan x
    rangeSpan (AKindedSymb _ x) = rangeSpan x

instance ShATermConvertible GKind where
 toShATermAux att0 xv = case xv of
    Implicit -> return $ addATerm (ShAAppl "Implicit" [] []) att0
    HKindAsG a -> do
      (att1, a') <- toShATerm' att0 a
      return $ addATerm (ShAAppl "HKindAsG" [a'] []) att1
 fromShATermAux ix att0 = case getShATerm ix att0 of
    ShAAppl "Implicit" [] _ -> (att0, Implicit)
    ShAAppl "HKindAsG" [a] _ -> 
      case fromShATerm' a att0 of
      { (att1, a') ->
      (att1, HKindAsG a') }
    u -> fromShATermError "GKind" u

instance (ShATermConvertible raw_sym, ShATermConvertible sym) => ShATermConvertible (HRawSymbol sym raw_sym) where
  toShATermAux att0 xv = case xv of
    BaseRawSymbol a -> do
      (att1, a') <- toShATerm' att0 a
      return $ addATerm (ShAAppl "BaseRawSymbol" [a'] []) att1
    ASymbol a -> do
      (att1, a') <- toShATerm' att0 a
      return $ addATerm (ShAAppl "ASymbol" [a'] []) att1
    AKindedSymb a b -> do
      (att1, a') <- toShATerm' att0 a
      (att2, b') <- toShATerm' att1 b
      return $ addATerm (ShAAppl "AKindedSymb" [a', b'] []) att2
  fromShATermAux ix att0 = case getShATerm ix att0 of
    ShAAppl "BaseRawSymbol" [a] _ ->
      case fromShATerm' a att0 of
      { (att1, a') ->
      (att1, BaseRawSymbol a') }
    ShAAppl "ASymbol" [a] _ ->
      case fromShATerm' a att0 of
      { (att1, a') ->
      (att1, ASymbol a') }
    ShAAppl "AKindedSymb" [a, b] _ ->
      case fromShATerm' a att0 of
      { (att1, a') ->
      case fromShATerm' b att1 of
      { (att2, b') ->
      (att2, AKindedSymb a' b') }}
    u -> fromShATermError "HRawSymbol" u



