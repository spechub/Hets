{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances, DeriveDataTypeable #-}
{- |
Module      :  ./GenHyb/GenTypes
Description :  Instance of class Logic for rigid CASL


Instance of class Logic for rigid logic.
-}

module GenHyb.GenTypes where

import qualified Data.Set as Set
import qualified Data.Map as Map
import Common.Id as Id
import Data.Data
import Common.AS_Annotation as AS_Anno
import Common.Doc
import Common.DocUtils
import qualified CASL.AS_Basic_CASL as CBasic


-- | generic hybrid signatures
data HSign sig = HSign {
                  baseSig :: sig,
                  noms :: Set.Set Id,
                  mods :: Map.Map Id Int}
  deriving (Show, Eq, Ord, Typeable, Data)

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

-- | generic hybrid signature morphisms
data HMorphism sig mor = HMorphism
  { source :: HSign sig
  , target :: HSign sig
  , baseMor :: mor
  , nomMap :: Map.Map Id Id
  , modMap :: Map.Map Id Id
  } deriving (Show, Eq, Ord, Typeable, Data)

instance (Pretty sig, Pretty mor) => Pretty (HMorphism sig mor) where
    pretty = printMorphism

printMorphism :: (Pretty sig, Pretty mor) => HMorphism sig mor -> Doc
printMorphism hmor = error "printmorphism nyi"

-- | generic hybrid formulas

data HFORMULA sen symb_items raw_sym =
    Base_formula sen Id.Range -- add a Maybe String to handle multiple layers of hybridization
    -- base sentences
  | Negation (HFORMULA sen symb_items raw_sym) Id.Range
   -- pos: not
  | Conjunction [HFORMULA sen symb_items raw_sym] Id.Range
    -- pos: "/\"s
  | Disjunction [HFORMULA sen symb_items raw_sym] Id.Range
    -- pos: "\/"s
  | Implication (HFORMULA sen symb_items raw_sym) (HFORMULA sen symb_items raw_sym) Id.Range
    -- pos: "=>"
  | Equivalence (HFORMULA sen symb_items raw_sym) (HFORMULA sen symb_items raw_sym) Id.Range
    -- pos: "<=>"
  | Nominal Bool Id.Token Id.Range -- the bool flag is true for nominal variables! 
   -- nominals as sentences
  | AtState Id.Token (HFORMULA sen symb_items raw_sym) Id.Range
   -- at_i formulas
  | BoxFormula Id.Token (HFORMULA sen symb_items raw_sym) Id.Range
   -- pos: "< >"
  | DiamondFormula Id.Token (HFORMULA sen symb_items raw_sym) Id.Range
   -- pos: "[ ]"
  | QuantVarsParse HQUANT [symb_items] (HFORMULA sen symb_items raw_sym) Id.Range 
   -- pos: QUANTIFIER, semi colons, dot
  | QuantVars HQUANT [raw_sym] (HFORMULA sen symb_items raw_sym) Id.Range 
  | QuantNominals HQUANT [Id.Token] (HFORMULA sen symb_items raw_sym) Id.Range
    deriving (Show, Eq, Ord, Typeable, Data)

instance (Pretty sen, Pretty raw_sym, Show symb_items) => Pretty (HFORMULA sen symb_items raw_sym)
 where
   pretty = printFormula

printFormula :: (Pretty sen, Pretty raw_sym, Show symb_items) => HFORMULA sen symb_items raw_sym -> Doc
printFormula aFrm = case aFrm of
   Base_formula pfrm _ -> pretty pfrm
   Nominal _ nom _ -> pretty nom  
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
   QuantVars q rsyms frm _ -> printQuant q <+> pretty rsyms <+> bullet <+> printFormula frm
   QuantNominals q nomVars frm _ -> printQuant q <+> keyword nomS <+> sepByCommas (map pretty nomVars) <+> bullet <+> printFormula frm

printQuant :: HQUANT -> Doc
printQuant HUniversal = forallH
printQuant HExistential = existsH

nomS, modS :: String
nomS = "nominal"
modS = "modality"

sepByArbitrary :: Doc -> [Doc] -> Doc -- move to Common.Doc
sepByArbitrary d = fsep . prepPunctuate (d <> space)

forallH, existsH :: Doc
forallH = text "forallH"
existsH = text "existsH"


data HQUANT = HUniversal | HExistential -- the quantifier must have a logic identifier, and if it's missing it defaults to the current logic
                  deriving (Show, Eq, Ord, Typeable, Data)

-- | generic hybrid basic spec
data NOM_ITEM = Nom_item [Token] Range
               deriving (Show, Typeable, Data)

data MOD_ITEM = Mod_item [Token] Int Range
               deriving (Show, Typeable, Data)

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

data H_BASIC_ITEMS sen symb_items raw_sym =
      Nom_decl NOM_ITEM
    | Mod_decl MOD_ITEM
    | Axiom_items [AS_Anno.Annoted (HFORMULA sen symb_items raw_sym)]
  deriving (Show, Typeable, Data)

newtype H_BASIC_SPEC sen symb_items raw_sym = Basic_spec [AS_Anno.Annoted (H_BASIC_ITEMS sen symb_items raw_sym)]
                  deriving (Show, Typeable, Data)

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


-- | generic symb_items

data H_SYMB_KIND = NomKind | ModKind 
     deriving (Show, Eq, Ord, Typeable, Data)

data H_SYMB_ITEMS sym symb_items =  
                         BaseSymbItems symb_items
                       | HSymbItems H_SYMB_KIND [HSymbol sym] Id.Range
                  deriving (Show, Eq, Ord, Typeable, Data)

instance (Pretty sym, Pretty symb_items) => Pretty (H_SYMB_ITEMS sym symb_items)
 where pretty (BaseSymbItems s) = pretty s
       pretty (HSymbItems _ syms _) = pretty syms

-- | generic hybrid symbols

data HSymbol sym =  BaseSymb sym
                  | HSymb Id HKind
   deriving (Show, Eq, Ord, Typeable, Data)

data HKind = Mod Int | Nom
   deriving (Show, Eq, Ord, Typeable, Data)

instance Pretty sym => Pretty (HSymbol sym) where
 pretty (BaseSymb s) = pretty s
 pretty (HSymb i _) = pretty i

instance GetRange sym => GetRange (HSymbol sym) where
    getRange (BaseSymb s) = getRange s
    getRange (HSymb i _ ) = getRange i
    rangeSpan (BaseSymb s) = rangeSpan s
    rangeSpan (HSymb i _ ) = rangeSpan i
 
-- | generic raw symbols

data HRawSymbol sym raw_sym =
                         BaseRawSymbol raw_sym -- in the next two alternatives, only modalities and nominals 
                         | ASymbol (HSymbol sym) 
                         | AKindedSymb GKind Id
                 deriving (Show, Eq, Ord, Typeable, Data)

data GKind = Implicit -- it seems to me we never need this, we can rely on base logic for this! 
           | HKindAsG HKind
  deriving (Show, Eq, Ord, Typeable, Data)

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


