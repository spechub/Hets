{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./HPAR/AS_Basic_HPAR.der.hs
Description :  Abstract syntax for hybrid partial algebras
Copyright   :  (c) Mihai Codescu, IMAR, 2018
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  mscodescu@gmail.com
Stability   :  experimental
Portability :  portable

Definition of abstract syntax for hybrid partial algebras
-}

module HPAR.AS_Basic_HPAR
    ( HFORMULA (..)             -- datatype for HPAR Formulas
    , H_BASIC_ITEMS (..)         -- Items of a Basic Spec
    , H_BASIC_SPEC (..)          -- Basic Spec
    , H_SYMB_ITEMS (..)          -- List of symbols
    , H_SYMB_KIND (..)           -- symbol kinds
    , HQUANT (..)                -- quantifiers
    --, H_SYMB (..)                -- Symbols
    --, H_SYMB_MAP_ITEMS (..)      -- Symbol map
    --, SYMB_OR_MAP (..)         -- Symbol or symbol map
    , NOM_ITEM (..)              -- nominals
    , MOD_ITEM (..)              -- modalities
    --, isPrimForm
    ) where

import Common.Id as Id
import Common.Doc
import Common.DocUtils
import Common.Keywords
import Common.AS_Annotation as AS_Anno

import Data.Data
import qualified RigidCASL.AS_Rigid as PARBasic
import qualified CASL.AS_Basic_CASL as CASLBasic
import qualified CASL.ToDoc as CPrint
import RigidCASL.Print_AS ()

import Debug.Trace

-- DrIFT command
{-! global: GetRange !-}

-- | predicates = propositions
data NOM_ITEM = Nom_item [Id.Token] Id.Range
               deriving (Show, Typeable, Data)

-- | modalities with arities
data MOD_ITEM = Mod_item [Id.Token] Int Id.Range
               deriving (Show, Typeable, Data)

newtype H_BASIC_SPEC = Basic_spec [AS_Anno.Annoted H_BASIC_ITEMS]
                  deriving (Show, Typeable, Data)

instance Monoid H_BASIC_SPEC where
    mempty = Basic_spec []
    mappend (Basic_spec l1) (Basic_spec l2) = Basic_spec $ l1 ++ l2

data H_BASIC_ITEMS =
      PAR_decl (CASLBasic.BASIC_ITEMS () PARBasic.R_SIG_ITEM ())
    | Nom_decl NOM_ITEM
    | Mod_decl MOD_ITEM
    | Axiom_items [AS_Anno.Annoted HFORMULA]
    -- pos: dots
    deriving (Show, Typeable, Data)

-- | Datatype for hybrid propositional formulas
-- we need logical connectives between arbitrary hybrid formulas
-- so we need to cover these cases too
-- does this lead to parsing ambiguities? 
-- no: we can always have connectives at the global level
-- and only predications are from the basic level
-- at parsing time!
-- maybe in the case of quantifications for FOL we can have trouble
-- no: we use forallH and existsH
data HFORMULA =
    Base_formula CASLBasic.CASLFORMULA Id.Range
    -- base sentences
  | Negation HFORMULA Id.Range
   -- pos: not
  | Conjunction [HFORMULA] Id.Range
    -- pos: "/\"s
  | Disjunction [HFORMULA] Id.Range
    -- pos: "\/"s
  | Implication HFORMULA HFORMULA Id.Range
    -- pos: "=>"
  | Equivalence HFORMULA HFORMULA Id.Range
    -- pos: "<=>"
  | Nominal Bool Id.Token Id.Range -- the bool flag is true for nominal variables! 
   -- nominals as sentences
  | AtState Id.Token HFORMULA Id.Range
   -- at_i formulas
  | BoxFormula Id.Token HFORMULA Id.Range
   -- pos: "< >"
  | DiamondFormula Id.Token HFORMULA Id.Range
   -- pos: "[ ]"
  | QuantRigidVars HQUANT [CASLBasic.VAR_DECL] HFORMULA Id.Range
   -- pos: QUANTIFIER, semi colons, dot
  | QuantNominals HQUANT [Id.Token] HFORMULA Id.Range
    deriving (Show, Eq, Ord, Typeable, Data)

data HQUANT = HUniversal | HExistential
                  deriving (Show, Eq, Ord, Typeable, Data)

data H_SYMB_KIND = BaseSymbol CASLBasic.SYMB_KIND
                 | NomKind | ModKind 
     deriving (Show, Eq, Ord, Typeable, Data)

data H_SYMB_ITEMS = Symb_items H_SYMB_KIND [CASLBasic.SYMB] Id.Range
                  -- pos: SYMB_KIND, commas
                  deriving (Show, Eq, Ord, Typeable, Data)

instance Pretty HFORMULA where
    pretty = printFormula False
instance Pretty H_BASIC_SPEC where
    pretty = printBasicSpec
instance Pretty H_SYMB_ITEMS where
    pretty = printSymbItems
instance Pretty H_BASIC_ITEMS where
    pretty = printBasicItems
instance Pretty NOM_ITEM where
    pretty = printNomItem
instance Pretty MOD_ITEM where
    pretty = printModItem


sepByArbitrary :: Doc -> [Doc] -> Doc -- move to Common.Doc
sepByArbitrary d = fsep . prepPunctuate (d <> space)

forallH, existsH :: Doc
forallH = text "forallH"
existsH = text "existsH"

-- Pretty printing for formulas
printFormula :: Bool -> HFORMULA -> Doc
printFormula inJunct aFrm = 
  case aFrm of
   Base_formula pfrm _ -> CPrint.printFormula pfrm
   Nominal _ nom _ -> pretty nom  
   AtState nom frm _ -> let pf = prettyAt <+> pretty nom <+> colon <+> printFormula False frm 
                         in if inJunct then parens pf else pf
   BoxFormula md frm _ -> let pf = lbrack <+> pretty md <+> rbrack <+> printFormula False frm
                          in if inJunct then parens pf else pf
   DiamondFormula md frm _ -> let pf =  text "<" <+> pretty md <+> text ">" <+> printFormula False frm
                              in if inJunct then parens pf else pf
   Negation frm _ -> notDoc <+> printFormula inJunct frm
   Conjunction xs _ -> sepByArbitrary andDoc $ 
                        map (printFormula True) xs
   Disjunction xs _ -> sepByArbitrary orDoc $ 
                         map (printFormula True) xs
   Implication x y _ -> let 
                           ls = if leftParens x then parens (printFormula False x) else printFormula False x
                           rs = if rightParens y then parens (printFormula False y) else printFormula False y 
                        in if inJunct then ls <+> implies <+> rs else parens (ls <+> implies <+> rs)
   Equivalence x y _ -> let 
                           ls = if leftParens x then parens (printFormula False x) else printFormula False x
                           rs = if rightParens y then parens (printFormula False y) else printFormula False y 
                        in if inJunct then ls <+> equiv <+> rs else parens (ls <+> implies <+> rs)
   QuantRigidVars q vdecls frm _ -> let pf = printQuant q <+> CPrint.printVarDecls vdecls <+> bullet <+> printFormula False frm
                                    in if inJunct then parens pf else pf
   QuantNominals q noms frm _ -> let pf = printQuant q <+> keyword nomS <+> sepByCommas (map pretty noms) <+> bullet <+> printFormula False frm
                                 in if inJunct then parens pf else pf

leftParens :: HFORMULA -> Bool
leftParens sen = 
 case sen of
  AtState _ _ _ -> True
  BoxFormula _ _ _ -> True
  DiamondFormula _ _ _ -> True
  Implication _ _ _ -> True
  Equivalence _ _ _ -> True
  QuantRigidVars _ _ _ _ -> True
  QuantNominals _ _ _ _ -> True
  _ -> False

rightParens :: HFORMULA -> Bool
rightParens sen = 
 case sen of
  Implication _ _ _ -> True
  QuantRigidVars _ _ _ _ -> True
  QuantNominals _ _ _ _ -> True
  _ -> False

printQuant :: HQUANT -> Doc
printQuant HUniversal = forallH
printQuant HExistential = existsH

nomS, modS :: String
nomS = "nominal"
modS = "modality"

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
  

printBasicSpec :: H_BASIC_SPEC -> Doc
printBasicSpec (Basic_spec xs) = trace ("displaying: " ++ show xs) $ vcat $ map pretty xs

printBasicItems :: H_BASIC_ITEMS -> Doc
printBasicItems (Axiom_items xs) = vcat $ map (addBullet . pretty) xs
printBasicItems (PAR_decl x) = pretty x
printBasicItems (Nom_decl x) = pretty x
printBasicItems (Mod_decl x) = pretty x


printSymbItems :: H_SYMB_ITEMS -> Doc
printSymbItems (Symb_items _k xs _) = 
  fsep $ map pretty xs --TODO: improve


-- Generated by DrIFT, look but don't touch!

instance GetRange NOM_ITEM where
  getRange = const nullRange
  rangeSpan x = case x of
    Nom_item a b -> joinRanges [rangeSpan a, rangeSpan b]

instance GetRange MOD_ITEM where
  getRange = const nullRange
  rangeSpan x = case x of
    Mod_item a b c -> joinRanges [rangeSpan a, rangeSpan b,
                                  rangeSpan c]

instance GetRange H_BASIC_SPEC where
  getRange = const nullRange
  rangeSpan x = case x of
    Basic_spec a -> joinRanges [rangeSpan a]

instance GetRange H_BASIC_ITEMS where
  getRange = const nullRange
  rangeSpan x = case x of
    PAR_decl a -> joinRanges [rangeSpan a]
    Nom_decl a -> joinRanges [rangeSpan a]
    Mod_decl a -> joinRanges [rangeSpan a]
    Axiom_items a -> joinRanges [rangeSpan a]

instance GetRange HFORMULA where
  getRange = const nullRange
  rangeSpan x = case x of
    Base_formula a b -> joinRanges [rangeSpan a, rangeSpan b]
    Negation a b -> joinRanges [rangeSpan a, rangeSpan b]
    Conjunction a b -> joinRanges [rangeSpan a, rangeSpan b]
    Disjunction a b -> joinRanges [rangeSpan a, rangeSpan b]
    Implication a b c -> joinRanges [rangeSpan a, rangeSpan b,
                                     rangeSpan c]
    Equivalence a b c -> joinRanges [rangeSpan a, rangeSpan b,
                                     rangeSpan c]
    Nominal a b c -> joinRanges [rangeSpan a, rangeSpan b, rangeSpan c]
    AtState a b c -> joinRanges [rangeSpan a, rangeSpan b, rangeSpan c]
    BoxFormula a b c -> joinRanges [rangeSpan a, rangeSpan b,
                                    rangeSpan c]
    DiamondFormula a b c -> joinRanges [rangeSpan a, rangeSpan b,
                                        rangeSpan c]
    QuantRigidVars a b c d -> joinRanges [rangeSpan a, rangeSpan b,
                                          rangeSpan c, rangeSpan d]
    QuantNominals a b c d -> joinRanges [rangeSpan a, rangeSpan b,
                                         rangeSpan c, rangeSpan d]

instance GetRange HQUANT where
  getRange = const nullRange
  rangeSpan x = case x of
    HUniversal -> []
    HExistential -> []

instance GetRange H_SYMB_KIND where
  getRange = const nullRange
  rangeSpan x = case x of
    BaseSymbol a -> joinRanges [rangeSpan a]
    NomKind -> []
    ModKind -> []

instance GetRange H_SYMB_ITEMS where
  getRange = const nullRange
  rangeSpan x = case x of
    Symb_items a b c -> joinRanges [rangeSpan a, rangeSpan b,
                                    rangeSpan c]
