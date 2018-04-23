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
    , NOM_ITEM (..)              -- nominals
    , MOD_ITEM (..)              -- modalities
    ) where

import Common.Id as Id
import Common.Doc
import Common.DocUtils
import Common.AS_Annotation as AS_Anno

import Data.Data
import qualified RigidCASL.AS_Rigid as PARBasic
import qualified CASL.AS_Basic_CASL as CASLBasic
import qualified CASL.ToDoc as CPrint
import RigidCASL.Print_AS ()

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

{- All about pretty printing
we chose the easy way here :) -}
instance Pretty HFORMULA where
    pretty = printFormula
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
printFormula :: HFORMULA -> Doc
printFormula aFrm = 
  case aFrm of
   Base_formula pfrm _ -> CPrint.printFormula pfrm 
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
   QuantRigidVars q vdecls frm _ -> printQuant q <+> CPrint.printVarDecls vdecls <+> bullet <+> printFormula frm
   QuantNominals q noms frm _ -> printQuant q <+> keyword nomS <+> sepByCommas (map pretty noms) <+> bullet <+> printFormula frm

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
printBasicSpec (Basic_spec xs) = vcat $ map pretty xs

printBasicItems :: H_BASIC_ITEMS -> Doc
printBasicItems (Axiom_items xs) = vcat $ map (addBullet . pretty) xs
printBasicItems (PAR_decl x) = pretty x
printBasicItems (Nom_decl x) = pretty x
printBasicItems (Mod_decl x) = pretty x


printSymbItems :: H_SYMB_ITEMS -> Doc
printSymbItems (Symb_items _k xs _) = 
  fsep $ map pretty xs --TODO: improve

