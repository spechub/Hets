{-| 
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Sonja Groening, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  non-portable(Logic)

   Here is the place where the class Logic is instantiated for Haskell.
   Also the instances for Syntax an Category.

   todo:
     - writing real functions

-}

module Haskell.Logic_Haskell (Haskell(..)) where

import Data.Dynamic            

import Common.Result                     (Result (..))
import Common.PrettyPrint
import Common.Lib.Pretty
import Common.AS_Annotation

import Haskell.ATC_Haskell      -- generated ATerm conversions
import Haskell.PrintModuleInfo
import Haskell.HatParser                 (HsDecls,
                                          hatParser)
import Haskell.HatAna
import Haskell.Hatchet.MultiModuleBasics (ModuleInfo,
                                          emptyModuleInfo,
					  joinModuleInfo)
import Haskell.Hatchet.AnnotatedHsSyn    (AHsDecl)
import Haskell.Hatchet.HsSyn    (HsDecl)

import Logic.Logic             

moduleInfoTc, hsDeclTc, aHsDeclTc :: TyCon
moduleInfoTc   = mkTyCon "Haskell.Hatchet.MultiModuleBasics.ModuleInfo"
hsDeclTc       = mkTyCon "Haskell.Hatchet.HsSyn.HsDecl"
aHsDeclTc      = mkTyCon "Haskell.Hatchet.AnnotatedHsSyn.AHsDecl"

instance Typeable ModuleInfo where
    typeOf _ = mkTyConApp moduleInfoTc []
instance Typeable HsDecl where
    typeOf _ = mkTyConApp hsDeclTc []
instance Typeable AHsDecl where
    typeOf _ = mkTyConApp aHsDeclTc []

instance PrintLaTeX ModuleInfo where
  printLatex0 = printText0
instance PrintLaTeX HsDecls where
  printLatex0 = printText0
instance PrintLaTeX AHsDecl where
  printLatex0 = printText0

-- a dummy datatype for the LogicGraph and for identifying the right
-- instances

data Haskell = Haskell deriving (Show)
instance Language Haskell where
 description _ = 
  "Haskell - a purely functional programming language,\
  \featuring static typing, higher-order functions, polymorphism, type classes and monadic effects\
  \See http://www.haskell.org"

type Sign = ModuleInfo 
type Morphism = ()

instance Category Haskell Sign Morphism where
  dom Haskell _ = empty_signature Haskell

-- abstract syntax, parsing (and printing)

type SYMB_ITEMS = ()
type SYMB_MAP_ITEMS = ()

instance Syntax Haskell HsDecls
		SYMB_ITEMS SYMB_MAP_ITEMS
      where 
         parse_basic_spec Haskell = Just hatParser
	 parse_symb_items Haskell = Nothing
	 parse_symb_map_items Haskell = Nothing

type Haskell_Sublogics = ()

type Sentence = AHsDecl
instance Ord AHsDecl where
  compare _x _y = error "Haskell.Logic_Haskell: compare for AHsDecl"

type Symbol = ()
type RawSymbol = ()

instance Sentences Haskell Sentence () Sign Morphism Symbol where
    map_sen Haskell _m s = return s
    print_named Haskell ga (NamedSen lab sen) = printText0 ga sen <>
	if null lab then empty 
	else space <> text "{-" <+> text lab <+> text "-}" 
    provers Haskell = [] 
    cons_checkers Haskell = []


instance StaticAnalysis Haskell HsDecls
               Sentence () 
               SYMB_ITEMS SYMB_MAP_ITEMS
               Sign 
               Morphism 
               Symbol RawSymbol 


  where
    empty_signature Haskell 
       = emptyModuleInfo
    signature_union Haskell sig1 sig2 = return (joinModuleInfo sig1 sig2)
    inclusion Haskell _ _ = return ()
    basic_analysis Haskell = Just(basicAnalysis)
      where basicAnalysis (basicSpec, sig, _) = 	            
             let (modInfo, sens) = hatAna basicSpec sig
             in Result [] $ Just (basicSpec, diffModInfo modInfo sig, 
				  modInfo, sens)

instance Logic Haskell Haskell_Sublogics
               HsDecls Sentence SYMB_ITEMS SYMB_MAP_ITEMS
               Sign 
               Morphism
               Symbol RawSymbol ()
   where data_logic Haskell = Nothing
