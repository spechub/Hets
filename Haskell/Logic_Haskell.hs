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

module Haskell.Logic_Haskell (Haskell(..), HaskellMorphism) where

import Data.Dynamic            
import Common.DynamicUtils 

import Common.Result                     (Result (..))
import Common.PrettyPrint
import Common.Lib.Pretty
import Common.AS_Annotation
import Common.ATerm.Conversion

-- import Haskell.ATC_Haskell      -- generated ATerm conversions
import Haskell.HatParser                 (HsDecls,
                                          hatParser)
import Haskell.HatAna

import Logic.Logic             

instance ATermConvertible HsDecls
instance ATermConvertible Sign
instance ATermConvertible (HsDeclI PNT)

hsDeclsTc :: TyCon
hsDeclsTc = mkTyCon "Haskell.HatParser.HsDecls"

instance Typeable HsDecls where
    typeOf _ = mkTyConApp hsDeclsTc []

tyconSign :: TyCon
tyconSign = mkTyCon "Haskell.HatAna.Sign"

instance Typeable Sign where
  typeOf _ = mkTyConApp tyconSign []

tyconPNT :: TyCon
tyconPNT = mkTyCon "Haskell.HatAna.PNT"

instance Typeable PNT where
  typeOf _ = mkTyConApp tyconPNT []

hsDeclItc :: TyCon
hsDeclItc = mkTyCon "Haskell.HatAna.HsDeclI"

instance Typeable i => Typeable (HsDeclI i) where 
  typeOf s = mkTyConApp hsDeclItc [typeOf $ (undefined :: HsDeclI a -> a) s]

instance PrintLaTeX HsDecls where
  printLatex0 = printText0

instance PrintLaTeX Sign where
     printLatex0 = printText0

instance PrintLaTeX (HsDeclI PNT) where
     printLatex0 = printText0

-- a dummy datatype for the LogicGraph and for identifying the right
-- instances

data Haskell = Haskell deriving (Show)
instance Language Haskell where
 description _ = 
  "Haskell - a purely functional programming language,\ 
  \ featuring static typing, higher-order functions, polymorphism,\
  \ type classes and monadic effects.\ 
  \ See http://www.haskell.org"

type HaskellMorphism = (Sign,Sign)

instance Category Haskell Sign HaskellMorphism where
  dom Haskell = fst
  cod Haskell = snd
  ide Haskell sig = (sig,sig)
  comp Haskell (sig1,_) (_,sig3) = Just (sig1,sig3)

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

type Symbol = ()
type RawSymbol = ()

instance Sentences Haskell (HsDeclI PNT) () Sign HaskellMorphism Symbol where
    map_sen Haskell _m s = return s
    print_named Haskell ga (NamedSen lab sen) = printText0 ga sen <>
	if null lab then empty 
	else space <> text "{-" <+> text lab <+> text "-}" 
    provers Haskell = [] 
    cons_checkers Haskell = []

instance PrettyPrint HaskellMorphism where
  printText0 ga (sig1,sig2) =
    printText0 ga sig1 $$ ptext "->" $$ printText0 ga sig1

instance PrintLaTeX HaskellMorphism where
  printLatex0 ga (sig1,sig2) =
    printLatex0 ga sig1 $$ ptext "\\rightarrow" $$ printLatex0 ga sig1

instance StaticAnalysis Haskell HsDecls
               (HsDeclI PNT) () 
               SYMB_ITEMS SYMB_MAP_ITEMS
               Sign 
               HaskellMorphism 
               Symbol RawSymbol where
    basic_analysis Haskell = Just hatAna 
    empty_signature Haskell = emptySign
    signature_union Haskell s = return . addSign s
    final_union Haskell = signature_union Haskell
    inclusion Haskell sig1 sig2 = return (sig1,sig2)
    is_subsig Haskell = isSubSign

instance Logic Haskell Haskell_Sublogics
               HsDecls (HsDeclI PNT) SYMB_ITEMS SYMB_MAP_ITEMS
               Sign 
               HaskellMorphism
               Symbol RawSymbol ()
