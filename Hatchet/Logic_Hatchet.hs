{-| 
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Sonja Groening, Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  non-portable(Logic)

Here is the place where the class Logic is instantiated for Hatchet.
   Also the instances for Syntax an Category.

   todo:
     - writing real functions

-}

module Hatchet.Logic_Hatchet (Hatchet(..)) where

import Data.Dynamic            
import Common.DynamicUtils 

import Common.Result                     (Result (..))
import Common.PrettyPrint
import Common.Lib.Pretty
import Common.AS_Annotation

import Hatchet.ATC_Hatchet      -- generated ATerm conversions
import Hatchet.PrintModuleInfo
import Hatchet.HatParser (HsDecls(..), hatParser)
import Hatchet.HatAna
import Haskell.Hatchet.MultiModuleBasics (ModuleInfo,
                                          emptyModuleInfo,
                                          joinModuleInfo)
import Haskell.Hatchet.AnnotatedHsSyn    (AHsDecl)
import Haskell.Hatchet.HsSyn    (HsDecl)

import Logic.Logic             

moduleInfoTc, hsDeclTc, aHsDeclTc :: TyCon
moduleInfoTc   = mkTyCon "Haskell.Hatchet.MultiModuleBasics.ModuleInfo"
hsDeclTc       = mkTyCon "Hatchet.HatParser.HsDecls"
aHsDeclTc      = mkTyCon "Haskell.Hatchet.AnnotatedHsSyn.AHsDecl"

instance Typeable ModuleInfo where
    typeOf _ = mkTyConApp moduleInfoTc []
instance Typeable HsDecls where
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

data Hatchet = Hatchet deriving (Show)
instance Language Hatchet where
 description _ = 
  "Haskell - a purely functional programming language, \ 
  \featuring static typing, higher-order functions, polymorphism, \ 
  \type classes and monadic effects. \ 
  \See http://www.haskell.org. This version is based on Hatchet, \ 
  \see http://www.cs.mu.oz.au/~bjpop/hatchet.html"

type Sign = ModuleInfo 
type Morphism = ()

instance Category Hatchet Sign Morphism where
  dom Hatchet _ = empty_signature Hatchet

-- abstract syntax, parsing (and printing)

type SYMB_ITEMS = ()
type SYMB_MAP_ITEMS = ()

instance Syntax Hatchet HsDecls
                SYMB_ITEMS SYMB_MAP_ITEMS
      where 
         parse_basic_spec Hatchet = Just hatParser
         parse_symb_items Hatchet = Nothing
         parse_symb_map_items Hatchet = Nothing

type Hatchet_Sublogics = ()

type Sentence = AHsDecl
instance Ord AHsDecl where
  compare _x _y = error "Hatchet.Logic_Hatchet: compare for AHsDecl"

type Symbol = ()
type RawSymbol = ()

instance Sentences Hatchet Sentence () Sign Morphism Symbol where
    map_sen Hatchet _m s = return s
    print_named Hatchet ga (NamedSen lab _ sen) = printText0 ga sen <>
        if null lab then empty 
        else space <> text "{-" <+> text lab <+> text "-}" 
    provers Hatchet = [] 
    cons_checkers Hatchet = []


instance StaticAnalysis Hatchet HsDecls
               Sentence () 
               SYMB_ITEMS SYMB_MAP_ITEMS
               Sign 
               Morphism 
               Symbol RawSymbol 


  where
    empty_signature Hatchet 
       = emptyModuleInfo
    signature_union Hatchet sig1 sig2 = return (joinModuleInfo sig1 sig2)
    inclusion Hatchet _ _ = return ()
    basic_analysis Hatchet = Just(basicAnalysis)
      where basicAnalysis (b@(HsDecls basicSpec), sig, _) =                 
             let (modInfo, sens) = hatAna basicSpec sig
             in Result [] $ Just (b, diffModInfo modInfo sig, 
                                  modInfo, sens)
    is_subsig Hatchet s1 s2 = joinModuleInfo s1 s2 == s2

instance Logic Hatchet Hatchet_Sublogics
               HsDecls Sentence SYMB_ITEMS SYMB_MAP_ITEMS
               Sign 
               Morphism
               Symbol RawSymbol ()
   where data_logic Hatchet = Nothing
