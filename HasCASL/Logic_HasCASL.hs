-- {-# OPTIONS -fno-warn-missing-methods #-}
{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003
Licence     :  All rights reserved.

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

   Here is the place where the class Logic is instantiated for HasCASL.
   Also the instances for Syntax an Category.

   todo:
     - writing real functions
-}

module HasCASL.Logic_HasCASL where

import HasCASL.As
import HasCASL.Le
import HasCASL.PrintLe
import HasCASL.AsToLe
import HasCASL.Symbol
import HasCASL.ParseItem
import Common.Result
import Logic.ParsecInterface
import Logic.Logic
import Common.AnnoState(emptyAnnos)
import Data.Dynamic
import Common.Lib.State
import HasCASL.Morphism
import Common.PrettyPrint

type HasCASL_Sublogics = ()

-- a dummy datatype for the LogicGraph and for identifying the right
-- instances
data HasCASL = HasCASL deriving (Show)
instance Language HasCASL -- default definition is okay

basicSpecTc, envTc, termTc, morphismTc, symbolTc, rawSymbolTc, symbItemsTc
	       , symbMapItemsTc  :: TyCon
basicSpecTc      = mkTyCon "HasCASL.BasicSpec"
envTc            = mkTyCon "HasCASL.Env"
termTc           = mkTyCon "HasCASL.Term"
morphismTc       = mkTyCon "HasCASL.Morphism"
symbolTc         = mkTyCon "HasCASL.Symbol"
rawSymbolTc      = mkTyCon "HasCASL.RawSymbol"
symbItemsTc      = mkTyCon "HasCASL.SymbItems"
symbMapItemsTc   = mkTyCon "HasCASL.SymbMapItems"

instance Typeable BasicSpec where
    typeOf _ = mkAppTy basicSpecTc []
instance Typeable Env where
    typeOf _ = mkAppTy envTc []
instance Typeable Term where
    typeOf _ = mkAppTy termTc []
instance Typeable Morphism where
  typeOf _ = mkAppTy morphismTc []
instance Typeable Symbol where
  typeOf _ = mkAppTy symbolTc []
instance Typeable RawSymbol where
  typeOf _ = mkAppTy rawSymbolTc []
instance Typeable SymbItems where
  typeOf _ = mkAppTy symbItemsTc []
instance Typeable SymbMapItems where
  typeOf _ = mkAppTy symbMapItemsTc []

-- abstract syntax, parsing (and printing)

instance Syntax HasCASL BasicSpec
		SymbItems SymbMapItems
      where 
         parse_basic_spec HasCASL = Just(toParseFun basicSpec emptyAnnos)
	 parse_symb_items HasCASL = Just(toParseFun symbItems emptyAnnos)
	 parse_symb_map_items HasCASL = Just(toParseFun symbMapItems 
					     emptyAnnos)

instance Category HasCASL Env Morphism where 
    ide HasCASL e = ideMor e
    comp HasCASL m1 m2 = Just $ compMor m1 m2
    dom HasCASL m = msource m
    cod HasCASL m = mtarget m
    legal_obj HasCASL e = legalEnv e
    legal_mor HasCASL m = legalMor m


instance Sentences HasCASL Term () Env Morphism Symbol

instance StaticAnalysis HasCASL BasicSpec Term ()
               SymbItems SymbMapItems
               Env 
               Morphism 
               Symbol RawSymbol where
    basic_analysis HasCASL = Just ( \ (b, e, ga) ->
		let (nb, ne) = runState (anaBasicSpec ga b) e 
		    in Result (reverse (envDiags ne)) $ 
				    Just (nb, ne, ne, sentences ne)) 
  
    signature_union HasCASL = merge
    empty_signature HasCASL = initialEnv
    induced_from_to_morphism HasCASL _ e1 e2 = return $ mkMorphism e1 e2
    induced_from_morphism HasCASL _ e = return $ ideMor e
    morphism_union HasCASL m1 m2 = morphismUnion m1 m2

    cogenerated_sign HasCASL _ e = return $ ideMor e

    stat_symb_map_items HasCASL = statSymbMapItems
    stat_symb_items HasCASL = statSymbItems
    symbol_to_raw HasCASL = symbolToRaw
    id_to_raw HasCASL = idToRaw
    matches HasCASL = matchSymb
    sym_name HasCASL = symName

instance Logic HasCASL HasCASL_Sublogics
               BasicSpec Term SymbItems SymbMapItems
               Env 
               Morphism
               Symbol RawSymbol () 

