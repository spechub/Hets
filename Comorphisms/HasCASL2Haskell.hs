{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Uni Bremen 2004
Licence     :  All rights reserved.

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

   
   The embedding comorphism from CASL to HasCASL.

-}

module Comorphisms.HasCASL2Haskell where

import Logic.Logic
import Logic.Comorphism
import Common.Id
import qualified Common.Lib.Map as Map
import Common.Lib.Set as Set
import Common.Result
import Common.AS_Annotation
import Common.GlobalAnnotations
import Data.Dynamic

import HasCASL.Logic_HasCASL
import HasCASL.As
import HasCASL.Le
import HasCASL.Symbol
import HasCASL.Morphism

import ToHaskell.TranslateAna
import Haskell.Logic_Haskell
import Haskell.HatParser
import Haskell.Hatchet.MultiModuleBasics 
import Haskell.Hatchet.AnnotatedHsSyn


-- | The identity of the comorphism
data HasCASL2Haskell = HasCASL2Haskell deriving Show

instance Language HasCASL2Haskell -- default definition is okay

tycon_HasCASL2Haskell :: TyCon
tycon_HasCASL2Haskell = mkTyCon "Comorphisms.HasCASL2Haskell.HasCASL2Haskell"

instance Typeable HasCASL2Haskell where
  typeOf _ = mkAppTy tycon_HasCASL2Haskell []

instance Comorphism HasCASL2Haskell
               HasCASL ()
               BasicSpec Term SymbItems SymbMapItems
               Env
               Morphism
               Symbol RawSymbol ()
               Haskell ()
               HsDecls AHsDecl () ()
               ModuleInfo
               ()
               () () () where
    sourceLogic _ = HasCASL
    sourceSublogic _ = ()
    targetLogic _ = Haskell
    targetSublogic _ = ()
    map_sign _ = mapSignature
    --map_morphism _ morphism1 -> Maybe morphism2
    --map_sentence _ sign1 -> sentence1 -> Maybe sentence2
    --map_symbol :: cid -> symbol1 -> Set symbol2

mapSignature :: Env -> Maybe(ModuleInfo,[Named AHsDecl]) 
mapSignature sign = do 
     anaFun <- basic_analysis Haskell
     let Result ds mt = anaFun (translateAna sign,  
				empty_signature Haskell,
				emptyGlobalAnnos)
     (_, _, r, hs) <- mt
     return (r, map (emptyName . sentence) hs) 
