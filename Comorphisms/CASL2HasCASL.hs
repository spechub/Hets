{- |
Module      :  $Header$
Copyright   :  (c) Till Mossakowski and Uni Bremen 2003
Licence     :  All rights reserved.

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

   
   The embedding comorphism from CASL to HasCASL.

-}

module Comorphisms.CASL2HasCASL where

import Logic.Logic
import Logic.Comorphism
import Common.Id
import qualified Common.Lib.Map as Map
import Common.Lib.Set as Set
import Data.Dynamic

-- CASL
import CASL.Logic_CASL 
import CASL.AS_Basic_CASL
import CASL.Sublogic
import CASL.StaticAna
import CASL.Morphism

import HasCASL.Logic_HasCASL
import HasCASL.As
import HasCASL.Le
import HasCASL.Symbol
import HasCASL.Morphism

-- | The identity of the comorphism
data CASL2HasCASL = CASL2HasCASL deriving (Show)
instance Language CASL2HasCASL -- default definition is okay
tycon_CASL2HasCASL = mkTyCon "G_sign"
instance Typeable CASL2HasCASL where
  typeOf _ = mkAppTy tycon_CASL2HasCASL []
instance Comorphism CASL2HasCASL
               CASL CASL.Sublogic.CASL_Sublogics
               BASIC_SPEC Sentence SYMB_ITEMS SYMB_MAP_ITEMS
               Sign 
               CASL.Morphism.Morphism
               CASL.Morphism.Symbol CASL.Morphism.RawSymbol ()
               HasCASL HasCASL_Sublogics
               BasicSpec Term SymbItems SymbMapItems
               HasCASL.Le.Env 
               HasCASL.Morphism.Morphism
               HasCASL.Morphism.Symbol HasCASL.Morphism.RawSymbol () where
    sourceLogic _ = CASL
    sourceSublogic _ = CASL_SL
                      { has_sub = False, -- no subsorting in HasCASL yet...
                        has_part = True,
                        has_cons = True,
                        has_eq = True,
                        has_pred = True,
                        which_logic = FOL
                      }
    targetLogic _ = HasCASL
    targetSublogic _ = ()
    map_sign _ = mapSignature
    --map_morphism _ morphism1 -> Maybe morphism2
    --map_sentence _ sign1 -> sentence1 -> Maybe sentence2
    --map_symbol :: cid -> symbol1 -> Set symbol2

sortTypeinfo :: TypeInfo
sortTypeinfo = TypeInfo { typeKind = star,
			  otherTypeKinds = [],
			  superTypes = [],
			  typeDefn = NoTypeDefn
			 } 
makeType :: Id -> HasCASL.As.Type
makeType ide = TypeName ide star 0

trOpType :: CASL.StaticAna.OpType -> HasCASL.Le.OpInfo
trOpType ot = OpInfo { opType = TypeScheme [] ([] :=> t) [],
		       opAttrs = [],
		       opDefn = NoOpDefn
		     }
               where t = FunType arg arrow res []
                     arrow = case opKind ot of
                       CASL.StaticAna.Total -> FunArr 
                       CASL.StaticAna.Partial -> PFunArr
                     arg = ProductType (map makeType $ opArgs ot) []
                     res = makeType $ opRes ot

trPredType :: CASL.StaticAna.PredType -> HasCASL.Le.OpInfo
trPredType pt = OpInfo { opType = TypeScheme [] ([] :=> t) [],
		         opAttrs = [],
		         opDefn = NoOpDefn
		     }
               where t = predType arg
                     arg = ProductType (map makeType $ predArgs pt) []

mapSignature :: CASL.StaticAna.Sign -> Maybe(HasCASL.Le.Env,[Term]) 
mapSignature sign = Just (HasCASL.Le.Env { 
    classMap = Map.empty,
    typeMap = Map.fromList $ map (\s -> (s,sortTypeinfo)) 
                           $ Set.toList $ sortSet sign,
    assumps = Map.map OpInfos $ Map.unionWith (++) opmap predmap,
    HasCASL.Le.sentences = [],	 
    HasCASL.Le.envDiags = [],
    counter = 1
  }, [])
  where
    opmap   = Map.map (map trOpType . Set.toList) $ opMap sign 
    predmap = Map.map (map trPredType . Set.toList) $ predMap sign

