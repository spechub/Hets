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
import Common.AS_Annotation (Named)
import qualified Common.Lib.Map as Map
import Common.Lib.Set as Set
import Data.Dynamic

-- CASL
import CASL.Logic_CASL 
import CASL.AS_Basic_CASL
import CASL.Sublogic
import CASL.Sign
import CASL.Morphism

import HasCASL.Logic_HasCASL
import HasCASL.As
import HasCASL.Le
import HasCASL.Symbol
import HasCASL.Morphism

-- | The identity of the comorphism
data CASL2HasCASL = CASL2HasCASL deriving (Show)

instance Language CASL2HasCASL -- default definition is okay

tycon_CASL2HasCASL :: TyCon
tycon_CASL2HasCASL = mkTyCon "G_sign"

instance Typeable CASL2HasCASL where
  typeOf _ = mkAppTy tycon_CASL2HasCASL []

instance Comorphism CASL2HasCASL
               CASL CASL.Sublogic.CASL_Sublogics
               BASIC_SPEC FORMULA SYMB_ITEMS SYMB_MAP_ITEMS
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
makeType i = TypeName i star 0

trOpType :: CASL.Sign.OpType -> HasCASL.Le.OpInfo
trOpType ot = OpInfo { opType = simpleTypeScheme t,
		       opAttrs = [],
		       opDefn = NoOpDefn Op
		     }
               where t = if null args then res 
			 else FunType arg arrow res []
                     arrow = case opKind ot of
                       CASL.Sign.Total -> FunArr 
                       CASL.Sign.Partial -> PFunArr
		     args = map makeType $ opArgs ot
                     arg = if isSingle args then head args else 
			   ProductType args []
                     res = makeType $ opRes ot

trPredType :: CASL.Sign.PredType -> HasCASL.Le.OpInfo
trPredType pt = OpInfo { opType = simpleTypeScheme t,
		         opAttrs = [],
		         opDefn = NoOpDefn Pred
		     }
               where t = if null args then logicalType else 
			 predType arg
		     args = map makeType $ predArgs pt
                     arg = if isSingle args then head args else 
			   ProductType args []

mapSignature :: CASL.Sign.Sign -> Maybe(HasCASL.Le.Env,[Named Term]) 
mapSignature sign = Just (initialEnv { 
    classMap = Map.empty,
    typeMap = Map.fromList $ map (\s -> (s,sortTypeinfo)) 
                           $ Set.toList $ sortSet sign,
    assumps = Map.map OpInfos $ Map.unionWith (++) opmap predmap }, [])
  where
    opmap   = Map.map (map trOpType . Set.toList) $ opMap sign 
    predmap = Map.map (map trPredType . Set.toList) $ predMap sign

