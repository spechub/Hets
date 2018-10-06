{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./RigidCASL/Sign.hs
License     :  GPLv2 or higher, see LICENSE.txt

Stability   :  provisional
Portability :  portable

Signatures for hybrid logic, as extension of CASL signatures.
-}

module RigidCASL.Sign where

import CASL.Sign
import CASL.Morphism
import qualified CASL.AS_Basic_CASL as CBasic

import qualified Common.Lib.MapSet as MapSet
import Common.Id
import Common.Result

import Data.Data
import qualified Data.Set as Set
import qualified Common.Lib.Rel as Rel

import RigidCASL.AS_Rigid

import Debug.Trace

data RigidExt = RigidExt
  { rigidSorts :: Set.Set CBasic.SORT
  , rigidOps :: OpMap
  , rigidPreds :: PredMap
  } deriving (Show, Eq, Ord, Typeable, Data)

type RSign = Sign () RigidExt

emptyRigidExt :: RigidExt
emptyRigidExt = RigidExt Set.empty MapSet.empty MapSet.empty

addRigidExt :: RigidExt -> RigidExt -> RigidExt
addRigidExt a b = a
  { rigidSorts = Set.union (rigidSorts a) $ rigidSorts b
  , rigidOps = addOpMapSet (rigidOps a) $ rigidOps b
  , rigidPreds = addMapSet (rigidPreds a) $ rigidPreds b
  }

interRigidExt :: RigidExt -> RigidExt -> RigidExt
interRigidExt a b = a
  { rigidSorts = Set.intersection (rigidSorts a) $ rigidSorts b
  , rigidOps = interOpMapSet (rigidOps a) $ rigidOps b
  , rigidPreds = interMapSet (rigidPreds a) $ rigidPreds b
  }

diffRigidExt :: RigidExt -> RigidExt -> RigidExt
diffRigidExt a b = a
  { rigidSorts = Set.difference (rigidSorts a) $ rigidSorts b
  , rigidOps = diffOpMapSet (rigidOps a) $ rigidOps b
  , rigidPreds = diffMapSet (rigidPreds a) $ rigidPreds b
  }

isSubRigidExt :: RigidExt -> RigidExt -> Bool
isSubRigidExt a b =
       Set.isSubsetOf (rigidSorts a) (rigidSorts b)
    && isSubOpMap (rigidOps a) (rigidOps b)
    && isSubMap (rigidPreds a) (rigidPreds b)

instance SignExtension RigidExt where
    isSubSignExtension = isSubRigidExt  

caslSign :: RSign -> CASLSign
caslSign sig = Sign
    { sortRel = sortRel sig
    , revSortRel = revSortRel sig
    , emptySortSet = emptySortSet sig
    , opMap = opMap sig
    , assocOps = assocOps sig
    , predMap = predMap sig
    , varMap = varMap sig
    , sentences = sentences sig
    , declaredSymbols = declaredSymbols sig
    , envDiags = envDiags sig
    , annoMap = annoMap sig
    , globAnnos = globAnnos sig
    , extendedInfo = ()
    }

toRSign :: CASLSign -> RigidExt -> RSign
toRSign sig anExt = Sign
    { sortRel = sortRel sig
    , revSortRel = revSortRel sig
    , emptySortSet = emptySortSet sig
    , opMap = opMap sig
    , assocOps = assocOps sig
    , predMap = predMap sig
    , varMap = varMap sig
    , sentences = sentences sig
    , declaredSymbols = declaredSymbols sig
    , envDiags = envDiags sig
    , annoMap = annoMap sig
    , globAnnos = globAnnos sig
    , extendedInfo = anExt
    }

removeRigidDupl :: RSign -> RSign
removeRigidDupl sig = 
  sig {sortRel = Rel.difference (Rel.transReduce $ sortRel sig)
                . Rel.transReduce $ Rel.fromSet $
                Set.map (\x->(x,x)) $ rigidSorts $ extendedInfo sig,
       opMap = diffOpMapSet (opMap sig) $ rigidOps $ extendedInfo sig,
       predMap = diffMapSet (predMap sig) $ rigidPreds $ extendedInfo sig}

symOfRigid :: RSign -> [Set.Set RigidSymbol]
symOfRigid rsig = 
 let
   allSyms = symOf rsig
   cSyms = Set.unions $ symOf $ removeRigidDupl rsig
 in map (\sSet -> Set.map (\s -> if Set.member s cSyms then CSym s else RSym s) sSet ) allSyms

rigidSymName :: RigidSymbol -> Id
rigidSymName (CSym s) = symName s
rigidSymName (RSym s) = symName s

rigidExtSymKind :: RigidSymbol -> String
rigidExtSymKind (CSym s) = (extSymbolKind . symbType) s
rigidExtSymKind (RSym s) = "rigid " ++ (extSymbolKind . symbType) s
 

rigidSymToRaw :: RigidSymbol -> RawSymbol
rigidSymToRaw (CSym s) = symbolToRaw s
rigidSymToRaw (RSym s) = symbolToRaw s

rigidRawToSymbol :: RawSymbol -> Maybe RigidSymbol
rigidRawToSymbol (ASymbol s) = Just $ CSym s -- TODO: this is a hack!
rigidRawToSymbol _ = Nothing

rigidMatches :: RigidSymbol -> RawSymbol -> Bool
rigidMatches (CSym s) = matches s 
rigidMatches (RSym s) = matches s 

rigidAddSymbToSign :: RSign -> RigidSymbol -> Result RSign
rigidAddSymbToSign rsig rsym = 
 case rsym of 
  CSym s -> do 
   bsig' <- addSymbToSign (caslSign rsig) s
   return $ toRSign bsig' $ extendedInfo rsig
  RSym s -> error "nyi"

