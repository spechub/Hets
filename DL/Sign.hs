{- |
Module      :  $Header$
Description :  Signaure for DL
Copyright   :  (c) Dominik Luecke, Uni Bremen 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

The signatures for DL as they are extracted from the spec.
-}

module DL.Sign where

import Common.Id
import Common.AS_Annotation()
import Common.Doc
import Common.DocUtils
import Data.Set as Set
import Common.Lib.Rel as Rel
import Common.Result as Result
import DL.AS

data DLSymbol = DLSymbol
	{
		symName :: Id
	,   symType :: SymbType
	}
	deriving (Eq, Ord, Show)

data DataPropType = DataPropType Id Id
		deriving (Eq, Ord, Show)
		
data ObjPropType = ObjPropType Id Id
		deriving (Eq, Ord, Show)
			
data IndivType = IndivType [Id]
		deriving (Eq, Ord, Show)

data SymbType = ClassSym | 
				DataProp DataPropType |
				ObjProp ObjPropType |
				Indiv IndivType
				
	deriving (Eq, Ord, Show)
	
type RawDLSymbol = Id

topSort :: Id
topSort = stringToId "Thing"
	
instance Pretty DLSymbol where
	pretty = text . show

data Sign = Sign 
	{
		classes :: Set.Set Id 
	,	subclassRelation :: Rel.Rel Id
	,   funDataProps :: Set.Set QualDataProp
	,   dataProps :: Set.Set QualDataProp
	,   funcObjectProps :: Set.Set QualObjProp
	,   objectProps :: Set.Set QualObjProp
	,   individuals :: Set.Set QualIndiv
	}
	deriving (Eq, Show)
	
instance Pretty Sign where
	pretty sg = text $ show sg
	
data QualIndiv = QualIndiv
	{
		iid   :: Id
	,   types :: [Id]
	}
	deriving (Eq,Ord, Show)
	
data QualDataProp = QualDataProp
	{
		nameD   :: Id
	,	domD    :: Id
	,	rngD    :: Id
	}
	deriving (Eq,Ord, Show)
	
data QualObjProp = QualObjProp
	{
		nameO   :: Id
	,	domO    :: Id
	,	rngO    :: Id
	}
	deriving (Eq, Ord, Show)
	
emptyDLSig :: Sign
emptyDLSig = Sign{
				  classes = Set.empty
				, subclassRelation = Rel.empty
				, funDataProps = Set.empty
				, dataProps = Set.empty
				, funcObjectProps = Set.empty
				, objectProps = Set.empty
                , individuals = Set.empty
				}

				
data DLMorphism = DLMorphism
  { msource :: Sign
  , mtarget :: Sign
  } deriving (Eq, Show)

emptyMor :: DLMorphism  				
emptyMor = DLMorphism
 	{
 	 msource = emptyDLSig
 	,mtarget = emptyDLSig
 	}
  				
instance Pretty DLMorphism where
 	pretty = text . show

compDLmor :: DLMorphism -> DLMorphism -> Result.Result DLMorphism
compDLmor mor1 mor2 = 
	case (mtarget mor1 == msource mor2) of
		True -> Result.hint
			emptyMor
					{
						msource = msource mor1
					,   mtarget = mtarget mor2
					} 	
			"All fine"
			nullRange
		False -> Result.fatal_error "Not composable" nullRange

idMor :: Sign -> DLMorphism
idMor sig = emptyMor
	{
		msource = sig
	,   mtarget = sig
	}
