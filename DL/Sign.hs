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
	pretty _ = text ""
	
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
