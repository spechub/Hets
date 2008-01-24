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
	}
	deriving (Eq, Show)
	
instance Pretty Sign where
	pretty = text . show
	
emptyDLSig :: Sign
emptyDLSig = Sign{
				  classes = Set.empty
				, subclassRelation = Rel.empty
				}
