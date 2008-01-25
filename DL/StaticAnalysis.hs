{- |
Module      :  $Header$
Description :  Static Analysis for DL
Copyright   :  (c) Dominik Luecke, Uni Bremen 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

The static analysis of DL basic specs is implemented here.
-}

module DL.StaticAnalysis where

import DL.AS
import Common.GlobalAnnotations
import Common.Result
import Common.AS_Annotation
import Common.ExtSign
import qualified Data.Set as Set
import DL.Sign

basic_DL_analysis :: (DLBasic, Sign,GlobalAnnos) -> 
                      Result (DLBasic, ExtSign Sign DLSymbol,[Named DLBasicItem])
basic_DL_analysis (spec, _, _) = 
	do
		let sens = case spec of
				DLBasic x -> x
		return (spec, ExtSign{
					 plainSign = emptyDLSig
					,nonImportedSymbols = Set.empty
					}
				, map (makeNamedSen . emptyAnno) sens)
		                   