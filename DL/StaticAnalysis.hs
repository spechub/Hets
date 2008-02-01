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

module DL.StaticAnalysis 
	(basic_DL_analysis)
	where

import DL.AS
import Logic.Logic()
import Common.GlobalAnnotations
import Common.Result
import Common.AS_Annotation
import Common.ExtSign
import qualified Data.Set as Set
import DL.Sign
import Common.Id
import qualified Common.Lib.Rel as Rel()

basic_DL_analysis :: (DLBasic, Sign,GlobalAnnos) -> 
                      Result (DLBasic, ExtSign Sign DLSymbol,[Named DLBasicItem])
basic_DL_analysis (spec, _, globAnnos) = 
	do
		let sens = case spec of
				DLBasic x -> x
		let (cls, clsSym)  = getClasses sens
		    (fnDtPp, dtS1) = getFunDataProps sens (cls)
		    (dtPp, dtS2)   = getDataProps sens (cls)
		    (fnObPp, ob1)  = getFunObjProps sens (cls)
		    (obPp, ob2)    = getObjProps sens (cls)
		    (ind, indS)    = getIndivs sens (cls)
		return (spec, ExtSign{
					 plainSign = emptyDLSig
					 				{
					 					classes      = cls
					 				,	funDataProps = fnDtPp
					 				,   dataProps = dtPp
					 				,   funcObjectProps = fnObPp
					 				,   objectProps = obPp
					 				,   individuals = ind
					 				}
					,nonImportedSymbols = Set.empty `Set.union` clsSym 
							`Set.union` dtS1 `Set.union` dtS2
							`Set.union` ob1 `Set.union` ob2
							`Set.union` indS
					}
				, map (makeNamedSen . emptyAnno) sens)


insert_unique :: (Show a, Ord a) => a -> Set.Set a -> Set.Set a 
insert_unique i st = 
    case (Set.member i st) of 
        True  -> error ("Duplicate definition of: " ++ (show i) ++"!")
        False -> Set.insert i st

getClasses :: [DLBasicItem] -> (Set.Set Id, Set.Set DLSymbol)
getClasses sens = 
	let
		cls  = filter (\x -> case x of 
								DLClass _ _ _ -> True
								_             -> False
						) sens
		ids   = map (\x -> case x of 
							DLClass i _ _ -> i
							_             -> error "Runtime Error!") cls
	in
		(foldl (\x y -> insert_unique y x) Set.empty ids,
		 foldl (\x y -> Set.insert (DLSymbol
		 							{
		 								symName = y
		 							,   symType = ClassSym
		 							}) x) Set.empty ids
		)

-- Building a set of Individuals
getIndivs :: [DLBasicItem] ->  Set.Set Id -> (Set.Set QualIndiv, Set.Set DLSymbol)
getIndivs sens cls = 
	let 
		indivs = filter (\x -> case x of 
			DLIndividual _ _ _ _ _ -> True
			_                      -> False
			) sens
		indIds = map (\x -> case x of
					DLIndividual tid (Nothing) _ _ _ ->
						QualIndiv
							{
								iid = tid
							,   types = [topSort]
							}					
					DLIndividual tid (Just y) _ _ _ -> 
						(case y of
							DLType tps -> 
								bucketIndiv $ map (\z -> case (z `Set.member` cls) of
									True -> 										
										QualIndiv	
											{
												iid = tid
											,   types = [z]
											}
									_    -> error ("Class " ++ (show z) ++ " not defined")
									) tps) 
					_                               -> error "Runtime error"
						) indivs
													
	in
		(foldl (\x y -> insert_unique y x) Set.empty indIds,
		 foldl (\x y -> Set.insert DLSymbol
		 							{
		 							  symName = iid y
		 							, symType = Indiv (IndivType (types y))
		 							}x) Set.empty indIds
		)

bucketIndiv :: [QualIndiv] -> QualIndiv
bucketIndiv ids = case ids of
	[]     -> QualIndiv 
				{
				  iid   = stringToId ""
				, types = []
				}
	(x:xs) -> QualIndiv 
				{
				  iid = iid x
				, types = (types x) ++ types (bucketIndiv xs)
				}

-- Sets of Object and Data Properties a built

getDataProps :: [DLBasicItem] -> Set.Set Id -> (Set.Set QualDataProp, Set.Set DLSymbol)
getDataProps sens cls = 
	let
		fnDataProps = filter (\x -> case x of
			DLDataProperty _ _ _ _ (Nothing) _ -> True
			DLDataProperty _ _ _ _ (Just DLInvFuntional) _ ->  error "InvFunctional not available for data properties"
			DLDataProperty _ _ _ _ (Just DLSymmetric)    _ ->  error "Symmetric not available for data properties"
			DLDataProperty _ _ _ _ (Just DLTransitive) _   ->  error "Transitive not available for data properties"
			_                                  -> False
				) sens 
	in
		(foldl (\x y -> insert_unique (examineDataProp y cls) x) Set.empty fnDataProps,
		 foldl (\x y -> Set.insert (examineDataPropS y cls) x) Set.empty fnDataProps
		)

getFunDataProps :: [DLBasicItem] -> Set.Set Id -> (Set.Set QualDataProp, Set.Set DLSymbol)
getFunDataProps sens cls = 
	let
		fnDataProps = filter (\x -> case x of
			DLDataProperty _ _ _ _ (Just DLFunctional) _ -> True
			_                                            -> False
				) sens 
	in
		(foldl (\x y -> insert_unique (examineDataProp y cls) x) Set.empty fnDataProps,
		 foldl (\x y -> Set.insert (examineDataPropS y cls) x) Set.empty fnDataProps
		)

getObjProps :: [DLBasicItem] -> Set.Set Id -> (Set.Set QualObjProp, Set.Set DLSymbol)
getObjProps sens cls =
	let 
		fnObjProps = filter (\x -> case x of
			DLObjectProperty _ _ _ _ chars _ ->
				let
					cSet = Set.fromList chars
					cSetSize = Set.size cSet
					cLen = length chars
					isFunc = DLFunctional `Set.member` cSet
				in
					case (cSetSize == cLen) of
						True -> not isFunc
						_    -> error "Duplicate characteristics definition"
			_                                -> False
					) sens
	in
		(foldl (\x y -> insert_unique (examineObjProp y cls) x) Set.empty fnObjProps,
	     foldl (\x y -> Set.insert (examineObjPropS y cls) x) Set.empty fnObjProps		
		)

getFunObjProps :: [DLBasicItem] -> Set.Set Id -> (Set.Set QualObjProp, Set.Set DLSymbol)
getFunObjProps sens cls =
	let 
		fnObjProps = filter (\x -> case x of
			DLObjectProperty _ _ _ _ chars _ ->
				let
					cSet = Set.fromList chars
					cSetSize = Set.size cSet
					cLen = length chars
					isFunc = DLFunctional `Set.member` cSet
				in
					case (cSetSize == cLen) of
						True -> isFunc
						_    -> error "Duplicate characteristics definition"
			_                                -> False
					) sens
	in
		(foldl (\x y -> insert_unique (examineObjProp y cls) x) Set.empty fnObjProps,
		 foldl (\x y -> Set.insert (examineObjPropS y cls) x) Set.empty fnObjProps
		)

examineDataProp :: DLBasicItem -> Set.Set Id -> QualDataProp
examineDataProp bI ids = 
	case bI of
		DLDataProperty nm (Just dm) (Just rn) _ _ _-> 
			if ((dm `Set.member` ids) && (rn `Set.member` ids)) 
			then
				QualDataProp
					{
						nameD = nm
					,   domD  = dm
					,   rngD  = rn
					}
			else
				error ("Class undefiend in: " ++ show bI)
		DLDataProperty nm (Nothing) (Just rn) _ _ _-> 
			if (rn `Set.member` ids)
			then
				QualDataProp
					{
						nameD = nm
					,   domD  = topSort
					,   rngD  = rn
					}
			else
				error ("Class undefiend in: " ++ show bI)
		DLDataProperty nm (Just dm) (Nothing) _ _ _-> 
			if (dm `Set.member` ids)
			then
				QualDataProp
					{
						nameD = nm
					,   domD  = dm
					,   rngD  = topSort
					}
			else
				error ("Class undefiend in: " ++ show bI)
		DLDataProperty nm (Nothing) (Nothing) _ _ _-> 
				QualDataProp
					{
						nameD = nm
					,   domD  = topSort
					,   rngD  = topSort
					}
		_                                          -> error "Runtime error!"

examineDataPropS :: DLBasicItem -> Set.Set Id -> DLSymbol
examineDataPropS bI ids = 
	case bI of
		DLDataProperty nm (Just dm) (Just rn) _ _ _-> 
			if ((dm `Set.member` ids) && (rn `Set.member` ids)) 
			then
				DLSymbol
					{
						symName = nm
					,   symType  = DataProp (DataPropType dm rn)
					}
			else
				error ("Class undefiend in: " ++ show bI)
		DLDataProperty nm (Nothing) (Just rn) _ _ _-> 
			if (rn `Set.member` ids)
			then
				DLSymbol
					{
						symName = nm
					,   symType  = DataProp (DataPropType topSort rn)
					}			
			else
				error ("Class undefiend in: " ++ show bI)
		DLDataProperty nm (Just dm) (Nothing) _ _ _-> 
			if (dm `Set.member` ids)
			then
				DLSymbol
					{
						symName = nm
					,   symType  = DataProp (DataPropType dm topSort)
					}					
			else
				error ("Class undefiend in: " ++ show bI)
		DLDataProperty nm (Nothing) (Nothing) _ _ _-> 
				DLSymbol
					{
						symName = nm
					,   symType  = DataProp (DataPropType topSort topSort)
					}
		_                                          -> error "Runtime error!"
		
examineObjProp :: DLBasicItem -> Set.Set Id -> QualObjProp
examineObjProp bI ids = 
	case bI of
		DLObjectProperty nm (Just dm) (Just rn) _ _ _-> 
			if ((dm `Set.member` ids) && (rn `Set.member` ids)) 
			then
				QualObjProp
					{
						nameO = nm
					,   domO  = dm
					,   rngO  = rn
					}
			else
				error ("Class undefiend in: " ++ show bI)
		DLObjectProperty nm (Nothing) (Just rn) _ _ _-> 
			if (rn `Set.member` ids)
			then
				QualObjProp
					{
						nameO = nm
					,   domO  = topSort
					,   rngO  = rn
					}
			else
				error ("Class undefiend in: " ++ show bI)
		DLObjectProperty nm (Just dm) (Nothing) _ _ _-> 
			if (dm `Set.member` ids)
			then
				QualObjProp
					{
						nameO = nm
					,   domO  = dm
					,   rngO  = topSort
					}
			else
				error ("Class undefiend in: " ++ show bI)
		DLObjectProperty nm (Nothing) (Nothing) _ _ _-> 
				QualObjProp
					{
						nameO = nm
					,   domO  = topSort
					,   rngO  = topSort
					}
		_                                          -> error "Runtime error!"			
		
examineObjPropS :: DLBasicItem -> Set.Set Id -> DLSymbol
examineObjPropS bI ids = 
	case bI of
		DLObjectProperty nm (Just dm) (Just rn) _ _ _-> 
			if ((dm `Set.member` ids) && (rn `Set.member` ids)) 
			then
				DLSymbol
					{
						symName = nm
					,   symType = ObjProp (ObjPropType dm rn)
					}
			else
				error ("Class undefiend in: " ++ show bI)
		DLObjectProperty nm (Nothing) (Just rn) _ _ _-> 
			if (rn `Set.member` ids)
			then
				DLSymbol
					{
						symName = nm
					,   symType = ObjProp (ObjPropType topSort rn)
					}
			else
				error ("Class undefiend in: " ++ show bI)
		DLObjectProperty nm (Just dm) (Nothing) _ _ _-> 
			if (dm `Set.member` ids)
			then
				DLSymbol
					{
						symName = nm
					,   symType = ObjProp (ObjPropType dm topSort)
					}
			else
				error ("Class undefiend in: " ++ show bI)
		DLObjectProperty nm (Nothing) (Nothing) _ _ _-> 
				DLSymbol
					{
						symName = nm
					,   symType = ObjProp (ObjPropType topSort topSort)
					}
		_                                          -> error "Runtime error!"	
		