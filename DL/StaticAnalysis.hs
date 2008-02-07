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
import Data.List
import Data.Maybe

basic_DL_analysis :: (DLBasic, Sign,GlobalAnnos) -> 
                      Result (DLBasic, ExtSign Sign DLSymbol,[Named DLBasicItem])
basic_DL_analysis (spec, _, globAnnos) = 
    let 
        sens = case spec of
                    DLBasic x -> x
        [cCls, cObjProps, cDtProps, cIndi, cMIndi] = splitSentences sens
        oCls = uniteClasses cCls
        (cls, clsSym)  = getClasses $ map item $ oCls
        (dtPp, dtS2)   = getDataProps (map item cDtProps) (cls)
        (obPp, ob2)    = getObjProps (map item cObjProps) (cls)
        (ind, indS)    = getIndivs (map item cIndi) (cls)        
    in
	do
		return (spec, ExtSign{
					 plainSign = emptyDLSig
					 				{
					 					classes      = cls
					 				,   dataProps    = dtPp
					 				,   objectProps  = obPp
					 				,   individuals  = ind
					 				}
					,nonImportedSymbols = Set.empty `Set.union` clsSym 
							`Set.union` dtS2
							`Set.union` ob2
							`Set.union` indS
					}
				, map (makeNamedSen) $ concat [oCls, cObjProps, cDtProps, cIndi, cMIndi])

-- | Union of class definitions in different blocks
uniteClasses :: [Annoted DLBasicItem] -> [Annoted DLBasicItem]
uniteClasses cls = 
        map uniteClass $ getSame cls

uniteClass :: [Annoted DLBasicItem] -> (Annoted DLBasicItem)
uniteClass cls = 
    let
        para = map (\x -> case item x of
                    DLClass _ _ mpa -> mpa
                    _                  -> error "No"
                   ) cls
        props = concat $ map (\x -> case item x of
                    DLClass _ p _ -> p
                    _                  -> error "No"
                   ) cls
        name = map (\x -> case item x of
                    DLClass n _ _ -> n
                    _                  -> error "No"
                   ) cls
        rAnnos = concat $ map r_annos cls
        lAnnos = concat $ map l_annos cls
    in
        Annoted 
        {
            item = DLClass (head name) (uniteProps props) (unitePara para)
        ,   opt_pos = nullRange
        ,   l_annos = lAnnos
        ,   r_annos = rAnnos
        }
    where
        uniteProps :: [DLClassProperty] -> [DLClassProperty]
        uniteProps ps = 
            let
                subs = Set.toList $ Set.fromList $ concat $ map (\x -> case x of
                            DLSubClassof y -> y
                            _              -> error "No") $ filter (\x -> case x of
                        DLSubClassof _ -> True
                        _              -> False) ps
                equiv = Set.toList $ Set.fromList $ concat $ map (\x -> case x of
                            DLEquivalentTo y -> y
                            _              -> error "No") $ filter (\x -> case x of
                        DLEquivalentTo _ -> True
                        _              -> False) ps
                dis   = Set.toList $ Set.fromList $ concat $ map (\x -> case x of
                            DLDisjointWith y -> y
                            _              -> error "No") $ filter (\x -> case x of
                        DLDisjointWith _ -> True
                        _              -> False) ps
                
            in
                [] ++
                    (if subs /= [] then ([DLSubClassof subs]) else []) ++
                    (if equiv /= [] then ([DLEquivalentTo equiv]) else []) ++
                    (if dis /= [] then ([DLDisjointWith dis]) else [])

-- | Union of Paraphrases
unitePara :: [Maybe DLPara] -> (Maybe DLPara)
unitePara pa = 
    case allNothing pa of
        True  -> Nothing
        False -> Just $ DLPara $ concat $ map (\x -> case x of 
                        DLPara y -> y) $
                 map fromJust $ filter (\x -> x /= Nothing) pa
    where
        allNothing :: [Maybe DLPara] -> Bool
        allNothing pan = and $ map (== Nothing) pan

getSame :: [Annoted DLBasicItem] -> [[Annoted DLBasicItem]]
getSame x = case x of
    []    -> []
    (z:zs)  ->  let
                 (p1, p2) = partition (\y -> getName z == getName y) (z:zs)
              in
                [p1] ++ (getSame p2)

getName :: Annoted DLBasicItem -> Id
getName x = case item x of
    DLClass  n _ _ -> n
    DLObjectProperty n _ _ _ _ _ -> n
    DLDataProperty n _ _ _ _ _ -> n
    DLIndividual n _ _ _ _ -> n
    DLMultiIndi _ _ _ _ _ -> error "No"
    
splitSentences :: [Annoted DLBasicItem] -> [[Annoted DLBasicItem]]
splitSentences sens = 
    let
        cls = filter (\x -> case item x of
                        DLClass _ _ _ -> True
                        _             -> False) sens
        objProp = filter (\x -> case item x of 
                DLObjectProperty _ _ _ _ _ _ -> True
                _                            -> False) sens
        dtProp = filter (\x -> case item x of
                    DLDataProperty _ _ _ _ (Nothing) _ -> True
                    DLDataProperty _ _ _ _ (Just DLFunctional) _ -> True
                    DLDataProperty _ _ _ _ (Just DLInvFuntional) _ ->  error "InvFunctional not available for data properties"
                    DLDataProperty _ _ _ _ (Just DLSymmetric)    _ ->  error "Symmetric not available for data properties"
                    DLDataProperty _ _ _ _ (Just DLTransitive) _   ->  error "Transitive not available for data properties"
                    _                                  -> False
                ) sens 
        indi = filter (\x -> case item x of
            DLIndividual _ _ _ _ _ -> True
            _                      -> False        
                ) sens
        mIndi = filter (\x -> case item x of
                    DLMultiIndi _ _ _ _ _ -> True
                    _                     -> False
                ) sens
    in
    [cls, objProp, dtProp, indi, mIndi]

getClasses :: [DLBasicItem] -> (Set.Set Id, Set.Set DLSymbol)
getClasses cls = 
	let
   		ids   = map (\x -> case x of 
							DLClass i _ _ -> i
							_             -> error "Runtime Error!") cls
	in
		(foldl (\x y -> Set.insert y x) Set.empty ids,
		 foldl (\x y -> Set.insert (DLSymbol
		 							{
		 								symName = y
		 							,   symType = ClassSym
		 							}) x) Set.empty ids
		)

-- Building a set of Individuals
getIndivs :: [DLBasicItem] ->  Set.Set Id -> (Set.Set QualIndiv, Set.Set DLSymbol)
getIndivs indivs cls = 
	let 
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
		(foldl (\x y -> Set.insert y x) Set.empty indIds,
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
getDataProps fnDataProps cls = 
		(foldl (\x y -> Set.insert (examineDataProp y cls) x) Set.empty fnDataProps,
		 foldl (\x y -> Set.insert (examineDataPropS y cls) x) Set.empty fnDataProps
		)

getObjProps :: [DLBasicItem] -> Set.Set Id -> (Set.Set QualObjProp, Set.Set DLSymbol)
getObjProps fnObjProps cls =
		(foldl (\x y -> Set.insert (examineObjProp y cls) x) Set.empty fnObjProps,
	     foldl (\x y -> Set.insert (examineObjPropS y cls) x) Set.empty fnObjProps		
		)

examineDataProp :: DLBasicItem -> Set.Set Id -> QualDataProp
examineDataProp bI _ = 
	case bI of
		DLDataProperty nm (Just dm) (Just rn) _ _ _-> 
				QualDataProp
					{
						nameD = nm
					,   domD  = dm
					,   rngD  = rn
					}
		DLDataProperty nm (Nothing) (Just rn) _ _ _-> 
				QualDataProp
					{
						nameD = nm
					,   domD  = DLClassId topSort
					,   rngD  = rn
					}
		DLDataProperty nm (Just dm) (Nothing) _ _ _-> 
				QualDataProp
					{
						nameD = nm
					,   domD  = dm
					,   rngD  = DLClassId topSort
					}
		DLDataProperty nm (Nothing) (Nothing) _ _ _-> 
				QualDataProp
					{
						nameD = nm
					,   domD  = DLClassId topSort
					,   rngD  = DLClassId topSort
					}
		_                                          -> error "Runtime error!"

examineDataPropS :: DLBasicItem -> Set.Set Id -> DLSymbol
examineDataPropS bI _ = 
	case bI of
		DLDataProperty nm (Just dm) (Just rn) _ _ _-> 
				DLSymbol
					{
						symName = nm
					,   symType  = DataProp (DataPropType dm rn)
					}
		DLDataProperty nm (Nothing) (Just rn) _ _ _-> 
				DLSymbol
					{
						symName = nm
					,   symType  = DataProp (DataPropType (DLClassId topSort) rn)
					}			
		DLDataProperty nm (Just dm) (Nothing) _ _ _-> 
				DLSymbol
					{
						symName = nm
					,   symType  = DataProp (DataPropType dm (DLClassId topSort))
					}					
		DLDataProperty nm (Nothing) (Nothing) _ _ _-> 
				DLSymbol
					{
						symName = nm
					,   symType  = DataProp (DataPropType (DLClassId topSort) (DLClassId topSort))
					}
		_                                          -> error "Runtime error!"
		
examineObjProp :: DLBasicItem -> Set.Set Id -> QualObjProp
examineObjProp bI _ = 
	case bI of
		DLObjectProperty nm (Just dm) (Just rn) _ _ _-> 
				QualObjProp
					{
						nameO = nm
					,   domO  = dm
					,   rngO  = rn
					}
		DLObjectProperty nm (Nothing) (Just rn) _ _ _-> 
				QualObjProp
					{
						nameO = nm
					,   domO  = (DLClassId topSort)
					,   rngO  = rn
					}
		DLObjectProperty nm (Just dm) (Nothing) _ _ _-> 
				QualObjProp
					{
						nameO = nm
					,   domO  = dm
					,   rngO  = (DLClassId topSort)
					}
		DLObjectProperty nm (Nothing) (Nothing) _ _ _-> 
				QualObjProp
					{
						nameO = nm
					,   domO  = (DLClassId topSort)
					,   rngO  = (DLClassId topSort)
					}
		_                                          -> error "Runtime error!"			
		
examineObjPropS :: DLBasicItem -> Set.Set Id -> DLSymbol
examineObjPropS bI _ = 
	case bI of
		DLObjectProperty nm (Just dm) (Just rn) _ _ _-> 
				DLSymbol
					{
						symName = nm
					,   symType = ObjProp (ObjPropType dm rn)
					}
		DLObjectProperty nm (Nothing) (Just rn) _ _ _-> 
				DLSymbol
					{
						symName = nm
					,   symType = ObjProp (ObjPropType (DLClassId topSort) rn)
					}
		DLObjectProperty nm (Just dm) (Nothing) _ _ _-> 
				DLSymbol
					{
						symName = nm
					,   symType = ObjProp (ObjPropType dm (DLClassId topSort))
					}
		DLObjectProperty nm (Nothing) (Nothing) _ _ _-> 
				DLSymbol
					{
						symName = nm
					,   symType = ObjProp (ObjPropType (DLClassId topSort) (DLClassId topSort))
					}
		_                                          -> error "Runtime error!"	
		