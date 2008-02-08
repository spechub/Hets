{- |
Module      :  $Header$
Description :  Static Analysis for DL
Copyright   :  (c) Dominik Luecke, Uni Bremen 2008
License     :  similar to LGPL, see Hets/LICENSE.txt or LIZENZ.txt

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
basic_DL_analysis (spec, _, _) = 
    let 
        sens = case spec of
                    DLBasic x -> x
        [cCls, cObjProps, cDtProps, cIndi, cMIndi] = splitSentences sens
        oCls = uniteClasses cCls
        oObjProps = uniteObjProps cObjProps
        oDtProps = uniteDataProps cDtProps
        oIndi    = uniteIndividuals cIndi
        (cls, clsSym)  = getClasses $ map item $ oCls
        (dtPp, dtS2)   = getDataProps (map item oDtProps) (cls)
        (obPp, ob2)    = getObjProps (map item oObjProps) (cls)
        (ind, indS)    = getIndivs (map item oIndi) (cls)        
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
				, map (makeNamedSen) $ concat [oCls, oObjProps, oDtProps, oIndi])


-- | Union of blocks with the same name
uniteIndividuals :: [Annoted DLBasicItem] -> [Annoted DLBasicItem]
uniteIndividuals inds =
    map uniteIndividual $ getSame inds
    
uniteIndividual :: [Annoted DLBasicItem] -> (Annoted DLBasicItem)
uniteIndividual inds =
    let 
          name = head $ map (\x -> case item x of
                    DLIndividual nm _ _ _ _ -> nm
                    _                       -> error "No"
                   ) inds    
          para = unitePara $ map (\x -> case item x of
                    DLIndividual _ _ _ _ mpa -> mpa
                    _                        -> error "No"
                   ) inds         
          tpes = (\x -> case x of 
            [] -> Nothing
            y  -> Just $ DLType y) $          
            Set.toList $ Set.fromList $ concat $ map (\x -> case x of
                    DLType y -> y) $ map fromJust $ filter (/=Nothing) $ map (\x -> case item x of
                    DLIndividual _ tp _ _ _ -> tp
                    _                       -> error "No"
                   ) inds          
          fts = Set.toList $ Set.fromList $ concat $ map (\x -> case item x of
                    DLIndividual _ _ ft _ _ -> ft
                    _                       -> error "No"
                   ) inds    
          iRel = bucketIrel $ Set.toList $ Set.fromList $ concat $ map (\x -> case item x of
                    DLIndividual _ _ _ iR _ -> iR
                    _                       -> error "No"
                   ) inds              
          rAnnos = concat $ map r_annos inds
          lAnnos = concat $ map l_annos inds     
    in
        Annoted
        {
            item = DLIndividual name tpes fts iRel para
        ,   opt_pos = nullRange
        ,   l_annos = lAnnos
        ,   r_annos = rAnnos        
        }

uniteDataProps :: [Annoted DLBasicItem] -> [Annoted DLBasicItem]
uniteDataProps op = 
    map uniteDataProp $ getSame op

uniteDataProp :: [Annoted DLBasicItem] -> (Annoted DLBasicItem)
uniteDataProp op =
    let 
         para = unitePara $ map (\x -> case item x of
                    DLDataProperty _ _ _ _ _ mpa -> mpa
                    _                  -> error "No"
                   ) op   
         dom  = bucketDomRn $ map fromJust $ Set.toList $ Set.fromList $ filter (/= Nothing) $ map (\x -> case item x of
                    DLDataProperty _ dm _ _ _ _ -> dm
                    _                  -> error "No"
                   ) op   
         rn   = bucketDomRn $ map fromJust $ Set.toList $ Set.fromList $ filter (/=Nothing) $ map (\x -> case item x of
                    DLDataProperty _ _ mrn _ _ _ -> mrn
                    _                  -> error "No"
                   ) op  
         propsRel = bucketPropsRel $ Set.toList $ Set.fromList $ concat $ map (\x -> case item x of
                    DLDataProperty _ _ _ prel _ _ -> prel
                    _                  -> error "No"
                   ) op                   
         chars = filter (/= Nothing) $ map (\x -> case item x of
                    DLDataProperty _ _ _ _ char  _ -> char
                    _                  -> error "No"
                   ) op    
         ochar = case chars of 
            [] -> Nothing
            (x:xs) -> case length (map fromJust (x:xs)) == length (filter (== DLFunctional) $ map fromJust (x:xs)) of
                True -> Just DLFunctional
                _    -> error ("Wrong characteristics " ++ (concatComma $ map show (filter (/=DLFunctional) $ map fromJust (x:xs)))                
                         ++ " in Data property " ++ show name)           
         name = head $ map (\x -> case item x of
                    DLDataProperty nm _ _ _ _ _ -> nm
                    _                  -> error "No"
                   ) op    
         rAnnos = concat $ map r_annos op
         lAnnos = concat $ map l_annos op    
    in
        Annoted 
        {
            item = DLDataProperty name dom rn propsRel ochar para
        ,   opt_pos = nullRange
        ,   l_annos = lAnnos
        ,   r_annos = rAnnos
        }

bucketIrel :: [DLIndRel] -> [DLIndRel]
bucketIrel inR = 
    let 
        sameS = Set.toList $ Set.fromList $ concat $ map stripIRel $ filter (\x -> case x of
            DLSameAs _ -> True
            _          -> False) inR
        diffS = Set.toList $ Set.fromList $ concat $ map stripIRel $ filter (\x -> case x of
            DLDifferentFrom _ -> True
            _          -> False) inR
    in
        [] ++
            (if sameS /= [] then [DLSameAs sameS] else []) ++ 
            (if diffS /= [] then [DLDifferentFrom diffS] else []) 

stripIRel :: DLIndRel -> [Id]
stripIRel iR = case iR of
    DLSameAs y -> y
    DLDifferentFrom y -> y

uniteObjProps :: [Annoted DLBasicItem] -> [Annoted DLBasicItem]
uniteObjProps op = 
    map uniteObjProp $ getSame op

uniteObjProp :: [Annoted DLBasicItem] -> (Annoted DLBasicItem)
uniteObjProp op =
    let 
         para = unitePara $ map (\x -> case item x of
                    DLObjectProperty _ _ _ _ _ mpa -> mpa
                    _                  -> error "No"
                   ) op   
         dom  = bucketDomRn $ map fromJust $ Set.toList $ Set.fromList $ filter (/= Nothing) $ map (\x -> case item x of
                    DLObjectProperty _ dm _ _ _ _ -> dm
                    _                  -> error "No"
                   ) op   
         rn   = bucketDomRn $ map fromJust $ Set.toList $ Set.fromList $ filter (/=Nothing) $ map (\x -> case item x of
                    DLObjectProperty _ _ mrn _ _ _ -> mrn
                    _                  -> error "No"
                   ) op  
         propsRel = bucketPropsRel $ Set.toList $ Set.fromList $ concat $ map (\x -> case item x of
                    DLObjectProperty _ _ _ prel _ _ -> prel
                    _                  -> error "No"
                   ) op                   
         chars = Set.toList $ Set.fromList $ concat $ map (\x -> case item x of
                    DLObjectProperty _ _ _ _ char  _ -> char
                    _                  -> error "No"
                   ) op    
         name = head $ map (\x -> case item x of
                    DLObjectProperty nm _ _ _ _ _ -> nm
                    _                  -> error "No"
                   ) op    
         rAnnos = concat $ map r_annos op
         lAnnos = concat $ map l_annos op    
    in
        Annoted 
        {
            item = DLObjectProperty name dom rn propsRel chars para
        ,   opt_pos = nullRange
        ,   l_annos = lAnnos
        ,   r_annos = rAnnos
        }

bucketPropsRel :: [DLPropsRel] -> [DLPropsRel]
bucketPropsRel inR =
    let 
        subs = stripPRel $ filter (\x -> case x of
            DLSubProperty _ -> True
            _               -> False) inR
        invs = stripPRel $ filter (\x -> case x of
            DLInverses _ -> True
            _            -> False) inR 
        eqivs = stripPRel $ filter (\x -> case x of
            DLEquivalent _ -> True
            _              -> False) inR 
        dis = stripPRel $ filter (\x -> case x of
            DLDisjoint _ -> True
            _              -> False) inR                 
    in
        [] ++
        (if subs /= [] then [DLSubProperty subs] else []) ++
        (if invs /= [] then [DLInverses invs] else []) ++
        (if eqivs /= [] then [DLEquivalent eqivs] else []) ++
        (if dis /= [] then [DLDisjoint dis] else [])

stripPRel :: [DLPropsRel] -> [Id]
stripPRel inR = concat $ map (\x -> case x of
       DLSubProperty y -> y
       DLInverses    y -> y
       DLEquivalent  y -> y
       DLDisjoint    y -> y) inR

bucketDomRn :: [DLConcept] -> (Maybe DLConcept)
bucketDomRn lst = case lst of
    [] -> Nothing
    (x:xs) -> Just $ foldl (\z y -> DLAnd z y) x xs

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
		 							, symType = Indiv 
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
		DLDataProperty nm _ _ _ _ _-> 
				QualDataProp
					{
						nameD = nm
					}
		_                                          -> error "Runtime error!"

examineDataPropS :: DLBasicItem -> Set.Set Id -> DLSymbol
examineDataPropS bI _ = 
	case bI of
		DLDataProperty nm _ _ _ _ _-> 
				DLSymbol
					{
						symName = nm
					,   symType  = DataProp 
					}
		_                                          -> error "Runtime error!"
		
examineObjProp :: DLBasicItem -> Set.Set Id -> QualObjProp
examineObjProp bI _ = 
	case bI of
		DLObjectProperty nm _ _ _ _ _-> 
				QualObjProp
					{
						nameO = nm
					}
		_                                          -> error "Runtime error!"			
		
examineObjPropS :: DLBasicItem -> Set.Set Id -> DLSymbol
examineObjPropS bI _ = 
	case bI of
		DLObjectProperty nm _ _ _ _ _-> 
				DLSymbol
					{
						symName = nm
					,   symType = ObjProp
					}
		_                                          -> error "Runtime error!"	
		