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
import qualified Data.Set as Set
import Common.Result as Result
import qualified Data.Map as Map
import DL.AS
import DL.DLKeywords
import Data.Char

data DLSymbol = DLSymbol
	{
		symName :: Id
    ,   symType :: SymbType
	}
	deriving (Eq, Ord, Show)

data SymbType = ClassSym |
				DataProp  |
				ObjProp  |
				Indiv
				
	deriving (Eq, Ord, Show)
	
type RawDLSymbol = Id

symbol2raw :: DLSymbol -> RawDLSymbol
symbol2raw sm = symName sm

topSort :: Id
topSort = stringToId dlThing

bottomSort :: Id
bottomSort = stringToId dlNothing

dlinteger :: Id
dlinteger = stringToId dlInteger
	
dldata :: Id    
dldata = stringToId dlData

dlnonposint :: Id
dlnonposint = stringToId  dlNonPosInt
   
dlposint :: Id
dlposint = stringToId  dlPosInt   
   
dlnonnegint :: Id
dlnonnegint = stringToId dlNonNegInt
   
dlnegint :: Id
dlnegint = stringToId dlNegInt   
   
dlfloat :: Id 
dlfloat = stringToId dlFloat   
   
dlDefData :: Set.Set Id
dlDefData = Set.fromList [dldata, dlinteger, dlnonposint, dlposint, dlnonnegint, dlnegint, dlfloat]

isInteger :: Id -> Bool
isInteger iis = 
    let
        str = concat $ map tokStr $ getTokens iis
    in
        (and $ map isDigit $ str) || ((head str == '-') && (and $ map isDigit $ tail $ str)) ||
        ((head str == '+') && (and $ map isDigit $ tail $ str))

isFloat :: Id -> Bool
isFloat iis =
    let
        str = concat $ map tokStr $ getTokens iis
    in
        case (head str) of
            '+' ->
                let 
                    (h, t) = break (== '.') $ tail str
                in
                  (and $ map isDigit h) && (and $ map isDigit (tail t)) &&
                  ((t == []) == (tail t == []))
            '-' ->
                let 
                    (h, t) = break (== '.') $ tail str
                in
                  (and $ map isDigit h) && (and $ map isDigit (tail t)) &&
                  ((t == []) == (tail t == []))
            _   ->
                let 
                    (h, t) = break (== '.') $ str
                in
                  (and $ map isDigit h) && (and $ map isDigit (tail t)) &&
                  ((t == []) == (tail t == []))
                    
isDatatype :: Id -> Bool
isDatatype i = isInteger i || isFloat i
   
illegalId :: Id -> Bool
illegalId iis =      
    let
        str = concat $ map tokStr $ getTokens iis
    in  
        (head str == '+') || (head str == '-') || (isDigit $ head str)
   
instance Pretty DLSymbol where
	pretty = text . show

type Classes_map = Map.Map Id Id
type DataProps_map = Map.Map QualDataProp QualDataProp
type ObjectProps_map = Map.Map QualObjProp QualObjProp
type Individuals_map = Map.Map QualIndiv QualIndiv

data Sign = Sign
	{
		classes :: Set.Set Id
    ,   pData   :: Set.Set Id
	,   dataProps :: Set.Set QualDataProp
	,   objectProps :: Set.Set QualObjProp
	,   individuals :: Set.Set QualIndiv
	}
	deriving (Eq)

isClass :: Id -> Sign -> Bool
isClass i s = Set.member i $ classes s

isDataProp :: Id -> Sign -> Bool
isDataProp i s = Set.member i $ Set.map nameD $ dataProps s

isObjProp :: Id -> Sign -> Bool
isObjProp i s = Set.member i $ Set.map nameO $ objectProps s

isIndi :: Id -> Sign -> Bool
isIndi i s = Set.member i $ Set.map iid $ individuals s

isDefined :: Id -> Sign -> Bool
isDefined i s = isClass i s ||
                isDataProp i s ||
                isObjProp i s ||
                isIndi i s 

isSubSig :: Sign -> Sign -> Bool
isSubSig s1 s2 = (classes s1) `Set.isSubsetOf` (classes s2) &&
                 (dataProps s1) `Set.isSubsetOf` (dataProps s2) &&
                 (objectProps s1) `Set.isSubsetOf` (objectProps s2) &&
                 (individuals s1) `Set.isSubsetOf` (individuals s2)

uniteSigOK :: Sign -> Sign -> Sign
uniteSigOK s1 s2 =
    Sign
    {
        classes = (classes s1) `Set.union` (classes s2)
    ,   pData   = dlDefData
    ,   dataProps = (dataProps s1) `Set.union` (dataProps s2)
    ,   objectProps = (objectProps s1) `Set.union` (objectProps s2)
    ,   individuals = (individuals s1) `Set.union` (individuals s2)
    }

uniteSig :: Sign -> Sign -> Result Sign
uniteSig s1 s2 = message
    Sign
    {
        classes = (classes s1) `Set.union` (classes s2)
    ,   pData   = dlDefData    
    ,   dataProps = (dataProps s1) `Set.union` (dataProps s2)
    ,   objectProps = (objectProps s1) `Set.union` (objectProps s2)
    ,   individuals = (individuals s1) `Set.union` (individuals s2)
    }
    "All fine!"

data DLMorphism = DLMorphism
  { msource :: Sign
  , mtarget :: Sign
  , c_map   :: Classes_map
  , dp_map  :: DataProps_map
  , op_map  :: ObjectProps_map
  , i_map   :: Individuals_map
  } deriving (Eq, Show)

inclusionMor :: Sign -> Sign -> Result DLMorphism
inclusionMor s1 s2 =
    case s1 `isSubSig` s2 of
        True -> message
            DLMorphism
            {
                msource = s1
            ,   mtarget = s2
            ,   c_map = Set.fold (\x y-> Map.insert x x y) Map.empty $ classes s1
            ,  dp_map = Set.fold (\x y-> Map.insert x x y) Map.empty $ dataProps s1
            ,  op_map = Set.fold (\x y-> Map.insert x x y) Map.empty $ objectProps s1
            ,   i_map = Set.fold (\x y-> Map.insert x x y) Map.empty $ individuals s1
            }
            "All fine!"
        False -> fatal_error "Not a subsignature" nullRange

emptyMor :: DLMorphism  				
emptyMor = DLMorphism
 	{
 	 msource = emptyDLSig
 	,mtarget = emptyDLSig
 	,c_map   = Map.empty
 	, dp_map = Map.empty
 	, op_map = Map.empty
 	,  i_map = Map.empty
 	}

idMor :: Sign -> DLMorphism
idMor sig = emptyMor
	{
		msource = sig
	,   mtarget = sig
	,   c_map   = Set.fold (\x y -> Map.insert x x y) Map.empty $ classes sig
	,    dp_map = Set.fold (\x y -> Map.insert x x y) Map.empty $ dataProps sig
	,    op_map = Set.fold (\x y -> Map.insert x x y) Map.empty $ objectProps sig
	,     i_map = Set.fold (\x y -> Map.insert x x y) Map.empty $ individuals sig
	}

showSig ::  Sign -> String
showSig sg = "%[\n" ++
			 "Class: " ++ (concatComma $ map show $ Set.toAscList $ classes sg) ++ "\n" ++
             "Data: " ++ (concatComma $ map show $ Set.toAscList $ pData sg) ++ "\n" ++
			 "Data Properties: " ++ (concatComma $ map show $ Set.toAscList $ dataProps sg) ++ "\n" ++		
			 "Object Properties: " ++ (concatComma $ map show $ Set.toAscList $ objectProps sg) ++ "\n" ++		
			 "Individuals: " ++ (concatComma $ map show $ Set.toAscList $ individuals sg) ++ "\n"
			 ++ "\n]%"

instance Show Sign where
	show =  showSig
			
instance Pretty Sign where
	pretty sg = text $ show sg
	
data QualIndiv = QualIndiv
	{
		iid   :: Id
	,   types :: [Id]
	}
	deriving (Eq,Ord)

showIndiv :: QualIndiv -> String
showIndiv myId = (show $ iid myId)

instance Show QualIndiv where
	show = showIndiv

data QualDataProp = QualDataProp
	{
		nameD   :: Id
	}
	deriving (Eq,Ord)
	
data QualObjProp = QualObjProp
	{
		nameO   :: Id
	}
	deriving (Eq, Ord)

showDataProp :: QualDataProp -> String
showDataProp pp = (show $  nameD pp)

showObjProp :: QualObjProp -> String
showObjProp pp = (show $  nameO pp)

instance Show QualDataProp where
	show = showDataProp
	
instance Show QualObjProp where
	show = showObjProp
	
emptyDLSig :: Sign
emptyDLSig = Sign{
				  classes = bottomSort `Set.insert` (topSort `Set.insert` Set.empty)
                , pData   = dlDefData
				, dataProps = Set.empty
				, objectProps = Set.empty
                , individuals = Set.empty
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

map_maybe_class :: DLMorphism -> (Maybe Id) -> Result.Result (Maybe Id)
map_maybe_class mor inI =
    case inI of
        Nothing  -> return $ (Just topSort)
        Just inC ->
            do
                tinC <- Map.lookup inC $ c_map mor
                return $ return $ tinC

map_maybe_concept :: DLMorphism -> (Maybe DLConcept) -> Result.Result (Maybe DLConcept)
map_maybe_concept mor inI =
    case inI of
        Nothing  -> return $ (Just $ DLClassId topSort nullRange)
        Just inC ->
            do
                outC <- map_concept mor inC
                return $ Just $ outC

     -- | Mapping of concepts
map_concept :: DLMorphism -> DLConcept -> Result.Result DLConcept
map_concept mor con = case con of
    DLAnd c1 c2 _->
        do
            tc1 <- map_concept mor c1
            tc2 <- map_concept mor c2
            return $ DLAnd tc1 tc2 nullRange
    DLOr c1 c2 _->
        do
            tc1 <- map_concept mor c1
            tc2 <- map_concept mor c2
            return $ DLOr tc1 tc2 nullRange
    DLXor c1 c2 _->
        do
            tc1 <- map_concept mor c1
            tc2 <- map_concept mor c2
            return $ DLXor tc1 tc2 nullRange
    DLNot c1 _->
        do
            tc1 <- map_concept mor c1
            return $ DLNot tc1 nullRange
    DLOneOf cs _->
        do
            tcs <- mapM (\x -> Map.lookup x $ Map.map iid $ Map.mapKeys iid $ i_map mor) cs
            return $ DLOneOf tcs nullRange
    DLSome (DLClassId r _) c _->
        do
            let daMap = Map.union (Map.mapKeys (nameD) $ Map.map (nameD) $ dp_map mor) (Map.mapKeys (nameO) $ Map.map (nameO) $ op_map mor)
            tr <- Map.lookup r daMap
            cr <- map_concept mor c
            return $ DLSome (DLClassId tr nullRange) cr nullRange
    DLHas (DLClassId r _) c _->
        do
            let daMap = Map.union (Map.mapKeys (nameD) $ Map.map (nameD) $ dp_map mor) (Map.mapKeys (nameO) $ Map.map (nameO) $ op_map mor)
            tr <- Map.lookup r daMap
            cr <- map_concept mor c
            return $ DLHas (DLClassId tr nullRange) cr nullRange
    DLOnly (DLClassId r _) c _->
        do
            let daMap = Map.union (Map.mapKeys (nameD) $ Map.map (nameD) $ dp_map mor) (Map.mapKeys (nameO) $ Map.map (nameO) $ op_map mor)
            tr <- Map.lookup r daMap
            cr <- map_concept mor c
            return $ DLOnly (DLClassId tr nullRange) cr nullRange
    DLMin (DLClassId c1 _) i _ ->
        do
            let daMap = Map.union (Map.mapKeys (nameD) $ Map.map (nameD) $ dp_map mor) (Map.mapKeys (nameO) $ Map.map (nameO) $ op_map mor)
            tc1 <- Map.lookup c1 daMap
            return $ DLMin (DLClassId tc1 nullRange) i nullRange
    DLMax (DLClassId c1 _) i _->
        do
            let daMap = Map.union (Map.mapKeys (nameD) $ Map.map (nameD) $ dp_map mor) (Map.mapKeys (nameO) $ Map.map (nameO) $ op_map mor)
            tc1 <- Map.lookup c1 daMap        
            return $ DLMax (DLClassId tc1 nullRange) i nullRange
    DLExactly (DLClassId c1 _) i _->
        do
            let daMap = Map.union (Map.mapKeys (nameD) $ Map.map (nameD) $ dp_map mor) (Map.mapKeys (nameO) $ Map.map (nameO) $ op_map mor)
            tc1 <- Map.lookup c1 daMap
            return $ DLExactly (DLClassId tc1 nullRange) i nullRange
    DLValue (DLClassId r _) i _->
        do
            let daMap = Map.union (Map.mapKeys (nameD) $ Map.map (nameD) $ dp_map mor) (Map.mapKeys (nameO) $ Map.map (nameO) $ op_map mor)
            tr <- Map.lookup r daMap
            ti <- Map.lookup i $ Map.mapKeys iid $ Map.map iid $ i_map mor
            return $ DLValue (DLClassId tr nullRange) ti nullRange
    DLThat c1 c2 _->
        do
            tc1 <- map_concept mor c1
            tc2 <- map_concept mor c2
            return $ DLThat tc1 tc2 nullRange
    DLOnlysome (DLClassId r _) cs _->
        do
            let daMap = Map.union (Map.mapKeys (nameD) $ Map.map (nameD) $ dp_map mor) (Map.mapKeys (nameO) $ Map.map (nameO) $ op_map mor)
            tr  <- Map.lookup r daMap
            tcs <- mapM (\x -> map_concept mor x) cs
            return $ DLOnlysome (DLClassId tr nullRange) tcs nullRange
    DLClassId cid _->
        do
            rpl <- Map.lookup cid $ c_map mor
            return $ DLClassId rpl nullRange
    _             -> fatal_error ("Cannot determine mapping for: " ++ show con) nullRange

mapClassProperty :: DLMorphism -> DLClassProperty -> Result.Result DLClassProperty
mapClassProperty mor cp = case cp of
    DLSubClassof cs _->
        do
            tcs <- mapM (map_concept mor) cs
            return $ DLSubClassof tcs nullRange
    DLEquivalentTo cs _->
        do
            tcs <- mapM (map_concept mor) cs
            return $ DLEquivalentTo tcs nullRange
    DLDisjointWith cs _->
        do
            tcs <- mapM (map_concept mor) cs
            return $ DLDisjointWith tcs nullRange

map_facts :: DLMorphism -> DLFacts -> Result.Result DLFacts
map_facts mor fts =
    let
        propIdsMap = Map.mapKeys (nameO) $ Map.map (nameO) $ (op_map mor)
        dIdsMap = Map.mapKeys (nameD) $ Map.map (nameD) $ (dp_map mor)
    in
    case fts of
        DLPosFact (obi, iids) _->
            case isInteger iids of
                False ->
                    do
                        tobi <- Map.lookup obi propIdsMap
                        tiid <- Map.lookup iids $ Map.mapKeys (iid) $ Map.map (iid) $ i_map mor
                        return $ DLPosFact (tobi, tiid) nullRange
                True  ->
                     do
                        tobi <- Map.lookup obi dIdsMap
                        return $ DLPosFact (tobi, iids) nullRange                   
        DLNegFact (obi, iids) _->
            case isInteger iids of
                False ->
                    do
                        tobi <- Map.lookup obi propIdsMap
                        tiid <- Map.lookup iids $ Map.mapKeys (iid) $ Map.map (iid) $ i_map mor
                        return $ DLNegFact (tobi, tiid) nullRange
                True  ->
                     do
                        tobi <- Map.lookup obi dIdsMap 
                        return $ DLNegFact (tobi, iids) nullRange      

map_type :: DLMorphism -> DLType -> Result.Result DLType
map_type mor tp = case tp of
    DLType iids _->
        do
            tiids <- mapM (\x -> Map.lookup x $ c_map mor) iids
            return $ DLType tiids nullRange

map_ind_rel :: DLMorphism -> DLIndRel -> Result.Result DLIndRel
map_ind_rel mor ind =
    let
        ind_map = Map.mapKeys (iid) $ Map.map (iid) $ i_map mor
    in
    case ind of
        DLDifferentFrom inds _->
            do
                tinds <- mapM (\x -> Map.lookup x ind_map) inds
                return $ DLDifferentFrom tinds nullRange
        DLSameAs inds _->
            do
                tinds <- mapM (\x -> Map.lookup x ind_map) inds
                return $ DLSameAs tinds nullRange

map_props_rel ::  DLMorphism -> DLPropsRel -> Result.Result DLPropsRel
map_props_rel mor props =
    let
        op_p = Map.mapKeys (nameO) $ Map.map (nameO) $ (op_map mor)
        dp_p = Map.mapKeys (nameD) $ Map.map (nameD) $ (dp_map mor)
        p_p  = Map.union op_p dp_p
    in
    case props of
        DLSubProperty iids _->
            do
                tiids <- mapM (\x -> Map.lookup x p_p) iids
                return $ DLSubProperty tiids nullRange
        DLInverses iids _->
            do
                tiids <- mapM (\x -> Map.lookup x p_p) iids
                return $ DLInverses tiids nullRange
        DLEquivalent iids _->
            do
                tiids <- mapM (\x -> Map.lookup x p_p) iids
                return $ DLEquivalent tiids nullRange
        DLDisjoint iids _->
            do
                tiids <- mapM (\x -> Map.lookup x p_p) iids
                return $ DLDisjoint tiids nullRange

map_sentence :: DLMorphism -> DLBasicItem -> Result.Result DLBasicItem
map_sentence mor sen =
    case sen of
        DLClass iic cp pa _ ->
            do
                tiid <- Map.lookup iic $ c_map mor
                tcp  <- mapM (mapClassProperty mor) cp
                return $ DLClass tiid tcp pa nullRange
        DLObjectProperty inC inD inR inRel inChar pa _ ->
            do
                tinC <- Map.lookup inC $ Map.mapKeys (nameO) $ Map.map (nameO) $ (op_map mor)
                tinD <- map_maybe_concept mor inD
                tinR <- map_maybe_concept mor inR
                tinRel <- mapM (map_props_rel mor) inRel
                return $ DLObjectProperty tinC tinD tinR tinRel inChar pa nullRange
        DLDataProperty inC inD inR inRel inChar pa _ ->
            do
                tinC <- Map.lookup inC $ Map.mapKeys (nameD) $ Map.map (nameD) $ (dp_map mor)
                tinD <- map_maybe_concept mor inD
                tinR <- map_maybe_concept mor inR
                tinRel <- mapM (map_props_rel mor) inRel
                return $ DLDataProperty tinC tinD tinR tinRel inChar pa nullRange
        DLIndividual inC mtype fts indRel pa _ ->
            do
                tinC <- Map.lookup inC $ Map.mapKeys (iid) $ Map.map (iid) $
                            i_map mor
                tT   <- map_mDLType mor mtype
                tfts <- mapM (map_facts mor) fts
                tind <- mapM (map_ind_rel mor) indRel
                return $ DLIndividual tinC tT tfts tind pa nullRange
        DLMultiIndi inCs mtype fts rel pa _ ->
            do
                tinC <- mapM (\x -> Map.lookup x $ Map.mapKeys (iid) $ Map.map (iid) $
                            i_map mor) inCs
                tT   <- map_mDLType mor mtype
                tfts <- mapM (map_facts mor) fts
                return $ DLMultiIndi tinC tT tfts rel pa nullRange

map_mDLType :: DLMorphism -> Maybe DLType -> Result.Result (Maybe DLType)
map_mDLType mor mT =
    case mT of
        Just x ->
            do
                tx <- map_type mor x
                return $ Just tx
        Nothing ->
            return $ Nothing
