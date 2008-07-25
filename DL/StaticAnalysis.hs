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
        ( basic_DL_analysis
        )
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
import Control.Monad

basic_DL_analysis :: (DLBasic, Sign,GlobalAnnos) ->
                      Result (DLBasic, ExtSign Sign DLSymbol,[Named DLBasicItem])
basic_DL_analysis (spec, sig, _) =
    let
        sens = case spec of
                    DLBasic x -> x
        [cCls, cObjProps, cDtProps, cIndi, cMIndi] = splitSentences sens
        oCls        = uniteClasses cCls
        oObjProps   = uniteObjProps cObjProps
        oDtProps    = uniteDataProps cDtProps
        oIndi       = uniteIndividuals (cIndi ++ splitUpMIndis cMIndi)
        cls         = getClasses $ map item $ oCls
        dtPp        = getDataProps (map item oDtProps) (cls)
        obPp        = getObjProps (map item oObjProps) (cls)
        (ind, mcls) = getIndivs (map item oIndi) (cls)
        outSig      = emptyDLSig
                          {
                              classes      = cls `Set.union` mcls
                          ,   dataProps    = dtPp
                          ,   objectProps  = obPp
                          ,   individuals  = ind
                          }
    in
      do
        outImpSig <- addImplicitDeclarations outSig (oCls ++ oObjProps ++ oDtProps ++ oIndi)
        case Set.intersection (Set.map nameD $ dataProps outImpSig) (Set.map nameO $ objectProps outImpSig) == Set.empty of
            True ->
                 return (spec, ExtSign{
                          plainSign = outImpSig `uniteSigOK` sig
                        ,nonImportedSymbols = generateSignSymbols outImpSig
                        }
                        , map (makeNamedSen) $ concat [oCls, oObjProps, oDtProps, oIndi])
            False ->
                do
                    let doubles = Set.toList $ Set.intersection (Set.map nameD $ dataProps outImpSig) (Set.map nameO $ objectProps outImpSig)
                    fail ("Sets of Object and Data Properties are not disjoint: " ++ show doubles)

-- | Generation of symbols out of a signature
generateSignSymbols :: Sign -> Set.Set DLSymbol
generateSignSymbols inSig =
    let
        cls = Set.map (\x -> DLSymbol
            {
                symName = x
            ,   symType = ClassSym
            }) $ classes inSig
        dtP = Set.map (\x -> DLSymbol
            {
                symName = x
            ,   symType = DataProp
            }) $ Set.map nameD $ dataProps inSig
        obP = Set.map (\x -> DLSymbol
            {
                symName = x
            ,   symType = ObjProp
            }) $ Set.map nameO $ objectProps inSig
        inD = Set.map (\x -> DLSymbol
            {
                symName = x
            ,   symType = Indiv
            }) $ Set.map iid $ individuals inSig
    in
        cls `Set.union` dtP `Set.union` obP `Set.union` inD

isLegalSuperProperty :: Id -> DLPropertyComp -> Bool
isLegalSuperProperty cId cProps =
    case cProps of
        DLPropertyComp cPI ->
            case length cPI > 1 of
                True -> cId `Set.notMember` ( Set.fromList $ tail $ reverse $ tail cPI )
                False -> True

-- | Functions for adding implicitly defined stuff to signature
addImplicitDeclarations :: Sign -> [Annoted DLBasicItem] -> Result Sign
addImplicitDeclarations inSig sens =
    do
        foldM (\ s a -> do
                    s2 <- addImplicitDeclaration s a
                    uniteSig s s2) inSig sens

addImplicitDeclaration :: Sign -> Annoted DLBasicItem -> Result Sign
addImplicitDeclaration inSig sens =
    case item sens of
        DLClass _ props _ _ ->
          do
            oSig <- mapM (\x ->
                        case x of
                            DLSubClassof ps _->
                                do
                                    sig <- mapM (\y -> analyseConcepts inSig y True) ps
                                    foldM (uniteSig) emptyDLSig sig
                            DLEquivalentTo ps _->
                                do
                                    sig <- mapM (\y -> analyseConcepts inSig y True) ps
                                    foldM (uniteSig) emptyDLSig sig
                            DLDisjointWith ps _->
                                do
                                    sig <- mapM (\y -> analyseConcepts inSig y True) ps
                                    foldM (uniteSig) emptyDLSig sig) props
            foldM (uniteSig) emptyDLSig oSig
        DLObjectProperty nt mC1 mC2 propRel _ _ _ ->
                  do
                    c1 <- analyseMaybeConcepts inSig mC1 False
                    c2 <- analyseMaybeConcepts inSig mC2 False
                    c3 <- mapM (\x ->
                        case x of
                            DLSubProperty r _->
                                do
                                    foldM (\z y -> addToObjProps z inSig y) emptyDLSig r
                            DLInverses r _->
                                do
                                    foldM (\z y -> addToObjProps z inSig y) emptyDLSig r
                            DLEquivalent r _->
                                do
                                    foldM (\z y -> addToObjProps z inSig y) emptyDLSig r
                            DLDisjoint r _->
                                do
                                    foldM (\z y -> addToObjProps z inSig y) emptyDLSig r
                            DLSuperProperty r _ ->
                             do
                              foldM (\a b ->
                                 case b of
                                    DLPropertyComp c ->
                                        case isLegalSuperProperty nt b of
                                            True  ->
                                                (foldM (\z y -> addToObjProps z inSig y) a c)
                                            False -> fail (show b ++ " does not fulfill the SROIQ restrictions for " ++ show nt)
                                                ) emptyDLSig r

                            ) propRel
                    c4 <- foldM (uniteSig) emptyDLSig c3
                    ct <- c1 `uniteSig` c2
                    ct `uniteSig` c4
        DLDataProperty nt mC1 mC2 propRel _ _ _ ->
            do
                analyseMaybeConcepts inSig mC1 True
                analyseMaybeDataConcepts inSig mC2 True
                c3 <- mapM (\x ->
                    case x of
                        DLSubProperty r _->
                            do
                                foldM (\z y -> addToDataProps z inSig y) emptyDLSig r
                        DLInverses r _->
                            do
                                foldM (\z y -> addToDataProps z inSig y) emptyDLSig r
                        DLEquivalent r _->
                            do
                                foldM (\z y -> addToDataProps z inSig y) emptyDLSig r
                        DLDisjoint r _->
                            do
                                foldM (\z y -> addToDataProps z inSig y) emptyDLSig r
                        DLSuperProperty r _ ->
                            do
                              foldM (\a b ->
                                 case b of
                                    DLPropertyComp c ->
                                        case isLegalSuperProperty nt b of
                                            True  ->
                                                (foldM (\z y -> addToDataProps z inSig y) a c)
                                            False -> fail (show b ++ " does not fulfill the SROIQ restrictions for " ++ show nt)
                                                ) emptyDLSig r

                            ) propRel
                c4 <- foldM (uniteSig) emptyDLSig c3
                return c4
        DLIndividual _ mType ftc indRel _ _ ->
             do
                tt <- (case mType of
                    Nothing -> return emptyDLSig
                    Just rp  ->
                        case rp of
                            DLType r _->
                                foldM (\z y -> addToClasses z inSig y) emptyDLSig r)
                it <- mapM (\x ->
                    case x of
                        DLSameAs r _-> foldM (\z y -> addToIndi z inSig y) emptyDLSig r
                        DLDifferentFrom r _-> foldM (\z y -> addToIndi z inSig y) emptyDLSig r) indRel
                it2 <- foldM (uniteSig) emptyDLSig it
                ftt <- mapM (\x -> case x of
                    DLPosFact (oP, indi) rn->
                            case Set.member (QualDataProp oP) (dataProps inSig) of
                                False ->
                                        case isDatatype indi of
                                            False ->
                                                case illegalId indi of
                                                    False ->
                                                        do
                                                            nOps <- addToObjProps emptyDLSig inSig oP
                                                            addToIndi nOps inSig indi
                                                    True  -> fatal_error ("Illegal indentifier for individual: " ++ show indi) rn
                                            True  ->
                                                do
                                                    addToDataProps emptyDLSig inSig oP
                                True ->
                                      case isDatatype indi of
                                        True -> return $ emptyDLSig
                                        False -> fatal_error "Unknown Datatype" rn
                    DLNegFact (oP, indi) rn->
                            case Set.member (QualDataProp oP) (dataProps inSig) of
                                False ->
                                        case isDatatype indi of
                                            False ->
                                                case illegalId indi of
                                                    False ->
                                                        do
                                                            nOps <- addToObjProps emptyDLSig inSig oP
                                                            addToIndi nOps inSig indi
                                                    True  -> fatal_error ("Illegal indentifier for individual: " ++ show indi) rn
                                            True  ->
                                                do
                                                    addToDataProps emptyDLSig inSig oP
                                True ->
                                      case isDatatype indi of
                                        True -> return $ emptyDLSig
                                        False -> fatal_error "Unknown Datatype" rn
                            ) ftc
                ftf <- foldM (uniteSig) emptyDLSig ftt
                oS <- tt `uniteSig` it2
                oss <- ftf `uniteSig` oS
                return oss
        _ -> fail ("Error in derivation of signature at: " ++ show (item sens))

analyseMaybeConcepts :: Sign -> Maybe DLConcept -> Bool -> Result Sign
analyseMaybeConcepts inSig inC isData =
    case inC of
        Nothing ->
            do
                return emptyDLSig
        Just x  ->
            analyseConcepts inSig x isData

analyseMaybeDataConcepts :: Sign -> Maybe DLConcept -> Bool -> Result Sign
analyseMaybeDataConcepts _ inC _ =
    case inC of
        Nothing ->
            do
                return emptyDLSig
        Just x  ->
            case x of
                DLClassId y rn->
                    case Set.member y dlDefData of
                        True  -> return emptyDLSig
                        False -> fatal_error "Unknown Data Type" rn
                _ -> fail "Unknown Data Type"

isDType :: DLConcept -> Bool
isDType dt =
    case dt of
      DLClassId c _ -> c `Set.member` dlDefData
      _             -> False

analyseConcepts :: Sign -> DLConcept -> Bool -> Result Sign -- Bool is true if DataProperty
analyseConcepts inSig inC isData =
        case inC of
            DLAnd c1 c2 _->
                do
                    recS1 <- analyseConcepts inSig c1 isData
                    recS2 <- analyseConcepts inSig c2 isData
                    oSig <- uniteSig recS1 recS2
                    return oSig
            DLOr c1 c2 _->
                do
                    recS1 <- analyseConcepts inSig c1 isData
                    recS2 <- analyseConcepts inSig c2 isData
                    oSig <- uniteSig recS1 recS2
                    return oSig
            DLXor c1 c2 _->
                do
                    recS1 <- analyseConcepts inSig c1 isData
                    recS2 <- analyseConcepts inSig c2 isData
                    oSig <- uniteSig recS1 recS2
                    return oSig
            DLNot c1 _->
                do
                    recS1 <- analyseConcepts inSig c1 isData
                    return recS1
            DLSome r c _->
                  if isDType c
                  then
                      if isData
                      then
                          addToDataProps emptyDLSig inSig r
                      else
                          fail $ "Trying to define dataproperty " ++ show r
                                   ++ " in relation to Object Property"
                  else
                      do
                        recSig <- (analyseConcepts inSig c isData)
                        addToObjProps recSig inSig r
            DLOneOf ids _->
                do
                    foldM (\x y -> addToIndi x inSig y) emptyDLSig ids
            DLHas r c _->
                        case isDatatype c of
                          True  -> addToDataProps emptyDLSig inSig r
                          False ->
                              do
                                   withr <- addToObjProps emptyDLSig inSig r
                                   addToIndi emptyDLSig withr c
            DLOnly r c _->
                  if isDType c
                  then
                      if isData
                      then
                          addToDataProps emptyDLSig inSig r
                      else
                          fail $ "Trying to define dataproperty " ++ show r
                                   ++ " in relation to Object Property"
                  else
                      do
                        recSig <- (analyseConcepts inSig c isData)
                        addToObjProps recSig inSig r
            DLOnlysome r c _-> analyseConcepts inSig (expand (DLOnlysome r c nullRange)) isData
            DLMin r _ cp _->
                do
                    cps <- (\x -> case x of
                        Nothing -> return emptyDLSig
                        Just y  -> analyseConcepts inSig y isData) cp
                    ops <- addToDataProps emptyDLSig inSig r
                    (cps `uniteSig` ops)
            DLMax r _ cp _->
                do
                    cps <- (\x -> case x of
                        Nothing -> return emptyDLSig
                        Just y  -> analyseConcepts inSig y isData) cp
                    ops <- addToDataProps emptyDLSig inSig r
                    (cps `uniteSig` ops)
            DLExactly r _ cp _->
                do
                    cps <- (\x -> case x of
                        Nothing -> return emptyDLSig
                        Just y  -> analyseConcepts inSig y isData) cp
                    ops <- addToDataProps emptyDLSig inSig r
                    (cps `uniteSig` ops)
            DLValue r c _->
               do
                sig <- addToObjProps emptyDLSig inSig r
                addToIndi sig inSig c
            DLClassId r _->
                addToClasses emptyDLSig inSig r
            DLSelf _ ->
                return inSig

addToObjProps :: Sign -> Sign -> Id -> Result Sign
addToObjProps recSig inSig r =
      if (not (isDataProp r inSig))
        then
         do
           uniteSig emptyDLSig{objectProps=Set.singleton $ QualObjProp r} recSig
        else
         do
           fatal_error (show r ++ " is already a Data Property") $ posOfId r

addToDataProps :: Sign -> Sign -> Id -> Result Sign
addToDataProps recSig inSig r =
      if (not (isObjProp r inSig))
        then
         do
           uniteSig emptyDLSig{dataProps=Set.singleton $ QualDataProp r} recSig
        else
         do
           fatal_error (show r ++ " is already an Object Property") $ posOfId r

addToClasses :: Sign -> Sign -> Id -> Result Sign
addToClasses recSig _ r =
        uniteSig emptyDLSig{classes=Set.singleton r} recSig

addToIndi :: Sign -> Sign -> Id -> Result Sign
addToIndi recSig _ r =
        uniteSig emptyDLSig{individuals=Set.singleton $ QualIndiv r [topSort]} recSig

splitUpMIndis :: [Annoted DLBasicItem] -> [Annoted DLBasicItem]
splitUpMIndis inD = concat $ map splitUpMIndi inD

splitUpMIndi :: Annoted DLBasicItem -> [Annoted DLBasicItem]
splitUpMIndi inD =
    let
        (idDs, dType, dFacts, eql, pa, rn)   = (\x -> case x of
            DLMultiIndi idS dlT fts eqlD para rn1-> (idS, dlT, fts, eqlD, para, rn1)
            _                                -> error "no") $ item inD
        idSet = Set.fromList idDs
        rAnnos = r_annos inD
        lAnnos = l_annos inD
    in
        case eql of
            Nothing -> map (\x -> Annoted
                {
                    item = DLIndividual x dType dFacts [] pa rn
                ,   opt_pos = rn
                ,   l_annos = lAnnos
                ,   r_annos = rAnnos
                }) idDs
            (Just DLSame) -> map (\x -> Annoted
                {
                    item = DLIndividual x dType dFacts [DLSameAs (Set.toList (Set.delete x idSet)) rn] pa rn
                ,   opt_pos = rn
                ,   l_annos = lAnnos
                ,   r_annos = rAnnos
                }) idDs
            (Just DLDifferent) -> map (\x -> Annoted
                {
                    item = DLIndividual x dType dFacts [DLDifferentFrom (Set.toList (Set.delete x idSet)) rn] pa rn
                ,   opt_pos = rn
                ,   l_annos = lAnnos
                ,   r_annos = rAnnos
                }) idDs

-- | Union of blocks with the same name
uniteIndividuals :: [Annoted DLBasicItem] -> [Annoted DLBasicItem]
uniteIndividuals inds =
    map uniteIndividual $ getSame inds

uniteIndividual :: [Annoted DLBasicItem] -> (Annoted DLBasicItem)
uniteIndividual inds =
    let
          name = head $ map (\x -> case item x of
                    DLIndividual nm _ _ _ _ _-> nm
                    _                       -> error "No"
                   ) inds
          rn   = foldl appRange nullRange $ map (\x -> case item x of
                    DLIndividual _ _ _ _ _ rn1-> rn1
                    _                       -> error "No"
                   ) inds
          para = unitePara $ map (\x -> case item x of
                    DLIndividual _ _ _ _ mpa _-> mpa
                    _                        -> error "No"
                   ) inds
          tpes = (\x -> case x of
            [] -> Nothing
            y  -> Just $ DLType y rn) $
            Set.toList $ Set.fromList $ concat $ map (\x -> case x of
                    DLType y _-> y) $ map fromJust $ filter (/=Nothing) $ map (\x -> case item x of
                    DLIndividual _ tp _ _ _ _-> tp
                    _                       -> error "No"
                   ) inds
          fts = Set.toList $ Set.fromList $ concat $ map (\x -> case item x of
                    DLIndividual _ _ ft _ _ _-> ft
                    _                       -> error "No"
                   ) inds
          iRel = bucketIrel $ Set.toList $ Set.fromList $ concat $ map (\x -> case item x of
                    DLIndividual _ _ _ iR _ _-> iR
                    _                       -> error "No"
                   ) inds
          rAnnos = concat $ map r_annos inds
          lAnnos = concat $ map l_annos inds
    in
        Annoted
        {
            item = DLIndividual name tpes fts iRel para rn
        ,   opt_pos = rn
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
                    DLDataProperty _ _ _ _ _ mpa _-> mpa
                    _                  -> error "No"
                   ) op
         dom  = bucketDomRn $ map fromJust $ Set.toList $ Set.fromList $ filter (/= Nothing) $ map (\x -> case item x of
                    DLDataProperty _ dm _ _ _ _ _-> dm
                    _                  -> error "No"
                   ) op
         rn   = bucketDomRn $ map fromJust $ Set.toList $ Set.fromList $ filter (/=Nothing) $ map (\x -> case item x of
                    DLDataProperty _ _ mrn _ _ _ _-> mrn
                    _                  -> error "No"
                   ) op
         propsRel = bucketPropsRel $ Set.toList $ Set.fromList $ concat $ map (\x -> case item x of
                    DLDataProperty _ _ _ prel _ _ _-> prel
                    _                  -> error "No"
                   ) op
         chars = filter (/= Nothing) $ map (\x -> case item x of
                    DLDataProperty _ _ _ _ char  _ _-> char
                    _                  -> error "No"
                   ) op
         ochar = case chars of
            [] -> Nothing
            (x:xs) -> case length (map fromJust (x:xs)) == length (filter (== DLFunctional) $ map fromJust (x:xs)) of
                True -> Just DLFunctional
                _    -> error ("Wrong characteristics " ++ (concatComma $ map show (filter (/=DLFunctional) $ map fromJust (x:xs)))
                         ++ " in Data property " ++ show name)
         name = head $ map (\x -> case item x of
                    DLDataProperty nm _ _ _ _ _ _-> nm
                    _                  -> error "No"
                   ) op
         rng  = foldl appRange nullRange $ map (\x -> case item x of
                    DLDataProperty _ _ _ _ _ _ rn1-> rn1
                    _                  -> error "No"
                   ) op
         rAnnos = concat $ map r_annos op
         lAnnos = concat $ map l_annos op
    in
        Annoted
        {
            item = DLDataProperty name dom rn propsRel ochar para rng
        ,   opt_pos = rng
        ,   l_annos = lAnnos
        ,   r_annos = rAnnos
        }

bucketIrel :: [DLIndRel] -> [DLIndRel]
bucketIrel inR =
    let
        sameS = Set.toList $ Set.fromList $ concat $ map stripIRel $ filter (\x -> case x of
            DLSameAs _ _-> True
            _          -> False) inR
        sameR = foldl appRange nullRange $ map (\x -> case x of
                        DLSameAs _ rn1 -> rn1
                        _                -> error "No") $
                filter (\x -> case x of
                            DLSameAs _ _-> True
                            _           -> False) inR
        diffS = Set.toList $ Set.fromList $ concat $ map stripIRel $ filter (\x -> case x of
            DLDifferentFrom _ _-> True
            _          -> False) inR
        diffR = foldl appRange nullRange $ map (\x -> case x of
                        DLDifferentFrom _ rn1 -> rn1
                        _                -> error "No") $
                filter (\x -> case x of
                            DLDifferentFrom _ _-> True
                            _           -> False) inR
    in
        [] ++
            (if sameS /= [] then [DLSameAs sameS sameR] else []) ++
            (if diffS /= [] then [DLDifferentFrom diffS diffR] else [])

stripIRel :: DLIndRel -> [Id]
stripIRel iR = case iR of
    DLSameAs y _-> y
    DLDifferentFrom y _-> y

uniteObjProps :: [Annoted DLBasicItem] -> [Annoted DLBasicItem]
uniteObjProps op =
    map uniteObjProp $ getSame op

uniteObjProp :: [Annoted DLBasicItem] -> (Annoted DLBasicItem)
uniteObjProp op =
    let
         para = unitePara $ map (\x -> case item x of
                    DLObjectProperty _ _ _ _ _ mpa _-> mpa
                    _                  -> error "No"
                   ) op
         dom  = bucketDomRn $ map fromJust $ Set.toList $ Set.fromList $ filter (/= Nothing) $ map (\x -> case item x of
                    DLObjectProperty _ dm _ _ _ _ _-> dm
                    _                  -> error "No"
                   ) op
         rn   = bucketDomRn $ map fromJust $ Set.toList $ Set.fromList $ filter (/=Nothing) $ map (\x -> case item x of
                    DLObjectProperty _ _ mrn _ _ _ _-> mrn
                    _                  -> error "No"
                   ) op
         propsRel = bucketPropsRel $ Set.toList $ Set.fromList $ concat $ map (\x -> case item x of
                    DLObjectProperty _ _ _ prel _ _ _-> prel
                    _                  -> error "No"
                   ) op
         chars = Set.toList $ Set.fromList $ concat $ map (\x -> case item x of
                    DLObjectProperty _ _ _ _ char  _ _-> char
                    _                  -> error "No"
                   ) op
         name = head $ map (\x -> case item x of
                    DLObjectProperty nm _ _ _ _ _ _-> nm
                    _                  -> error "No"
                   ) op
         rng = foldl appRange nullRange $ map (\x -> case item x of
                    DLObjectProperty _ _ _ _ _ _ rn1-> rn1
                    _                  -> error "No"
                   ) op
         rAnnos = concat $ map r_annos op
         lAnnos = concat $ map l_annos op
    in
        Annoted
        {
            item = DLObjectProperty name dom rn propsRel chars para rng
        ,   opt_pos = rng
        ,   l_annos = lAnnos
        ,   r_annos = rAnnos
        }

bucketPropsRel :: [DLPropsRel] -> [DLPropsRel]
bucketPropsRel inR =
    let
        subs = stripPRel $ filter (\x -> case x of
            DLSubProperty _ _-> True
            _               -> False) inR
        subsR = stripPRelRng $ filter (\x -> case x of
            DLSubProperty _ _-> True
            _               -> False) inR
        invs = stripPRel $ filter (\x -> case x of
            DLInverses _ _-> True
            _            -> False) inR
        invsR = stripPRelRng $ filter (\x -> case x of
            DLInverses _ _-> True
            _            -> False) inR
        eqivs = stripPRel $ filter (\x -> case x of
            DLEquivalent _ _-> True
            _              -> False) inR
        eqivsR = stripPRelRng $ filter (\x -> case x of
            DLEquivalent _ _-> True
            _              -> False) inR
        dis = stripPRel $ filter (\x -> case x of
            DLDisjoint _ _-> True
            _              -> False) inR
        disR = stripPRelRng $ filter (\x -> case x of
            DLDisjoint _ _-> True
            _              -> False) inR
        sups = Set.toList $ Set.fromList $ concat $ map (\y -> case y of
                DLSuperProperty z _ -> z
                _                   -> error "Nope") $
                filter (\x -> case x of
                DLSuperProperty _ _-> True
                _               -> False) inR
        supsR = stripPRelRng $filter (\x -> case x of
            DLSuperProperty _ _-> True
            _               -> False) inR
    in
        [] ++
        (if subs /= [] then [DLSubProperty subs subsR] else []) ++
        (if invs /= [] then [DLInverses invs invsR] else []) ++
        (if eqivs /= [] then [DLEquivalent eqivs eqivsR] else []) ++
        (if dis /= [] then [DLDisjoint dis disR] else []) ++
        (if sups /=[] then [DLSuperProperty sups supsR] else [])

stripPRel :: [DLPropsRel] -> [Id]
stripPRel inR = concat $ map (\x -> case x of
       DLSubProperty y _-> y
       DLInverses    y _-> y
       DLEquivalent  y _-> y
       DLDisjoint    y _-> y
       DLSuperProperty _ _ -> error "I deny to do this") inR

stripPRelRng :: [DLPropsRel] -> Range
stripPRelRng inR = foldl appRange nullRange $  map (\x -> case x of
       DLSubProperty _ y -> y
       DLInverses    _ y -> y
       DLEquivalent  _ y -> y
       DLDisjoint    _ y -> y
       DLSuperProperty _ y -> y) inR

bucketDomRn :: [DLConcept] -> (Maybe DLConcept)
bucketDomRn lst = case lst of
    [] -> Nothing
    (x:xs) -> Just $ foldl (\z y -> DLAnd z y nullRange) x xs

-- | Union of class definitions in different blocks
uniteClasses :: [Annoted DLBasicItem] -> [Annoted DLBasicItem]
uniteClasses cls =
        map uniteClass $ getSame cls

uniteClass :: [Annoted DLBasicItem] -> (Annoted DLBasicItem)
uniteClass cls =
    let
        para = map (\x -> case item x of
                    DLClass _ _ mpa _-> mpa
                    _                  -> error "No"
                   ) cls
        props = concat $ map (\x -> case item x of
                    DLClass _ p _ _-> p
                    _                  -> error "No"
                   ) cls
        name = map (\x -> case item x of
                    DLClass n _ _ _-> n
                    _                  -> error "No"
                   ) cls
        rng = foldl appRange nullRange $ map (\x -> case item x of
                    DLClass _ _ _ n-> n
                    _                  -> error "No"
                   ) cls
        rAnnos = concat $ map r_annos cls
        lAnnos = concat $ map l_annos cls
    in
        Annoted
        {
            item = DLClass (head name) (uniteProps props) (unitePara para) rng
        ,   opt_pos = rng
        ,   l_annos = lAnnos
        ,   r_annos = rAnnos
        }
    where
        uniteProps :: [DLClassProperty] -> [DLClassProperty]
        uniteProps ps =
            let
                subs = Set.toList $ Set.fromList $ concat $ map (\x -> case x of
                            DLSubClassof y _ -> y
                            _              -> error "No") $ filter (\x -> case x of
                        DLSubClassof _ _-> True
                        _              -> False) ps
                subsR = foldl appRange nullRange $ map (\x -> case x of
                            DLSubClassof _ y -> y
                            _              -> error "No") $ filter (\x -> case x of
                        DLSubClassof _ _-> True
                        _              -> False) ps
                equiv = Set.toList $ Set.fromList $ concat $ map (\x -> case x of
                            DLEquivalentTo y _-> y
                            _              -> error "No") $ filter (\x -> case x of
                        DLEquivalentTo _ _-> True
                        _              -> False) ps
                equivR = foldl appRange nullRange $ map (\x -> case x of
                            DLEquivalentTo _ y-> y
                            _              -> error "No") $ filter (\x -> case x of
                        DLEquivalentTo _ _-> True
                        _              -> False) ps
                dis   = Set.toList $ Set.fromList $ concat $ map (\x -> case x of
                            DLDisjointWith y _-> y
                            _              -> error "No") $ filter (\x -> case x of
                        DLDisjointWith _ _-> True
                        _              -> False) ps
                disR  = foldl appRange nullRange $ map (\x -> case x of
                            DLDisjointWith _ y-> y
                            _              -> error "No") $ filter (\x -> case x of
                        DLDisjointWith _ _-> True
                        _              -> False) ps

            in
                [] ++
                    (if subs /= [] then ([DLSubClassof subs subsR]) else []) ++
                    (if equiv /= [] then ([DLEquivalentTo equiv equivR]) else []) ++
                    (if dis /= [] then ([DLDisjointWith dis disR]) else [])

-- | Union of Paraphrases
unitePara :: [Maybe DLPara] -> (Maybe DLPara)
unitePara pa =
    case allNothing pa of
        True  -> Nothing
        False ->
            let
                paraStrings =
                    concat $ map (\x -> case x of
                        DLPara y _-> y) $
                    map fromJust $ filter (\x -> x /= Nothing) pa
                cds = getLangCodes paraStrings
                outPara = map (\x -> concatPara x paraStrings) cds
            in
                Just $ DLPara outPara nullRange
    where
        allNothing :: [Maybe DLPara] -> Bool
        allNothing pan = and $ map (== Nothing) pan

        getLangCodes :: [(String, String)] -> [String]
        getLangCodes cds = Set.toList $ Set.fromList $ map (\(x,_) -> x) cds

        concatPara :: String -> [(String, String)] -> (String,String)
        concatPara cd paras = (cd, concat $ map (\(_,y) -> y) $ filter (\(x,_) -> x == cd) paras)

getSame :: [Annoted DLBasicItem] -> [[Annoted DLBasicItem]]
getSame x = case x of
    []    -> []
    (z:zs)  ->  let
                 (p1, p2) = partition (\y -> getName z == getName y) (z:zs)
              in
                [p1] ++ (getSame p2)

getName :: Annoted DLBasicItem -> Id
getName x = case item x of
    DLClass  n _ _ _-> n
    DLObjectProperty n _ _ _ _ _ _-> n
    DLDataProperty n _ _ _ _ _ _-> n
    DLIndividual n _ _ _ _ _-> n
    DLMultiIndi _ _ _ _ _ _-> error "No"

splitSentences :: [Annoted DLBasicItem] -> [[Annoted DLBasicItem]]
splitSentences sens =
    let
        cls = filter (\x -> case item x of
                        DLClass _ _ _ _-> True
                        _             -> False) sens
        objProp = filter (\x -> case item x of
                DLObjectProperty _ _ _ _ _ _ _-> True
                _                            -> False) sens
        dtProp = filter (\x -> case item x of
                    DLDataProperty _ _ _ _ (Nothing) _ _-> True
                    DLDataProperty _ _ _ _ (Just DLFunctional) _ _-> True
                    DLDataProperty _ _ _ _ (Just DLInvFuntional) _ _->  error "InvFunctional not available for data properties"
                    DLDataProperty _ _ _ _ (Just DLSymmetric)    _ _->  error "Symmetric not available for data properties"
                    DLDataProperty _ _ _ _ (Just DLTransitive) _   _->  error "Transitive not available for data properties"
                    _                                  -> False
                ) sens
        indi = filter (\x -> case item x of
            DLIndividual _ _ _ _ _ _-> True
            _                      -> False
                ) sens
        mIndi = filter (\x -> case item x of
                    DLMultiIndi _ _ _ _ _ _-> True
                    _                     -> False
                ) sens
    in
    [cls, objProp, dtProp, indi, mIndi]

getClasses :: [DLBasicItem] -> Set.Set Id
getClasses cls =
        let
                ids   = map (\x -> case x of
                                     DLClass i _ _ _-> i
                                     _             -> error "Runtime Error!") cls
        in
                foldl (\x y -> Set.insert y x) Set.empty ids

-- Building a set of Individuals
getIndivs :: [DLBasicItem] ->  Set.Set Id -> (Set.Set QualIndiv, Set.Set Id)
getIndivs indivs cls =
    let
        indIds = map (\x -> case x of
                              DLIndividual tid (Nothing) _ _ _ _->
                                  (QualIndiv
                                  {
                                    iid = tid
                                  ,   types = [topSort]
                                  }, cls)
                              DLIndividual tid (Just y) _ _ _ _->
                                  (case y of
                                     DLType tps _->
                                         bucketIndiv $ map (\z -> case (z `Set.member` cls) of
                                                                    True ->
                                                                        (QualIndiv
                                                                        {
                                                                          iid = tid
                                                                        ,   types = [z]
                                                                        }, cls)
                                                                    _    ->
                                                                        (QualIndiv
                                                                        {
                                                                          iid = tid
                                                                        ,   types = [z]
                                                                        }, Set.union cls $ Set.singleton z)

                                                           ) tps)
                              _                               -> error "Runtime error"
                     ) indivs
        inIndis = map fst indIds
        inCls   = foldl (Set.union) Set.empty $ map snd indIds
        in
                (foldl (\x y -> Set.insert y x) Set.empty inIndis, inCls)

bucketIndiv :: [(QualIndiv, Set.Set Id)] -> (QualIndiv, Set.Set Id)
bucketIndiv ids = case ids of
        []     -> (QualIndiv
                   {
                     iid   = stringToId ""
                   , types = []
                   }, Set.empty)
        ((x,cls):xs) -> (QualIndiv
                         {
                           iid = iid x
                         , types = (types x) ++ types (fst (bucketIndiv xs))
                         }, cls)

-- Sets of Object and Data Properties a built

getDataProps :: [DLBasicItem] -> Set.Set Id -> Set.Set QualDataProp
getDataProps fnDataProps cls =
                foldl (\x y -> Set.insert (examineDataProp y cls) x) Set.empty fnDataProps

getObjProps :: [DLBasicItem] -> Set.Set Id -> Set.Set QualObjProp
getObjProps fnObjProps cls =
                foldl (\x y -> Set.insert (examineObjProp y cls) x) Set.empty fnObjProps


examineDataProp :: DLBasicItem -> Set.Set Id -> QualDataProp
examineDataProp bI _ =
        case bI of
                DLDataProperty nm _ _ _ _ _ _->
                                QualDataProp
                                        {
                                          nameD = nm
                                        }
                _                                          -> error "Runtime error!"

examineObjProp :: DLBasicItem -> Set.Set Id -> QualObjProp
examineObjProp bI _ =
        case bI of
                DLObjectProperty nm _ _ _ _ _ _->
                                QualObjProp
                                {
                                  nameO = nm
                                }
                _                                          -> error "Runtime error!"
