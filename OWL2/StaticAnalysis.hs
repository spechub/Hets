{- |
Module      :  ./OWL2/StaticAnalysis.hs
Copyright   :  Felix Gabriel Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisional
Portability :  portable

Static analysis for OWL 2
-}

module OWL2.StaticAnalysis where

import OWL2.Sign
import OWL2.Morphism
import OWL2.AS
import OWL2.MS
import OWL2.Print ()
import OWL2.Theorem
import OWL2.Function
import OWL2.Symbols

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List

import Common.AS_Annotation hiding (Annotation)
import Common.DocUtils
import Common.Result
import Common.GlobalAnnotations hiding (PrefixMap)
import Common.ExtSign
import Common.Lib.State
import Common.IRI --(iriToStringUnsecure, setAngles)
import Common.Id
import Common.SetColimit

import Control.Monad

import Logic.Logic

import Debug.Trace

-- | Error messages for static analysis
failMsg :: Entity -> ClassExpression -> Result a
failMsg (Entity _ ty e) desc =
  fatal_error
    ("undeclared `" ++ showEntityType ty
          ++ " " ++ showIRI e ++ "` in the following ClassExpression:\n"
          ++ showDoc desc "") $ iriPos e

-- | checks if an entity is in the signature
checkEntity :: Sign -> Entity -> Result ()
checkEntity s t@(Entity _ ty e) =
  let errMsg = mkError ("unknown " ++ showEntityType ty) e
  in case ty of
   Datatype -> unless (Set.member e (datatypes s) || isDatatypeKey e) errMsg
   Class -> unless (Set.member e (concepts s) || isThing e) errMsg
   ObjectProperty -> unless (isDeclObjProp s $ ObjectProp e) errMsg
   DataProperty -> unless (isDeclDataProp s e) errMsg
   AnnotationProperty -> unless (Set.member e (annotationRoles s)
        || isPredefAnnoProp e) $ justWarn () $ showDoc t " unknown"
   _ -> return ()

-- | takes an iri and finds out what entities it belongs to
correctEntity :: Sign -> IRI -> [Entity]
correctEntity s iri =
    [mkEntity AnnotationProperty iri | Set.member iri (annotationRoles s)] ++
    [mkEntity Class iri | Set.member iri (concepts s)] ++
    [mkEntity ObjectProperty iri | Set.member iri (objectProperties s)] ++
    [mkEntity DataProperty iri | Set.member iri (dataProperties s)] ++
    [mkEntity Datatype iri | Set.member iri (datatypes s)] ++
    [mkEntity NamedIndividual iri | Set.member iri (individuals s)]

checkLiteral :: Sign -> Literal -> Result ()
checkLiteral s l = case l of
    Literal _ (Typed dt) -> checkEntity s $ mkEntity Datatype dt
    _ -> return ()

isDeclInd :: Sign -> Individual -> Bool
isDeclInd s ind = Set.member ind $ individuals s

isDeclObjProp :: Sign -> ObjectPropertyExpression -> Bool
isDeclObjProp s ope = let op = objPropToIRI ope in
    Set.member op (objectProperties s) || isPredefObjProp op

isDeclDataProp :: Sign -> DataPropertyExpression -> Bool
isDeclDataProp s dp = Set.member dp (dataProperties s) || isPredefDataProp dp

{- | takes a list of object properties and discards the ones
    which are not in the signature -}
filterObjProp :: Sign -> [ObjectPropertyExpression]
    -> [ObjectPropertyExpression]
filterObjProp = filter . isDeclObjProp

checkObjPropList :: Sign -> [ObjectPropertyExpression] -> Result ()
checkObjPropList s ol = do
    let ls = map (isDeclObjProp s) ol
    unless (and ls) $ fail $ "undeclared object properties:\n" ++
                      showDoc (map (\o -> case o of
                                     ObjectProp _ -> o
                                     ObjectInverseOf x -> x
                                     _ -> error "unsolved string or variable") ol) ""

checkDataPropList :: Sign -> [DataPropertyExpression] -> Result ()
checkDataPropList s dl = do
    let ls = map (isDeclDataProp s) dl
    unless (and ls) $ fail $ "undeclared data properties:\n" ++ showDoc dl ""

-- | checks if a DataRange is valid
checkDataRange :: Sign -> DataRange -> Result ()
checkDataRange s dr = case dr of
    DataType dt rl -> do
        checkEntity s $ mkEntity Datatype dt
        mapM_ (checkLiteral s . snd) rl
    DataJunction _ drl -> mapM_ (checkDataRange s) drl
    DataComplementOf r -> checkDataRange s r
    DataOneOf ll -> mapM_ (checkLiteral s) ll

{- | converts ClassExpression to DataRanges because some
     DataProperties may be parsed as ObjectProperties -}
classExpressionToDataRange :: Sign -> ClassExpression -> Result DataRange
classExpressionToDataRange s ce = case ce of
    Expression u -> checkEntity s (mkEntity Datatype u)
        >> return (DataType u [])
    ObjectJunction jt cel -> fmap (DataJunction jt)
        $ mapM (classExpressionToDataRange s) cel
    ObjectComplementOf c -> fmap DataComplementOf
        $ classExpressionToDataRange s c
    _ -> fail $ "cannot convert ClassExpression to DataRange\n"
            ++ showDoc ce ""

{- | checks a ClassExpression and recursively converts the
     (maybe inappropriately) parsed syntax to a one satisfying the signature -}
checkClassExpression :: Sign -> ClassExpression -> Result ClassExpression
checkClassExpression s desc =
    let errMsg i = failMsg i desc
        objErr i = errMsg $ mkEntity ObjectProperty i
        datErr i = errMsg $ mkEntity DataProperty i
    in case desc of
    Expression u -> if isThing u
        then return $ Expression $ setReservedPrefix u
        else checkEntity s (mkEntity Class u) >> return desc
    ObjectJunction ty ds -> fmap (ObjectJunction ty)
        $ mapM (checkClassExpression s) ds
    ObjectComplementOf d -> fmap ObjectComplementOf $ checkClassExpression s d
    ObjectOneOf _ -> return desc
    ObjectValuesFrom q opExpr d -> if isDeclObjProp s opExpr
        then fmap (ObjectValuesFrom q opExpr) $ checkClassExpression s d
        else let iri = objPropToIRI opExpr
             in if isDeclDataProp s iri then
                    fmap (DataValuesFrom q iri)
                      $ classExpressionToDataRange s d
                else objErr iri
    ObjectHasSelf opExpr -> if isDeclObjProp s opExpr then return desc
        else objErr $ objPropToIRI opExpr
    ObjectHasValue opExpr _ -> if isDeclObjProp s opExpr then return desc
        else objErr $ objPropToIRI opExpr
    ObjectCardinality (Cardinality a b opExpr md) -> do
        let iri = objPropToIRI opExpr
            mbrOP = Set.member iri $ objectProperties s
        case md of
            Nothing
                | mbrOP -> return desc
                | isDeclDataProp s iri ->
                        return $ DataCardinality $ Cardinality a b iri Nothing
                | otherwise -> objErr iri
            Just d ->
                if mbrOP then fmap (ObjectCardinality . Cardinality a b opExpr
                            . Just) $ checkClassExpression s d
                else do
                    dr <- classExpressionToDataRange s d
                    if isDeclDataProp s iri then
                        return $ DataCardinality
                          $ Cardinality a b iri $ Just dr
                        else datErr iri
    DataValuesFrom _ dExp r -> checkDataRange s r
        >> if isDeclDataProp s dExp then return desc else datErr dExp
    DataHasValue dExp l -> do
        checkLiteral s l
        if isDeclDataProp s dExp then return desc
            else datErr dExp
    DataCardinality (Cardinality _ _ dExp mr) -> if isDeclDataProp s dExp
        then case mr of
            Nothing -> return desc
            Just d -> checkDataRange s d >> return desc
        else datErr dExp
    _ -> error "unsolved string or class variable"

checkFact :: Sign -> Fact -> Result ()
checkFact s f = case f of
    ObjectPropertyFact _ op ind ->
     if not $ isDeclObjProp s op then
       fail $ "unknown object property:" ++ showDoc op ""
      else if not $ isDeclInd s ind then
        fail $ "unknown individual: " ++ showDoc ind ""
            else return ()
    DataPropertyFact _ dp l -> do
        checkLiteral s l
        unless (isDeclDataProp s dp)
            $ fail $ "Static analysis. DataProperty fact failed " ++ show f

checkFactList :: Sign -> [Fact] -> Result ()
checkFactList = mapM_ . checkFact

-- | sorts the data and object properties
checkHasKey :: Sign -> [ObjectPropertyExpression] -> [DataPropertyExpression]
    -> Result AnnFrameBit
checkHasKey s ol dl = do
    let nol = filterObjProp s ol
        ndl = map objPropToIRI (ol \\ nol) ++ dl
        key = ClassHasKey nol ndl
        decl = map (isDeclDataProp s) ndl
    if and decl then return key
        else fail $ "Keys failed " ++ showDoc ol "" ++ showDoc dl "\n"

checkAnnotation :: Sign -> Annotation -> Result ()
checkAnnotation s (Annotation ans apr av) = do
    checkAnnos s [ans]
    checkEntity s (mkEntity AnnotationProperty apr)
    case av of
        AnnValLit lit -> checkLiteral s lit
        _ -> return ()

checkAnnos :: Sign -> [Annotations] -> Result ()
checkAnnos = mapM_ . mapM . checkAnnotation

checkAnnoList :: Sign -> ([t] -> Result ()) -> [(Annotations, t)] -> Result ()
checkAnnoList s f anl = do
    checkAnnos s $ map fst anl
    f $ map snd anl

checkListBit :: Sign -> Maybe Relation -> ListFrameBit -> Result ListFrameBit
checkListBit s r fb = case fb of
    AnnotationBit anl -> case r of
        Just (DRRelation _) -> checkAnnos s (map fst anl) >> return fb
        _ -> checkAnnoList s (mapM_ $ checkEntity s .
                    mkEntity AnnotationProperty) anl >> return fb
    ExpressionBit anl -> do
        let annos = map fst anl
        checkAnnos s annos
        n <- mapM (checkClassExpression s . snd) anl
        return $ ExpressionBit $ zip annos n
    ObjectBit anl -> do
        let annos = map fst anl
            ol = map snd anl
            sorted = filterObjProp s ol
        if null sorted then do
            checkAnnos s annos
            checkObjPropList s ol
            return $ ObjectBit anl
         else if length sorted == length ol then return fb
                    else fail $ "Static analysis found that there are" ++
                        " multiple types of properties in\n\n" ++
                        show sorted ++ show (map objPropToIRI $ ol \\ sorted)
    ObjectCharacteristics anl -> checkAnnos s (map fst anl) >> return fb
    DataBit anl -> checkAnnoList s (checkDataPropList s) anl >> return fb
    DataPropRange anl -> checkAnnoList s (mapM_ $ checkDataRange s) anl
            >> return fb
    IndividualFacts anl -> checkAnnoList s (checkFactList s) anl >> return fb
    IndividualSameOrDifferent anl -> checkAnnos s (map fst anl) >> return fb

checkAnnBit :: Sign -> AnnFrameBit -> Result AnnFrameBit
checkAnnBit s fb = case fb of
    DatatypeBit dr -> checkDataRange s dr >> return fb
    ClassDisjointUnion cel -> fmap ClassDisjointUnion
        $ mapM (checkClassExpression s) cel
    ClassHasKey ol dl -> checkHasKey s ol dl
    ObjectSubPropertyChain ol -> checkObjPropList s ol >> return fb
    _ -> return fb

checkAssertion :: Sign -> IRI -> Annotations -> Result [Axiom]
checkAssertion s iri ans = do
    let entList = correctEntity s iri
        ab = AnnFrameBit ans $ AnnotationFrameBit Assertion
    if null entList
        then let misc = Misc [Annotation [] iri $ AnnValue iri]
             in return [PlainAxiom misc ab] -- only for anonymous individuals
        else return $ map (\ x -> PlainAxiom (SimpleEntity x) ab) entList

checkExtended :: Sign -> Extended -> Result Extended
checkExtended s e = case e of
    ClassEntity ce -> fmap ClassEntity $ checkClassExpression s ce
    ObjectEntity oe -> case oe of
        ObjectInverseOf op -> let i = objPropToIRI op in
            if Set.member i (objectProperties s)
            then return e else mkError "unknown object property" i
        _ -> return e
    Misc ans -> checkAnnos s [ans] >> return e
    _ -> return e

-- | corrects the axiom according to the signature
checkAxiom :: Sign -> Axiom -> Result [Axiom]
checkAxiom s ax@(PlainAxiom ext fb) = case fb of
    ListFrameBit mr lfb -> do
      next <- checkExtended s ext
      nfb <- fmap (ListFrameBit mr) $ checkListBit s mr lfb
      return [PlainAxiom next nfb]
    ab@(AnnFrameBit ans afb) -> do
      checkAnnos s [ans]
      case afb of
        AnnotationFrameBit ty -> case ty of
            Assertion -> case ext of
                    -- this can only come from XML
                Misc [Annotation _ iri _] -> checkAssertion s iri ans
                    -- these can only come from Manchester Syntax
                SimpleEntity (Entity _ _ iri) -> checkAssertion s iri ans
                ClassEntity (Expression iri) -> checkAssertion s iri ans
                ObjectEntity (ObjectProp iri) -> checkAssertion s iri ans
                _ -> do
                  next <- checkExtended s ext
                  -- could rarely happen, and only in our extended syntax
                  return [PlainAxiom next ab]
            Declaration -> return [ax]
            _ -> return []
        _ -> do
            next <- checkExtended s ext
            nfb <- fmap (AnnFrameBit ans) $ checkAnnBit s afb
            return [PlainAxiom next nfb]

-- | checks a frame and applies desired changes
checkFrame :: Sign -> Frame -> Result [Frame]
checkFrame s (Frame eith fbl) = if null fbl then do
    ext <- checkExtended s eith
    return [Frame ext []]
  else fmap (map axToFrame . concat) $ mapM (checkAxiom s . PlainAxiom eith) fbl

correctFrames :: Sign -> [Frame] -> Result [Frame]
correctFrames s = fmap concat . mapM (checkFrame s)

collectEntities :: Frame -> State Sign ()
collectEntities f = case f of
    Frame (SimpleEntity e) _ -> addEntity e
    Frame (ClassEntity (Expression e)) _ -> addEntity $ mkEntity Class e
    Frame (ObjectEntity (ObjectProp e)) _ ->
        addEntity $ mkEntity ObjectProperty e
    _ -> return ()

-- | collects all entites from the frames
createSign :: [Frame] -> State Sign ()
createSign f = do
  pm <- gets prefixMap
  mapM_ (collectEntities . function Expand (StringMap pm)) f

noDecl :: Axiom -> Bool
noDecl ax = case ax of
  PlainAxiom _ (AnnFrameBit _ (AnnotationFrameBit Declaration)) -> False
  _ -> True

-- | corrects the axioms according to the signature
createAxioms :: Sign -> [Frame] -> Result ([Named Axiom], [Frame])
createAxioms s fl = do
    cf <- correctFrames s $ map (function Expand $ StringMap $ prefixMap s) fl
    return (map anaAxiom . filter noDecl $ concatMap getAxioms cf, cf)

check1Prefix :: Maybe String -> String -> Bool
check1Prefix ms s =
  let
    dropCharPre c str = if isPrefixOf [c] str then drop 1 str else str
    dropBracketSuf str = reverse $ dropCharPre '>' $ reverse str
  in case ms of
      Nothing -> True
      Just iri -> let iri' = dropBracketSuf $ dropCharPre '<' iri
                      s' = dropBracketSuf $ dropCharPre '<' s
                  in iri' == s'

checkPrefixMap :: PrefixMap -> Bool
checkPrefixMap pm =
    let pl = map (`Map.lookup` pm) ["owl", "rdf", "rdfs", "xsd"]
    in and $ zipWith check1Prefix pl
            (map snd $ tail $ Map.toList predefPrefixes)

newODoc :: OntologyDocument -> [Frame] -> Result OntologyDocument
newODoc OntologyDocument {ontology = mo, prefixDeclaration = pd} fl =
    if checkPrefixMap pd
        then return OntologyDocument
                { ontology = mo {ontFrames = fl}, prefixDeclaration = pd}
        else fail $ "Incorrect predefined prefixes " ++ showDoc pd "\n"

-- | static analysis of ontology with incoming sign.
basicOWL2Analysis :: (OntologyDocument, Sign, GlobalAnnos)
    -> Result (OntologyDocument, ExtSign Sign Entity, [Named Axiom])
basicOWL2Analysis (inOnt, inSign, ga) = do
    let pm = Map.union (prefixDeclaration inOnt)
          . Map.map (iriToStringUnsecure . setAngles False)
          . Map.delete "" $ prefix_map ga
        odoc = inOnt { prefixDeclaration = pm }
        fs = ontFrames $ ontology odoc
        accSign = execState (createSign fs) inSign { prefixMap = pm }
        syms = Set.difference (symOf accSign) $ symOf inSign
    (axl, nfl) <- createAxioms accSign fs
    newdoc <- newODoc odoc nfl
    return (newdoc
      , ExtSign accSign {labelMap = generateLabelMap accSign nfl} syms, axl)

-- | extrace labels from Frame-List (after processing with correctFrames)
generateLabelMap :: Sign -> [Frame] -> Map.Map IRI String
generateLabelMap sig = foldr (\ (Frame ext fbl) -> case ext of
        SimpleEntity (Entity _ _ ir) -> case fbl of
            [AnnFrameBit [Annotation _ apr (AnnValLit (Literal s' _))] _]
                | prefixName apr == "rdfs" && show (iriPath apr) == "label"
                  -> Map.insert ir s'
            _ -> id
        _ -> id ) (labelMap sig)

-- | adding annotations for theorems
anaAxiom :: Axiom -> Named Axiom
anaAxiom ax = findImplied ax $ makeNamed nm ax
   where names = getNames ax
         nm = concat $ intersperse "_" names
         
findImplied :: Axiom -> Named Axiom -> Named Axiom
findImplied ax sent =
  if prove ax then sent
         { isAxiom = False
         , isDef = False
         , wasTheorem = False }
   else sent { isAxiom = True }

getNames1 :: Annotation -> [String]
getNames1 anno = case anno of
      Annotation _ aIRI (AnnValLit (Literal value _)) ->
          if show (iriPath aIRI) == "label"
             then [value]
             else []
      _ -> []

getNamesList :: (Annotations, a) -> [String]
getNamesList (ans, _) = concatMap getNames1 ans

getNamesAnnList :: AnnotatedList a -> [String]
getNamesAnnList = concatMap getNamesList

getNamesLFB :: ListFrameBit -> [String]
getNamesLFB fb = case fb of
    AnnotationBit a -> getNamesAnnList a
    ExpressionBit a -> getNamesAnnList a
    ObjectBit a -> getNamesAnnList a
    DataBit a -> getNamesAnnList a
    IndividualSameOrDifferent a -> getNamesAnnList a
    ObjectCharacteristics a -> getNamesAnnList a
    DataPropRange a -> getNamesAnnList a
    IndividualFacts a -> getNamesAnnList a

getNamesFB :: FrameBit -> [String]
getNamesFB fb = case fb of
    ListFrameBit _ lfb -> getNamesLFB lfb
    AnnFrameBit ans _ -> concatMap getNames1 ans

getNames :: Axiom -> [String]
getNames (PlainAxiom eith fb) = case eith of
      Misc ans -> concatMap getNames1 ans ++ getNamesFB fb
      _ -> getNamesFB fb


addEquiv :: Sign -> Sign -> [SymbItems] -> [SymbItems] ->
            Result (Sign, Sign, Sign,
                     EndoMap Entity, EndoMap Entity)
addEquiv ssig tsig l1 l2 = do
  let l1' = statSymbItems ssig l1
      l2' = statSymbItems tsig l2
  case (l1', l2') of
    ([rs1], [rs2]) -> do
      let match1 = filter (`matchesSym` rs1) $ Set.toList $ symOf ssig
          match2 = filter (`matchesSym` rs2) $ Set.toList $ symOf tsig
      case
       (match1, match2) of
          ([e1], [e2]) ->
           if entityKind e1 == entityKind e2 then do
              s <- pairSymbols e1 e2
              sig <- addSymbToSign emptySign s
              sig1 <- addSymbToSign emptySign e1
              sig2 <- addSymbToSign emptySign e2
              return (sig, sig1, sig2,
                         Map.insert e1 s Map.empty,
                         Map.insert e2 s Map.empty)
             else
              fail "only symbols of same kind can be equivalent in an alignment"
          _ -> fail $ "non-unique symbol match:" ++ showDoc l1 " "
                                                 ++  showDoc l2 " "
    _ -> fail "terms not yet supported in alignments"

corr2theo :: String -> Bool -> Sign -> Sign -> [SymbItems] -> [SymbItems] ->
             EndoMap Entity -> EndoMap Entity -> REL_REF ->
             Result (Sign, [Named Axiom], Sign, Sign,
                     EndoMap Entity, EndoMap Entity)
corr2theo _aname flag ssig tsig l1 l2 eMap1 eMap2 rref = do
  let l1' = statSymbItems ssig l1
      l2' = statSymbItems tsig l2
  case (l1', l2') of
    ([rs1], [rs2]) -> do
      let match1 = filter (`matchesSym` rs1) $ Set.toList $ symOf ssig
          match2 = filter (`matchesSym` rs2) $ Set.toList $ symOf tsig
      case
       (match1, match2) of
          ([e1], [e2]) -> do
           let e1' = if flag then e1 {cutIRI =  addString (cutIRI e1, "_source")} else e1
               e2' = if flag then e2 {cutIRI =  addString (cutIRI e2, "_target")} else e2
               sig = emptySign
               eMap1' = Map.union eMap1 $ Map.fromAscList [(e1', e1)]
               eMap2' = Map.union eMap2 $ Map.fromAscList [(e2', e2)]
           sig1 <- addSymbToSign sig e1'
           sig2 <- addSymbToSign sig e2'
           sigB <- addSymbToSign sig1 e2'
           case rref of
            Equiv -> do
             let extPart = mkExtendedEntity e2'
                 axiom = PlainAxiom extPart $
                           ListFrameBit (Just $
                              case (entityKind e1', entityKind e2') of
                                (Class, Class) -> EDRelation Equivalent
                                (ObjectProperty, ObjectProperty) ->
                                   EDRelation Equivalent
                                (NamedIndividual, NamedIndividual) -> SDRelation Same
                                _ -> error $ "use subsumption only between"
                                              ++ "classes or roles:" ++
                                              show l1 ++ " " ++ show l2) $
                           ExpressionBit [([], Expression $ cutIRI e1')]
             return (sigB, [makeNamed "" axiom], sig1, sig2, eMap1', eMap2')
            Subs -> do
             let extPart = mkExtendedEntity e2'
                 axiom = PlainAxiom extPart $
                           ListFrameBit (Just $
                              case (entityKind e1', entityKind e2') of
                                (Class, Class) -> SubClass
                                (ObjectProperty, ObjectProperty) ->
                                    SubPropertyOf
                                _ -> error $ "use subsumption only between"
                                              ++ "classes or roles:" ++
                                              show l1 ++ " " ++ show l2) $
                           ExpressionBit [([], Expression $ cutIRI e1')]
             return (sigB, [makeNamed "" axiom], sig1, sig2, eMap1', eMap2')
            Incomp -> do
             let extPart = mkExtendedEntity e1'
                 axiom = PlainAxiom extPart $
                           ListFrameBit (Just $ EDRelation Disjoint) $
                           ExpressionBit [([], Expression $ cutIRI e2')]
             return (sigB, [makeNamed "" axiom], sig1, sig2, eMap1', eMap2')
            IsSubs -> do
             let extPart = mkExtendedEntity e1'
                 axiom = PlainAxiom extPart $
                           ListFrameBit (Just SubClass) $
                           ExpressionBit [([], Expression $ cutIRI e2')]
             return (sigB, [makeNamed "" axiom], sig1, sig2, eMap1', eMap2')
            InstOf -> do
             let extPart = mkExtendedEntity e1'
                 axiom = PlainAxiom extPart $
                           ListFrameBit (Just Types) $
                           ExpressionBit [([], Expression $ cutIRI e2')]
             return
                 (sigB, [makeNamed "" axiom], sig1, sig2, eMap1', eMap2')
            HasInst -> do
             let extPart = mkExtendedEntity e2'
                 axiom = PlainAxiom extPart $
                           ListFrameBit (Just Types) $
                           ExpressionBit [([], Expression $ cutIRI e1')]
             return
                 (sigB, [makeNamed "" axiom], sig1, sig2, eMap1', eMap2')
            RelName _r -> error "nyi" {- do
             let extPart = mkExtendedEntity e1'
                 rQName = QN "" (iriToStringUnsecure r)
                             Abbreviated (iriToStringUnsecure r) Id.nullRange
                 sym = mkEntity ObjectProperty rQName
                 rSyms = filter (== sym) $
                            Set.toList $ symOf tsig
             case rSyms of
               [] -> fail $ "relation " ++ show rQName ++
                                " not in " ++ show tsig
               [rsym] -> do
                 let sym'@(Entity _ ObjectProperty rQName') =
                             Map.findWithDefault rsym rsym eMap2'
                     axiom = PlainAxiom extPart $
                              ListFrameBit (Just SubClass) $
                               ExpressionBit [([],
                                ObjectValuesFrom
                                 SomeValuesFrom
                                 (ObjectProp rQName')
                                 (Expression $ cutIRI e2'))]
                 sigB' <- addSymbToSign sigB sym'
                 sig2' <- addSymbToSign sig2 rsym
                 return
                   (sigB', [makeNamed "" axiom], sig1, sig2', eMap1',
                      Map.union eMap2' $ Map.fromAscList [(rsym, sym')])
               _ -> fail $ "too many matches for " ++ show rQName -}
            _ -> fail $ "nyi:" ++ show rref
          _ -> fail $ "non-unique symbol match:" ++ showDoc l1 " "
                                                 ++ showDoc l2 " "
    _ -> fail "terms not yet supported in alignments"

-- solving symbols of a pattern

solveSymbols :: Set.Set Entity -> PatternVarMap -> OntologyDocument -> Result OntologyDocument
solveSymbols impSyms vMap (OntologyDocument pd (Ontology n is as fs)) = do
 (declSyms, usedSyms, fs') <- 
         foldM (\(ds, us, flist) f -> do
                   (f', ds', us') <- solveFrame impSyms vMap f
                   return (Set.union ds ds', Set.union us us', flist++[f']) ) 
               (Set.empty, Set.empty, []) fs
 let getKind str = case str of
                    "Class" -> Class
                    "ObjectProperty" -> ObjectProperty
                    "Individual" -> NamedIndividual
                    _ -> error $ "nyi:" ++ str
     varSyms = foldl Set.union Set.empty $ map (\(x, (f, k)) -> if f then Set.empty else Set.singleton $ Entity Nothing (getKind k) x) $ Map.toList vMap
     diffSyms = Set.difference usedSyms (Set.union declSyms $ Set.union impSyms varSyms) 
     -- each used symbol must be declared, imported or variable
 if Set.null diffSyms then 
  return $ OntologyDocument pd $ Ontology n is as fs'
 else error $ "undeclared symbols in the body of the pattern. impSyms:" ++ show impSyms ++  
              " declSyms:" ++ show declSyms ++ " usedSyms:" ++ show usedSyms ++ 
              " varSyms:" ++ show varSyms ++ " diffSyms:" ++ show diffSyms 

-- solving symbols for each frame, also keep track of declared and used symbols
   
solveFrame :: Set.Set Entity  -> PatternVarMap -> Frame -> Result (Frame, Set.Set Entity, Set.Set Entity)
solveFrame impSyms vMap (Frame ext fBits) = do
 let (ext', decl) = 
          case ext of 
             Misc _ -> (ext, Set.empty) 
             ClassEntity (UnsolvedClass i) -> 
               if i `elem` Map.keys vMap 
                then (ClassEntity $ VarExpression $ MVar False i, Set.empty) -- TODO: handle lists
                else if (Entity Nothing Class i) `elem` impSyms 
                      then (ClassEntity $ Expression i, Set.empty) -- add only if not member of impSyms
                      else (ClassEntity $ Expression i, Set.singleton $ Entity Nothing Class i)  
             ClassEntity _ -> error $ show ext 
             ObjectEntity (UnsolvedObjProp i) -> 
               if i `elem` Map.keys vMap
                then (ObjectEntity $ ObjectPropertyVar False i, Set.empty) -- TODO: handle lists
                else if (Entity Nothing ObjectProperty i) `elem` impSyms 
                      then (ObjectEntity $ ObjectProp i, Set.empty) -- add only if not member of impSyms
                      else (ObjectEntity $ ObjectProp i, Set.singleton $ Entity Nothing ObjectProperty i)
             ObjectEntity _ -> error $ show ext -- TODO: handle oexp
             SimpleEntity (Entity l UnsolvedEntity i) ->
                if i `elem` Map.keys vMap 
                 then -- TODO: tests that it's an individual!
                      (IndividualVar i, Set.empty)
                else (SimpleEntity $ Entity l NamedIndividual i, Set.singleton $ Entity l NamedIndividual i)
 (fBits', used) <- foldM (\(fbs, us) fbit -> do 
                                (fbit', us') <- solveFrameBit impSyms vMap fbit
                                return (fbs ++ [fbit'], Set.union us us')) ([], Set.empty) fBits
 return (Frame ext' fBits', decl, used)

-- solve symbols for each frame bit

solveFrameBit :: Set.Set Entity -> PatternVarMap -> FrameBit -> Result (FrameBit, Set.Set Entity)
solveFrameBit impSyms vMap fbit = -- trace ("fbit:" ++ show fbit) $ 
 case fbit of 
  ListFrameBit mr lft ->
    case lft of 
      AnnotationBit _ -> return (fbit, Set.empty)
      ExpressionBit aces -> do
       let (aces', used') = foldl (\(as, us) ace -> let (ace', us') = solveClassExpression impSyms vMap ace
                                                    in (as ++ [ace'], Set.union us us')) ([], Set.empty) aces 
       -- trace ("solved lft:" ++ show (ExpressionBit aces')) $ 
       return (ListFrameBit mr $ ExpressionBit aces', used')
      ObjectBit aopes -> do
       let (aopes', used') = foldl (\(as, us) aope -> 
                                        let (aope', us') = solveObjPropExpression impSyms vMap aope
                                        in (as ++ [aope'], Set.union us us')) ([], Set.empty) aopes 
       -- trace ("solved lft:" ++ show (ObjectBit aopes')) $ 
       return (ListFrameBit mr $ ObjectBit aopes', used')
      DataBit adpes -> error "nyi"
      IndividualSameOrDifferent ainds -> return (fbit, Set.empty)
      ObjectCharacteristics achars -> return (fbit, Set.empty)
      IndividualFacts afacts -> do
       let (afacts', used') = foldl (\(afs, usyms) (a, af) -> do
                                       case af of
                                         ObjectPropertyFact pn ope i -> let ((_, ope'), us') = solveObjPropExpression impSyms vMap ([], ope)
                                                                        in (afs ++ [(a,ObjectPropertyFact pn ope' i)], Set.union usyms us')
                                         DataPropertyFact _ _ _ -> error "data property nyi") 
                                   ([], Set.empty) afacts
       return (ListFrameBit mr $ IndividualFacts afacts', used')
  AnnFrameBit annos (AnnotationFrameBit _) -> return (fbit, Set.empty)
  AnnFrameBit annos DataFunctional -> return (fbit, Set.empty)
  AnnFrameBit annos (DatatypeBit drg) -> error "nyi"
  AnnFrameBit annos (ClassDisjointUnion cexps) -> error "nyi"
  AnnFrameBit annos (ClassHasKey opexps dpexps) -> error "nyi"
  AnnFrameBit annos (ObjectSubPropertyChain opexps) -> do
      let (opexps', used') = foldl (\(as, us) ope -> 
                                        let (aope', us') = solveObjPropExpression impSyms vMap ([], ope)
                                        in (as ++ [snd aope'], Set.union us us')) ([], Set.empty) opexps
      -- trace ("solved lft:" ++ show (ObjectSubPropertyChain opexps')) $ 
      return (AnnFrameBit annos $ ObjectSubPropertyChain opexps', used')

-- solve class expressions

solveClassExpression :: Set.Set Entity  -> PatternVarMap -> (Annotations, ClassExpression) -> ((Annotations, ClassExpression), Set.Set Entity) 
solveClassExpression impSyms vMap (annos, cexp) = 
 let (cexp', used) = case cexp of 
                       UnsolvedClass i -> if i `elem` Map.keys vMap then 
                                             let (b, _) = Map.findWithDefault (error "just checked") i vMap
                                             in (VarExpression $ MVar b i, Set.empty)
                                          else (Expression i, Set.singleton $ Entity Nothing Class i)
                       ObjectJunction j cexps -> let  (cexps', used')  = foldl (\(cs, u) c -> let ((_a, c'), u') = solveClassExpression impSyms vMap ([], c)
                                                                                              in (cs ++ [c'], Set.union u u')) ([], Set.empty) cexps
                                                 in (ObjectJunction j cexps', used')
                       Expression i -> error "nyi"
                       ObjectComplementOf cexp -> let ((_a, cexp'), u) = solveClassExpression impSyms vMap ([], cexp)
                                                  in (ObjectComplementOf cexp', u) 
                       VarExpression _ -> error $ "should get a class expression but instead got " ++ show cexp
                       ObjectOneOf indivs -> error "nyi"
                       ObjectValuesFrom q opexp cexp -> let ((_, cexp'),  u1) = solveClassExpression impSyms vMap ([], cexp)
                                                            ((_, opexp'), u2) = solveObjPropExpression impSyms vMap ([], opexp)
                                                        in (ObjectValuesFrom q opexp' cexp', Set.union u1 u2)
                       ObjectHasValue opexp indiv -> error "nyi"
                       ObjectHasSelf opexp -> let ((_, opexp'), u) = solveObjPropExpression impSyms vMap ([], opexp)
                                              in (ObjectHasSelf opexp', u)
                       ObjectCardinality (Cardinality cType aInt opexp mcexp) -> 
                          let 
                            (mcexp', u1) = 
                              case mcexp of
                               Nothing -> (Nothing, Set.empty)
                               Just cexp ->   let ((_a, cexp'), u) = solveClassExpression impSyms vMap ([], cexp)
                                              in (Just cexp', u)
                            ((_, opexp'), u2) = solveObjPropExpression impSyms vMap ([], opexp)
                           in ( ObjectCardinality (Cardinality cType aInt opexp' mcexp'), Set.union u1 u2)                  
                       DataValuesFrom q dpexp drg -> error "nyi"
                       DataHasValue dpexp lit -> error "nyi" 
                       DataCardinality (Cardinality cType aInt dpexp mdrg) -> error "nyi"
                       -- _ -> error $ "nyi:" ++ show cexp
 in ((annos, cexp'), used)

solveObjPropExpression :: Set.Set Entity  -> PatternVarMap -> (Annotations,  ObjectPropertyExpression) -> ((Annotations,  ObjectPropertyExpression), Set.Set Entity)
solveObjPropExpression impSyms vMap (annos, opexp) =
 let (opexp', used) = 
       case opexp of
        ObjectProp r -> (opexp, Set.singleton $ Entity Nothing ObjectProperty r)
        ObjectInverseOf opexp0 -> let ((_, opexp1), u) = solveObjPropExpression impSyms vMap ([], opexp0)
                                  in (ObjectInverseOf opexp1, u)
        ObjectPropertyVar _ _ -> error $ "expected object property expression but got " ++ show opexp
        UnsolvedObjProp i -> if i `elem` Map.keys vMap then 
                                             let (b, _) = Map.findWithDefault (error "just checked") i vMap
                                             in (ObjectPropertyVar b i, Set.empty)
                                          else (ObjectProp i, Set.singleton $ Entity Nothing ObjectProperty i)
 in ((annos, opexp'), used)

solveIndividual :: Set.Set Entity  -> PatternVarMap -> (Annotations,  IndExpression) -> ((Annotations,  IndExpression), Set.Set Entity) 
solveIndividual _ _ _ = error "nyi"

-- TODO: 
-- write a method that solves a data property expression etc.
-- note: individuals are not stored as vars at any moment.


-- instantiate a macro with the values stored in a substitution

instantiateMacro :: PatternVarMap -> Map.Map (IRI, String) IRI -> OntologyDocument -> Result OntologyDocument
instantiateMacro vars subst (OntologyDocument pd (Ontology n is as fs)) = do
  fs'<- instantiateFrames subst vars fs
  return $ OntologyDocument pd $ Ontology n is as fs'

-- instantiate frames

instantiateFrames :: Map.Map (IRI, String) IRI -> PatternVarMap -> [Frame] -> Result [Frame]
instantiateFrames subst vars = 
 mapM (instantiateFrame subst vars)

-- instantiate a single frame

instantiateFrame :: Map.Map (IRI, String) IRI -> PatternVarMap -> Frame -> Result Frame
instantiateFrame subst var (Frame ext fBits) = do
 ext' <- case ext of
           ClassEntity (VarExpression (MVar b i)) -> -- TODO: handle lists! 
             if (i, "Class") `elem` Map.keys subst then do
                let j = Map.findWithDefault (error "instantiateFrame") (i, "Class") subst
                return $ ClassEntity $ Expression j
              else fail $ "unknown class variable: " ++ show i
           ClassEntity (Expression i) -> return $ ClassEntity $ Expression $ instParamName subst i
           ClassEntity _ -> return ext
           ObjectEntity (ObjectPropertyVar b i) -> -- TODO: handle lists!
             if (i, "ObjectProperty") `elem` Map.keys subst then do
               let j = Map.findWithDefault (error "instantiateFrame") (i, "ObjectProperty") subst
               return $ ObjectEntity $ ObjectProp j
             else fail $ "unknown object property variable: " ++ show i
           ObjectEntity (ObjectProp i) -> 
             return $ ObjectEntity $ ObjectProp 
                    $ instParamName subst i
           ObjectEntity _ -> return ext
           SimpleEntity ent -> return $ SimpleEntity $ ent{cutIRI = instParamName subst $ cutIRI ent}
             -- TODO: we get this for individuals declared in the bodies! what about data props?
           IndividualVar i -> 
              if (i, "Individual") `elem` Map.keys subst then do
                let j = Map.findWithDefault (error "instantiateFrame") (i, "Individual") subst
                return $ SimpleEntity $ Entity Nothing NamedIndividual j
              else fail $ "unknown individual variable: " ++ show i
           Misc _ -> error $ show ext
 fBits' <- mapM (instantiateFrameBit subst var) fBits 
 return $ Frame ext' fBits'

-- instantiate paramerized names
-- p[X] becomes p[V] if subst maps X to V
-- the string argument is the kind

instParamName :: Map.Map (IRI, String) IRI -> IRI -> IRI
instParamName subst p = 
 let pPath = iriPath p
     comps = getComps pPath
     solveId t = 
       let tIRI = idToIRI t
           k = let tSubsts = filter (\(x,y) -> x == tIRI) $ Map.keys subst
               in case tSubsts of 
                    [(a,b)] -> b
                    []-> "Class" -- does not matter  
                    (a,b):_ -> b
       in  Map.findWithDefault tIRI (tIRI,k) subst -- this will most likely need to change for complex nesting!
     comps' = map (\t -> iriPath $ solveId t) comps
     newPath = trace ("comps:" ++ show comps ++ " comps':" ++ show comps') $ pPath{getComps = comps'}  
 in p{iriPath = newPath}

instantiateFrameBit :: Map.Map (IRI, String) IRI -> PatternVarMap -> FrameBit -> Result FrameBit
instantiateFrameBit subst var fbit =
 case fbit of
  ListFrameBit mr lfb -> 
    case lfb of 
     AnnotationBit _ -> return fbit
     ExpressionBit aces -> do
      aces' <- mapM (instantiateClassExpression subst var) aces
      return $ ListFrameBit mr $ ExpressionBit aces'
     ObjectBit aopexps -> do
      aopexps' <- mapM (instantiateObjectPropertyExpression subst var) aopexps
      return $ ListFrameBit mr $ ObjectBit aopexps'
     DataBit adpexps -> error $ show lfb 
     IndividualSameOrDifferent aindivs -> 
       return $ ListFrameBit mr $ IndividualSameOrDifferent $
       map (\(a,i) -> if (i,"Individual")`elem` Map.keys subst then 
                       let j = Map.findWithDefault (error "instantiateFrameBit") (i, "Individual") subst
                       in (a, j)
                      else (a,i)) aindivs
     ObjectCharacteristics _achars -> return fbit
     DataPropRange _ -> return fbit
     IndividualFacts afacts -> do 
      afacts' <- mapM (\(a, af) -> case af of
                                       ObjectPropertyFact pn ope i -> do
                                         (_, ope') <- instantiateObjectPropertyExpression subst var ([], ope)
                                         let j = if (i,"Individual")`elem` Map.keys subst then 
                                                    Map.findWithDefault (error "instantiateFrameBit") (i, "Individual") subst
                                                 else i
                                         return (a, ObjectPropertyFact pn ope' j)
                                       DataPropertyFact pn dpe lit -> error "data property fact nyi") afacts
      return $ ListFrameBit mr $ IndividualFacts afacts' 
  AnnFrameBit annos afb -> do
    annos' <-
     case annos of 
      [] -> return annos
      _ -> mapM (instantiateAnno subst var) annos 
    case afb of
     AnnotationFrameBit at -> return $ AnnFrameBit annos' afb
     DataFunctional -> return $ AnnFrameBit annos' afb
     DatatypeBit drg -> error $ show fbit
     ClassDisjointUnion cexps -> do
      aexps' <- mapM (instantiateClassExpression subst var) $ map (\x -> ([], x)) cexps
      return $ AnnFrameBit annos' $ ClassDisjointUnion $ map snd aexps'
     ClassHasKey opexps dpexps -> error $ show fbit
     ObjectSubPropertyChain opexps -> do
      aopexps' <- mapM (instantiateObjectPropertyExpression subst var) $ map (\x -> ([], x)) opexps
      return $ AnnFrameBit annos' $ ObjectSubPropertyChain $ map snd aopexps'

instantiateAnno :: Map.Map (IRI, String) IRI -> PatternVarMap -> Annotation -> Result Annotation
instantiateAnno subst var anno = 
 case anno of
   Annotation annos aprop aval -> do
    case aval of
     AnnValue x -> 
      if (x, "String") `elem` Map.keys subst then do
       let v = Map.findWithDefault (error "already checked") (x, "String") subst
       return $ Annotation annos aprop $ AnnValue v -- should be AnnValLit but I don't know yet what to put in it! TODO
      else return anno
     _ -> return anno
    

instantiateClassExpression :: Map.Map (IRI, String) IRI -> PatternVarMap -> (Annotations, ClassExpression) -> Result (Annotations, ClassExpression)
instantiateClassExpression subst var (annos, cexp) = 
 case cexp of 
   UnsolvedClass _ -> error $ "unsolved class at instantiation: " ++ show cexp
   Expression i -> return (annos, Expression $ instParamName subst i)
   VarExpression (MVar b x) -> do
    let v = Map.findWithDefault (error $ "unknown var:" ++ show x) (x, "Class") subst
    return (annos, Expression v)
   ObjectJunction q cexps -> do
    acexps <- mapM (instantiateClassExpression subst var) $ 
                     map (\x -> ([], x)) cexps
    return (annos, ObjectJunction q $ map snd acexps)
   ObjectComplementOf cexp0 -> do  
     (_, cexp') <- instantiateClassExpression subst var ([], cexp0)
     return (annos, ObjectComplementOf cexp')
   ObjectOneOf indivs -> error "nyi"
   ObjectValuesFrom q opexp cexp0 -> do
    (_, opexp') <- instantiateObjectPropertyExpression subst var ([], opexp)
    (_, cexp') <- instantiateClassExpression subst var ([], cexp0)
    return (annos, ObjectValuesFrom q opexp' cexp')
   ObjectHasValue opexp indiv -> do
    (_, opexp') <- instantiateObjectPropertyExpression subst var ([], opexp)
    error "nyi"
   ObjectHasSelf opexp -> do 
    (_, opexp') <- instantiateObjectPropertyExpression subst var ([], opexp)
    return (annos, ObjectHasSelf opexp')
   ObjectCardinality (Cardinality cType aInt opexp mcexp) -> do 
    mcexp' <- case mcexp of
                  Nothing -> return Nothing
                  Just cexp0 -> do 
                    (_, cexp') <- instantiateClassExpression subst var ([], cexp0)
                    return $ Just cexp'
    (_, opexp') <- instantiateObjectPropertyExpression subst var ([], opexp)
    return (annos, ObjectCardinality (Cardinality cType aInt opexp' mcexp'))
   _ -> return (annos, cexp)
{-  Expression Class -- nothing to instantiate
  | DataValuesFrom QuantifierType DataPropertyExpression DataRange --TODO: once we have data properties as well!
  | DataHasValue DataPropertyExpression Literal
  | DataCardinality (Cardinality DataPropertyExpression DataRange)
-}

instantiateObjectPropertyExpression :: Map.Map (IRI, String) IRI -> PatternVarMap -> (Annotations, ObjectPropertyExpression) -> Result (Annotations, ObjectPropertyExpression)
instantiateObjectPropertyExpression subst var (annos, obexp) = 
 case obexp of
  ObjectProp i -> return (annos, ObjectProp $ instParamName subst i) -- nothing to instantiate
  ObjectInverseOf opexp -> do
   (_, opexp') <- instantiateObjectPropertyExpression subst var ([], opexp)
   return (annos, ObjectInverseOf opexp')
  ObjectPropertyVar b x -> do -- TODO: lists
   let v = Map.findWithDefault (error $ "unknown var:" ++ show x ++ " subst:" ++ show subst) (x, "ObjectProperty") subst
   return (annos, ObjectProp v)
  UnsolvedObjProp _ -> error $ "unsolved object property at instantiation: " ++ show obexp 

-- delete symbols from a solved macro, for optional parameters
deleteSymbolsMacro :: Set.Set Entity -> OntologyDocument -> Result OntologyDocument
deleteSymbolsMacro delSyms (OntologyDocument pd (Ontology n is as fs)) = do
 fs' <- deleteSymbolsFrames delSyms fs
 return $ OntologyDocument pd $ Ontology n is as fs'

deleteSymbolsFrames :: Set.Set Entity -> [Frame] -> Result [Frame]
deleteSymbolsFrames delSyms fs = do
 fs' <- mapM (deleteSymbolsFrame delSyms) fs
 return $ concat fs'

deleteSymbolsFrame :: Set.Set Entity -> Frame -> Result [Frame]
deleteSymbolsFrame delSyms f@(Frame ext fBits) =
 case ext of
   ClassEntity (VarExpression (MVar b i)) -> 
     if Set.member i $ Set.map (\x -> idToIRI $ entityToId x) delSyms  --TODO: handle lists
      then return []
      else return [f]
   _ -> error $ "nyi: " ++ show ext
