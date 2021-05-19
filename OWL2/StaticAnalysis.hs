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
import qualified OWL2.AS as AS
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
import Common.SetColimit

import Control.Monad

import Logic.Logic

-- | Error messages for static analysis
failMsg :: AS.Entity -> AS.ClassExpression -> Result a
failMsg (AS.Entity _ ty e) desc =
  fatal_error
    ("undeclared `" ++ AS.showEntityType ty
          ++ " " ++ showIRI e ++ "` in the following ClassExpression:\n"
          ++ showDoc desc "") $ iriPos e

-- | checks if an entity is in the signature
checkEntity :: Sign -> AS.Entity -> Result ()
checkEntity s t@(AS.Entity _ ty e) =
  let errMsg = mkError ("unknown " ++ AS.showEntityType ty) e
  in case ty of
   AS.Datatype -> unless (Set.member e (datatypes s) || AS.isDatatypeKey e) errMsg
   AS.Class -> unless (Set.member e (concepts s) || AS.isThing e) errMsg
   AS.ObjectProperty -> unless (isDeclObjProp s $ AS.ObjectProp e) errMsg
   AS.DataProperty -> unless (isDeclDataProp s e) errMsg
   AS.AnnotationProperty -> unless (Set.member e (annotationRoles s)
        || AS.isPredefAnnoProp e) $ justWarn () $ showDoc t " unknown"
   _ -> return ()

-- | takes an iri and finds out what entities it belongs to
correctEntity :: Sign -> IRI -> [AS.Entity]
correctEntity s iri =
    [AS.mkEntity AS.AnnotationProperty iri | Set.member iri (annotationRoles s)] ++
    [AS.mkEntity AS.Class iri | Set.member iri (concepts s)] ++
    [AS.mkEntity AS.ObjectProperty iri | Set.member iri (objectProperties s)] ++
    [AS.mkEntity AS.DataProperty iri | Set.member iri (dataProperties s)] ++
    [AS.mkEntity AS.Datatype iri | Set.member iri (datatypes s)] ++
    [AS.mkEntity AS.NamedIndividual iri | Set.member iri (individuals s)]

checkLiteral :: Sign -> AS.Literal -> Result ()
checkLiteral s l = case l of
    AS.Literal _ (AS.Typed dt) -> checkEntity s $ AS.mkEntity AS.Datatype dt
    _ -> return ()

isDeclInd :: Sign -> AS.Individual -> Bool
isDeclInd s ind = Set.member ind $ individuals s

isDeclObjProp :: Sign -> AS.ObjectPropertyExpression -> Bool
isDeclObjProp s ope = let op = AS.objPropToIRI ope in
    Set.member op (objectProperties s) || AS.isPredefObjProp op

isDeclDataProp :: Sign -> AS.DataPropertyExpression -> Bool
isDeclDataProp s dp = Set.member dp (dataProperties s) || AS.isPredefDataProp dp

{- | takes a list of object properties and discards the ones
    which are not in the signature -}
filterObjProp :: Sign -> [AS.ObjectPropertyExpression]
    -> [AS.ObjectPropertyExpression]
filterObjProp = filter . isDeclObjProp

checkObjPropList :: Sign -> [AS.ObjectPropertyExpression] -> Result ()
checkObjPropList s ol = do
    let ls = map (isDeclObjProp s) ol
    unless (and ls) $ fail $ "undeclared object properties:\n" ++
                      showDoc (map (\o -> case o of
                                     AS.ObjectProp _ -> o
                                     AS.ObjectInverseOf x -> x) ol) ""

checkDataPropList :: Sign -> [AS.DataPropertyExpression] -> Result ()
checkDataPropList s dl = do
    let ls = map (isDeclDataProp s) dl
    unless (and ls) $ fail $ "undeclared data properties:\n" ++ showDoc dl ""

-- | checks if a DataRange is valid
checkDataRange :: Sign -> AS.DataRange -> Result ()
checkDataRange s dr = case dr of
    AS.DataType dt rl -> do
        checkEntity s $ AS.mkEntity AS.Datatype dt
        mapM_ (checkLiteral s . snd) rl
    AS.DataJunction _ drl -> mapM_ (checkDataRange s) drl
    AS.DataComplementOf r -> checkDataRange s r
    AS.DataOneOf ll -> mapM_ (checkLiteral s) ll

{- | converts ClassExpression to DataRanges because some
     DataProperties may be parsed as ObjectProperties -}
classExpressionToDataRange :: Sign -> AS.ClassExpression -> Result AS.DataRange
classExpressionToDataRange s ce = case ce of
    AS.Expression u -> checkEntity s (AS.mkEntity AS.Datatype u)
        >> return (AS.DataType u [])
    AS.ObjectJunction jt cel -> fmap (AS.DataJunction jt)
        $ mapM (classExpressionToDataRange s) cel
    AS.ObjectComplementOf c -> fmap AS.DataComplementOf
        $ classExpressionToDataRange s c
    _ -> fail $ "cannot convert ClassExpression to DataRange\n"
            ++ showDoc ce ""

{- | checks a ClassExpression and recursively converts the
     (maybe inappropriately) parsed syntax to a one satisfying the signature -}
checkClassExpression :: Sign -> AS.ClassExpression -> Result AS.ClassExpression
checkClassExpression s desc =
    let errMsg i = failMsg i desc
        objErr i = errMsg $ AS.mkEntity AS.ObjectProperty i
        datErr i = errMsg $ AS.mkEntity AS.DataProperty i
    in case desc of
    AS.Expression u -> if AS.isThing u
        then return $ AS.Expression $ AS.setReservedPrefix u
        else checkEntity s (AS.mkEntity AS.Class u) >> return desc
    AS.ObjectJunction ty ds -> fmap (AS.ObjectJunction ty)
        $ mapM (checkClassExpression s) ds
    AS.ObjectComplementOf d -> fmap AS.ObjectComplementOf $ checkClassExpression s d
    AS.ObjectOneOf _ -> return desc
    AS.ObjectValuesFrom q opExpr d -> if isDeclObjProp s opExpr
        then fmap (AS.ObjectValuesFrom q opExpr) $ checkClassExpression s d
        else let iri = AS.objPropToIRI opExpr
             in if isDeclDataProp s iri then
                    fmap (AS.DataValuesFrom q [iri])
                      $ classExpressionToDataRange s d
                else objErr iri
    AS.ObjectHasSelf opExpr -> if isDeclObjProp s opExpr then return desc
        else objErr $ AS.objPropToIRI opExpr
    AS.ObjectHasValue opExpr _ -> if isDeclObjProp s opExpr then return desc
        else objErr $ AS.objPropToIRI opExpr
    AS.ObjectCardinality (AS.Cardinality a b opExpr md) -> do
        let iri = AS.objPropToIRI opExpr
            mbrOP = Set.member iri $ objectProperties s
        case md of
            Nothing
                | mbrOP -> return desc
                | isDeclDataProp s iri ->
                        return $ AS.DataCardinality $ AS.Cardinality a b iri Nothing
                | otherwise -> objErr iri
            Just d ->
                if mbrOP then fmap (AS.ObjectCardinality . AS.Cardinality a b opExpr
                            . Just) $ checkClassExpression s d
                else do
                    dr <- classExpressionToDataRange s d
                    if isDeclDataProp s iri then
                        return $ AS.DataCardinality
                          $ AS.Cardinality a b iri $ Just dr
                        else datErr iri
    AS.DataValuesFrom _ dExp r -> checkDataRange s r
        >> if isDeclDataProp s (head dExp) then return desc else datErr (head dExp)
    AS.DataHasValue dExp l -> do
        checkLiteral s l
        if isDeclDataProp s dExp then return desc
            else datErr dExp
    AS.DataCardinality (AS.Cardinality _ _ dExp mr) -> if isDeclDataProp s dExp
        then case mr of
            Nothing -> return desc
            Just d -> checkDataRange s d >> return desc
        else datErr dExp

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
checkHasKey :: Sign -> [AS.ObjectPropertyExpression] -> [AS.DataPropertyExpression]
    -> Result AnnFrameBit
checkHasKey s ol dl = do
    let nol = filterObjProp s ol
        ndl = map AS.objPropToIRI (ol \\ nol) ++ dl
        key = ClassHasKey nol ndl
        decl = map (isDeclDataProp s) ndl
    if and decl then return key
        else fail $ "Keys failed " ++ showDoc ol "" ++ showDoc dl "\n"

checkAnnotation :: Sign -> AS.Annotation -> Result ()
checkAnnotation s (AS.Annotation ans apr av) = do
    checkAnnos s [ans]
    checkEntity s (AS.mkEntity AS.AnnotationProperty apr)
    case av of
        AS.AnnValLit lit -> checkLiteral s lit
        _ -> return ()

checkAnnos :: Sign -> [Annotations] -> Result ()
checkAnnos = mapM_ . mapM . checkAnnotation

checkAnnoList :: Sign -> ([t] -> Result ()) -> [(Annotations, t)] -> Result ()
checkAnnoList s f anl = do
    checkAnnos s $ map fst anl
    f $ map snd anl

checkListBit :: Sign -> Maybe AS.Relation -> ListFrameBit -> Result ListFrameBit
checkListBit s r fb = case fb of
    AnnotationBit anl -> case r of
        Just (AS.DRRelation _) -> checkAnnos s (map fst anl) >> return fb
        _ -> checkAnnoList s (mapM_ $ checkEntity s .
                    AS.mkEntity AS.AnnotationProperty) anl >> return fb
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
                        show sorted ++ show (map AS.objPropToIRI $ ol \\ sorted)
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
        then let misc = Misc [AS.Annotation [] iri $ AS.AnnValue iri]
             in return [PlainAxiom misc ab] -- only for anonymous individuals
        else return $ map (\ x -> PlainAxiom (SimpleEntity x) ab) entList

checkExtended :: Sign -> Extended -> Result Extended
checkExtended s e = case e of
    ClassEntity ce -> fmap ClassEntity $ checkClassExpression s ce
    ObjectEntity oe -> case oe of
        AS.ObjectInverseOf op -> let i = AS.objPropToIRI op in
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
                Misc [AS.Annotation _ iri _] -> checkAssertion s iri ans
                    -- these can only come from Manchester Syntax
                SimpleEntity (AS.Entity _ _ iri) -> checkAssertion s iri ans
                ClassEntity (AS.Expression iri) -> checkAssertion s iri ans
                ObjectEntity (AS.ObjectProp iri) -> checkAssertion s iri ans
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
    Frame (SimpleEntity e) _ ->  addEntity e
    Frame (ClassEntity (AS.Expression e)) _ -> addEntity $ AS.mkEntity AS.Class e
    Frame (ObjectEntity (AS.ObjectProp e)) _ ->
        addEntity $ AS.mkEntity AS.ObjectProperty e
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

checkPrefixMap :: AS.PrefixMap -> Bool
checkPrefixMap pm =
    let pl = map (`Map.lookup` pm) ["owl", "rdf", "rdfs", "xsd"]
    in and $ zipWith check1Prefix pl
            (map snd $ tail $ Map.toList AS.predefPrefixes)

newODoc :: OntologyDocument -> [Frame] -> Result OntologyDocument
newODoc OntologyDocument {ontology = mo, prefixDeclaration = pd} fl =
    if checkPrefixMap pd
        then return OntologyDocument
                { ontology = mo {ontFrames = fl}, prefixDeclaration = pd}
        else fail $ "Incorrect predefined prefixes " ++ showDoc pd "\n"

-- | static analysis of ontology with incoming sign.
basicOWL2Analysis :: (OntologyDocument, Sign, GlobalAnnos)
    -> Result (OntologyDocument, ExtSign Sign AS.Entity, [Named Axiom])
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

-- | extract labels from Frame-List (after processing with correctFrames)
generateLabelMap :: Sign -> [Frame] -> Map.Map IRI String
generateLabelMap sig = foldr (\ (Frame ext fbl) -> case ext of
        SimpleEntity (AS.Entity _ _ ir) -> case fbl of
            [AnnFrameBit [AS.Annotation _ apr (AS.AnnValLit (AS.Literal s' _))] _]
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

getNames1 :: AS.Annotation -> [String]
getNames1 anno = case anno of
      AS.Annotation _ aIRI (AS.AnnValLit (AS.Literal value _)) ->
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
                     EndoMap AS.Entity, EndoMap AS.Entity)
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
           if AS.entityKind e1 == AS.entityKind e2 then do
              s <- AS.pairSymbols e1 e2
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
             EndoMap AS.Entity -> EndoMap AS.Entity -> REL_REF ->
             Result (Sign, [Named Axiom], Sign, Sign,
                     EndoMap AS.Entity, EndoMap AS.Entity)
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
           let e1' = if flag then e1 {AS.cutIRI =  addString (AS.cutIRI e1, "_source")} else e1
               e2' = if flag then e2 {AS.cutIRI =  addString (AS.cutIRI e2, "_target")} else e2
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
                              case (AS.entityKind e1', AS.entityKind e2') of
                                (AS.Class, AS.Class) -> AS.EDRelation AS.Equivalent
                                (AS.ObjectProperty, AS.ObjectProperty) ->
                                   AS.EDRelation AS.Equivalent
                                (AS.NamedIndividual, AS.NamedIndividual) -> AS.SDRelation AS.Same
                                _ -> error $ "use subsumption only between"
                                              ++ "classes or roles:" ++
                                              show l1 ++ " " ++ show l2) $
                           ExpressionBit [([], AS.Expression $ AS.cutIRI e1')]
             return (sigB, [makeNamed "" axiom], sig1, sig2, eMap1', eMap2')
            Subs -> do
             let extPart = mkExtendedEntity e2'
                 axiom = PlainAxiom extPart $
                           ListFrameBit (Just $
                              case (AS.entityKind e1', AS.entityKind e2') of
                                (AS.Class, AS.Class) -> AS.SubClass
                                (AS.ObjectProperty, AS.ObjectProperty) ->
                                    AS.SubPropertyOf
                                _ -> error $ "use subsumption only between"
                                              ++ "classes or roles:" ++
                                              show l1 ++ " " ++ show l2) $
                           ExpressionBit [([], AS.Expression $ AS.cutIRI e1')]
             return (sigB, [makeNamed "" axiom], sig1, sig2, eMap1', eMap2')
            Incomp -> do
             let extPart = mkExtendedEntity e1'
                 axiom = PlainAxiom extPart $
                           ListFrameBit (Just $ AS.EDRelation AS.Disjoint) $
                           ExpressionBit [([], AS.Expression $ AS.cutIRI e2')]
             return (sigB, [makeNamed "" axiom], sig1, sig2, eMap1', eMap2')
            IsSubs -> do
             let extPart = mkExtendedEntity e1'
                 axiom = PlainAxiom extPart $
                           ListFrameBit (Just AS.SubClass) $
                           ExpressionBit [([], AS.Expression $ AS.cutIRI e2')]
             return (sigB, [makeNamed "" axiom], sig1, sig2, eMap1', eMap2')
            InstOf -> do
             let extPart = mkExtendedEntity e1'
                 axiom = PlainAxiom extPart $
                           ListFrameBit (Just AS.Types) $
                           ExpressionBit [([], AS.Expression $ AS.cutIRI e2')]
             return
                 (sigB, [makeNamed "" axiom], sig1, sig2, eMap1', eMap2')
            HasInst -> do
             let extPart = mkExtendedEntity e2'
                 axiom = PlainAxiom extPart $
                           ListFrameBit (Just AS.Types) $
                           ExpressionBit [([], AS.Expression $ AS.cutIRI e1')]
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
