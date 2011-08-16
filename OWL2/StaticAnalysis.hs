{- |
Module      :  $Header$
Copyright   :  Felix Gabriel Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisional
Portability :  portable

Static analysis for OWL 2
-}

module OWL2.StaticAnalysis where

import OWL2.Sign
import OWL2.AS
import OWL2.MS
import OWL2.Print ()
import OWL2.Theorem
import OWL2.Function

import qualified Data.Set as Set
import Data.List

import Common.AS_Annotation
import Common.DocUtils
import Common.Result
import Common.GlobalAnnotations
import Common.ExtSign
import Common.Lib.State

import Control.Monad

-- | Error messages for static analysis
failMsg :: Entity -> ClassExpression -> Result a
failMsg (Entity ty e) desc =
  fatal_error
    ("undeclared `" ++ showEntityType ty
          ++ " " ++ showQN e ++ "` in the following ClassExpression:\n"
          ++ showDoc desc "") $ iriPos e

-- | takes an entity and modifies the sign according to the given function
modEntity :: (IRI -> Set.Set IRI -> Set.Set IRI) -> Entity -> State Sign ()
modEntity f (Entity ty u) = do
  s <- get
  let chg = f u
  unless (isDatatypeKey u || isThing u) $ put $ case ty of
    Datatype -> s { datatypes = chg $ datatypes s }
    Class -> s { concepts = chg $ concepts s }
    ObjectProperty -> s { objectProperties = chg $ objectProperties s }
    DataProperty -> s { dataProperties = chg $ dataProperties s }
    NamedIndividual -> if isAnonymous u then s
         else s { individuals = chg $ individuals s }
    AnnotationProperty -> s {annotationRoles = chg $ annotationRoles s}

-- | adding entities to the signature
addEntity :: Entity -> State Sign ()
addEntity = modEntity Set.insert

-- | checks if an entity is in the signature
checkEntity :: Sign -> Entity -> Result ()
checkEntity s (Entity ty e) =
  let errMsg = mkError ("unknown " ++ showEntityType ty) e
  in case ty of
   Datatype -> unless (Set.member e (datatypes s) || isDatatypeKey e) errMsg
   Class -> unless (Set.member e (concepts s) || isThing e) errMsg
   ObjectProperty -> unless (Set.member e $ objectProperties s) errMsg
   DataProperty -> unless (Set.member e $ dataProperties s) errMsg
   AnnotationProperty -> unless (Set.member e $ annotationRoles s) errMsg
   _ -> return ()

-- | takes an iri and finds out what entities it belongs to
correctEntity :: Sign -> IRI -> [Entity]
correctEntity s iri =
    [Entity AnnotationProperty iri | Set.member iri (annotationRoles s)] ++
    [Entity Class iri | Set.member iri (concepts s)] ++
    [Entity ObjectProperty iri | Set.member iri (objectProperties s)] ++
    [Entity DataProperty iri | Set.member iri (dataProperties s)] ++
    [Entity Datatype iri | Set.member iri (datatypes s)] ++
    [Entity NamedIndividual iri | Set.member iri (individuals s)]

objPropToIRI :: ObjectPropertyExpression -> Individual
objPropToIRI opExp = case opExp of
    ObjectProp u -> u
    ObjectInverseOf objProp -> objPropToIRI objProp

isDeclObjProp :: Sign -> ObjectPropertyExpression -> Bool
isDeclObjProp s ope = Set.member (objPropToIRI ope) $ objectProperties s

isDeclDataProp :: Sign -> DataPropertyExpression -> Bool
isDeclDataProp s dp = Set.member dp $ dataProperties s

{- | takes a list of object properties and discards the ones
    which are not in the signature -}
filterObjProp :: Sign -> [ObjectPropertyExpression]
    -> [ObjectPropertyExpression]
filterObjProp = filter . isDeclObjProp

checkObjPropList :: Sign -> [ObjectPropertyExpression] -> Result ()
checkObjPropList s ol = do
    let ls = map (isDeclObjProp s) ol
    unless (and ls) $ fail $ "Static analysis found that not all properties" ++
        " in the following list are ObjectProperties\n\n" ++ show ol

checkDataPropList :: Sign -> [DataPropertyExpression] -> Result ()
checkDataPropList s dl = do
    let ls = map (isDeclDataProp s) dl
    unless (and ls) $ fail $ "Static analysis found that not all properties" ++
        " in the following list are DataProperties\n\n" ++ show dl

-- | checks if a DataRange is valid
checkDataRange :: Sign -> DataRange -> Result ()
checkDataRange s dr = case dr of
    DataType dt _ -> checkEntity s $ Entity Datatype dt
    DataJunction _ drl -> mapM_ (checkDataRange s) drl
    DataComplementOf r -> checkDataRange s r
    _ -> return ()

{- | converts ClassExpression to DataRanges because some
     DataProperties may be parsed as ObjectProperties -}
classExpressionToDataRange :: Sign -> ClassExpression -> Result DataRange
classExpressionToDataRange s ce = case ce of
    Expression u -> checkEntity s (Entity Datatype u) >> return (DataType u [])
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
        objErr i = errMsg $ Entity ObjectProperty i
        datErr i = errMsg $ Entity DataProperty i
    in case desc of
    Expression u -> if isThing u
        then return $ Expression $ setReservedPrefix u
        else checkEntity s (Entity Class u) >> return desc
    ObjectJunction ty ds -> fmap (ObjectJunction ty)
        $ mapM (checkClassExpression s) ds
    ObjectComplementOf d -> fmap ObjectComplementOf $ checkClassExpression s d
    ObjectOneOf _ -> return desc
    ObjectValuesFrom q opExpr d -> if isDeclObjProp s opExpr
        then fmap (ObjectValuesFrom q opExpr) $ checkClassExpression s d
        else let iri = objPropToIRI opExpr
             in if isDeclDataProp s iri then do
                        ndr <- classExpressionToDataRange s d
                        checkDataRange s ndr
                        return $ DataValuesFrom q iri ndr
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
                    checkDataRange s dr
                    if isDeclDataProp s iri then
                        return $ DataCardinality $ Cardinality a b iri $ Just dr
                        else datErr iri
    DataValuesFrom _ dExp r -> do
        checkDataRange s r
        if isDeclDataProp s dExp then return desc else datErr dExp
    DataHasValue dExp _ -> if isDeclDataProp s dExp then return desc
        else datErr dExp
    DataCardinality (Cardinality _ _ dExp mr) -> if isDeclDataProp s dExp
        then case mr of
            Nothing -> return desc
            Just d -> checkDataRange s d >> return desc
        else datErr dExp

checkFact :: Sign -> Fact -> Result ()
checkFact s f = case f of
    ObjectPropertyFact _ op _ -> unless (isDeclObjProp s op) $
        fail $ "Static analysis. ObjectPropertyFact failed " ++ show f
    DataPropertyFact _ dp _ -> unless (isDeclDataProp s dp) $
        fail $ "Static analysis. DataProperty fact failed " ++ show f

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

checkListBit :: Sign -> Maybe Relation -> ListFrameBit -> Result ListFrameBit
checkListBit s r fb = case fb of
    AnnotationBit anl -> case r of
        Just (DRRelation _) -> return fb
        _ -> mapM_ (checkEntity s . Entity AnnotationProperty . snd) anl
                >> return fb
    ExpressionBit anl -> do
        n <- mapM (checkClassExpression s . snd) anl
        return $ ExpressionBit $ zip (map fst anl) n
    ObjectBit anl -> do
        let ol = map snd anl
            sorted = filterObjProp s ol
        if null sorted then do
            let dpl = map objPropToIRI ol
            checkDataPropList s dpl >> return (DataBit $ zip (map fst anl) dpl)
            else if length sorted == length ol then return fb
                    else fail $ "Static analysis found that there are" ++
                        " multiple types of properties in\n\n" ++
                        show sorted ++ show (map objPropToIRI $ ol \\ sorted)
    ObjectCharacteristics _ -> return fb
    DataBit anl -> checkDataPropList s (map snd anl) >> return fb
    DataPropRange anl -> mapM_ (checkDataRange s . snd) anl >> return fb
    IndividualFacts anl -> checkFactList s (map snd anl) >> return fb
    IndividualSameOrDifferent _ -> return fb

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
    _ -> return e

-- | corrects the axiom according to the signature
checkAxiom :: Sign -> Axiom -> Result [Axiom]
checkAxiom s ax@(PlainAxiom ext fb) = case fb of
    ListFrameBit mr lfb -> do
        next <- checkExtended s ext
        nfb <- fmap (ListFrameBit mr) $ checkListBit s mr lfb
        return [PlainAxiom next nfb]
    ab@(AnnFrameBit ans afb) -> case afb of
        AnnotationFrameBit ty -> case ty of
            Assertion -> case ext of
                    -- this can only come from XML
                Misc [Annotation _ iri _] -> checkAssertion s iri ans
                    -- these can only come from Manchester Syntax
                SimpleEntity (Entity _ iri) -> checkAssertion s iri ans
                ClassEntity (Expression iri) -> checkAssertion s iri ans
                ObjectEntity (ObjectProp iri) -> checkAssertion s iri ans
                _ -> do next <- checkExtended s ext
                        -- could rarely happen, and only in our extended syntax
                        return [PlainAxiom next ab]
            Declaration -> return [ax]
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
    Frame (ClassEntity (Expression e)) _ -> addEntity $ Entity Class e
    Frame (ObjectEntity (ObjectProp e)) _ ->
        addEntity $ Entity ObjectProperty e
    _ -> return ()

-- | collects all entites from the frames
createSign :: [Frame] -> State Sign ()
createSign f = do
  pm <- gets prefixMap
  mapM_ (collectEntities . function Expand pm) f

-- | corrects the axioms according to the signature
createAxioms :: Sign -> [Frame] -> Result ([Named Axiom], [Frame])
createAxioms s fl = do
    cf <- correctFrames s $ map (function Expand $ prefixMap s) fl
    return (map anaAxiom $ concatMap getAxioms cf, cf)

newODoc :: OntologyDocument -> [Frame] -> OntologyDocument
newODoc OntologyDocument {ontology = mo, prefixDeclaration = pd} fl =
    OntologyDocument { ontology = mo {ontFrames = fl}, prefixDeclaration = pd}

-- | static analysis of ontology with incoming sign.
basicOWL2Analysis :: (OntologyDocument, Sign, GlobalAnnos)
    -> Result (OntologyDocument, ExtSign Sign Entity, [Named Axiom])
basicOWL2Analysis (odoc, inSign, _) = do
    let fs = ontFrames $ ontology odoc
        syms = Set.difference (symOf accSign) $ symOf inSign
        accSign = execState (createSign fs)
          inSign {prefixMap = prefixDeclaration odoc}
    (axl, nfl) <- createAxioms accSign fs
    let newdoc = newODoc odoc nfl
    return (newdoc , ExtSign accSign syms, axl)

-- | adding annotations for theorems
anaAxiom :: Axiom -> Named Axiom
anaAxiom ax = findImplied ax $ makeNamed "" ax

findImplied :: Axiom -> Named Axiom -> Named Axiom
findImplied ax sent =
  if prove ax then sent
         { isAxiom = False
         , isDef = False
         , wasTheorem = False }
   else sent { isAxiom = True }
