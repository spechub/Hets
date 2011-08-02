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
import Data.Maybe

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

objPropToIRI :: ObjectPropertyExpression -> Individual
objPropToIRI opExp = case opExp of
    ObjectProp u -> u
    ObjectInverseOf objProp -> objPropToIRI objProp

maybeObjProp :: Sign -> ObjectPropertyExpression
                -> Maybe ObjectPropertyExpression
maybeObjProp s op = if Set.member (objPropToIRI op) (objectProperties s)
                   then Just op else Nothing

{- | takes a list of object properties and discards the ones
    which are not in the signature -}
sortObjDataList :: Sign -> [ObjectPropertyExpression]
                -> [ObjectPropertyExpression]
sortObjDataList = mapMaybe . maybeObjProp

checkObjPropList :: Sign -> a -> [ObjectPropertyExpression] -> Result a
checkObjPropList s fb ol = do
    let ls = map (\ u -> Set.member (objPropToIRI u)
              (objectProperties s) ) ol
    if elem False ls then
        fail $ "Static analysis found that not all properties" ++
               " in the following list are ObjectProperties\n\n"
          ++ show ol
     else return fb

checkDataPropList :: Sign -> a -> [DataPropertyExpression] -> Result a
checkDataPropList s fb dl = do
    let ls = map (\ u -> Set.member u (dataProperties s) ) dl
    if elem False ls then
        fail $ "Static analysis found that not all properties" ++
               " in the following list are DataProperties\n\n"
          ++ show dl
     else return fb

-- | checks if a DataRange is valid
checkDataRange :: Sign -> DataRange -> Result DataRange
checkDataRange s dr = case dr of
    DataType dt _ -> checkEntity s (Entity Datatype dt) >> return dr
    DataJunction _ drl -> mapM_ (checkDataRange s) drl >> return dr
    DataComplementOf r -> checkDataRange s r
    _ -> return dr

{- | converts ClassExpression to DataRanges because some
     DataProperties may be parsed as ObjectProperties -}
classExpressionToDataRange :: Sign -> ClassExpression -> Result DataRange
classExpressionToDataRange s ce = case ce of
    Expression u -> checkEntity s (Entity Datatype u)
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
      objErr i = errMsg $ Entity ObjectProperty i
      datErr i = errMsg $ Entity DataProperty i
  in case desc of
  Expression u ->
     if isThing u then
     return $ Expression u { namePrefix = "owl", iriType = Abbreviated }
     else checkEntity s (Entity Class u) >> return desc
  ObjectJunction a ds -> fmap (ObjectJunction a)
        $ mapM (checkClassExpression s) ds
  ObjectComplementOf d -> fmap ObjectComplementOf
        $ checkClassExpression s d
  ObjectOneOf _ -> return desc
  ObjectValuesFrom a opExpr d -> do
    let iri = objPropToIRI opExpr
        mbrOP = Set.member iri (objectProperties s)
        mbrDP = Set.member iri (dataProperties s)
    if mbrOP then fmap (ObjectValuesFrom a opExpr) $ checkClassExpression s d
     else if mbrDP then do
            ndr <- classExpressionToDataRange s d
            _ <- checkDataRange s ndr
            return $ DataValuesFrom a iri ndr
           else objErr iri
  ObjectHasSelf opExpr -> do
    let iri = objPropToIRI opExpr
    if Set.member iri (objectProperties s) then return desc
     else objErr iri
  ObjectHasValue opExpr _ -> do
    let iri = objPropToIRI opExpr
    if Set.member iri (objectProperties s) then return desc else objErr iri
  ObjectCardinality (Cardinality a b opExpr md) -> do
    let iri = objPropToIRI opExpr
    let mbrOP = Set.member iri (objectProperties s)
    let mbrDP = Set.member iri (dataProperties s)
    case md of
      Nothing -> if mbrOP then return desc else objErr iri
      Just d ->
        if mbrOP then do
           n <- checkClassExpression s d
           return $ ObjectCardinality (Cardinality a b opExpr (Just n))
         else do
           dr <- classExpressionToDataRange s d
           _ <- checkDataRange s dr
           if mbrDP then return $ DataCardinality
                (Cardinality a b iri (Just dr))
            else datErr iri
  DataValuesFrom _ dExp r -> do
    _ <- checkDataRange s r
    if Set.member dExp (dataProperties s) then return desc else datErr dExp
  DataHasValue dExp _ ->
    if Set.member dExp (dataProperties s) then return desc else datErr dExp
  DataCardinality (Cardinality _ _ dExp mr) -> 
    if Set.member dExp (dataProperties s) then case mr of
          Nothing -> return desc
          Just d -> checkDataRange s d >> return desc
      else datErr dExp

checkFactList :: Sign -> ListFrameBit -> [Fact] -> Result ListFrameBit
checkFactList s fb fl = mapM_ (checkFact s fb) fl >> return fb

checkFact :: Sign -> ListFrameBit -> Fact -> Result ListFrameBit
checkFact s fb f = case f of
    ObjectPropertyFact _ op _ ->
        if Set.member (objPropToIRI op) (objectProperties s) then return fb
         else fail "Static analysis. ObjectPropertyFact failed"
    DataPropertyFact _ dp _ ->
        if Set.member dp (dataProperties s) then return fb
         else fail "Static analysis. DataProperty fact failed"

checkHasKeyAll :: Sign -> AnnFrameBit -> Result AnnFrameBit
checkHasKeyAll s k = case k of
  ClassHasKey ol dl -> do
    let l1 = map (\ u -> Set.member (objPropToIRI u) (objectProperties s) ) ol
        l2 = map (`Set.member` dataProperties s) dl
    if elem False (l1 ++ l2) then
      fail "Static analysis. Keys failed, undeclared Data or Object Properties"
     else return k
  _ -> return k

-- | sorts the data and object properties
checkHasKey :: Sign -> AnnFrameBit -> Result AnnFrameBit
checkHasKey s k = case k of
  ClassHasKey ol dl -> do
    let sl = sortObjDataList s ol
    let k2 = ClassHasKey sl (map objPropToIRI (ol \\ sl) ++ dl)
    checkHasKeyAll s k2
  _ -> return k

checkListBit :: Sign -> Maybe Relation -> ListFrameBit -> Result ListFrameBit
checkListBit s r fb = case fb of
    AnnotationBit anl -> case r of
        Just (DRRelation _) -> return fb
        _ -> mapM_ (checkEntity s . Entity AnnotationProperty
                . snd) anl >> return fb
    ExpressionBit anl -> do
        n <- mapM (checkClassExpression s . snd) anl
        return $ ExpressionBit $ zip (map fst anl) n
    ObjectBit anl -> do
        let ol = map snd anl
        let sorted = sortObjDataList s ol
        if null sorted then do
            let dpl = map objPropToIRI ol
            let nb = DataBit $ zip (map fst anl) dpl
            checkDataPropList s nb dpl
          else
            if length sorted == length ol then return fb
               else fail $ "Static analysis found that there are" ++
                           " multiple types of properties in\n\n" ++
                            show sorted ++ show
                              (map objPropToIRI (ol \\ sorted))
    ObjectCharacteristics _ -> return fb
    DataBit anl -> checkDataPropList s fb $ map snd anl
    DataPropRange anl -> mapM_ (checkDataRange s . snd) anl >> return fb
    IndividualFacts anl -> checkFactList s fb $ map snd anl
    IndividualSameOrDifferent _ -> return fb

checkAnnBit :: Sign -> AnnFrameBit -> Result AnnFrameBit
checkAnnBit s fb = case fb of
    DatatypeBit dr -> checkDataRange s dr >> return fb
    ClassDisjointUnion cel -> fmap ClassDisjointUnion
        $ mapM (checkClassExpression s) cel
    ClassHasKey _ _ -> checkHasKey s fb
    ObjectSubPropertyChain ol -> checkObjPropList s fb ol
    _ -> return fb

-- | corrects the frame bits according to the signature
checkBit :: Sign -> FrameBit -> Result FrameBit
checkBit s fb = case fb of
    ListFrameBit mr lfb -> fmap (ListFrameBit mr) $ checkListBit s mr lfb
    AnnFrameBit ans afb -> fmap (AnnFrameBit ans) $ checkAnnBit s afb

checkExtended :: Sign -> Extended -> Result Extended
checkExtended s e = case e of
    ClassEntity ce -> fmap ClassEntity $ checkClassExpression s ce
    ObjectEntity oe -> case oe of
        ObjectInverseOf op ->
            if Set.member (objPropToIRI op) (objectProperties s)
            then return e else fail $ "unknown object property" ++ show op
        _ -> return e
    _ -> return e

-- | checks a frame and applies desired changes
checkFrame :: Sign -> Frame -> Result Frame
checkFrame s (Frame eith fbl) = do
    ne <- checkExtended s eith
    nl <- mapM (checkBit s) fbl
    return $ Frame ne nl

correctFrames :: Sign -> [Frame] -> Result [Frame]
correctFrames = mapM . checkFrame

getEntityFromFrame :: Frame -> State Sign ()
getEntityFromFrame f = case f of
    Frame (SimpleEntity e) _ -> addEntity e
    Frame (ClassEntity (Expression e)) _ -> addEntity $ Entity Class e
    Frame (ObjectEntity (ObjectProp e)) _ ->
        addEntity $ Entity ObjectProperty e
    Frame _ [AnnFrameBit al AnnotationFrameBit] -> case al of
        [Annotation [] iri1 (AnnValue iri2)] ->
            when (iri1 == iri2) $ addEntity $ Entity AnnotationProperty iri1
        _ -> return ()
    _ -> return ()

-- | collects all entites from the frames
createSign :: [Frame] -> State Sign ()
createSign f = do
  pm <- gets prefixMap
  mapM_ (getEntityFromFrame . function Expand pm) f

-- | corrects the axioms according to the signature
createAxioms :: Sign -> [Frame] -> Result ([Named Axiom], [Frame])
createAxioms s fl = do
    cf <- correctFrames s $ map (function Expand $ prefixMap s) fl
    return (map anaAxiom $ concatMap getAxioms cf, cf)

modifyOntologyDocument :: OntologyDocument -> [Frame] -> OntologyDocument
modifyOntologyDocument
    OntologyDocument {ontology = mo, prefixDeclaration = pd} fl =
      OntologyDocument { ontology = mo {ontFrames = fl},
            prefixDeclaration = pd}

-- | static analysis of ontology with incoming sign.
basicOWL2Analysis ::
    (OntologyDocument, Sign, GlobalAnnos) ->
        Result (OntologyDocument, ExtSign Sign Entity, [Named Axiom])

basicOWL2Analysis (odoc, inSign, _) = do
    let pd = prefixDeclaration odoc
        fs = ontFrames $ ontology odoc
    let syms = Set.difference (symOf accSign) $ symOf inSign
        accSign = execState
          (createSign fs)
          inSign {prefixMap = pd}
    (axl, nfl) <- createAxioms accSign fs
    let newdoc = modifyOntologyDocument odoc nfl
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
