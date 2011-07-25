{- |
Module      :  $Header$
Copyright   :  Felix Gabriel Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisional
Portability :  portable

Contains    :  static analysis for OWL 2
-}

module OWL2.StaticAnalysis where

import OWL2.Sign
import OWL2.AS
import OWL2.MS
import OWL2.Print ()
import OWL2.Theorem
import OWL2.Expand

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

getObjRoleFromExpression :: ObjectPropertyExpression -> IndividualRoleIRI
getObjRoleFromExpression opExp =
    case opExp of
       ObjectProp u -> u
       ObjectInverseOf objProp -> getObjRoleFromExpression objProp

sortObjData :: Sign -> ObjectPropertyExpression
                -> Maybe ObjectPropertyExpression
sortObjData s op =
    let p = getObjRoleFromExpression op in
    if Set.member p (objectProperties s) then Just op
     else Nothing

sortObjDataList :: Sign -> [ObjectPropertyExpression]
                -> [ObjectPropertyExpression]
sortObjDataList s = mapMaybe $ sortObjData s

modEntity :: (IRI -> Set.Set IRI -> Set.Set IRI) -> Entity -> State Sign ()
modEntity f (Entity ty u) = do
  s <- get
  let chg = f u
  unless (isDatatypeKey u) $ put $ case ty of
    Datatype -> s { datatypes = chg $ datatypes s }
    Class -> s { concepts = chg $ concepts s }
    ObjectProperty -> s { objectProperties = chg $ objectProperties s }
    DataProperty -> s { dataProperties = chg $ dataProperties s }
    NamedIndividual ->
        if isAnonymous u then s
         else s { individuals = chg $ individuals s }
    AnnotationProperty -> s {annotationRoles = chg $ annotationRoles s}

-- | adding entities to the signature
addEntity :: Entity -> State Sign ()
addEntity = modEntity Set.insert

-- | adding annotations for theorems
anaAxiom :: Axiom -> Named Axiom
anaAxiom x = findImplied x $ makeNamed "" x

-- | checks if an entity is in the signature
checkEntity :: Sign -> a -> Entity -> Result a
checkEntity s a (Entity ty e) =
  let errMsg = mkError ("unknown " ++ showEntityType ty) e
  in case ty of
   Datatype -> if Set.member e (datatypes s) ||
                    isDatatypeKey e
                  then return a
                else errMsg
   Class -> if Set.member e (concepts s) then return a
             else errMsg
   ObjectProperty -> if Set.member e (objectProperties s) then return a
                      else errMsg
   DataProperty -> if Set.member e (dataProperties s) then return a
                    else errMsg
   NamedIndividual -> if Set.member e (individuals s) then return a
                       else errMsg
   AnnotationProperty -> if Set.member e (annotationRoles s) then return a
                          else errMsg

-- | checks if a DataRange is valid
checkDataRange :: Sign -> DataRange -> Result DataRange
checkDataRange s dr =
  case dr of
    DataType dt _ -> do
      checkEntity s dr (Entity Datatype dt)
      return dr
    DataJunction _ drl -> do
      mapM_ (checkDataRange s) drl
      return dr
    DataComplementOf r -> checkDataRange s r
    _ -> return dr

{- | converts ClassExpression to DataRanges because some
     DataProperties may be parsed as ObjectProperties -}
classExpressionToDataRange :: Sign -> ClassExpression -> Result DataRange
classExpressionToDataRange s ce = case ce of
    Expression u -> do
      checkEntity s ce (Entity Datatype u)
      return $ DataType u []
    ObjectJunction jt cel -> do
      nrl <- mapM (classExpressionToDataRange s) cel
      return $ DataJunction jt nrl
    ObjectComplementOf c -> do
      nr <- classExpressionToDataRange s c
      return $ DataComplementOf nr
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
     return $ Expression u { namePrefix = "owl", isFullIri = False }
     else checkEntity s desc (Entity Class u)
  ObjectJunction a ds -> do
    nl <- mapM (checkClassExpression s) ds
    return $ ObjectJunction a nl
  ObjectComplementOf d -> do
    n <- checkClassExpression s d
    return $ ObjectComplementOf n
  ObjectOneOf is -> do
    mapM_ (checkEntity s desc . Entity NamedIndividual) is
    return desc
  ObjectValuesFrom a opExpr d -> do
    let iri = getObjRoleFromExpression opExpr
        x = Set.member iri (objectProperties s)
        z = Set.member iri (dataProperties s)
    if x then do
      n <- checkClassExpression s d
      return $ ObjectValuesFrom a opExpr n
     else if z then do
            ndr <- classExpressionToDataRange s d
            checkDataRange s ndr
            return $ DataValuesFrom a iri ndr
           else objErr iri
  ObjectHasSelf opExpr -> do
    let iri = getObjRoleFromExpression opExpr
    if Set.member iri (objectProperties s) then return desc
     else objErr iri
  ObjectHasValue opExpr i -> do
    let iri = getObjRoleFromExpression opExpr
        x = Set.member iri (objectProperties s)
    if x then do
         checkEntity s desc (Entity NamedIndividual i)
         return desc
      else objErr iri
  ObjectCardinality (Cardinality a b opExpr md) -> do
    let iri = getObjRoleFromExpression opExpr
    let x = Set.member iri (objectProperties s)
    let z = Set.member iri (dataProperties s)
    case md of
      Nothing ->
        if x then return desc
         else objErr iri
      Just d ->
        if x then do
           n <- checkClassExpression s d
           return $ ObjectCardinality (Cardinality a b opExpr (Just n))
         else do
           dr <- classExpressionToDataRange s d
           checkDataRange s dr
           if z then return $ DataCardinality (Cardinality a b iri (Just dr))
            else datErr iri
  DataValuesFrom _ dExp r -> do
    checkDataRange s r
    let x = Set.member dExp (dataProperties s)
    if x then return desc
     else datErr dExp
  DataHasValue dExp _ -> do
    let x = Set.member dExp (dataProperties s)
    if x then return desc
     else datErr dExp
  DataCardinality (Cardinality _ _ dExp mr) -> do
    let x = Set.member dExp (dataProperties s)
    if x then
        case mr of
          Nothing -> return desc
          Just d -> do
            checkDataRange s d
            return desc
      else datErr dExp

-- corrects the frame bits according to the signature

checkAnnBit :: Sign -> AnnFrameBit -> Result AnnFrameBit
checkAnnBit s fb = case fb of
    DatatypeBit dr -> do
        checkDataRange s dr
        return fb
    ClassDisjointUnion cel -> do
        n <- mapM (checkClassExpression s) cel
        return $ ClassDisjointUnion n
    ClassHasKey _ _ -> checkHasKey s fb
    ObjectSubPropertyChain ol -> checkObjPropList s fb ol
    _ -> return fb


checkListBit :: Sign -> Maybe Relation -> ListFrameBit -> Result ListFrameBit
checkListBit s r fb = case fb of
    AnnotationBit anl -> case r of
        Just (DRRelation _) -> return fb
        _ -> do
            let apl = map snd anl
            mapM_ (checkEntity s fb . Entity AnnotationProperty) apl
            return fb
    ExpressionBit anl -> do
        let ans = map fst anl
        let ce = map snd anl
        n <- mapM (checkClassExpression s) ce
        return $ ExpressionBit $ zip ans n
    ObjectBit anl -> do
        let ans = map fst anl
        let ol = map snd anl
        let x = sortObjDataList s ol
        if null x then do
            let dpl = map getObjRoleFromExpression ol
            let nb = DataBit $ zip ans dpl
            checkDataPropList s nb dpl
          else
            if length x == length ol then return fb
               else fail $ "Static analysis found that there are" ++
                           " multiple types of properties in\n\n" ++
                            show x ++ show
                              (map getObjRoleFromExpression (ol \\ x))
    ObjectCharacteristics _ -> return fb
    DataBit anl -> do
        let dl = map snd anl
        checkDataPropList s fb dl
    DataPropRange anl -> do
        let dr = map snd anl
        mapM_ (checkDataRange s) dr
        return fb
    IndividualFacts anl -> do
        let f = map snd anl
        checkFactList s fb f
    IndividualSameOrDifferent anl -> do
        let i = map snd anl
        mapM_ (checkEntity s fb . Entity NamedIndividual) i
        return fb

checkBit :: Sign -> FrameBit -> Result FrameBit
checkBit s fb = case fb of
    ListFrameBit mr lfb -> do
        nf <- checkListBit s mr lfb
        return $ ListFrameBit mr nf
    AnnFrameBit ans afb -> do
        nf <- checkAnnBit s afb
        return $ AnnFrameBit ans nf

checkFactList :: Sign -> ListFrameBit -> [Fact] -> Result ListFrameBit
checkFactList s fb fl = do
    mapM_ (checkFact s fb) fl
    return fb

checkFact :: Sign -> ListFrameBit -> Fact -> Result ListFrameBit
checkFact s fb f =
    case f of
      ObjectPropertyFact _ op _ ->
        if Set.member (getObjRoleFromExpression op) (objectProperties s) then
            return fb
         else fail "Static analysis. ObjectPropertyFact failed"
      DataPropertyFact _ dp _ ->
            if Set.member dp (dataProperties s) then return fb
             else fail "Static analysis. DataProperty fact failed"

checkObjPropList :: Sign -> a -> [ObjectPropertyExpression] -> Result a
checkObjPropList s fb ol = do
    let x = map (\ u -> Set.member (getObjRoleFromExpression u)
              (objectProperties s) ) ol
    if elem False x then
        fail $ "Static analysis found that not all properties" ++
               " in the following list are ObjectProperties\n\n"
          ++ show ol
     else return fb

checkDataPropList :: Sign -> a -> [DataPropertyExpression] -> Result a
checkDataPropList s fb dl = do
    let x = map (\ u -> Set.member u (dataProperties s) ) dl
    if elem False x then
        fail $ "Static analysis found that not all properties" ++
               " in the following list are DataProperties\n\n"
          ++ show dl
     else return fb

checkHasKeyAll :: Sign -> AnnFrameBit -> Result AnnFrameBit
checkHasKeyAll s k = case k of
  ClassHasKey ol dl -> do
    let x = map (\ u -> Set.member (getObjRoleFromExpression u)
              (objectProperties s) ) ol
        y = map (\ u -> Set.member u (dataProperties s) ) dl
    if elem False (x ++ y) then
      fail "Static analysis. Keys failed, undeclared Data or Object Properties"
     else return k
  _ -> return k

checkHasKey :: Sign -> AnnFrameBit -> Result AnnFrameBit
checkHasKey s k = case k of
  ClassHasKey ol dl -> do
    let x = sortObjDataList s ol
    let k2 = ClassHasKey x (map getObjRoleFromExpression (ol \\ x) ++ dl)
    checkHasKeyAll s k2
  _ -> return k

checkExtended :: Sign -> Extended -> Result Extended
checkExtended s e = case e of
    ClassEntity ce -> do
        ne <- checkClassExpression s ce
        return $ ClassEntity ne
    _ -> return e

-- | checks a frame and applies desired changes
checkFrame :: Sign -> Frame -> Result Frame
checkFrame s (Frame eith fbl) = do
      ne <- checkExtended s eith
      nl <- mapM (checkBit s) fbl
      return $ Frame ne nl

correctFrames :: Sign -> [Frame] -> Result [Frame]
correctFrames s = mapM (checkFrame s)

getEntityFromFrame :: Frame -> State Sign ()
getEntityFromFrame f = case f of
    Frame (SimpleEntity e) _ -> addEntity e
    Frame (ClassEntity (Expression e)) _ ->
        addEntity $ Entity Class e
    Frame (ObjectEntity (ObjectProp e)) _ ->
        addEntity $ Entity ObjectProperty e
    Frame _ [AnnFrameBit al AnnotationFrameBit]
        -> case al of
            [Annotation [] iri1 (AnnValue iri2)] ->
                when (iri1 == iri2) $ addEntity $ Entity AnnotationProperty iri1
            _ -> return ()
    _ -> return ()

createSign :: [Frame] -> State Sign ()
createSign f = do
  pm <- gets prefixMap
  mapM_ (getEntityFromFrame . expF pm) f

createAxioms :: Sign -> [Frame] -> Result ([Named Axiom], [Frame])
createAxioms s fl = do
    x <- correctFrames s $ map (expF $ prefixMap s) fl
    return (map anaAxiom $ concatMap getAxioms x, x)

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

findImplied :: Axiom -> Named Axiom -> Named Axiom
findImplied ax sent =
  if prove ax then sent
         { isAxiom = False
         , isDef = False
         , wasTheorem = False }
   else sent { isAxiom = True }
