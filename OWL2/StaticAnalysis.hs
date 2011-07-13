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
import OWL2.Theorem
import OWL2.XML (simpleSplit)
import OWL2.Expand

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List
import Data.Maybe

import Common.AS_Annotation
import Common.Result
import Common.GlobalAnnotations
import Common.ExtSign
import Common.Lib.State
import Control.Monad

-- | Error messages for static analysis
failMsg :: Maybe Entity -> String -> String
failMsg ent s = case ent of
    Just (Entity ty e) -> "Static analysis cannot find " ++ showEntityType ty
          ++ " " ++ showQN e ++ s
    Nothing -> s

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
  if elem u $ map (simpleSplit . mkQName) datatypeKeys then put s
   else put $ case ty of
    Datatype -> s { datatypes = chg $ datatypes s }
    Class -> s { concepts = chg $ concepts s }
    ObjectProperty -> s { objectProperties = chg $ objectProperties s }
    DataProperty -> s { dataProperties = chg $ dataProperties s }
    NamedIndividual -> s { individuals = chg $ individuals s }
    AnnotationProperty -> s {annotationRoles = chg $ annotationRoles s}

-- | adding entities to the signature
addEntity :: Entity -> State Sign ()
addEntity = modEntity Set.insert

-- | adding annotations for theorems
anaAxiom :: Axiom -> Named Axiom
anaAxiom x = findImplied x $ makeNamed "" x

-- | checks if an entity is in the signature
checkEntity :: Sign -> a -> Entity -> Result a
checkEntity s a ent =
  let Entity ty e = ent
  in case ty of
   Datatype -> if Set.member e (datatypes s) ||
                    elem (localPart e) datatypeKeys
                  then return a
                else fail $ failMsg (Just ent) ""
   Class -> if Set.member e (concepts s) then return a
             else fail $ failMsg (Just ent) ""
   ObjectProperty -> if Set.member e (objectProperties s) then return a
                      else fail $ failMsg (Just ent) ""
   DataProperty -> if Set.member e (dataProperties s) then return a
                    else fail $ failMsg (Just ent) ""
   NamedIndividual -> if Set.member e (individuals s) then return a
                       else fail $ failMsg (Just ent) ""
   AnnotationProperty -> if Set.member e (annotationRoles s) then return a
                          else fail $ failMsg (Just ent) ""

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
    _ -> fail $ failMsg Nothing
            "Static analysis cannot correct so parsed ClassExpression\n\n"
            ++ show ce ++ "\n\nto a DataRange"

{- | checks a ClassExpression and recursively converts the
     (maybe inappropriately) parsed syntax to a one satisfying the signature -}
checkClassExpression :: Sign -> ClassExpression -> Result ClassExpression
checkClassExpression s desc = case desc of
  Expression u -> case u of
    QN _ "Thing" _ _ -> return $ Expression $ QN "owl" "Thing" False ""
    QN _ "Nothing" _ _ -> return $ Expression $ QN "owl" "Nothing" False ""
    _ -> checkEntity s desc (Entity Class u)
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
            return $ DataValuesFrom a iri [] ndr
           else fail $ failMsg (Just $ Entity ObjectProperty iri)
              " in the following ClassExpression\n\n" ++ show desc
  ObjectHasSelf opExpr -> do
    let iri = getObjRoleFromExpression opExpr
    if Set.member iri (objectProperties s) then return desc
     else fail $ failMsg (Just $ Entity ObjectProperty iri)
              " in the following ClassExpression\n\n" ++ show desc
  ObjectHasValue opExpr i -> do
    let iri = getObjRoleFromExpression opExpr
        x = Set.member iri (objectProperties s)
    if x then do
         checkEntity s desc (Entity NamedIndividual i)
         return desc
      else fail $ failMsg (Just $ Entity ObjectProperty iri)
               " in the following ClassExpression\n\n" ++ show desc
  ObjectCardinality (Cardinality a b opExpr md) -> do
    let iri = getObjRoleFromExpression opExpr
    let x = Set.member iri (objectProperties s)
    let z = Set.member iri (dataProperties s)
    case md of
      Nothing ->
        if x then return desc
         else fail $ failMsg (Just $ Entity ObjectProperty iri)
              " in the following ClassExpression\n\n" ++ show desc
      Just d ->
        if x then do
           n <- checkClassExpression s d
           return $ ObjectCardinality (Cardinality a b opExpr (Just n))
         else do
           dr <- classExpressionToDataRange s d
           checkDataRange s dr
           if z then return $ DataCardinality (Cardinality a b iri (Just dr))
            else fail $ failMsg (Just $ Entity DataProperty iri)
                       " in the following ClassExpression\n\n" ++ show desc
  DataValuesFrom _ dExp ds r -> do
    checkDataRange s r
    let x = Set.isSubsetOf (Set.fromList (dExp : ds)) (dataProperties s)
    if x then return desc
     else fail $ failMsg (Just $ Entity DataProperty dExp)
                " in the following ClassExpression\n\n" ++ show desc
  DataHasValue dExp _ -> do
    let x = Set.member dExp (dataProperties s)
    if x then return desc
     else fail $ failMsg (Just $ Entity DataProperty dExp)
                " in the following ClassExpression\n\n" ++ show desc
  DataCardinality (Cardinality _ _ dExp mr) -> do
    let x = Set.member dExp (dataProperties s)
    if x then
        case mr of
          Nothing -> return desc
          Just d -> do
            checkDataRange s d
            return desc
      else fail $ failMsg (Just $ Entity DataProperty dExp)
                 " in the following ClassExpression\n\n" ++ show desc

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
    _ -> return ()

createSign :: [Frame] -> State Sign ()
createSign f = do
  s <- get
  mapM_ (getEntityFromFrame . expF s) f

createAxioms :: Sign -> [Frame] -> Result ([Named Axiom], [Frame])
createAxioms s fl = do
    x <- correctFrames s $ map (expF s) fl
    return (map anaAxiom $ concatMap getAxioms x, x)

modifyOntologyDocument :: OntologyDocument -> [Frame] -> OntologyDocument
modifyOntologyDocument
    OntologyDocument {mOntology = mo, prefixDeclaration = pd} fl =
      OntologyDocument { mOntology = mo {ontologyFrame = fl},
            prefixDeclaration = pd}

-- | static analysis of ontology with incoming sign.
basicOWL2Analysis ::
    (OntologyDocument, Sign, GlobalAnnos) ->
        Result (OntologyDocument, ExtSign Sign Entity, [Named Axiom])

basicOWL2Analysis (odoc, inSign, _) = do
    let ns = prefixDeclaration odoc
        fs = ontologyFrame $ mOntology odoc
    integNamespace <- integrateNamespaces (prefixMap inSign) ns
    let syms = Set.difference (symOf accSign) $ symOf inSign
        accSign = execState
          (createSign fs)
          inSign {prefixMap = integNamespace}
    (axl, nfl) <- createAxioms accSign fs
    let newdoc = modifyOntologyDocument odoc nfl
    return (newdoc , ExtSign accSign syms, axl)

testAndInteg :: PrefixMap -> (String, String) -> Result PrefixMap

testAndInteg old (pre, ouri) =
    case Map.lookup pre old of
      Just iri -> if ouri == iri then return old else
       fail $ "Static analysis found a prefix clash " ++ pre
      Nothing -> return $ Map.insert pre ouri old

uniteSign :: Sign -> Sign -> Result Sign
uniteSign s1 s2 = do
    pm <- integrateNamespaces (prefixMap s1) (prefixMap s2)
    return $ (addSign s1 s2) {prefixMap = pm}

integrateNamespaces :: PrefixMap -> PrefixMap
                    -> Result PrefixMap
integrateNamespaces oldNsMap testNsMap =
        foldM testAndInteg oldNsMap (Map.toList testNsMap)

findImplied :: Axiom -> Named Axiom -> Named Axiom
findImplied ax sent =
  if isToProve ax then sent
         { isAxiom = False
         , isDef = False
         , wasTheorem = False }
   else sent { isAxiom = True }
