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

import OWL2.PrefixMap
import OWL2.Sign
import OWL2.AS
import OWL2.MS
import OWL2.FS
import OWL2.GetAxioms

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List
import Data.Maybe

import Common.AS_Annotation
import Common.Result
import Common.GlobalAnnotations
import Common.ExtSign
import Common.Lib.State

modEntity :: (IRI -> Set.Set IRI -> Set.Set IRI) -> Entity -> State Sign ()
modEntity f (Entity ty u) = do
  s <- get
  let chg = f u
  put $ case ty of
    Datatype -> s { datatypes = chg $ datatypes s }
    Class -> s { concepts = chg $ concepts s }
    ObjectProperty -> s { objectProperties = chg $ objectProperties s }
    DataProperty -> s { dataProperties = chg $ dataProperties s }
    NamedIndividual -> s { individuals = chg $ individuals s }
    AnnotationProperty -> s {annotationRoles = chg $ annotationRoles s}

addEntity :: Entity -> State Sign ()
addEntity = modEntity Set.insert

anaAxiom :: Axiom -> Named Axiom
anaAxiom x = case x of PlainAxiom as _ -> findImplied as $ makeNamed "" x

checkEntity :: Sign -> a -> Entity -> Result a
checkEntity s a (Entity ty e) = case ty of
      Datatype -> if Set.member e (datatypes s) then return a 
                    else fail $ "Static analysis. Datatype undeclared " ++ showQN e
      Class -> if Set.member e (concepts s) then return a 
                    else fail $ "Static analysis. Class undeclared " ++ showQN e 
      ObjectProperty -> if Set.member e (objectProperties s) then return a 
                          else fail $ "Static analysis. ObjectProperty undeclared " ++ showQN e
      DataProperty -> if Set.member e (dataProperties s) then return a 
                        else fail $ "Static analysis. DataProperty undeclared " ++ showQN e 
      NamedIndividual -> if Set.member e (individuals s) then return a 
                          else fail $ "Static analysis. Individual undeclared " ++ showQN e
      AnnotationProperty -> if Set.member e (annotationRoles s) then return a 
                             else fail $ "Static analysis. AnnotationProperty undeclared " ++ showQN e
    
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
    _-> return dr

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
    _ -> fail "Static analysis. Failed to convert ClassExpression to DataRange"
    
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
      mapM_ (checkEntity s desc) (map (Entity NamedIndividual) is)
      return desc
  ObjectValuesFrom a opExpr d -> do
      let iri = getObjRoleFromExpression opExpr 
      let x = Set.member iri (objectProperties s)
      let z = Set.member iri (dataProperties s)
      if x then do
          n <- checkClassExpression s d
          return $ ObjectValuesFrom a opExpr n
        else if z then do
                ndr <- classExpressionToDataRange s d
                checkDataRange s ndr
                return $ DataValuesFrom a iri [] ndr 
              else fail $ "Static analysis. ObjectValuesFrom failed, Data or Object Property undeclared " ++ showQN iri 
  ObjectHasSelf opExpr -> do
    let iri = getObjRoleFromExpression opExpr
    if Set.member iri (objectProperties s) then return desc
     else fail $ "Static analysis. ObjectHasSelf failed, ObjectProperty undeclared " ++ showQN iri
  ObjectHasValue opExpr i -> do             
    let iri = getObjRoleFromExpression opExpr
    let x = Set.member iri (objectProperties s)
    if x then do
                checkEntity s desc (Entity NamedIndividual i)
                return desc
      else fail $ "Static analysis. ObjectHasValue failed, ObjectProperty undeclared " ++ showQN iri
  ObjectCardinality (Cardinality a b opExpr md) -> do
    let iri = getObjRoleFromExpression opExpr 
    let x = Set.member iri (objectProperties s)
    let z = Set.member iri (dataProperties s)
    case md of 
      Nothing -> if x then return desc 
                  else fail $ "Static analysis. ObjectCardinality failed with no class expression provided, ObjectProperty undeclared " ++ showQN iri 
      Just d -> if x then do
                    n <- checkClassExpression s d
                    return $ ObjectCardinality (Cardinality a b opExpr (Just n))
                  else do
                      dr <- classExpressionToDataRange s d
                      checkDataRange s dr 
                      if z then return $ DataCardinality (Cardinality a b iri (Just dr))
                        else fail $ "Static analysis. Corrected DataCardinality failed, Object or Data Property undeclared " ++ showQN iri
  DataValuesFrom _ dExp ds r -> do
    checkDataRange s r
    let x = Set.isSubsetOf (Set.fromList(dExp : ds)) (dataProperties s) 
    if x then return desc else fail "Static analysis. DataValuesFrom failed, some DataProperty undeclared"
  DataHasValue dExp _ -> do
    let x = Set.member dExp (dataProperties s) 
    if x then return desc else fail $ "Static analysis. DataHasValue failed, DataProperty undeclared " ++ showQN dExp 
  DataCardinality (Cardinality _ _ dExp mr) -> do
    let x = Set.member dExp (dataProperties s)
    if x then do
        case mr of 
          Nothing -> return desc
          Just d -> do
            checkDataRange s d
            return desc
      else fail $ "Static analysis. DataCardinality failed, DataProperty undeclared " ++ showQN dExp

checkBit :: Sign -> FrameBit -> Result FrameBit
checkBit s fb = case fb of
    AnnotationFrameBit _ -> return fb
    AnnotationBit r anl -> case r of
        DRRelation _ -> return fb
        _ -> do
            let apl = map snd $ convertAnnList anl
            mapM_ (checkEntity s fb) $ map (Entity AnnotationProperty) apl
            return fb
    DatatypeBit _ dr -> do 
        checkDataRange s dr
        return fb
    ExpressionBit a anl -> do
        let ans = map fst $ convertAnnList anl
        let ce = map snd $ convertAnnList anl
        n <- mapM (checkClassExpression s) ce
        return $ ExpressionBit a $ AnnotatedList $ zip ans n
    ClassDisjointUnion a cel -> do
        n <- mapM (checkClassExpression s) cel
        return $ ClassDisjointUnion a n
    ClassHasKey _ _ _ -> checkHasKey s fb 
    ObjectBit _ anl -> do
        let ol = map snd $ convertAnnList anl
        checkObjPropList s fb ol
    ObjectCharacteristics _ -> return fb
    ObjectSubPropertyChain _ ol -> checkObjPropList s fb ol
    DataBit _ anl -> do
        let dl = map snd $ convertAnnList anl
        checkDataPropList s fb dl
    DataPropRange anl -> do
        let dr = map snd $ convertAnnList anl
        mapM_ (checkDataRange s) dr
        return fb  
    DataFunctional _ -> return fb
    IndividualFacts anl -> do
        let f = map snd $ convertAnnList anl
        checkFactList s fb f 
    IndividualSameOrDifferent _ anl -> do
        let i = map snd $ convertAnnList anl
        mapM_ (checkEntity s fb) (map (Entity NamedIndividual) i)
        return fb

checkFactList :: Sign -> FrameBit -> [Fact] -> Result FrameBit
checkFactList s fb fl = do
    mapM_ (checkFact s fb) fl
    return fb   

checkFact :: Sign -> FrameBit -> Fact -> Result FrameBit
checkFact s fb f = do 
    case f of
      ObjectPropertyFact _ op _ -> 
        if Set.member (getObjRoleFromExpression op) (objectProperties s) then return fb
         else fail "Static analysis. ObjectPropertyFact failed"
      DataPropertyFact _ dp _ -> 
            if Set.member dp (dataProperties s) then return fb
             else fail "Static analysis. DataProperty fact failed" 
    
checkObjPropList :: Sign -> a -> [ObjectPropertyExpression] -> Result a
checkObjPropList s fb ol = do
        let x = map (\ u -> Set.member (getObjRoleFromExpression u) (objectProperties s) ) ol
        if elem False x then fail "Static analysis. Error: not all properties in the list are ObjectProperties"
                  else return fb

checkDataPropList :: Sign -> a -> [DataPropertyExpression] -> Result a
checkDataPropList s fb dl = do
        let x = map (\ u -> Set.member u (dataProperties s) ) dl
        if elem False x then fail "Static analysis. Error: not all properties in the list are DataProperties"
                  else return fb

checkHasKeyAll :: Sign -> FrameBit -> Result FrameBit
checkHasKeyAll s k = case k of
  ClassHasKey a ol dl -> do
    let x = map (\ u -> Set.member (getObjRoleFromExpression u) (objectProperties s) ) ol
        y = map (\ u -> Set.member u (dataProperties s) ) dl 
    if elem False (x ++ y) then fail "Static analysis. Keys failed, undeclared Data or Object Properties"
              else return (ClassHasKey a ol dl)
  _ -> return k

checkHasKey :: Sign -> FrameBit -> Result FrameBit
checkHasKey s k = case k of 
  ClassHasKey a ol _ -> do 
    let x = sortObjDataList s ol 
    let k2 = ClassHasKey a x (map getObjRoleFromExpression (ol \\ x)) 
    checkHasKeyAll s k2
  _ -> return k

sortObjData :: Sign -> ObjectPropertyExpression -> Maybe ObjectPropertyExpression
sortObjData s op = 
    let p = getObjRoleFromExpression op in
    if Set.member p (objectProperties s) then Just op
     else Nothing

sortObjDataList :: Sign -> [ObjectPropertyExpression] -> [ObjectPropertyExpression]
sortObjDataList s = catMaybes . map (sortObjData s)

checkMisc :: Sign -> Misc -> Result Misc
checkMisc s m = case m of
    MiscEquivOrDisjointClasses cl -> do
      n <- mapM (checkClassExpression s) cl
      return $ MiscEquivOrDisjointClasses n
    MiscEquivOrDisjointObjProp ol -> do
      let x = sortObjDataList s ol
      if null x then do
          let dpl = map getObjRoleFromExpression ol
          let nm = MiscEquivOrDisjointDataProp dpl
          checkDataPropList s nm dpl
          return nm 
        else if length x == length ol then return m else fail "Static analysis. Error: Object and Data Properties mixed in the wrong place."
    _ -> return m

getEntityFromFrame :: Frame -> State Sign ()
getEntityFromFrame f = case f of
    Frame e _ -> addEntity e
    _ -> return ()

createSign :: [Frame] -> State Sign ()
createSign = mapM_ getEntityFromFrame

checkFrame :: Sign -> Frame -> Result Frame
checkFrame s f = case f of
    Frame a fbl -> do
      nl <- mapM (checkBit s) fbl
      return $ Frame a nl
    MiscFrame r al misc -> do
      x <- checkMisc s misc
      return $ MiscFrame r al x
    MiscSameOrDifferent _ _ il -> do
      mapM_ (checkEntity s f) (map (Entity NamedIndividual) il)
      return f

correctFrames :: Sign -> [Frame] -> Result [Frame]
correctFrames s fl = mapM (checkFrame s) fl

createAxioms :: Sign -> [Frame] -> Result ([Named Axiom], [Frame])
createAxioms s fl = do
    x <- correctFrames s fl 
    return (map anaAxiom $ concatMap getAxioms x, x)

modifyOntologyDocument :: OntologyDocument -> [Frame] -> OntologyDocument
modifyOntologyDocument OntologyDocument {mOntology = mo, prefixDeclaration = pd} fl = 
            OntologyDocument { mOntology = mo {ontologyFrame = fl}, prefixDeclaration = pd}

-- | static analysis of ontology with incoming sign.
basicOWL2Analysis ::
    (OntologyDocument, Sign, GlobalAnnos) ->
        Result (OntologyDocument, ExtSign Sign Entity, [Named Axiom])

basicOWL2Analysis (odoc, inSign, _) = do 
    let syms = Set.difference (symOf accSign) $ symOf inSign
        (_, accSign) = runState
          (createSign $ ontologyFrame $ mOntology odoc)
          inSign
    (axl, nfl) <- createAxioms accSign (ontologyFrame (mOntology odoc))
    let newdoc = modifyOntologyDocument odoc nfl
    return (newdoc , ExtSign accSign syms, axl)

getObjRoleFromExpression :: ObjectPropertyExpression -> IndividualRoleIRI
getObjRoleFromExpression opExp =
    case opExp of
       ObjectProp u -> u
       ObjectInverseOf objProp -> getObjRoleFromExpression objProp

getObjRoleFromSubExpression :: SubObjectPropertyExpression
                            -> [IndividualRoleIRI]
getObjRoleFromSubExpression sopExp =
    case sopExp of
      OPExpression opExp -> [getObjRoleFromExpression opExp]
      SubObjectPropertyChain expList ->
          map getObjRoleFromExpression expList

findImplied :: [OWL2.AS.Annotation] -> Named Axiom -> Named Axiom
findImplied anno sent =
  if isToProve anno then sent
         { isAxiom = False
         , isDef = False
         , wasTheorem = False }
   else sent { isAxiom = True }
