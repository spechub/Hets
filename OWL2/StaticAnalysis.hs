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

--import OWL.Namespace
import OWL2.Sign
import OWL2.AS
import OWL2.MS
import OWL2.FS
import OWL2.GetAxioms

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
anaAxiom x = case x of 
  PlainAxiom as _ -> findImplied as
  _ -> id
 $ makeNamed "" x

checkLiteral :: Sign -> Literal -> Result Literal
checkLiteral s (Literal a ty) = case ty of
  Typed u -> checkEntity s (Literal a ty) (Entity Datatype u)
  _ -> return (Literal a ty)

checkEntity :: Sign -> a -> Entity -> Result a
checkEntity s a (Entity ty e) = case ty of
      Datatype -> if Set.member e (datatypes s) then return a else fail $ showQN e ++ " datatype undeclared"
      Class -> if Set.member e (concepts s) then return a else fail $ showQN e ++ " class undeclared"
      ObjectProperty -> if Set.member e (objectProperties s) then return a else fail $ showQN e ++ "object property undeclared"
      DataProperty -> if Set.member e (dataProperties s) then return a else fail $ showQN e ++ " data property undeclared" 
      NamedIndividual -> if Set.member e (individuals s) then return a else fail $ showQN e ++ " individual undeclared"
      AnnotationProperty -> if Set.member e (annotationRoles s) then return a else fail $ showQN e ++ " annotation property undeclared"
    
checkDataRange :: Sign -> DataRange -> Result DataRange
checkDataRange s dr = 
  case dr of
    DataType dt fcs -> do
      let x = checkEntity s dr (Entity Datatype dt)
      let y = map (checkLiteral s) (map snd fcs)
      if any isNothing (map maybeResult y) || isNothing (maybeResult x) then fail "datatype restriction failed" else return dr 
    DataJunction _ drl -> do
      let x = map (checkDataRange s) drl
      if any isNothing (map maybeResult x) then fail "data junction failed"
       else return dr
    DataComplementOf r -> checkDataRange s r
    DataOneOf ls -> do
      let x = map (checkLiteral s) ls
      if any isNothing (map maybeResult x) then fail "data one of failed" 
       else return dr
    
checkClassExpression :: Sign -> ClassExpression -> Result ClassExpression
checkClassExpression s desc = case desc of
  Expression u -> case u of
        QN _ "Thing" _ _ -> return $ Expression $ QN "owl" "Thing" False ""
        QN _ "Nothing" _ _ -> return $ Expression $ QN "owl" "Nothing" False ""
        _ -> checkEntity s desc (Entity Class u) 
  ObjectJunction _ ds -> do 
      let x = map (checkClassExpression s) ds 
      if any isNothing (map maybeResult x) then fail "object junction failed"
       else return desc
  ObjectComplementOf d -> do  
      checkClassExpression s d
  ObjectOneOf is -> do 
      let x = map (checkEntity s desc) (map (Entity NamedIndividual) is)
      if any isNothing (map maybeResult x) then fail "data one of failed"
       else return desc
  ObjectValuesFrom a opExpr d -> do
      let iri = getObjRoleFromExpression opExpr 
      let x = Set.member iri (objectProperties s)
      let z = Set.member iri (dataProperties s)
      if x == True then do
          let y = checkClassExpression s d
          if isNothing (maybeResult y) then fail "corrected data values from failed"
            else return desc
        else if z == True then do
                let Expression u = d
                return (DataValuesFrom a iri [] (DataType u []))  
              else fail "corrected data values from failed"
          
  ObjectHasSelf opExpr -> do
    if Set.member (getObjRoleFromExpression opExpr) (objectProperties s) then return desc
     else fail "Failed"
  ObjectHasValue opExpr i -> do
    let x = Set.member (getObjRoleFromExpression opExpr) (objectProperties s) 
    let y = checkEntity s desc (Entity NamedIndividual i)
    if (x == False || isNothing (maybeResult y) ) then fail "object has value failed" 
              else return desc
  ObjectCardinality (Cardinality a b opExpr md) -> do
    let iri = getObjRoleFromExpression opExpr 
    let x = Set.member iri (objectProperties s)
    let z = Set.member iri (dataProperties s)
    case md of 
        Nothing -> if x == False then fail "object cardinality failed with no class expression provided"
                        else return desc
        Just d -> if x then do
                      let y = checkClassExpression s d
                      if isNothing (maybeResult y) then fail "object cardinality failed"
                        else return desc
                    else do
                        let Expression u = d
                            dr = DataType u []
                        let chk = checkDataRange s dr 
                        if isNothing (maybeResult chk) then fail $ "corrected data cardinality failed: " ++ showQN iri
                          else 
                            if z == False then fail $ "corrected data cardinality failed: " ++ showQN iri 
                              else return $ DataCardinality (Cardinality a b iri (Just dr))
  DataValuesFrom _ dExp ds r -> do
    let x = Set.isSubsetOf (Set.fromList(dExp : ds)) (dataProperties s) 
    let y = checkDataRange s r
    if (x == False || isNothing (maybeResult y) ) then fail "data values from failed" 
              else return desc
  DataHasValue dExp _ -> do
    let x = Set.member dExp (dataProperties s) 
    if x == False then fail "data has value failed" 
              else return desc  
  DataCardinality (Cardinality _ _ dExp mr) -> do
    let x = Set.member dExp (dataProperties s)
    case mr of 
        Nothing -> if x == False then fail "data cardinality failed with no class expression provided"
                             else return desc
        Just d -> do
            let y = checkDataRange s d
            if (x == False || isNothing (maybeResult y) ) then fail "data cardinality failed"
                      else return desc

checkBit :: Sign -> FrameBit -> Result FrameBit
checkBit s fb = case fb of
    AnnotationFrameBit _ -> return fb
    AnnotationBit _ anl -> do
        let apl = map snd (convertAnnList anl)
        let x = map (checkEntity s fb) (map (Entity AnnotationProperty) apl)
        if any isNothing (map maybeResult x) then fail "annotation bit failed"
                  else return fb
    AnnotationDR _ _ -> return fb
    DatatypeBit _ dr -> do 
        let x = checkDataRange s dr
        if isNothing (maybeResult x) then fail "datatype bit failed" 
                  else return fb
    ExpressionBit _ anl -> do
        let x = map (checkClassExpression s) (map snd $ convertAnnList anl)
        if any isNothing (map maybeResult x) then fail "expression bit failed"
                  else return fb
    ClassDisjointUnion _ cel -> do
        let x = map (checkClassExpression s) cel
        if any isNothing (map maybeResult x) then fail "class disjoint union failed" 
                  else return fb
    ClassHasKey _ _ _ -> checkHasKey s fb 
    ObjectBit _ anl -> do
        let ol = map snd $ convertAnnList anl
        checkObjPropList s fb ol
    ObjectDomainOrRange _ anl -> do
        let ds = map snd $ convertAnnList anl
        let y = map (checkClassExpression s) ds
        if any isNothing (map maybeResult y) then fail "obj domain or range failed" 
                else return fb
    ObjectCharacteristics _ -> return fb
    ObjectSubPropertyChain _ ol -> checkObjPropList s fb ol
    DataBit _ anl -> do
        let dl = map snd $ convertAnnList anl
        checkDataPropList s fb dl
    DataPropDomain anl -> do
        let dr = map snd $ convertAnnList anl
        let x = map (checkClassExpression s) dr
        if any isNothing (map maybeResult x) then fail "data property domain failed"
                  else return fb 
    DataPropRange anl -> do
        let dr = map snd $ convertAnnList anl
        let x = map (checkDataRange s) dr
        if any isNothing (map maybeResult x) then fail "data property range failed"
                  else return fb  
    DataFunctional _ -> return fb
    IndividualFacts anl -> do
        let f = map snd $ convertAnnList anl
        checkFactList s fb f 
    IndividualSameOrDifferent _ anl -> do
        let i = map snd $ convertAnnList anl
        let y = map (checkEntity s fb) (map (Entity NamedIndividual) i)
        if any isNothing (map maybeResult y) then fail "individual same or different failed" 
                  else return fb

checkFactList :: Sign -> FrameBit -> [Fact] -> Result FrameBit
checkFactList s fb fl = do
    let x = map (checkFact s fb) fl
    if any isNothing (map maybeResult x) then fail "fact failed" 
              else return fb   

checkFact :: Sign -> FrameBit -> Fact -> Result FrameBit
checkFact s fb f = do 
    case f of
      ObjectPropertyFact _ op _ -> 
        if Set.member (getObjRoleFromExpression op) (objectProperties s) then return fb
         else fail "object property fact failed"
      DataPropertyFact _ dp _ -> 
            if Set.member dp (dataProperties s) then return fb
             else fail "data property fact failed" 
    
checkObjPropList :: Sign -> FrameBit -> [ObjectPropertyExpression] -> Result FrameBit
checkObjPropList s fb ol = do
        let x = map (\ u -> Set.member (getObjRoleFromExpression u) (objectProperties s) ) ol
        if elem False x then fail "not obj property list"
                  else return fb

checkDataPropList :: Sign -> FrameBit -> [DataPropertyExpression] -> Result FrameBit
checkDataPropList s fb dl = do
        let x = map (\ u -> Set.member u (dataProperties s) ) dl
        if elem False x then fail "not data property list"
                  else return fb

checkHasKeyAll :: Sign -> FrameBit -> Result FrameBit
checkHasKeyAll s k = case k of
  ClassHasKey a ol dl -> do
    let x = map (\ u -> Set.member (getObjRoleFromExpression u) (objectProperties s) ) ol
        y = map (\ u -> Set.member u (dataProperties s) ) dl 
    if elem False (x ++ y) then fail "keys failed"
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
      let x = map (checkClassExpression s) cl
      if any isNothing (map maybeResult x) then fail "equiv or disjoint classes failed" else return m
    MiscEquivOrDisjointObjProp ol -> do
      let x = sortObjDataList s ol
      if null x then return $ MiscEquivOrDisjointDataProp (map getObjRoleFromExpression x) else return m
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
      let x = map (checkBit s) fbl
      if any isNothing (map maybeResult x) then fail "bit failed" else return $ Frame a (catMaybes (map maybeResult x)) 
    MiscFrame r al misc -> do
      let x = maybeResult $ checkMisc s misc
      case x of 
        Nothing -> fail "misc failed"
        Just m -> return (MiscFrame r al m)
    MiscSameOrDifferent _ _ il -> do
      let y = map (checkEntity s f) (map (Entity NamedIndividual) il)
      if any isNothing (map maybeResult y) then fail "same or different individuals failed"
                  else return f

correctFrames :: Sign -> [Frame] -> Result [Frame]
correctFrames s fl = do
    let x = map (checkFrame s) fl
    if any isNothing (map maybeResult x) then fail "correct frames failed"
                  else return (catMaybes (map maybeResult x))

createAxioms :: Sign -> [Frame] -> Result [Named Axiom]
createAxioms s fl = do
    let x = correctFrames s fl 
    if isNothing (maybeResult x) then fail "unable to create axioms from frames"
              else return $ map anaAxiom $ concatMap getAxioms (fromJust (maybeResult x))

-- | static analysis of ontology with incoming sign.
basicOWL2Analysis ::
    (OntologyDocument, Sign, GlobalAnnos) ->
        Result (OntologyDocument, ExtSign Sign Entity, [Named Axiom])

basicOWL2Analysis (odoc, inSign, _) = do 
    let --ns = prefixDeclaration odoc
        syms = Set.difference (symOf accSign) $ symOf inSign
        (_, accSign) = runState
          (createSign $ ontologyFrame $ mOntology odoc)
          inSign
    axl <- createAxioms accSign (ontologyFrame (mOntology odoc))
    return (odoc, ExtSign accSign syms, axl)

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

isToProve :: [OWL2.AS.Annotation] -> Bool
isToProve [] = False
isToProve (anno : r) =
    case anno of
      Annotation _ aIRI (AnnValLit(Literal value (Typed _))) ->
          if localPart aIRI == "Implied" then isInfixOf "true" value
            else isToProve r
      _ -> isToProve r

