{- |
Module      :  $Header$
Copyright   :  Heng Jiang, Uni Bremen 2004-2007
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

static analysis of basic specifications for OWL 1.1.
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
{-
anaAxiom :: Axiom -> State Sign [Named Axiom]
anaAxiom x = let PlainAxiom as p = x in do
    anaPlainAxiom p
    return [findImplied as $ makeNamed "" $ x]
-}

checkLiteral :: Literal -> State Sign (Maybe Literal)
checkLiteral (Literal a ty) = case ty of
  Typed u -> checkEntity (Literal a ty) (Entity Datatype u)
  _ -> return $ Just (Literal a ty)

checkEntity :: a -> Entity -> State Sign (Maybe a)
checkEntity a (Entity ty e) = do
    s <- get
    case ty of
      Datatype -> if Set.member e (datatypes s) then return $ return a else fail $ showQN e ++ " datatype undeclared"
      Class -> if Set.member e (concepts s) then return $ return a else fail $ showQN e ++ " class undeclared"
      ObjectProperty -> if Set.member e (objectProperties s) then return $ return a else fail $ showQN e ++ "object property undeclared"
      DataProperty -> if Set.member e (dataProperties s) then return $ return a else fail $ showQN e ++ " data property undeclared" 
      NamedIndividual -> if Set.member e (individuals s) then return $ return a else fail $ showQN e ++ " individual undeclared"
      AnnotationProperty -> if Set.member e (annotationRoles s) then return $ return a else fail $ showQN e ++ " annotation property undeclared"
    
checkDataRange :: DataRange -> State Sign (Maybe DataRange)
checkDataRange dr = 
  case dr of
    DataType u -> checkEntity dr (Entity Datatype u)
    DataJunction _ drl -> do
      x <- mapM checkDataRange drl
      if any isNothing x then fail "data junction failed"
       else return $ return dr
    DataComplementOf r -> checkDataRange r
    DataOneOf ls -> do
      x <- mapM checkLiteral ls
      if any isNothing x then fail "data one of failed" 
       else return $ return dr
    DatatypeRestriction dt fcs -> do
      x <- checkEntity dr (Entity Datatype dt)
      y <- mapM checkLiteral (map snd fcs)
      if any isNothing y || isNothing x then fail "datatype restriction failed" else return $ return dr 

checkClassExpression :: ClassExpression -> State Sign (Maybe ClassExpression)
checkClassExpression desc = case desc of
  Expression u -> case u of
        QN _ "Thing" _ _ -> return $ Just $ Expression $ QN "owl" "Thing" False ""
        QN _ "Nothing" _ _ -> return $ Just $ Expression $ QN "owl" "Nothing" False ""
        _ -> checkEntity desc (Entity Class u) 
  ObjectJunction _ ds -> do 
      x <- mapM checkClassExpression ds 
      if any isNothing x then fail "object junction failed"
       else return $ return desc
  ObjectComplementOf d -> do  
      checkClassExpression d
  ObjectOneOf is -> do 
      x <- mapM (checkEntity desc) (map (Entity NamedIndividual) is)
      if any isNothing x then fail "data one of failed"
       else return $ return desc
  ObjectValuesFrom a opExpr d -> do
      s <- get
      let iri = getObjRoleFromExpression opExpr 
      let x = Set.member iri (objectProperties s)
      let z = Set.member iri (dataProperties s)
      if x == True then do
          y <- checkClassExpression d
          if isNothing y then fail "corrected data values from failed"
            else return $ return desc
        else if z == True then do
                let Expression u = d
                return $ return (DataValuesFrom a iri [] (DataType u))  
              else fail "corrected data values from failed"
          
  ObjectHasSelf opExpr -> do
    s <- get
    if Set.member (getObjRoleFromExpression opExpr) (objectProperties s) then return (Just desc)
     else return $ fail "Failed"
  ObjectHasValue opExpr i -> do
    s <- get
    let x = Set.member (getObjRoleFromExpression opExpr) (objectProperties s) 
    y <- checkEntity desc (Entity NamedIndividual i)
    if (x == False || isNothing y ) then fail "object has value failed" 
              else return $ return desc
  ObjectCardinality (Cardinality a b opExpr md) -> do
    s <- get
    let iri = getObjRoleFromExpression opExpr 
    let x = Set.member iri (objectProperties s)
    let z = Set.member iri (dataProperties s)
    case md of 
        Nothing -> if x == False then fail "object cardinality failed with no class expression provided"
                        else return $ return desc
        Just d -> if x == True then do
                      y <- checkClassExpression d
                      if isNothing y then fail "object cardinality failed"
                        else return $ return desc
                    else do
                        let Expression u = d
                            dr = DataType u
                        chk <- checkDataRange dr 
                        if isNothing chk then fail $ "corrected data cardinality failed: " ++ showQN iri
                          else 
                            if z == False then fail $ "corrected data cardinality failed: " ++ showQN iri 
                              else return $ return $ DataCardinality (Cardinality a b iri (Just dr))
  DataValuesFrom _ dExp ds r -> do
    s <- get
    let x = Set.isSubsetOf (Set.fromList(dExp : ds)) (dataProperties s) 
    y <- checkDataRange r
    if (x == False || isNothing y ) then fail "data values from failed" 
              else return $ return desc
  DataHasValue dExp c -> do
    s <- get
    let x = Set.member dExp (dataProperties s) 
    if x == False then fail "data has value failed" 
              else return $ return desc  
  DataCardinality (Cardinality _ _ dExp mr) -> do
    s <- get
    let x = Set.member dExp (dataProperties s)
    case mr of 
        Nothing -> if x == False then fail "data cardinality failed with no class expression provided"
                             else return $ return desc
        Just d -> do
            y <- checkDataRange d
            if (x == False || isNothing y ) then fail "data cardinality failed"
                      else return $ return desc

checkBit :: FrameBit -> State Sign (Maybe FrameBit)
checkBit fb = case fb of
    AnnotationFrameBit _ -> return $ Just fb
    AnnotationBit _ anl -> do
        let apl = map snd (convertAnnList anl)
        x <- mapM (checkEntity fb) (map (Entity AnnotationProperty) apl)
        return $ if any isNothing x then Nothing 
                  else Just fb
    AnnotationDR _ _ -> return $ Just fb
    DatatypeBit _ dr -> do 
        x <- checkDataRange dr
        if isNothing x then fail "datatype bit failed" 
                  else return $ return $ fb
    ExpressionBit _ anl -> do
        x <- mapM checkClassExpression (map snd $ convertAnnList anl)
        if elem Nothing x then fail "expression bit failed"
                  else return $ return fb
    ClassDisjointUnion _ cel -> do
        x <- mapM checkClassExpression cel
        return $ if elem Nothing x then Nothing 
                  else Just fb
    ClassHasKey _ _ _ -> checkHasKey fb
    ObjectBit _ anl -> do
        let ol = map snd $ convertAnnList anl
        checkObjPropList fb ol
    ObjectDomainOrRange _ anl -> do
        let ds = map snd $ convertAnnList anl
        y <- mapM checkClassExpression ds
        return $ if any isNothing y then Nothing 
                else Just fb
    ObjectCharacteristics _ -> return $ Just fb
    ObjectSubPropertyChain _ ol -> checkObjPropList fb ol
    DataBit _ anl -> do
        let dl = map snd $ convertAnnList anl
        checkDataPropList fb dl
    DataPropDomain anl -> do
        let dr = map snd $ convertAnnList anl
        x <- mapM checkClassExpression dr
        return $ if any isNothing x then Nothing 
                  else Just fb 
    DataPropRange anl -> do
        let dr = map snd $ convertAnnList anl
        x <- mapM checkDataRange dr
        if any isNothing x then fail "data property range failed"
                  else return $ return fb  
    DataFunctional _ -> return $ Just fb
    IndividualFacts anl -> do
        let f = map snd $ convertAnnList anl
        checkFactList fb f 
    IndividualSameOrDifferent _ anl -> do
        let i = map snd $ convertAnnList anl
        y <- mapM (checkEntity fb) (map (Entity NamedIndividual) i)
        return $ if any isNothing y then Nothing 
                  else Just fb

checkFactList :: FrameBit -> [Fact] -> State Sign (Maybe FrameBit)
checkFactList fb fl = do
    x <- mapM (checkFact fb) fl
    if any isNothing x then fail "fact failed" 
              else return $ return fb   

checkFact :: FrameBit -> Fact -> State Sign (Maybe FrameBit)
checkFact fb f = do 
    s <- get
    case f of
      ObjectPropertyFact _ op i -> 
        if Set.member (getObjRoleFromExpression op) (objectProperties s) then return $ Just fb
         else fail "object property fact failed"
      DataPropertyFact _ dp x -> 
        case x of 
          Literal _ (Typed l) -> 
            if Set.member dp (dataProperties s) then return $ Just fb
             else fail "data property fact failed" 
          _ -> return $ Just fb
    
     
checkObjPropList :: FrameBit -> [ObjectPropertyExpression] -> State Sign (Maybe FrameBit)
checkObjPropList fb ol = do
        s <- get
        let x = map (\ u -> Set.member (getObjRoleFromExpression u) (objectProperties s) ) ol
        return $ if elem False x then Nothing 
                  else (Just fb)

checkDataPropList :: FrameBit -> [DataPropertyExpression] -> State Sign (Maybe FrameBit)
checkDataPropList fb dl = do
        s <- get
        let x = map (\ u -> Set.member u (dataProperties s) ) dl
        return $ if elem False x then Nothing 
                  else (Just $ fb)

checkHasKeyAll :: FrameBit -> State Sign (Maybe FrameBit)
checkHasKeyAll k = case k of
  ClassHasKey a ol dl -> do
    s <- get
    let x = map (\ u -> Set.member (getObjRoleFromExpression u) (objectProperties s) ) ol
        y = map (\ u -> Set.member u (dataProperties s) ) dl 
    if elem False (x ++ y) then fail "keys failed"
              else return $ return (ClassHasKey a ol dl)
  _ -> return $ Just k

checkHasKey :: FrameBit -> State Sign (Maybe FrameBit)
checkHasKey k = case k of 
  ClassHasKey a ol _ -> do 
    x <- sortObjDataList ol 
    let k2 = ClassHasKey a x (map getObjRoleFromExpression (ol \\ x)) 
    checkHasKeyAll k2
  _ -> return $ return k

sortObjData :: ObjectPropertyExpression -> State Sign (Maybe ObjectPropertyExpression)
sortObjData op = do
    s <- get
    let p = getObjRoleFromExpression op
    if Set.member p (objectProperties s) then return $ return op
     else return Nothing

sortObjDataList :: [ObjectPropertyExpression] -> State Sign [ObjectPropertyExpression]
sortObjDataList ls = fmap catMaybes (mapM sortObjData ls)   

checkMisc :: Misc -> State Sign (Maybe Misc)
checkMisc m = case m of
    MiscEquivOrDisjointClasses cl -> do
      x <- mapM checkClassExpression cl
      return $ if any isNothing x then Nothing else Just m
    MiscEquivOrDisjointObjProp ol -> do
      x <- sortObjDataList ol
      return $ if null x then Just $ MiscEquivOrDisjointDataProp (map getObjRoleFromExpression x) else Just m
    _ -> return $ Just m

getEntityFromFrame :: Frame -> State Sign ()
getEntityFromFrame f = case f of
    Frame e _ -> addEntity e
    _ -> return ()

createSign :: [Frame] -> State Sign ()
createSign = mapM_ getEntityFromFrame

checkFrame :: Frame -> State Sign (Maybe Frame)
checkFrame f = case f of
    Frame a fbl -> do
      x <- mapM checkBit fbl
      if any isNothing x then fail "bit failed" else return $ return $ Frame a (catMaybes x) 
    MiscFrame r al misc -> do
      x <- checkMisc misc
      case x of 
        Nothing -> return $ fail "misc failed"
        Just m -> return $ Just (MiscFrame r al m)
    MiscSameOrDifferent _ _ il -> do
      y <- mapM (checkEntity f) (map (Entity NamedIndividual) il)
      return $ if any isNothing y then fail "same or different individuals failed"
                  else Just f

correctFrames :: [Frame] -> State Sign (Maybe [Frame])
correctFrames fl = do
    createSign fl
    x <- mapM checkFrame fl
    return $ if any isNothing x then Nothing 
                  else Just (catMaybes x)

createAxioms :: [Frame] -> State Sign (Maybe [Named Axiom])
createAxioms fl = do
    x <- correctFrames fl 
    return $ if isNothing x then Nothing
              else Just $ map (makeNamed "") $ concatMap getAxioms (fromJust x)

-- | static analysis of ontology with incoming sign.
basicOWL2Analysis ::
    (OntologyDocument, Sign, GlobalAnnos) ->
        Result (OntologyDocument, ExtSign Sign Entity, [Named Axiom])

basicOWL2Analysis (odoc, inSign, _) = 
    let --ns = prefixDeclaration odoc
        syms = Set.difference (symOf accSign) $ symOf inSign
        (_, accSign) = runState
          (createSign $ ontologyFrame $ mOntology odoc)
          inSign
        (axl, _) = runState (createAxioms (ontologyFrame (mOntology odoc)))
                   accSign    
    in return $ case axl of
          Nothing -> error "could not correct axioms, bad ontolgy" --(odoc, ExtSign accSign syms, [])
          Just al -> (odoc, ExtSign accSign syms, al)

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

