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
    AnnotationProperty -> s -- ignore

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
      Datatype -> if Set.member e (datatypes s) then return $ return a else fail $ showQN e ++ " undeclared"
      Class -> if Set.member e (concepts s) then return $ return a else fail $ showQN e ++ " undeclared"
      ObjectProperty -> if Set.member e (objectProperties s) then return $ return a else fail $ showQN e ++ " undeclared"
      DataProperty -> if Set.member e (dataProperties s) then return $ return a else fail $ showQN e ++ " undeclared" 
      NamedIndividual -> if Set.member e (individuals s) then return $ return a else fail $ showQN e ++ " undeclared"
      AnnotationProperty -> if Set.member e (annotationRoles s) then return $ return a else fail $ showQN e ++ " undeclared"
    
checkDataRange :: DataRange -> State Sign (Maybe DataRange)
checkDataRange dr = do 
  s <- get  
  case dr of
    DataType u -> checkEntity dr (Entity Datatype u)
    DataJunction _ drl -> do
      x <- mapM checkDataRange drl
      if any isNothing x then return Nothing
       else return $ Just dr
    DataComplementOf r -> checkDataRange r
    DataOneOf ls -> do
      x <- mapM checkLiteral ls
      if any isNothing x then return Nothing
       else return $ Just dr
    DatatypeRestriction dt fcs -> do
      x <- checkEntity dr (Entity Datatype dt)
      y <- mapM checkLiteral (map snd fcs)
      return $ if any isNothing y || isNothing x then Nothing else Just dr 

checkClassExpression :: ClassExpression -> State Sign (Maybe ClassExpression)
checkClassExpression desc = case desc of
  Expression u -> case u of
        QN _ "Thing" _ _ -> return $ Just $ Expression $ QN "owl" "Thing" False ""
        QN _ "Nothing" _ _ -> return $ Just $ Expression $ QN "owl" "Nothing" False ""
        _ -> do 
            s <- get
            checkEntity desc (Entity Class u)
  ObjectJunction _ ds -> do 
      x <- mapM checkClassExpression ds 
      if any isNothing x then return Nothing
       else return $ Just desc
  ObjectComplementOf d -> do 
      checkClassExpression d
  ObjectOneOf is -> do 
      x <- mapM (checkEntity desc) (map (Entity NamedIndividual) is)
      if any isNothing x then return Nothing
       else return $ Just desc
  ObjectValuesFrom _ opExpr d -> do
      s <- get
      let x = Set.member (getObjRoleFromExpression opExpr) (objectProperties s)
      y <- checkClassExpression d
      return $ if (x == False || isNothing y ) then Nothing 
                else Just desc
  ObjectHasSelf opExpr -> do
    s <- get
    if Set.member (getObjRoleFromExpression opExpr) (objectProperties s) then return (Just desc)
     else return $ fail "Failed"
  ObjectHasValue opExpr i -> do
    s <- get
    let x = Set.member (getObjRoleFromExpression opExpr) (objectProperties s) 
    y <- checkEntity desc (Entity NamedIndividual i)
    return $ if (x == False || isNothing y ) then Nothing 
              else Just desc
  ObjectCardinality (Cardinality _ _ opExpr md) -> do
    s <- get
    let x = Set.member (getObjRoleFromExpression opExpr) (objectProperties s)
    case md of 
        Nothing -> return $ if x == False then Nothing 
              else Just desc
        Just d -> do
            y <- checkClassExpression d
            return $ if (x == False || isNothing y ) then Nothing 
                      else Just desc
  DataValuesFrom _ dExp ds r -> do
    s <- get
    let x = Set.isSubsetOf (Set.fromList(dExp : ds)) (dataProperties s) 
    y <- checkDataRange r
    return $ if (x == False || isNothing y ) then Nothing 
              else Just desc
  DataHasValue dExp c -> do
    s <- get
    let x = Set.member dExp (dataProperties s) 
    y <- checkLiteral c
    return $ if (x == False || isNothing y ) then Nothing 
              else Just desc  
  DataCardinality (Cardinality _ _ dExp mr) -> do
    s <- get
    let x = Set.member dExp (dataProperties s)
    case mr of 
        Nothing -> return $ if x == False then Nothing 
                             else Just desc
        Just d -> do
            y <- checkDataRange d
            return $ if (x == False || isNothing y ) then Nothing 
                      else Just desc

checkBit :: FrameBit -> State Sign (Maybe FrameBit)
checkBit fb = case fb of
    AnnotationFrameBit _ -> return $ Just fb
    AnnotationBit _ anl -> do
        let apl = map snd (convertAnnList anl)
        x <- mapM (checkEntity fb) (map (Entity AnnotationProperty) apl)
        return $ if any isNothing x then Nothing 
                  else Just fb
    DatatypeBit _ dr -> do 
        x <- checkDataRange dr
        return $ if isNothing x then Nothing 
                  else Just fb
    ExpressionBit _ anl -> do
        x <- mapM checkClassExpression (map snd $ convertAnnList anl)
        return $ if elem Nothing x then Nothing 
                  else Just fb
    ClassDisjointUnion _ cel -> do
        x <- mapM checkClassExpression cel
        return $ if elem Nothing x then Nothing 
                  else Just fb
    ClassHasKey _ _ _ -> checkHasKey fb
    ObjectBit _ anl -> do
        let ol = map snd $ convertAnnList anl
        checkObjPropList fb ol
    ObjectCharacteristics _ -> return $ Just fb
    ObjectSubPropertyChain _ ol -> checkObjPropList fb ol
    DataBit _ anl -> do
        let dl = map snd $ convertAnnList anl
        checkDataPropList fb dl
    DataPropRange anl -> do
        let dr = map snd $ convertAnnList anl
        x <- mapM checkDataRange dr
        return $ if any isNothing x then Nothing 
                  else Just fb  
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
    return $ if any isNothing x then Nothing 
              else (Just fb)   

checkFact :: FrameBit -> Fact -> State Sign (Maybe FrameBit)
checkFact fb f = do 
    s <- get
    case f of
      ObjectPropertyFact _ op i -> 
        if Set.member (getObjRoleFromExpression op) (objectProperties s) 
            && Set.member i (individuals s) then return $ Just fb
         else return Nothing
      DataPropertyFact _ dp (Literal _ (Typed l)) -> 
        if Set.member dp (dataProperties s) 
            && Set.member l (datatypes s) then return $ Just fb
         else return Nothing 
     
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
checkHasKeyAll (ClassHasKey a ol dl) = do
    s <- get
    let x = map (\ u -> Set.member (getObjRoleFromExpression u) (objectProperties s) ) ol
        y = map (\ u -> Set.member u (dataProperties s) ) dl 
    return $ if elem False (x ++ y) then Nothing
              else (Just $ ClassHasKey a ol dl)

checkHasKey :: FrameBit -> State Sign (Maybe FrameBit)
checkHasKey (ClassHasKey a ol dl) = do 
    x <- sortObjDataList ol 
    let k = ClassHasKey a x (map getObjRoleFromExpression (ol \\ x)) 
    checkHasKeyAll k

sortObjData :: ObjectPropertyExpression -> State Sign (Maybe ObjectPropertyExpression)
sortObjData op = do
    s <- get
    return $ if Set.member (getObjRoleFromExpression op) (objectProperties s) then Just op
     else Nothing

sortObjDataList :: [ObjectPropertyExpression] -> State Sign [ObjectPropertyExpression]
sortObjDataList = fmap catMaybes . mapM sortObjData   

checkMisc :: Misc -> State Sign (Maybe Misc)
checkMisc m = case m of
    MiscEquivOrDisjointClasses cl -> do
      x <- mapM checkClassExpression cl
      return $ if any isNothing x then Nothing else Just m
    MiscEquivOrDisjointObjProp ol -> do
      x <- sortObjDataList ol
      return $ if null x then Just $ MiscEquivOrDisjointDataProp (map getObjRoleFromExpression x) else Just m

getEntityFromFrame :: Frame -> State Sign ()
getEntityFromFrame f = case f of
    Frame e _ -> addEntity e
    _ -> return ()

createSign :: [Frame] -> State Sign ()
createSign = mapM_ getEntityFromFrame

checkFrame :: Frame -> State Sign (Maybe Frame)
checkFrame f = case f of
    Frame e fbl -> do
      x <- mapM checkBit fbl
      return $ if any isNothing x then Nothing else Just f 
    MiscFrame r al misc -> do
      x <- checkMisc misc
      case x of 
        Nothing -> return Nothing
        Just m -> return $ Just (MiscFrame r al m)
    MiscSameOrDifferent _ _ il -> do
      y <- mapM (checkEntity f) (map (Entity NamedIndividual) il)
      return $ if any isNothing y then Nothing 
                  else Just f

correctFrames :: [Frame] -> State Sign (Maybe [Frame])
correctFrames fl = do
    createSign fl
    x <- mapM checkFrame fl
    return $ if any isNothing x then Nothing 
                  else Just fl

createAxioms :: [Frame] -> State Sign (Maybe [Named Axiom])
createAxioms fl = do
    x <- correctFrames fl 
    return $ if isNothing x then Nothing 
              else Just $ map (makeNamed "") $ concatMap getAxioms fl

-- | static analysis of ontology with incoming sign.
basicOWL2Analysis ::
    (OntologyDocument, Sign, GlobalAnnos) ->
        Result (OntologyDocument, ExtSign Sign Entity, [Named Axiom])

basicOWL2Analysis (odoc, inSign, _) = 
    let ns = prefixDeclaration odoc
        syms = Set.difference (symOf accSign) $ symOf inSign
        (_, accSign) = runState
          (createSign $ ontologyFrame $ mOntology odoc)
          inSign
        (axl, _) = runState (createAxioms (ontologyFrame (mOntology odoc)))
                   accSign    
    in return $ case axl of
          Nothing -> (odoc, ExtSign accSign syms, []) 
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

