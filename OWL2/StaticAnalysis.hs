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
anaObjPropExpr :: ObjectPropertyExpression -> State Sign ()
anaObjPropExpr = addEntity . Entity ObjectProperty . getObjRoleFromExpression

anaDataPropExpr :: DataPropertyExpression -> State Sign ()
anaDataPropExpr = addEntity . Entity DataProperty

anaIndividual :: Individual -> State Sign ()
anaIndividual = addEntity . Entity NamedIndividual

anaLiteral :: Literal -> State Sign ()
anaLiteral (Literal _ ty) = case ty of
  Typed u -> addEntity $ Entity Datatype u
  _ -> return ()

anaDataRange :: DataRange -> State Sign ()
anaDataRange dr = case dr of
  DataType u -> addEntity $ Entity Datatype u
  DataJunction jt drl -> mapM_ anaDataRange drl
  DataComplementOf r -> anaDataRange r
  DataOneOf cs -> mapM_ anaLiteral cs
  DatatypeRestriction dt fcs -> do
    addEntity $ Entity Datatype dt
    mapM_ (anaLiteral . snd) fcs

anaDescription :: ClassExpression -> State Sign (Maybe ClassExpression)
anaDescription desc = case desc of
  Expression u -> case u of
        QN _ "Thing" _ _ -> return $ Just $ Expression $ QN "owl" "Thing" False ""
        QN _ "Nothing" _ _ -> return $ Just $ Expression $ QN "owl" "Nothing" False ""
        _ -> do 
            s <- get
            if Set.member u (concepts s) then return $ return desc
            else return $ fail "Class not found"
  ObjectJunction _ ds -> do 
      mapM_ anaDescription ds 
      return (Just desc)
  ObjectComplementOf d -> do 
      anaDescription d
      return (Just desc)
  ObjectOneOf is -> do 
      mapM_ anaIndividual is
      return (Just desc)
  ObjectValuesFrom _ opExpr d -> do
    s <- get
    if Set.member (getObjRoleFromExpression opExpr) (objectProperties s) then do
        anaDescription d
        return (Just desc)
    else return $ fail "Failed"
  ObjectHasSelf opExpr -> do
    s <- get
    if Set.member (getObjRoleFromExpression opExpr) (objectProperties s) then return (Just desc)
    else return $ fail "Failed"
  ObjectHasValue opExpr i -> do
    s <- get
    if Set.member (getObjRoleFromExpression opExpr) (objectProperties s) then do
        anaIndividual i
        return (Just desc)
    else return $ fail "Failed"
  ObjectCardinality (Cardinality _ _ opExpr md) -> do
    s <- get
    if Set.member (getObjRoleFromExpression opExpr) (objectProperties s) then do
        maybe (return (Just desc)) anaDescription md
    else return $ fail "Failed"
  DataValuesFrom _ dExp ds r -> do
    s <- get
    if Set.isSubsetOf (Set.fromList(dExp : ds)) (dataProperties s) then do
        anaDataPropExpr dExp
        mapM_ anaDataPropExpr ds
        anaDataRange r
        return (Just desc)
    else return $ fail "Failed"
  DataHasValue dExp c -> do
    s <- get
    if Set.member dExp (dataProperties s) then do
        anaDataPropExpr dExp
        anaLiteral c
        return (Just desc)
    else return $ fail "Failed"
  DataCardinality (Cardinality _ _ dExp mr) -> do
    s <- get
    if Set.member dExp (dataProperties s) then do
        anaDataPropExpr dExp
        maybe (return ()) anaDataRange mr
        return (Just desc)
    else return $ fail "Failed"

anaFrame :: Frame -> State Sign (Frame)
anaFrame f = case f of
    Frame e fbl -> do
      addEntity e
      let ckfbl = fbl in
        return $ Frame e ckfbl

checkBit :: FrameBit -> State Sign (Maybe FrameBit)
checkBit fb = case fb of
    AnnotationFrameBit _ -> return $ Just fb
    AnnotationBit _ _ -> return $ Just fb
    DatatypeBit _ dr -> do 
        anaDataRange dr
        return $ Just fb
    ExpressionBit _ anl -> do
        x <- mapM anaDescription (map snd $ convertAnnList anl)
        return $ if elem Nothing x then Nothing else Just fb
    ClassDisjointUnion _ cel -> do
        x <- mapM anaDescription cel
        return $ if elem Nothing x then Nothing else Just fb
    ClassHasKey _ _ _ -> checkHasKeyAll fb
    ObjectBit _ anl -> do
        s <- get
        let ol = map snd $ convertAnnList anl
            y = map (\ u -> Set.member (getObjRoleFromExpression u) (objectProperties s) ) ol
        return $ if elem False y then Nothing 
                 else (Just $ fb)
    ObjectCharacteristics _ -> return $ Just fb

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
    return $ if null x then Nothing
             else Just $ ClassHasKey a x (map getObjRoleFromExpression (ol \\ x)) 

sortObjData :: ObjectPropertyExpression -> State Sign (Maybe ObjectPropertyExpression)
sortObjData op = do
    s <- get
    return $ if Set.member (getObjRoleFromExpression op) (objectProperties s) then Just op
    else Nothing

sortObjDataList :: [ObjectPropertyExpression] -> State Sign [ObjectPropertyExpression]
sortObjDataList = fmap catMaybes . mapM sortObjData   

{-
anaPlainAxiom :: PlainAxiom -> State Sign ()
anaPlainAxiom pa = case pa of
  SubClassOf s1 s2 -> do
    anaDescription s1
    anaDescription s2
  EquivOrDisjointClasses _ ds ->
    mapM_ anaDescription ds
  DisjointUnion u ds -> do
    addEntity $ Entity Class u
    mapM_ anaDescription ds
  SubObjectPropertyOf sop op -> do
    mapM_ (addEntity . Entity ObjectProperty)
      $ getObjRoleFromSubExpression sop
    anaObjPropExpr op
  EquivOrDisjointObjectProperties _ os ->
    mapM_ anaObjPropExpr os
  ObjectPropertyDomainOrRange _ op d -> do
    anaObjPropExpr op
    anaDescription d
  InverseObjectProperties o1 o2 -> do
    anaObjPropExpr o1
    anaObjPropExpr o2
  ObjectPropertyCharacter _ op -> anaObjPropExpr op
  SubDataPropertyOf d1 d2 -> do
    anaDataPropExpr d1
    anaDataPropExpr d2
  EquivOrDisjointDataProperties _ ds ->
    mapM_ anaDataPropExpr ds
  DataPropertyDomainOrRange ddr dp -> do
    case ddr of
      DataDomain d -> anaDescription d
      DataRange r -> anaDataRange r
    anaDataPropExpr dp
  FunctionalDataProperty dp -> anaDataPropExpr dp
  SameOrDifferentIndividual _ is ->
    mapM_ anaIndividual is
  ClassAssertion d i -> do
    anaIndividual i
    anaDescription d
  ObjectPropertyAssertion (Assertion op _ s t) -> do
    anaObjPropExpr op
    anaIndividual s
    anaIndividual t
  DataPropertyAssertion (Assertion dp _ s c) -> do
    anaDataPropExpr dp
    anaIndividual s
    anaLiteral c
  Declaration e -> addEntity e
  DatatypeDefinition dt dr -> do
    addEntity $ Entity Datatype dt
    anaDataRange dr
  HasKey ce opl dpl -> do
    anaDescription ce
    s <- get
    mapM_ anaObjPropExpr opl
    mapM_ anaDataPropExpr dpl
-}

    

-- | static analysis of ontology with incoming sign.
basicOWLAnalysisMS ::
    (OntologyDocument, Sign, GlobalAnnos) ->
        Result (OntologyDocument, ExtSign Sign Entity, [Named Axiom])
basicOWLAnalysisMS = error "not implemented"

{-
basicOWLAnalysis ::
    (OntologyFile, Sign, GlobalAnnos) ->
        Result (OntologyFile, ExtSign Sign Entity, [Named Axiom])
basicOWLAnalysis (ofile, inSign, _) =
    let ns = prefixName ofile
        syms = Set.difference (symOf accSign) $ symOf inSign
        (sens, accSign) = runState
          (mapM anaAxiom $ axiomsList $ ontology ofile)
          inSign
        noDecl s = case sentence s of
                     PlainAxiom _ (Declaration _) -> False
                     _ -> True
    in return (ofile, ExtSign accSign syms
                  , filter noDecl $ concat sens)
    where
        oName = uri $ ontology ofile
-}

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

