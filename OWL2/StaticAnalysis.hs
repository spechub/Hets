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
import OWL.Namespace

import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.List

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

anaAxiom :: Axiom -> State Sign [Named Axiom]
anaAxiom (PlainAxiom as p) = let x = PlainAxiom as p in do
    anaPlainAxiom p
    return [findImplied as $ makeNamed "" $ x]

anaObjPropExpr :: ObjectPropertyExpression -> State Sign ()
anaObjPropExpr = addEntity . Entity ObjectProperty . getObjRoleFromExpression

anaDataPropExpr :: DataPropertyExpression -> State Sign ()
anaDataPropExpr = addEntity . Entity DataProperty

anaIndividual :: Individual -> State Sign ()
anaIndividual = addEntity . Entity NamedIndividual

anaConstant :: Literal -> State Sign ()
anaConstant (Literal _ ty) = case ty of
  Typed u -> addEntity $ Entity Datatype u
  _ -> return ()

anaDataRange :: DataRange -> State Sign ()
anaDataRange dr = case dr of
  DataType u -> addEntity $ Entity Datatype u
  DataComplementOf r -> anaDataRange r
  DataOneOf cs -> mapM_ anaConstant cs
  DatatypeRestriction dt fcs -> do
    addEntity $ Entity Datatype dt
    mapM_ (anaConstant . snd) fcs

anaDescription :: ClassExpression -> State Sign ()
anaDescription desc = case desc of
  Expression u ->
      case u of
        QN _ "Thing" _ _ -> addEntity $ Entity Class $
                          QN "owl" "Thing" False ""
        QN _ "Nothing" _ _ -> addEntity $ Entity Class $
                          QN "owl" "Nothing" False ""
        v -> addEntity $ Entity Class v
  ObjectJunction _ ds -> mapM_ anaDescription ds
  ObjectComplementOf d -> anaDescription d
  ObjectOneOf is -> mapM_ anaIndividual is
  ObjectValuesFrom _ opExpr d -> do
    anaObjPropExpr opExpr
    anaDescription d
  ObjectHasSelf opExpr -> anaObjPropExpr opExpr
  ObjectHasValue opExpr i -> do
    anaObjPropExpr opExpr
    anaIndividual i
  ObjectCardinality (Cardinality _ _ opExpr md) -> do
    anaObjPropExpr opExpr
    maybe (return ()) anaDescription md
  DataValuesFrom _ dExp ds r -> do
    anaDataPropExpr dExp
    mapM_ anaDataPropExpr ds
    anaDataRange r
  DataHasValue dExp c -> do
    anaDataPropExpr dExp
    anaConstant c
  DataCardinality (Cardinality _ _ dExp mr) -> do
    anaDataPropExpr dExp
    maybe (return ()) anaDataRange mr

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
    anaConstant c
  Declaration e -> addEntity e
  DatatypeDefinition dt dr -> do
    addEntity $ Entity Datatype dt
    anaDataRange dr
  HasKey ce opl dpl -> do
    anaDescription ce
    mapM_ anaObjPropExpr opl
    mapM_ anaDataPropExpr dpl

-- | static analysis of ontology with incoming sign.
basicOWLAnalysisMS ::
    (OntologyDocument, Sign, GlobalAnnos) ->
        Result (OntologyDocument, ExtSign Sign Entity, [Named Axiom])
basicOWLAnalysisMS = error "not implemented"


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

