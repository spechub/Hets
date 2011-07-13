{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module OWL2.Rename where

import OWL2.AS
import OWL2.MS
import OWL2.Sign
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Common.AS_Annotation as Common.Annotation
import Data.List (find, nub)
import Data.Maybe
import Data.Char (isDigit)

import Common.Result

type TranslationMap = Map.Map String String

class PrefixClass a where
  mv :: TranslationMap -> a -> a

maybeRename :: (PrefixClass a) => TranslationMap -> Maybe a -> Maybe a
maybeRename tMap = fmap $ mv tMap

instance PrefixClass PrefixMap where
  mv tMap oldPs =
    foldl (\ ns (pre, ouri) ->
           Map.insert (Map.findWithDefault pre pre tMap) ouri ns)
        Map.empty $ Map.toList oldPs

instance PrefixClass QName where
  mv tMap old = let pre = namePrefix old in
      old { namePrefix = Map.findWithDefault pre pre tMap }

instance PrefixClass Sign where
   mv tMap (Sign p1 p2 p3 p4 p5 p6 p7) =
       Sign (Set.map (mv tMap) p1)
            (Set.map (mv tMap) p2)
            (Set.map (mv tMap) p3)
            (Set.map (mv tMap) p4)
            (Set.map (mv tMap) p5)
            (Set.map (mv tMap) p6)
            (mv tMap p7)

instance PrefixClass (DomainOrRangeOrFunc a) where
   mv tMap dor = case dor of
     DomainOrRange ty des -> DomainOrRange ty $ mv tMap des
     RDRange dr -> RDRange $ mv tMap dr
     _ -> dor

instance PrefixClass SignAxiom where
   mv tMap signAxiom =
       case signAxiom of
       Subconcept cId1 cId2 ->
           Subconcept (mv tMap cId1)
                   (mv tMap cId2)
       Role rdr id1 ->
           Role (mv tMap rdr) (mv tMap id1)
       Data rdr id1 ->
           Data (mv tMap rdr) (mv tMap id1)
       Conceptmembership iId des ->
           Conceptmembership (mv tMap iId)
                             (mv tMap des)

instance PrefixClass (Common.Annotation.Named Axiom) where
    mv tMap sent = sent {
        Common.Annotation.sentence = mv tMap
                                     (Common.Annotation.sentence sent) }

instance PrefixClass Entity where
  mv tMap (Entity ty euri) = Entity ty $ mv tMap euri

instance PrefixClass Literal where
  mv tMap lit = case lit of
    Literal l (Typed curi) ->
        Literal l $ Typed $ mv tMap curi
    _ -> lit

instance PrefixClass ObjectPropertyExpression where
  mv tMap opExp = case opExp of
    ObjectProp opuri -> ObjectProp (mv tMap opuri)
    ObjectInverseOf invOp -> ObjectInverseOf (mv tMap invOp)

instance PrefixClass DataRange where
  mv tMap dr =
   let rnRest (facet, value) = (facet, mv tMap value)
   in case dr of
    DataType druri restrList ->
      DataType (mv tMap druri) (map rnRest restrList)
    DataJunction ty drlist -> DataJunction ty (map (mv tMap) drlist)
    DataComplementOf dataRange -> DataComplementOf (mv tMap dataRange)
    DataOneOf constList -> DataOneOf (map (mv tMap) constList)

instance PrefixClass ClassExpression where
  mv tMap desc = case desc of
   Expression curi -> Expression (mv tMap curi)
   ObjectJunction ty descList ->
      ObjectJunction ty (map (mv tMap) descList)
   ObjectComplementOf desc' -> ObjectComplementOf (mv tMap desc')
   ObjectOneOf indsList -> ObjectOneOf (map (mv tMap) indsList)
   ObjectValuesFrom ty opExp desc' -> ObjectValuesFrom ty
        (mv tMap opExp) (mv tMap desc')
   ObjectHasSelf opExp -> ObjectHasSelf (mv tMap opExp)
   ObjectHasValue opExp indUri -> ObjectHasValue
        (mv tMap opExp) (mv tMap indUri)
   ObjectCardinality (Cardinality ty card opExp maybeDesc) ->
      ObjectCardinality $ Cardinality ty card
        (mv tMap opExp) (maybeRename tMap maybeDesc)
   DataValuesFrom ty dpExp dpExpList dataRange ->
      DataValuesFrom ty (mv tMap dpExp) (map (mv tMap) dpExpList)
        (mv tMap dataRange)
   DataHasValue dpExp const' -> DataHasValue
        (mv tMap dpExp) (mv tMap const')
   DataCardinality (Cardinality ty card dpExp maybeRange) ->
      DataCardinality $ Cardinality ty card
        (mv tMap dpExp) (maybeRename tMap maybeRange)

instance PrefixClass Annotation where
  mv tMap anno = case anno of
   Annotation annos ap av -> Annotation (map (mv tMap) annos)
        (mv tMap ap) (mv tMap av)

instance PrefixClass AnnotationValue where
  mv ns av = case av of
   AnnValue iri -> AnnValue (mv ns iri)
   AnnValLit l -> AnnValLit (mv ns l)

instance PrefixClass Annotations where
  mv tMap = map (mv tMap)

instance PrefixClass a => PrefixClass (AnnotatedList a) where
  mv tMap = map (\ (ans, b) -> (mv tMap ans, mv tMap b))

instance PrefixClass ListFrameBit where
  mv tMap lfb = case lfb of
   AnnotationBit anl -> AnnotationBit (mv tMap anl)
   ExpressionBit anl -> ExpressionBit (mv tMap anl)
   ObjectBit anl -> ObjectBit (mv tMap anl)
   DataBit anl -> DataBit (mv tMap anl)
   IndividualSameOrDifferent anl ->
              IndividualSameOrDifferent (mv tMap anl)
   DataPropRange anl -> DataPropRange (mv tMap anl)
   IndividualFacts ans -> IndividualFacts (mv tMap ans)
   _ -> lfb

instance PrefixClass AnnFrameBit where
  mv tMap afb = case afb of
   DatatypeBit dr -> DatatypeBit (mv tMap dr)
   ClassDisjointUnion cel -> ClassDisjointUnion (map (mv tMap) cel)
   ClassHasKey ol dl -> ClassHasKey (map (mv tMap) ol) (map (mv tMap) dl)
   ObjectSubPropertyChain ol -> ObjectSubPropertyChain (map (mv tMap) ol)
   _ -> afb

instance PrefixClass FrameBit where
 mv tMap fb = case fb of
   ListFrameBit mr lfb -> ListFrameBit mr (mv tMap lfb)
   AnnFrameBit ans afb -> AnnFrameBit (mv tMap ans) (mv tMap afb)

instance PrefixClass Extended where
  mv tMap ex = case ex of
   Misc ans -> Misc $ mv tMap ans
   SimpleEntity e -> SimpleEntity $ mv tMap e
   ClassEntity ce -> ClassEntity $ mv tMap ce
   ObjectEntity op -> ObjectEntity $ mv tMap op

instance PrefixClass Frame where
  mv tMap (Frame ex fbl) = Frame (mv tMap ex) (map (mv tMap) fbl)

instance PrefixClass Axiom where
  mv tMap (PlainAxiom ex fbl) = PlainAxiom (mv tMap ex) (mv tMap fbl)

instance PrefixClass Fact where
  mv tMap f = case f of
    ObjectPropertyFact pn op i -> ObjectPropertyFact pn (mv tMap op) (mv tMap i)
    DataPropertyFact pn dp l -> DataPropertyFact pn (mv tMap dp) (mv tMap l)

instance PrefixClass OntologyDocument where
  mv tMap ( OntologyDocument pm onto) =
      OntologyDocument (mv tMap pm) (mv tMap onto)

instance PrefixClass MOntology where
  mv tMap ( MOntology ouri impList anList f) =
      MOntology (mv tMap ouri) (map (mv tMap) impList)
         (map (mv tMap) anList) (map (mv tMap) f)

testAndInteg :: (String, String)
     -> (PrefixMap, TranslationMap) -> (PrefixMap, TranslationMap)
testAndInteg (pre, oiri) (old, tm) = case Map.lookup pre old of
  Just iri ->
   if oiri == iri then (old, tm)
    else let pre' = disambiguateName pre old
         in (Map.insert pre' oiri old, Map.insert pre pre' tm)
  Nothing -> (Map.insert pre oiri old, tm)

disambiguateName :: String -> PrefixMap -> String
disambiguateName name nameMap =
  let newname = reverse . dropWhile isDigit $ reverse name
  in fromJust $ find (not . flip Map.member nameMap)
      [newname ++ show (i :: Int) | i <- [1 ..]]

uniteSign :: Sign -> Sign -> Result Sign
uniteSign s1 s2 = do
    let (pm, tm) = integPref (prefixMap s1) (prefixMap s2)
    if Map.null tm then return (addSign s1 s2) {prefixMap = pm}
      else fail "Static analysis could not unite signatures"

integPref :: PrefixMap -> PrefixMap
                    -> (PrefixMap, TranslationMap)
integPref oldNsMap testNsMap =
   foldr testAndInteg (oldNsMap, Map.empty) (Map.toList testNsMap)

integrateOntologyDoc :: OntologyDocument -> OntologyDocument
                      -> OntologyDocument
integrateOntologyDoc of1@( OntologyDocument ns1
                           ( MOntology oid1 imp1 anno1 frames1))
                      of2@( OntologyDocument ns2
                           ( MOntology oid2 imp2 anno2 frames2)) =
  if of1 == of2 then of1
   else
    let (newPref, tm) = integPref ns1 ns2
        newOid :: OntologyIRI -> OntologyIRI -> OntologyIRI
        newOid id1 id2 = let
              lid1 = localPart id1
              lid2 = localPart id2
            in if null lid1 then id2 else
               if null lid2 || id1 == id2 then id1 else id1
                  { localPart = uriToName lid1 ++ "_" ++ uriToName lid2 }
    in OntologyDocument newPref
            ( MOntology (newOid oid1 oid2)
                 (nub $ imp1 ++ map (mv tm) imp2)
                 (nub $ anno1 ++ map (mv tm) anno2)
                 (nub $ frames1 ++ map (mv tm) (frames2)))

uriToName :: String -> String
uriToName str = let
  str' = case str of
           '"' : _ -> read str
           _ -> str
  in takeWhile (/= '.') $ reverse $ case takeWhile (/= '/') $ reverse str' of
         '#' : r -> r
         r -> r
