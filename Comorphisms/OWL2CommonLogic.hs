{- |
Module      :  $Header$
Description :  Comorphism from OWL 1.1 to Common Logic
Copyright   :  (c) Uni Bremen DFKI 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt

Maintainer  :  mata@informatik.uni-bremen.de
Stability   :  experimental
Portability :  non-portable (via Logic.Logic)

a not yet implemented comorphism
-}

module Comorphisms.OWL2CommonLogic (OWL2CommonLogic(..)) where

import Logic.Logic as Logic
import Logic.Comorphism
import qualified Common.AS_Annotation as CommonAnno
import Common.Result
import Common.Id
import Control.Monad
import Data.Char
import qualified Data.Set as Set
import qualified Data.Map as Map

-- OWL = domain
import OWL.Logic_OWL
import OWL.AS
import OWL.Sublogic
import OWL.Morphism
import qualified OWL.Sign as OS
-- CommonLogic = codomain
import CommonLogic.Logic_CommonLogic
import CommonLogic.AS_CommonLogic
import CommonLogic.Sign
import CommonLogic.Symbol
--import CommonLogic.Morphism

import Common.ProofTree

data OWL2CommonLogic = OWL2CommonLogic deriving Show

instance Language OWL2CommonLogic

instance Comorphism
    OWL2CommonLogic        -- comorphism
    OWL             -- lid domain
    OWLSub          -- sublogics domain
    OntologyFile    -- Basic spec domain
    Axiom           -- sentence domain
    SymbItems       -- symbol items domain
    SymbMapItems    -- symbol map items domain
    OS.Sign         -- signature domain
    OWLMorphism     -- morphism domain
    Entity          -- symbol domain
    RawSymb         -- rawsymbol domain
    ProofTree       -- proof tree codomain
    CommonLogic            -- lid codomain
    ()--CommonLogic_Sublogics  -- sublogics codomain
    BASIC_SPEC   -- Basic spec codomain
    SENTENCE     -- sentence codomain
    NAME      -- symbol items codomain
    ()--SYMB_MAP_ITEMS  -- symbol map items codomain
    Sign        -- signature codomain
    Morphism         -- morphism codomain
    Symbol          -- symbol codomain
    Symbol       -- rawsymbol codomain
    ()       -- proof tree domain
    where
      sourceLogic OWL2CommonLogic    = OWL
      sourceSublogic OWL2CommonLogic = sl_top
      targetLogic OWL2CommonLogic    = CommonLogic
      mapSublogic OWL2CommonLogic _  = Just $ ()
      map_theory OWL2CommonLogic     = mapTheory
      --map_morphism OWL2CommonLogic   = mapMorphism
      isInclusionComorphism OWL2CommonLogic = True
      has_model_expansion OWL2CommonLogic = True

{-- | Mapping of OWL morphisms to CommonLogic morphisms
mapMorphism :: OWLMorphism -> Result CommonLogicMor
mapMorphism oMor =
  do
    cdm <- mapSign $ osource oMor
    ccd <- mapSign $ otarget oMor
    let emap = mmaps oMor
        preds = Map.foldWithKey (\ (Entity ty u1) u2 -> let
              i1 = uriToTok u1
              i2 = uriToTok u2
              in case ty of
                OWLClass -> Map.insert (i1, conceptPred) i2
                ObjectProperty -> Map.insert (i1, objectPropPred) i2
                DataProperty -> Map.insert (i1, dataPropPred) i2
                _ -> id) Map.empty emap
        ops = Map.foldWithKey (\ (Entity ty u1) u2 -> case ty of
                Individual ->
                    Map.insert (uriToTok u1, indiConst) (uriToId u2, Total)
                _ -> id) Map.empty emap
      return (embedMorphism () cdm ccd)
                 { op_map = ops
                 , pred_map = preds }
-}--TODO
-- | OWL topsort Thing
thing :: NAME --Id
thing = mkSimpleId "Thing" --stringToId "Thing"

noThing :: NAME
noThing = mkSimpleId "Nothing" --stringToId "Nothing"

-- | OWL bottom
mkThingTerm :: Id -> TERM
mkThingTerm (Id tokList _ _) =
  case tokList of
         [x] -> Name_term x
         (x:xs) -> Funct_term (Name_term x) (Term_seq (mkTokTermList xs) nullRange) nullRange
         _ -> Name_term noThing
         
mkTokTermList :: [Token] -> [TERM]
mkTokTermList toks =
  case toks of
       [x] -> [Name_term x]
       (x:xs) -> ((Name_term x):(mkTokTermList xs))

-- | OWL Data topSort DATA
dataS :: NAME
dataS = mkSimpleId $ drop 3 $ show OWLDATA

data VarOrIndi = OVar Int | OIndi URI

{-predefSorts :: Set.Set SORT
predefSorts = Set.singleton thing
-}
hetsPrefix :: String
hetsPrefix = ""
{-
conceptPred :: PredType
conceptPred = PredType [thing]

objectPropPred :: PredType
objectPropPred = PredType [thing, thing]

dataPropPred :: PredType
dataPropPred = PredType [thing, dataS]

indiConst :: OpType
indiConst = OpType Total [] thing
-}
mapSign :: OS.Sign                 -- ^ OWL signature
        -> Result Sign         -- ^ CommonLogic signature
mapSign sig = error "nyi"{-
  let conc = Set.union (OS.concepts sig) (OS.primaryConcepts sig)
      cvrt = map uriToTok . Set.toList
      tMp k = Map.fromList . map (\ u -> (u, Set.singleton k))
      cPreds = thing : noThing : cvrt conc
      oPreds = cvrt $ OS.indValuedRoles sig
      dPreds = cvrt $ OS.dataValuedRoles sig
      aPreds = Map.unions
        [ tMp conceptPred cPreds
        , tMp objectPropPred oPreds
        , tMp dataPropPred dPreds ]
  in return (emptySign ())
        { sortSet = predefSorts
        , predMap = aPreds
        , opMap = tMp indiConst . cvrt $ OS.inividuals sig
        }
-}--TODO

predefinedSentences :: [CommonAnno.Named SENTENCE]
predefinedSentences =
  [
    (
     CommonAnno.makeNamed "nothing in Nothing" $
     Quant_sent 
     (
      Universal
      [Name (mkNName 1)]
      ( Bool_sent (
       Negation
       (
        Atom_sent
        (
         Atom
         (
          Name_term noThing
         )
         (
          Term_seq [ Name_term (mkNName 1) ] nullRange
         )
        ) nullRange
       )
      ) nullRange))
      nullRange
    )
    ,
    (
     CommonAnno.makeNamed "thing in Thing" $
     Quant_sent 
     (
      Universal
      [Name (mkNName 1)]
      (
       Atom_sent
       (
        Atom
        (
         Name_term thing
        )
        (
         Term_seq [ Name_term (mkNName 1) ] nullRange
        )
       ) nullRange
      )
     )
      nullRange
    )
  ]

mapTheory :: (OS.Sign, [CommonAnno.Named Axiom])
             -> Result (Sign, [CommonAnno.Named SENTENCE])
mapTheory (owlSig, owlSens) =
  do
    cSig <- mapSign owlSig
    (cSensI, nSig) <- foldM (\ (x,y) z ->
              do
                (sen, sig) <- mapSentence y z
                return (sen:x, unite sig y)
                ) ([], cSig) owlSens
    let cSens = concatMap (\ x ->
            case x of 
                Nothing -> []
                Just a -> [a]
         ) cSensI
    return (nSig, predefinedSentences ++ cSens)

-- | mapping of OWL to CommonLogic_DL formulae
mapSentence :: Sign                    -- ^ CommonLogic Signature
  -> CommonAnno.Named Axiom                                  -- ^ OWL Sentence
  -> Result (Maybe (CommonAnno.Named SENTENCE), Sign) -- ^ CommonLogic SENTENCE
mapSentence cSig inSen = do
            (outAx, outSig) <- mapAxiom cSig $ CommonAnno.sentence inSen
            return (fmap (flip CommonAnno.mapNamed inSen . const) outAx, outSig)

-- | Mapping of Axioms
mapAxiom :: Sign                             -- ^ CommonLogic Signature
         -> Axiom                                -- ^ OWL Axiom
         -> Result (Maybe SENTENCE, Sign) -- ^ CommonLogic Formula
mapAxiom cSig ax =
    let
        a = 1
        b = 2
        c = 3
    in
      case ax of
        PlainAxiom _ pAx ->
            case pAx of
              SubClassOf sub super ->
                  do
                    domT <- mapDescription cSig sub   a
                    codT <- mapDescription cSig super a
                    return (Just $ Quant_sent (Universal
                               [Name (mkNName a)]
                               (Bool_sent (Implication
                                domT
                                codT)
                                nullRange)) nullRange, cSig)
              EquivOrDisjointClasses eD dS ->
                  do
                    decrsS <- mapDescriptionListP cSig a $ comPairs dS dS
                    let decrsP =
                            case eD of
                              Equivalent -> 
                                  map (\(x,y) -> Bool_sent (Biconditional x y) nullRange)
                                      decrsS
                              Disjoint   ->
                                  map (\(x,y) -> Bool_sent (Negation
                                       (Bool_sent (Conjunction [x,y]) nullRange)) nullRange)
                                       decrsS
                    return (Just $ Quant_sent (Universal
                              [Name (mkNName a)]
                               (
                                Bool_sent (Conjunction decrsP) nullRange
                               )) nullRange, cSig)
              DisjointUnion cls sD ->
                  do
                    decrs  <- mapDescriptionList cSig a sD
                    decrsS <- mapDescriptionListP cSig a $ comPairs sD sD
                    let decrsP = map (\ (x, y) -> Bool_sent (Conjunction [x,y]) nullRange)
                                 decrsS
                    mcls <- mapClassURI cSig cls (mkNName a)
                    return (Just $ Quant_sent (Universal
                              [Name (mkNName a)]
                               (
                                Bool_sent (Biconditional
                                  mcls                 -- The class
                                (                      -- The rest
                                  Bool_sent (Conjunction
                                  [
                                   (Bool_sent (Disjunction decrs) nullRange)
                                  ,(Bool_sent (Negation
                                     (
                                      Bool_sent (Conjunction decrsP) nullRange
                                     )
                                    ) nullRange)
                                  ]) nullRange
                                )
                               ) nullRange
                               )
                               ) nullRange, cSig)
              SubObjectPropertyOf ch op ->
                  do
                    os <- mapSubObjProp cSig ch op c
                    return (Just os, cSig)
              EquivOrDisjointObjectProperties disOrEq oExLst ->
                  do
                    pairs <- mapComObjectPropsList cSig oExLst a b
                    return (Just $ Quant_sent (Universal
                              [ Name (mkNName a)
                              , Name (mkNName b)]
                               (
                                Bool_sent (Conjunction
                                (
                                 case disOrEq of
                                   Equivalent ->
                                       map (\(x,y) ->
                                                Bool_sent (Biconditional x y) nullRange) pairs
                                   Disjoint   ->
                                       map (\(x,y) ->
                                                (Bool_sent (Negation
                                                 (Bool_sent (Conjunction [x,y]) nullRange)) nullRange
                                                )
                                           ) pairs
                                )
                               ) nullRange ))
                               nullRange, cSig)
              ObjectPropertyDomainOrRange domOrRn objP descr ->
                        do
                          tobjP <- mapObjProp cSig objP a b
                          tdsc  <- mapDescription cSig descr $
                                   case domOrRn of
                                     ObjDomain -> a
                                     ObjRange  -> b
                          let vars = case domOrRn of
                                       ObjDomain -> (mkNName a, mkNName b)
                                       ObjRange  -> (mkNName b, mkNName a)
                          return (Just $ Quant_sent (Universal
                                     [Name (fst vars)]
                                     (
                                      Quant_sent (Existential
                                         [Name (snd vars)]
                                         (
                                          Bool_sent (Implication
                                           tobjP
                                           tdsc
                                         ) nullRange))
                                      nullRange
                                     ))
                                     nullRange, cSig)
              InverseObjectProperties o1 o2 ->
                  do
                    so1 <- mapObjProp cSig o1 a b
                    so2 <- mapObjProp cSig o2 b a
                    return (Just $ Quant_sent (Universal
                             [Name (mkNName a)
                             ,Name (mkNName b)]
                             (
                             Bool_sent (
                              Biconditional
                              so1
                              so2
                             ) nullRange ))
                             nullRange, cSig)
              ObjectPropertyCharacter cha o ->
                  case cha of
                    Functional ->
                        do
                          so1 <- mapObjProp cSig o a b
                          so2 <- mapObjProp cSig o a c
                          return (Just $ Quant_sent (Universal
                                     [Name (mkNName a)
                                     ,Name (mkNName b)
                                     ,Name (mkNName c)
                                     ]
                                     (
                                      Bool_sent (Implication
                                      (
                                       Bool_sent (Conjunction [so1, so2]) nullRange
                                      )
                                      (
                                      Atom_sent 
                                        (
                                         Equation
                                          (
                                            Name_term (mkNName b)
                                          )
                                          (
                                            Name_term (mkNName c)
                                          )
                                        )
                                        nullRange
                                      )
                                     ) nullRange))
                                     nullRange, cSig)
                    InverseFunctional ->
                        do
                          so1 <- mapObjProp cSig o a c
                          so2 <- mapObjProp cSig o b c
                          return (Just $ Quant_sent (Universal
                                     [Name (mkNName a)
                                     ,Name (mkNName b)
                                     ,Name (mkNName c)
                                     ]
                                     (
                                      Bool_sent (Implication
                                      (
                                       Bool_sent (Conjunction [so1, so2]) nullRange
                                      )
                                      (
                                       Atom_sent 
                                       (
                                        Equation
                                        (
                                          Name_term (mkNName a)
                                        )
                                        (
                                          Name_term (mkNName b)
                                        )
                                       )
                                       nullRange
                                      )
                                     ) nullRange ))
                                     nullRange, cSig)
                    Reflexive  ->
                        do
                          so <- mapObjProp cSig o a a
                          return (Just $ Quant_sent (Universal
                                   [Name (mkNName a)]
                                    so)
                                    nullRange, cSig)
                    Irreflexive ->
                        do
                          so <- mapObjProp cSig o a a
                          return
                                 (Just $ Quant_sent (Universal
                                   [Name (mkNName a)]
                                   (Bool_sent (Negation so) nullRange))
                                   nullRange, cSig)
                    Symmetric ->
                        do
                          so1 <- mapObjProp cSig o a b
                          so2 <- mapObjProp cSig o b a
                          return
                           (Just $ Quant_sent (Universal
                               [Name (mkNName a)
                               ,Name (mkNName b)]
                               (
                                Bool_sent (Implication
                                so1
                                so2
                               ) nullRange))
                               nullRange, cSig)
                    Asymmetric ->
                        do
                          so1 <- mapObjProp cSig o a b
                          so2 <- mapObjProp cSig o b a
                          return
                           (Just $ Quant_sent (Universal
                               [Name (mkNName a)
                               ,Name (mkNName b)]
                               (
                                Bool_sent (Implication
                                so1
                                (Bool_sent (Negation so2) nullRange)
                               ) nullRange))
                               nullRange, cSig)
                    Antisymmetric ->
                        do
                          so1 <- mapObjProp cSig o a b
                          so2 <- mapObjProp cSig o b a
                          return
                           (Just $ Quant_sent (Universal
                               [Name (mkNName a)
                               ,Name (mkNName b)]
                               (
                                Bool_sent (Implication
                                 (Bool_sent (Conjunction [so1, so2]) nullRange)
                                 (
                                  Atom_sent 
                                  (
                                    Equation
                                    (
                                      Name_term (mkNName a)
                                    )
                                    (
                                      Name_term (mkNName b)
                                    )
                                  )
                                  nullRange
                                 )
                               ) nullRange))
                               nullRange, cSig)
                    Transitive ->
                        do
                          so1 <- mapObjProp cSig o a b
                          so2 <- mapObjProp cSig o b c
                          so3 <- mapObjProp cSig o a c
                          return
                           (Just $ Quant_sent (Universal
                               [Name (mkNName a)
                               ,Name (mkNName b)
                               ,Name (mkNName c)]
                               (
                                Bool_sent (Implication
                                (
                                 Bool_sent (Conjunction [so1, so2]) nullRange
                                )
                                 so3
                               ) nullRange))
                               nullRange, cSig)
              SubDataPropertyOf dP1 dP2 ->
                  do
                    l <- mapDataProp cSig dP1 a b
                    r <- mapDataProp cSig dP2  a b
                    return (Just $ Quant_sent (Universal
                               [ Name (mkNName a)
                               , Name (mkNName b)]
                               (
                                Bool_sent (Implication
                                l
                                r) nullRange)
                               )
                               nullRange, cSig)
              EquivOrDisjointDataProperties disOrEq dlst ->
                  do
                    pairs <- mapComDataPropsList cSig dlst a b
                    return (Just $ Quant_sent (Universal
                              [ Name (mkNName a)
                              , Name (mkNName b)]
                               (
                                Bool_sent (Conjunction
                                (
                                 case disOrEq of
                                   Equivalent ->
                                       map (\(x,y) ->
                                                Bool_sent (Biconditional x y) nullRange) pairs
                                   Disjoint   ->
                                       map (\(x,y) ->
                                                (Bool_sent (Negation
                                                 (Bool_sent (Conjunction [x,y]) nullRange)
                                                ) nullRange )
                                           ) pairs
                                )) nullRange
                               ))
                               nullRange, cSig)
              DataPropertyDomainOrRange domRn dpex ->
                        do
                          oEx <- mapDataProp cSig dpex a b
                          case domRn of
                            DataDomain mdom ->
                                do
                                  odes <- mapDescription cSig mdom a
                                  let vars = (mkNName a, mkNName b)
                                  return (Just $ Quant_sent (Universal
                                         [Name (fst vars)]
                                         (Quant_sent (Existential
                                         [Name (snd vars)]
                                         (Bool_sent (Implication oEx odes) nullRange))
                                         nullRange)) nullRange, cSig)
                            DataRange  rn  ->
                                do
                                  odes <- mapDataRange cSig rn b
                                  let vars = (mkNName a, mkNName b)
                                  return (Just $ Quant_sent (Universal
                                         [Name (fst vars)]
                                         (Quant_sent (Existential
                                         [Name (snd vars)]
                                         (Bool_sent (Implication oEx odes) nullRange))
                                         nullRange)) nullRange, cSig)
              FunctionalDataProperty o ->
                        do
                          so1 <- mapDataProp cSig o a b
                          so2 <- mapDataProp cSig o a c
                          return (Just $ Quant_sent (Universal
                                     [Name (mkNName a)
                                     ,Name (mkNName b)
                                     ,Name (mkNName c)
                                     ]
                                     (
                                      Bool_sent (Implication
                                      (
                                       Bool_sent (Conjunction [so1, so2]) nullRange
                                      )
                                      (Atom_sent (
                                        Equation
                                        (
                                          Name_term (mkNName b)
                                        )
                                        (
                                          Name_term (mkNName c)
                                        )
                                      ) nullRange)
                                     ) nullRange))
                                    nullRange, cSig
                                   )
              SameOrDifferentIndividual sameOrDiff indis ->
                  do
                    inD <- mapM (mapIndivURI cSig) indis
                    let inDL = comPairs inD inD
                    return (Just $ (Bool_sent (Conjunction
                             (map (\ (x, y) -> case sameOrDiff of
                                   Same -> Atom_sent (Equation x y) nullRange
                                   Different -> Bool_sent (Negation
                                     (Atom_sent (Equation x y) nullRange)) nullRange
                                 ) inDL)) nullRange), cSig)
              ClassAssertion indi cls ->
                  do
                    inD  <- mapIndivURI cSig indi
                    ocls <- mapDescription cSig cls a
                    return (Just $ Quant_sent (Universal
                             [Name (mkNName a)]
                             (
                              Bool_sent (Implication
                              ( Atom_sent (
                                Equation
                                  (Name_term (mkNName a))
                                  inD
                               ) nullRange)
                              ocls
                             ) nullRange))
                             nullRange, cSig)
              ObjectPropertyAssertion ass ->
                  case ass of
                    Assertion objProp posNeg sourceInd targetInd ->
                              do
                                inS <- mapIndivURI cSig sourceInd
                                inT <- mapIndivURI cSig targetInd
                                oPropH <- mapObjProp cSig objProp a b
                                let oProp = case posNeg of
                                              Positive -> oPropH
                                              Negative -> Bool_sent (Negation
                                                           oPropH) nullRange
                                                           
                                return (Just $ Quant_sent (Universal
                                           [Name (mkNName a)
                                           ,Name (mkNName b)]
                                         (
                                          Bool_sent (Implication
                                          (
                                           Bool_sent (Conjunction
                                           [
                                            Atom_sent 
                                            (
                                              Equation
                                                (Name_term (mkNName a))
                                                inS
                                            ) nullRange
                                           ,Atom_sent
                                            (
                                              Equation
                                                (Name_term (mkNName b))
                                              inT
                                            ) nullRange
                                           ]
                                          ) nullRange)
                                           oProp
                                         ) nullRange))
                                         nullRange, cSig)
              DataPropertyAssertion ass ->
                  case ass of
                    Assertion dPropExp posNeg sourceInd targetInd ->
                        do
                          inS <- mapIndivURI cSig sourceInd
                          inT <- mapConstant cSig targetInd
                          dPropH <- mapDataProp cSig dPropExp a b
                          let dProp = case posNeg of
                                        Positive -> dPropH
                                        Negative -> Bool_sent (Negation
                                                    dPropH) nullRange
                          return (Just $ Quant_sent (Universal
                                             [Name (mkNName a)
                                             ,Name (mkNName b)]
                                    (
                                     Bool_sent (Implication
                                     (
                                      Bool_sent (Conjunction
                                      [
                                            Atom_sent
                                            (
                                              Equation
                                                (Name_term (mkNName a))
                                                inS
                                            ) nullRange
                                           ,Atom_sent
                                            (
                                              Equation
                                                (Name_term (mkNName b))
                                              inT
                                            ) nullRange
                                      ]
                                     ) nullRange)
                                      dProp) nullRange
                                    ))
                                    nullRange, cSig)
              Declaration _ ->
                  return (Nothing, cSig)
        EntityAnno _  ->
              return (Nothing, cSig)

{- | Mapping along ObjectPropsList for creation of pairs for commutative
operations. -}
mapComObjectPropsList :: Sign                    -- ^ Signature
                      -> [ObjectPropertyExpression]
                      -> Int                         -- ^ First variable
                      -> Int                         -- ^ Last  variable
                      -> Result [(SENTENCE,SENTENCE)]
mapComObjectPropsList cSig props num1 num2 =
  mapM (\ (x, z) -> do
        l <- mapObjProp cSig x num1 num2
        r <- mapObjProp cSig z num1 num2
        return (l, r)
      ) $ comPairs props props


-- | mapping of data constants
mapConstant :: Sign
            -> Constant
            -> Result TERM 
mapConstant _ c =
  do
    let cl = case c of
              Constant l _ -> l
    return $ Funct_term
              (
               Name_term (mkSimpleId cl)
              )
              (
               Term_seq [] nullRange
              )
              nullRange

-- | Mapping of subobj properties
mapSubObjProp :: Sign
              -> SubObjectPropertyExpression
              -> ObjectPropertyExpression
              -> Int
              -> Result SENTENCE
mapSubObjProp cSig prop oP num1 = 
  let
      num2 = num1 + 1
  in
    case prop of
             OPExpression oPL ->
               do
                 l <- mapObjProp cSig oPL num1 num2
                 r <- mapObjProp cSig oP num1 num2
                 return $ Quant_sent (Universal
                    [ Name (mkNName num1)
                    , Name (mkNName num2)]
                    (
                     Bool_sent
                     (
                      Implication
                      r
                      l
                     )
                     nullRange
                    )
                    )
                    nullRange
             SubObjectPropertyChain props -> 
               do
                 let zprops = zip (tail props) [(num2 + 1) ..]
                     (_, vars) = unzip zprops
                 oProps  <- mapM (\ (z, x, y) -> mapObjProp cSig z x y) $
                                  zip3 props ((num1 : vars) ++ [num2]) $
                                       tail ((num1 : vars) ++ [num2])
                 ooP     <- mapObjProp cSig oP num1 num2
                 return $ Quant_sent (Universal
                           [ Name (mkNName num1)
                           , Name (mkNName num2)]
                           (
                            Quant_sent (Universal
                            (
                             map (\x -> Name (mkNName x)) vars
                            )
                            (
                            Bool_sent (
                             Implication
                             (Bool_sent (Conjunction oProps) nullRange)
                             ooP
                            )
                            nullRange
                            )
                            )
                            nullRange
                           )
                           )
                           nullRange

{- | Mapping along DataPropsList for creation of pairs for commutative
operations. -}
mapComDataPropsList :: Sign
                      -> [DataPropertyExpression]
                      -> Int                         -- ^ First variable
                      -> Int                         -- ^ Last  variable
                      -> Result [(SENTENCE,SENTENCE)]
mapComDataPropsList cSig props num1 num2 =
  mapM (\ (x, z) -> do
                  l <- mapDataProp cSig x num1 num2
                  r <- mapDataProp cSig z num1 num2
                  return (l, r)
             ) $ comPairs props props

-- | Mapping of data properties
mapDataProp :: Sign
            -> DataPropertyExpression
            -> Int
            -> Int
            -> Result SENTENCE
mapDataProp _ dP nO nD =
  do
    let
        l = Name_term (mkNName nO)
        r = Name_term (mkNName nD)
    ur <- uriToTokM dP
    return $ Atom_sent
             (
              Atom
              (
               Name_term ur
              )
              (
               Term_seq [ l, r] nullRange
              )
             )
             nullRange


-- | Mapping of obj props
mapObjProp :: Sign
              -> ObjectPropertyExpression
              -> Int
              -> Int
              -> Result SENTENCE
mapObjProp cSig ob num1 num2 =
  case ob of
         OpURI u ->
           do
             let l = Name_term (mkNName num1)
                 r = Name_term (mkNName num2)
             ur <- uriToTokM u
             return $ Atom_sent
                      (
                       Atom
                        (
                          Name_term ur 
                        )
                        (
                          Term_seq [l, r] nullRange
                        )
                      )
                      nullRange
         InverseOp u ->
           mapObjProp cSig u num2 num1


-- | Mapping of obj props with Individuals
mapObjPropI :: Sign
              -> ObjectPropertyExpression
              -> VarOrIndi
              -> VarOrIndi
              -> Result SENTENCE
mapObjPropI cSig ob lP rP =
  case ob of
       OpURI u ->
        do
          lT <- case lP of
                    OVar   num1   -> return $ Name_term (mkNName num1)
                    OIndi indivID -> mapIndivURI cSig indivID
          rT <- case rP of
                    OVar   num1   -> return $ Name_term (mkNName num1)
                    OIndi indivID -> mapIndivURI cSig indivID
          ur <- uriToTokM u
          return $ Atom_sent
                   (
                     Atom
                      (
                       Name_term ur
                      )
                      (
                       Term_seq [ lT, rT] nullRange
                      )
                   )
                   nullRange
       InverseOp u -> mapObjPropI cSig u rP lP

-- | Mapping of Class URIs
mapClassURI :: Sign
            -> OwlClassURI
            -> Token
            -> Result SENTENCE
mapClassURI _ uril uid =
  do
    ur <- uriToTokM uril
    return $ Atom_sent
             (
              Atom
              (
               Name_term ur
              )
              (
               Term_seq [Name_term uid] nullRange
              )
             )
             nullRange

-- | Mapping of Individual URIs
mapIndivURI :: Sign
            -> IndividualURI
            -> Result TERM
mapIndivURI _ uriI =
  do
    ur <- uriToTokM uriI
    return $ Funct_term
             (
              Name_term ur
             )
             (
              Term_seq [] nullRange
             )
             nullRange

uriToTokM :: URI -> Result Token
uriToTokM = return . uriToTok

-- | Extracts Token from URI
uriToTok :: URI -> Token
uriToTok urI =
    let
        ur = case urI of
               QN _ "Thing" _ _ -> mkQName "Thing"
               QN _ "Nothing" _ _ -> mkQName "Nothing"
               _ -> urI
        repl a = if isAlphaNum a
                  then
                      a
                  else
                      '_'
        nP = map repl $ namePrefix   ur
        lP = map repl $ localPart    ur
        nU = map repl $ namespaceUri ur
    in mkSimpleId $ nU ++ "" ++ nP ++ "" ++ lP

-- | Mapping of a list of descriptions
mapDescriptionList :: Sign
                      -> Int
                      -> [Description]
                      -> Result [SENTENCE]
mapDescriptionList cSig n lst =
  mapM (uncurry $ mapDescription cSig)
                        $ zip lst $ replicate (length lst) n

-- | Mapping of a list of pairs of descriptions
mapDescriptionListP :: Sign
                    -> Int
                    -> [(Description, Description)]
                    -> Result [(SENTENCE, SENTENCE)]
mapDescriptionListP cSig n lst =
    do
      let (l, r) = unzip lst
      llst  <- mapDescriptionList cSig n l
      rlst  <- mapDescriptionList cSig n r
      let olst = zip llst rlst
      return olst

-- | Build a name
mkNName :: Int -> Token
mkNName i = mkSimpleId $ hetsPrefix ++  mkNName_H i
    where
      mkNName_H k =
          case k of
            0 -> ""
            j -> mkNName_H (j `div` 26) ++ [chr (j `mod` 26 + 96)]

-- | Get all distinct pairs for commutative operations
comPairs :: [t] -> [t1] -> [(t, t1)]
comPairs [] []     = []
comPairs _  []     = []
comPairs [] _      = []
comPairs (a:as) (_:bs) = zip (replicate (length bs) a) bs ++ comPairs as bs

-- | mapping of Data Range
mapDataRange :: Sign
             -> DataRange                -- ^ OWL DataRange
             -> Int                      -- ^ Current Variablename
             -> Result SENTENCE       -- ^ CommonLogic SENTENCE
mapDataRange cSig rn inId =
  do 
    let uid = mkNName inId
    case rn of
         DRDatatype uril -> error "nyi"{-> --TODO
          do
            ur <- uriToTokM uril
            return $ -}
         DataComplementOf dr ->
          do
            dc <- mapDataRange cSig dr inId
            return $ Bool_sent (Negation dc) nullRange
         DataOneOf _ -> error "nyi"
         DatatypeRestriction _ _ -> error "nyi"

-- | mapping of OWL Descriptions
mapDescription :: Sign
               -> Description              -- ^ OWL Description
               -> Int                      -- ^ Current Variablename
               -> Result SENTENCE       -- ^ CommonLogic_DL Formula
mapDescription cSig des var = 
  case des of
         OWLClassDescription cl -> mapClassURI cSig cl (mkNName var)
         ObjectJunction jt desL ->
           do
             desO <- mapM (flip (mapDescription cSig) var) desL
             return $ case jt of
                UnionOf -> Bool_sent (Disjunction desO) nullRange
                IntersectionOf -> Bool_sent (Conjunction desO) nullRange
         ObjectComplementOf descr ->
           do 
             desO <- mapDescription cSig descr var
             return $ Bool_sent (Negation desO) nullRange
         ObjectOneOf indS ->
           do
             indO <- mapM (mapIndivURI cSig) indS
             let varO = Name_term (mkNName var)
             let forms = map ((\x y -> Atom_sent (Equation x y) nullRange) varO) indO
             return $ Bool_sent (Disjunction forms) nullRange
         ObjectValuesFrom qt oprop descr -> 
           do
             opropO <- mapObjProp cSig oprop var (var + 1)
             descO <- mapDescription cSig descr (var + 1)
             case qt of
               SomeValuesFrom ->
                    return $ Quant_sent (Existential [Name (mkNName 
                                        (var + 1))]
                        (
                         Bool_sent (Conjunction
                         [opropO, descO])
                         nullRange
                        ))
                 nullRange
               AllValuesFrom ->
                   return $ Quant_sent (Universal [Name (mkNName 
                                        (var + 1))]
                        (
                         Bool_sent (Implication
                         opropO descO)
                         nullRange
                        ))
                        nullRange
         ObjectExistsSelf oprop -> mapObjProp cSig oprop var var
         ObjectHasValue oprop indiv ->
                mapObjPropI cSig oprop (OVar var) (OIndi indiv)
         ObjectCardinality c -> 
          case c of
               Cardinality ct n oprop d
                        ->
                          do
                            let vlst = [(var+1) .. (n+var)]
                                vlstM = [(var+1) .. (n+var+1)]
                            dOut <- (\x -> case x of
                                            Nothing -> return []
                                            Just y ->
                                              mapM (mapDescription cSig y) vlst
                                    ) d
                            let dlst = map (\(x,y) -> 
                                            Bool_sent (Negation
                                            (
                                              Atom_sent (Equation
                                                (Name_term (mkNName x))
                                                (Name_term (mkNName y)))
                                                nullRange
                                            )
                                            )
                                            nullRange
                                            ) $ comPairs vlst vlst
                                dlstM = map (\(x,y) ->
                                                Atom_sent (Equation
                                                  (Name_term (mkNName x))
                                                  (Name_term (mkNName y)))
                                                  nullRange
                                            ) $ comPairs vlstM vlstM
                                qVars = map (\x ->
                                              Name (mkNName x)
                                            ) vlst
                                qVarsM = map (\x ->
                                                  Name (mkNName x)
                                             ) vlstM
                            oProps <- mapM (mapObjProp cSig oprop var) vlst
                            oPropsM <- mapM (mapObjProp cSig oprop var) vlstM
                            let minLst = Quant_sent (Existential
                                  qVars
                                  (
                                   Bool_sent (Conjunction
                                   (dlst ++ dOut ++ oProps))
                                   nullRange
                                  ))
                                  nullRange
                            let maxLst = Quant_sent (Universal
                                  qVarsM
                                  (
                                   Bool_sent (Implication
                                   (Bool_sent (Conjunction (oPropsM ++ dOut)) nullRange)
                                   (Bool_sent (Disjunction dlstM) nullRange))
                                   nullRange
                                  ))
                                  nullRange
                            case ct of
                               MinCardinality -> return minLst
                               MaxCardinality -> return maxLst
                               ExactCardinality -> return $
                                           Bool_sent (Conjunction
                                           [minLst, maxLst])
                                           nullRange                     
           
         DataValuesFrom _ _ _ _ -> fail "data handling nyi"
         DataHasValue _ _       -> fail "data handling nyi"
         DataCardinality _      -> fail "data handling nyi"
