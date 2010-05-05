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
import Common.AS_Annotation
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
import CommonLogic.AS_Basic_CommonLogic
import CommonLogic.Sign
import CommonLogic.Morphism
import CommonLogic.Sublogic

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
    --CommonLogic_Sublogics  -- sublogics codomain
    CommonLogicBasicSpec   -- Basic spec codomain
    CommonLogicSENTENCE     -- sentence codomain
    SYMB_ITEMS      -- symbol items codomain
    SYMB_MAP_ITEMS  -- symbol map items codomain
    CommonLogicSign        -- signature codomain
    CommonLogicMor         -- morphism codomain
    Symbol          -- symbol codomain
    RawSymbol       -- rawsymbol codomain
    ProofTree       -- proof tree domain
    where
      sourceLogic OWL2CommonLogic    = OWL
      sourceSublogic OWL2CommonLogic = sl_top
      targetLogic OWL2CommonLogic    = CommonLogic
      mapSublogic OWL2CommonLogic _  = Just $ ()
      map_theory OWL2CommonLogic     = mapTheory
      map_morphism OWL2CommonLogic   = mapMorphism
      isInclusionComorphism OWL2CommonLogic = True
      has_model_expansion OWL2CommonLogic = True

{-- | Mapping of OWL morphisms to CommonLogic morphisms
mapMorphism :: OWLMorphism -> Result CommonLogicMor
mapMorphism oMor =
-}
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
         (x:xs) -> Funct_term (Name x) (mkThingTerm xs)
         _ -> Name_term noThing

-- | OWL Data topSort DATA
dataS :: NAME
dataS = mkSimpleId $ drop 3 $ show OWLDATA
{-
data VarOrIndi = OVar Int | OIndi URI

predefSorts :: Set.Set SORT
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

mapSign :: OS.Sign                 -- ^ OWL signature
        -> Result CommonLogicSign         -- ^ CommonLogic signature
mapSign sig =


loadDataInformation :: OWLSub -> Sign f ()
loadDataInformation sl =
    let
        dts = Set.map (stringToId . printXSDName) $ datatype sl
    in
     (emptySign ()) { sortSet = dts }


predefinedSentences :: [Named SENTENCE]
predefinedSentences =

mapTheory :: (OS.Sign, [Named Axiom])
             -> Result (CommonLogicSign, [Named CommonLogicSENTENCE])
mapTheory (owlSig, owlSens) =
-}
-- | mapping of OWL to CommonLogic_DL formulae
mapSentence :: CommonLogicSign                    -- ^ CommonLogic Signature
  -> Named Axiom                                  -- ^ OWL Sentence
  -> Result (Maybe (Named CommonLogicSENTENCE), CommonLogicSign) -- ^ CommonLogic SENTENCE
mapSentence cSig inSen = do
    (outAx, outSig) <- mapAxiom cSig $ sentence inSen
    return (fmap (flip mapNamed inSen . const) outAx, outSig)

-- | Mapping of Axioms
mapAxiom :: CommonLogicSign                             -- ^ CommonLogic Signature
         -> Axiom                                -- ^ OWL Axiom
         -> Result (Maybe CommonLogicSENTENCE, CommonLogicSign) -- ^ CommonLogic Formula
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
                    return (Just $ Quant_sent Universal
                               [Name (mkNName a)]
                               (Implication
                                domT
                                codT) nullRange, cSig)
              EquivOrDisjointClasses eD dS ->
                  do
                    decrsS <- mapDescriptionListP cSig a $ comPairs dS dS
                    let decrsP =
                            case eD of
                              Equivalent -> 
                                  map (\(x,y) -> Biconditional x y)
                                      decrsS
                              Disjoint   ->
                                  map (\(x,y) -> Negation
                                       (Conjunction [x,y]))
                                       decrsS
                    return (Just $ Quant_sent Universal
                              [Name (mkNName a)]
                               (
                                Conjunction decrsP
                               ) nullRange, cSig)
              DisjointUnion cls sD ->
                  do
                    decrs  <- mapDescriptionList cSig a sD
                    decrsS <- mapDescriptionListP cSig a $ comPairs sD sD
                    let decrsP = map (\ (x, y) -> Conjunction [x,y])
                                 decrsS
                    mcls <- mapClassURI cSig cls (mkNName a)
                    return (Just $ Quant_sent Universal
                              [Name (mkNName a)]
                               (
                                Biconditional
                                  mcls                 -- The class
                                (                      -- The rest
                                  Conjunction
                                  [
                                   Disjunction decrs
                                  ,Negation
                                   (
                                    Conjunction decrsP
                                   )
                                  ]
                                )
                               ) nullRange, cSig)
              SubObjectPropertyOf ch op ->
                  do
                    os <- mapSubObjProp cSig ch op c
                    return (Just os, cSig)
              EquivOrDisjointObjectProperties disOrEq oExLst ->
                  do
                    pairs <- mapComObjectPropsList cSig oExLst a b
                    return (Just $ Quant_sent Universal
                              [ Name (mkNName a)
                              , Name (mkNName b)]
                               (
                                Conjunction
                                (
                                 case disOrEq of
                                   Equivalent ->
                                       map (\(x,y) ->
                                                Biconditional x y) pairs
                                   Disjoint   ->
                                       map (\(x,y) ->
                                                (Negation
                                                 (Conjunction [x,y])
                                                )
                                           ) pairs
                                )
                               )
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
                          return (Just $ Quant_sent Universal
                                     [Name (fst vars)]
                                     (
                                      Quant_sent Existential
                                         [Name (snd vars)]
                                         (
                                          Implication
                                           tobjP
                                           tdsc
                                         )
                                      nullRange
                                     )
                                     nullRange, cSig)
              InverseObjectProperties o1 o2 ->
                  do
                    so1 <- mapObjProp cSig o1 a b
                    so2 <- mapObjProp cSig o2 b a
                    return (Just $ Quant_sent Universal
                             [Name (mkNName a)
                             ,Name (mkNName b)]
                             (
                              Biconditional
                              so1
                              so2
                             )
                             nullRange, cSig)
              ObjectPropertyCharacter cha o ->
                  case cha of
                    Functional ->
                        do
                          so1 <- mapObjProp cSig o a b
                          so2 <- mapObjProp cSig o a c
                          return (Just $ Quant_sent Universal
                                     [Name (mkNName a)
                                     ,Name (mkNName b)
                                     ,Name (mkNName c)
                                     ]
                                     (
                                      Implication
                                      (
                                       Conjunction [so1, so2]
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
                                     )
                                     nullRange, cSig)
                    InverseFunctional ->
                        do
                          so1 <- mapObjProp cSig o a c
                          so2 <- mapObjProp cSig o b c
                          return (Just $ Quant_sent Universal
                                     [Name (mkNName a)
                                     ,Name (mkNName b)
                                     ,Name (mkNName c)
                                     ]
                                     (
                                      Implication
                                      (
                                       Conjunction [so1, so2]
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
                                     )
                                     nullRange, cSig)
                    Reflexive  ->
                        do
                          so <- mapObjProp cSig o a a
                          return (Just $ Quant_sent Universal
                                   [Name (mkNName a)]
                                    so
                                    nullRange, cSig)
                    Irreflexive ->
                        do
                          so <- mapObjProp cSig o a a
                          return
                                 (Just $ Quant_sent Universal
                                   [Name (mkNName a)]
                                   (Negation so)
                                   nullRange, cSig)
                    Symmetric ->
                        do
                          so1 <- mapObjProp cSig o a b
                          so2 <- mapObjProp cSig o b a
                          return
                           (Just $ Quant_sent Universal
                               [Name (mkNName a)
                               ,Name (mkNName b)]
                               (
                                Implication
                                so1
                                so2
                               )
                               nullRange, cSig)
                    Asymmetric ->
                        do
                          so1 <- mapObjProp cSig o a b
                          so2 <- mapObjProp cSig o b a
                          return
                           (Just $ Quant_sent Universal
                               [Name (mkNName a)
                               ,Name (mkNName b)]
                               (
                                Implication
                                so1
                                (Negation so2)
                               )
                               nullRange, cSig)
                    Antisymmetric ->
                        do
                          so1 <- mapObjProp cSig o a b
                          so2 <- mapObjProp cSig o b a
                          return
                           (Just $ Quant_sent Universal
                               [Name (mkNName a)
                               ,Name (mkNName b)]
                               (
                                Implication
                                 (Conjunction [so1, so2])
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
                               )
                               nullRange, cSig)
                    Transitive ->
                        do
                          so1 <- mapObjProp cSig o a b
                          so2 <- mapObjProp cSig o b c
                          so3 <- mapObjProp cSig o a c
                          return
                           (Just $ Quant_sent Universal
                               [Name (mkNName a)
                               ,Name (mkNName b)
                               ,Name (mkNName c)]
                               (
                                Implication
                                (
                                 Conjunction [so1, so2]
                                )
                                 so3
                               )
                               nullRange, cSig)
              SubDataPropertyOf dP1 dP2 ->
                  do
                    l <- mapDataProp cSig dP1 a b
                    r <- mapDataProp cSig dP2  a b
                    return (Just $ Quant_sent Universal
                               [ Name (mkNName a)
                               , Name [mkNName b] dataS nullRange]
                               (
                                Implication
                                l
                                r
                               )
                               nullRange, cSig)
              EquivOrDisjointDataProperties disOrEq dlst ->
                  do
                    pairs <- mapComDataPropsList cSig dlst a b
                    return (Just $ Quant_sent Universal
                              [ Name (mkNName a)
                              , Name [mkNName b] dataS nullRange]
                               (
                                Conjunction
                                (
                                 case disOrEq of
                                   Equivalent ->
                                       map (\(x,y) ->
                                                Biconditional x y) pairs
                                   Disjoint   ->
                                       map (\(x,y) ->
                                                (Negation
                                                 (Conjunction [x,y])
                                                )
                                           ) pairs
                                )
                               )
                               nullRange, cSig)
              DataPropertyDomainOrRange domRn dpex ->
                        do
                          oEx <- mapDataProp cSig dpex a b
                          case domRn of
                            DataDomain mdom ->
                                do
                                  odes <- mapDescription cSig mdom a
                                  let vars = (mkNName a, mkNName b)
                                  return (Just $ Quant_sent Universal
                                         [Name (fst vars)]
                                         (Quant_sent Existential
                                         [Name (snd vars)]
                                         (Implication oEx odes)
                                         nullRange) nullRange, cSig)
                            DataRange  rn  ->
                                do
                                  odes <- mapDataRange cSig rn b
                                  let vars = (mkNName a, mkNName b)
                                  return (Just $ Quant_sent Universal
                                         [Name (fst vars)]
                                         (Quant_sent Existential
                                         [Name [snd vars]]
                                         (Implication oEx odes)
                                         nullRange) nullRange, cSig)
              FunctionalDataProperty o ->
                        do
                          so1 <- mapDataProp cSig o a b
                          so2 <- mapDataProp cSig o a c
                          return (Just $ Quant_sent Universal
                                     [Name (mkNName a)
                                     ,Name [mkNName b] dataS nullRange
                                     ,Name [mkNName c] dataS nullRange
                                     ]
                                     (
                                      Implication
                                      (
                                       Conjunction [so1, so2]
                                      )
                                      (
                                       Atom
                                       (
                                        Equation
                                        (
                                          Name_term (mkNName b) dataS
                                        )
                                        (
                                          Name_term (mkNName c) dataS
                                        )
                                       )
                                      )
                                     )
                                    nullRange, cSig
                                   )
              SameOrDifferentIndividual sameOrDiff indis ->
                  do
                    inD <- mapM (mapIndivURI cSig) indis
                    let inDL = comPairs inD inD
                    return (Just $ Conjunction
                             (map (\ (x, y) -> case sameOrDiff of
                                   Same -> Atom (Equation x y)
                                   Different -> Negation
                                     (Atom (Equation x y))
                                 ) inDL), cSig)
              ClassAssertion indi cls ->
                  do
                    inD  <- mapIndivURI cSig indi
                    ocls <- mapDescription cSig cls a
                    return (Just $ Quant_sent Universal
                             [Name (mkNName a)]
                             (
                              Implication
                              (
                               Atom
                               (
                                Equation
                                  (Name (mkNName a))
                                  inD
                               )
                              )
                              ocls
                             )
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
                                              Negative -> Negation
                                                           oPropH
                                                           
                                return (Just $ Quant_sent Universal
                                           [Name (mkNName a)
                                           ,Name (mkNName b)]
                                         (
                                          Implication
                                          (
                                           Conjunction
                                           [
                                            Atom
                                            (
                                              Equation
                                                (Name (mkNName a))
                                                inS
                                            )
                                           ,Atom
                                            (
                                              Equation
                                                (Name (mkNName b))
                                              inT
                                            )
                                           ]
                                          )
                                           oProp
                                         )
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
                                        Negative -> Negation
                                                    dPropH
                          return (Just $ Quant_sent Universal
                                             [Name [mkNName a]
                                                       thing nullRange
                                             ,Name [mkNName b]
                                                       dataS nullRange]
                                    (
                                     Implication
                                     (
                                      Conjunction
                                      [
                                            Atom
                                            (
                                              Equation
                                                (Name (mkNName a))
                                                inS
                                            )
                                           ,Atom
                                            (
                                              Equation
                                                (Name (mkNName b))
                                              inT
                                            )
                                      ]
                                     )
                                      dProp
                                    )
                                    nullRange, cSig)
              Declaration _ ->
                  return (Nothing, cSig)
        EntityAnno _  ->
              return (Nothing, cSig)

{- | Mapping along ObjectPropsList for creation of pairs for commutative
operations. -}
mapComObjectPropsList :: CommonLogicSign                    -- ^ CommonLogicSignature
                      -> [ObjectPropertyExpression]
                      -> Int                         -- ^ First variable
                      -> Int                         -- ^ Last  variable
                      -> Result [(CommonLogicSENTENCE,CommonLogicSENTENCE)]
mapComObjectPropsList cSig props num1 num2 =
  mapM (\ (x, z) -> do
        l <- mapObjProp cSig x num1 num2
        r <- mapObjProp cSig z num1 num2
        return (l, r)
      ) $ comPairs props props


{-- | mapping of data constants
mapConstant :: CommonLogicSign
            -> Constant
            -> Result (TERM ())
mapConstant _ c =
-}
-- | Mapping of subobj properties
mapSubObjProp :: CommonLogicSign
              -> SubObjectPropertyExpression
              -> ObjectPropertyExpression
              -> Int
              -> Result CommonLogicSENTENCE
mapSubObjProp cSig prop oP num1 = 
  let
      num2 = num1 + 1
  in
    case prop of
             OPExpression oPL ->
               do
                 l <- mapObjProp cSig oPL num1 num2
                 r <- mapObjProp cSig oP num1 num2
                 return $ Quant_sent Universal
                    [ Name [mkNName num1] thing nullRange
                    , Name [mkNName num2] thing nullRange]
                    (
                      Implication
                      r
                      l
                    )
                    nullRange
                    SubObjectPropertzChain props ->
                      do
                        let zprops = zip (tail props) [(num2 + 1) ..]
                            (_, vars) = unzip zprops
                        oProps  <- mapM (\ z, x, y) -> mapObjProp cSig z x y) $
                                      zip3 props ((num1 : vars) ++ [num2]) $
                                          tail ((num1 : vars) ++ [num2])
                        ooP     <- mapObjProp cSig oP num1 num2
                        return $ Quant_sent Universal
                               [ Name [mkNName num1] thing nullRange
                               , Name [mkNName num2] thing nullRange]
                               (
                                  Quant_sent Universal
                                    (
                                    map (\x -> Name [mkNName x] thing nullRange) vars
                                    )
                                    (
                                      Implication
                                      (Conjunction oProps)
                                      ooP
                                    )
                                  nullRange
                               )
                               nullRange

{- | Mapping along DataPropsList for creation of pairs for commutative
operations. -}
mapComDataPropsList :: CommonLogicSign
                      -> [DataPropertyExpression]
                      -> Int                         -- ^ First variable
                      -> Int                         -- ^ Last  variable
                      -> Result [(CommonLogicSENTENCE,CommonLogicSENTENCE)]
mapComDataPropsList cSig props num1 num2 =
  mapM (\ (x, z) -> do
                  l <- mapDataProp cSig x num1 num2
                  r <- mapDataProp cSig z num1 num2
                  return (l, r)
             ) $ comPairs props props
{-
-- | Mapping of data properties
mapDataProp :: CommonLogicSign
            -> DataPropertyExpression
            -> Int
            -> Int
            -> Result CommonLogicSENTENCE
mapDataProp _ dP nO nD =
  do
    let
        l = mkNName nO
        r = mkNName nD
    ur <- uriToTokM dP
    return $ 

-}
-- | Mapping of obj props
mapObjProp :: CommonLogicSign
              -> ObjectPropertyExpression
              -> Int
              -> Int
              -> Result CommonLogicSENTENCE
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
                          Term_seq [l, r]
                        )
                      )
                      nullRange
         InverseOp u ->
           mapObjProp cSig u num2 num1


-- | Mapping of obj props with Individuals
mapObjPropI :: CommonLogicSign
              -> ObjectPropertyExpression
              -> VarOrIndi
              -> VarOrIndi
              -> Result CommonLogicSENTENCE
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
          ur <- uriToIdM u
          return $ Atom_sent
                   (
                     Atom
                      (
                       Name_term ur
                      )
                      (
                       Term_seq [ lT, rT]
                      )
                   )
                   nullRange
       InverseOp u -> mapObjPropI cSig u rP lP

-- | Mapping of Class URIs
mapClassURI :: CommonLogicSign
            -> OwlClassURI
            -> Token
            -> Result CommonLogicSENTENCE
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
               Term_seq [Name_term uid]
              )
             )
             nullRange

-- | Mapping of Individual URIs
mapIndivURI :: CommonLogicSign
            -> IndividualURI
            -> Result (TERM ())
mapIndivURI _ uriI =
  do
    ur <- uriToTokM uriI
    return $ Atom_sent
             (
              Atom
              (
               Name_term ur
              )
              (
               Term_seq []
              )
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
mapDescriptionList :: CommonLogicSign
                      -> Int
                      -> [Description]
                      -> Result [CommonLogicSENTENCE]
mapDescriptionList cSig n lst =
  mapM (uncurry $ mapDescription cSig)
                        $ zip lst $ replicate (length lst) n

-- | Mapping of a list of pairs of descriptions
mapDescriptionListP :: CommonLogicSign
                    -> Int
                    -> [(Description, Description)]
                    -> Result [(CommonLogicSENTENCE, CommonLogicSENTENCE)]
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
mapDataRange :: CommonLogicSign
             -> DataRange                -- ^ OWL DataRange
             -> Int                      -- ^ Current Variablename
             -> Result CommonLogicSENTENCE       -- ^ CommonLogic SENTENCE
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
            return $ Bool_sent Negation dc nullRange
         DataOneOf _ -> error "nyi"
         DatatypeRestriction _ _ -> error "nyi"

-- | mapping of OWL Descriptions
mapDescription :: CommonLogicSign
               -> Description              -- ^ OWL Description
               -> Int                      -- ^ Current Variablename
               -> Result CommonLogicSENTENCE       -- ^ CommonLogic_DL Formula
mapDescription cSig des var = 
  case des of
         OWLClassDescription cl -> mapClassURI cSig cl (mkNName var)
         ObjectJunction jt desL ->
           do
             desO <- mapM (flip (mapDescription cSig) var) desL
             return $ case jt of
                UnionOf -> Bool_sent Disjunction desO nullRange
                IntersectionOf -> Bool_sent Conjunction desO nullRange
         ObjectComplementOf descr ->
           do 
             desO <- mapDescription cSig descr var
             return $ Bool_sent Negation desO nullRange
         ObjectOneOf indS ->
           do
             indO <- mapM (mapIndivURI cSig) indS
             let varO = Name_term (mkNName var)
             let forms = map (mkStEq varO) indO
             return $ Bool_sent Disjunction forms nullRange
         ObjectValuesFrom qt oprop descr -> 
           do
             opropO <- mapObjProp cSig oprop var (var + 1)
             descO <- mapDescription cSig descr (var + 1)
             case qt of
               SomeValuesFrom ->
                    return $ Quant_sent Existential [Name [mkNName 
                                        (var + 1)] thing NullRange]
                        (
                         Bool_sent Conjunction
                         [opropO, descO]
                         nullRange
                        )
                 nullRange
                 AllValuesFrom ->
                   return $ Quant_sent Universal [Name [mkNName 
                                        (var + 1)] thing NullRange]
                        (
                         Bool_sent Implication
                         oprop descO
                         nullRange
                        )
                        nullRange
         ObjectExistsSelf oprop -> mapObjProp cSig oprop var var
         ObjectHasValue oprop indiv ->
                mapObjPropI cSig oprop (OVar var) (OInki indiv)
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
                            let dlst = map (\x,y) -> 
                                            Bool_sent Negation
                                            (
                                              Bool_sent Equation
                                                (Name (mkNName x))
                                                (Name (mkNName y))
                                                nullRange
                                            )
                                            nullRange
                                            ) $ comPairs vlst vlst
                                dlstM = map (\(x,y) ->
                                                Bool_sent Equation
                                                  (Name (mkNName x))
                                                  (Name (mkNName y))
                                                  nullRange
                                            ) $ comPairs vlstM vlstM
                                qVars = map (\x ->
                                              Name [mkNName x]
                                                        thing nullRange
                                            ) vlst
                                qVarsM = map (\x ->
                                                  Name [mkNName x]
                                                        thing nullRange
                                             ) vlstM
                            oProps <- mapM (mapObjProp cSig oprop var) vlst
                            oPropsM <- mapM (mapObjProp cSig oprop var) vlstM
                            let minLst = Quant_sent Existential
                                  qVars
                                  (
                                   Bool_sent Conjunction
                                   (dlst ++ dOut ++ oProps)
                                   nullRange
                                  )
                                  nullRange
                            let maxLst = Quant_sent Universal
                                  qVarsM
                                  (
                                   Bool_sent Implication
                                   (Bool_sent Conjunction (oPropsM ++ dOut) nullRange)
                                   (Bool_sent Disjunction dlstM nullRange)
                                   nullRange
                                  )
                                  nullRange
                            case ct of
                               MinCardinality -> return minLst
                               MaxCardinality -> return maxLst
                               ExactCardinality -> return $
                                           Bool_sent Conjunction
                                           [minLst, maxLst]
                                           nullRange                     
           
      DataValuesFrom _ _ _ _ -> fail "data handling nyi"
      DataHasValue _ _       -> fail "data handling nyi"
      DataCardinality _      -> fail "data handling nyi"
