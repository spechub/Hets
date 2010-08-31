{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances #-}
{- |
Module      :  $Header$
Description :  Comorphism from OWL 1.1 to Common Logic
Copyright   :  (c) Uni Bremen DFKI 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  mata@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (via Logic.Logic)

a comorphism from OWL to CommonLogic
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
import qualified CommonLogic.Morphism as CLM

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
    SYMB_MAP_ITEMS  -- symbol map items codomain
    Sign        -- signature codomain
    CLM.Morphism         -- morphism codomain
    Symbol          -- symbol codomain
    Symbol       -- rawsymbol codomain
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

-- | Mapping of OWL morphisms to CommonLogic morphisms
mapMorphism :: OWLMorphism -> Result CLM.Morphism
mapMorphism oMor =
  do
    dm <- mapSign $ osource oMor
    cd <- mapSign $ otarget oMor
    mapp <- mapMap $ mmaps oMor 
    return  (CLM.mkMorphism dm cd mapp)

-- | OWL topsort Thing
thing :: NAME --Id
thing = mkSimpleId "Thing" --stringToId "Thing"

noThing :: NAME
noThing = mkSimpleId "Nothing" --stringToId "Nothing"

data VarOrIndi = OVar Int | OIndi URI

hetsPrefix :: String
hetsPrefix = ""

mapMap :: Map.Map Entity URI -> Result (Map.Map Id Id)
mapMap m = 
  return $ Map.map uriToId $ Map.mapKeys entityToId m

mapSign :: OS.Sign                 -- ^ OWL signature
        -> Result Sign         -- ^ CommonLogic signature
mapSign sig =
  let preds = Set.fromList [ (mkQName "Nothing")
                           , (mkQName "Thing")]
      conc = Set.unions [ preds
                        , (OS.concepts sig)
                        , (OS.primaryConcepts sig)
                        , (OS.datatypes sig)
                        , (OS.indValuedRoles sig)
                        , (OS.dataValuedRoles sig)
                        , (OS.annotationRoles sig)
                        , (OS.individuals sig) ]
      itms = Set.map uriToId conc
  in return emptySig { items = itms }


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
          [ Term_seq (Name_term (mkNName 1)) ]
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
         [ Term_seq (Name_term (mkNName 1)) ]
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
         -> Result (Maybe SENTENCE, Sign) -- ^ CommonLogic SENTENCE
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
                    (domT, dSig) <- mapDescription cSig sub   (OVar a) a
                    (codT, eSig) <- mapDescription cSig super (OVar a) a
                    rSig <- sigUnion cSig (unite dSig eSig)
                    return (Just $ Quant_sent (Universal
                               [Name (mkNName a)]
                               (Bool_sent (Implication
                                domT
                                codT)
                                nullRange)) nullRange, rSig)
              EquivOrDisjointClasses eD dS ->
                  do
                    (decrsS, dSig) <- mapDescriptionListP cSig a $ comPairs dS dS
                    let decrsP = case eD of
                              Equivalent ->
                                  map (\(x,y) -> Bool_sent (Biconditional x y) nullRange)
                                      decrsS
                              Disjoint   ->
                                  map (\(x,y) -> Bool_sent (Negation
                                       (Bool_sent (Conjunction [x,y]) nullRange)) nullRange)
                                       decrsS
                        snt = if (length decrsP == 1) then
                                  head decrsP
                                else
                                  Bool_sent (Conjunction decrsP) nullRange
                    return (Just $ Quant_sent (Universal
                              [Name (mkNName a)]
                               snt) nullRange, dSig)
              DisjointUnion cls sD ->
                  do
                    (decrs, dSig)  <- mapDescriptionList cSig a sD
                    (decrsS, pSig) <- mapDescriptionListP cSig a $ comPairs sD sD
                    let decrsP = unzip decrsS
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
                                      Bool_sent (Conjunction 
                                      ((fst decrsP) ++ (snd decrsP))) nullRange
                                     )
                                    ) nullRange)
                                  ]) nullRange
                                )
                               ) nullRange
                               )
                               ) nullRange, unite dSig pSig)
              SubObjectPropertyOf ch op ->
                  do
                    os <- mapSubObjProp cSig ch op c
                    return (Just os, cSig)
              EquivOrDisjointObjectProperties disOrEq oExLst ->      
                  do
                    pairs <- mapComObjectPropsList cSig oExLst (OVar a) (OVar b)
                    let sntLst = case disOrEq of
                                   Equivalent ->
                                       map (\(x,y) ->
                                                Bool_sent (Biconditional x y) nullRange) pairs
                                   Disjoint   ->
                                       map (\(x,y) ->
                                                (Bool_sent (Negation
                                                 (Bool_sent (Conjunction [x,y]) nullRange)) nullRange
                                                )
                                           ) pairs
                        snt = if (length sntLst == 1) then
                                  head sntLst
                                else
                                  Bool_sent (Conjunction
                                    sntLst) nullRange
                    return (Just $ Quant_sent (Universal
                              [ Name (mkNName a)
                              , Name (mkNName b)]
                               snt) nullRange, cSig)
              ObjectPropertyDomainOrRange domOrRn objP descr ->
                        do
                          tobjP <- mapObjProp cSig objP (OVar a) (OVar b)
                          (tdsc, dSig)  <- uncurry (mapDescription cSig descr) $
                                   case domOrRn of
                                     ObjDomain -> (OVar a, a)
                                     ObjRange  -> (OVar b, b)
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
                                     nullRange, dSig)
              InverseObjectProperties o1 o2 ->
                  do
                    so1 <- mapObjProp cSig o1 (OVar a) (OVar b)
                    so2 <- mapObjProp cSig o2 (OVar b) (OVar a)
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
                          so1 <- mapObjProp cSig o (OVar a) (OVar b)
                          so2 <- mapObjProp cSig o (OVar a) (OVar c)
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
                          so1 <- mapObjProp cSig o (OVar a) (OVar c)
                          so2 <- mapObjProp cSig o (OVar b) (OVar c)
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
                          so <- mapObjProp cSig o (OVar a) (OVar a)
                          return (Just $ Quant_sent (Universal
                                   [Name (mkNName a)]
                                    so)
                                    nullRange, cSig)
                    Irreflexive ->
                        do
                          so <- mapObjProp cSig o (OVar a) (OVar a)
                          return
                                 (Just $ Quant_sent (Universal
                                   [Name (mkNName a)]
                                   (Bool_sent (Negation so) nullRange))
                                   nullRange, cSig)
                    Symmetric ->
                        do
                          so1 <- mapObjProp cSig o (OVar a) (OVar b)
                          so2 <- mapObjProp cSig o (OVar b) (OVar a)
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
                          so1 <- mapObjProp cSig o (OVar a) (OVar b)
                          so2 <- mapObjProp cSig o (OVar b) (OVar a)
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
                          so1 <- mapObjProp cSig o (OVar a) (OVar b)
                          so2 <- mapObjProp cSig o (OVar b) (OVar a)
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
                          so1 <- mapObjProp cSig o (OVar a) (OVar b)
                          so2 <- mapObjProp cSig o (OVar b) (OVar c)
                          so3 <- mapObjProp cSig o (OVar a) (OVar c)
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
              SubDataPropertyOf subDP superDP ->
                  do
                    l <- mapDataProp cSig subDP (OVar a) (OVar b)
                    r <- mapDataProp cSig superDP  (OVar a) (OVar b)
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
                    pairs <- mapComDataPropsList cSig dlst (OVar a) (OVar b)
                    let sntLst = case disOrEq of
                                   Equivalent ->
                                       map (\(x,y) ->
                                                Bool_sent (Biconditional x y) nullRange) pairs
                                   Disjoint   ->
                                       map (\(x,y) ->
                                                (Bool_sent (Negation
                                                 (Bool_sent (Conjunction [x,y]) nullRange)
                                                ) nullRange )
                                           ) pairs
                        snt = if (length sntLst == 1) then
                                 head sntLst
                               else
                                 Bool_sent (Conjunction sntLst) nullRange
                    return (Just $ Quant_sent (Universal
                              [ Name (mkNName a)
                              
                              
                              , Name (mkNName b)]
                               snt)
                               nullRange, cSig)
              DataPropertyDomainOrRange domRn dpex ->
                        do
                          oEx <- mapDataProp cSig dpex (OVar a) (OVar b)
                          case domRn of
                            DataDomain mdom ->
                                do
                                  (odes, dSig) <- mapDescription cSig mdom (OVar a) a
                                  let vars = (mkNName a, mkNName b)
                                  return (Just $ Quant_sent (Universal
                                         [Name (fst vars)]
                                         (Quant_sent (Existential
                                         [Name (snd vars)]
                                         (Bool_sent (Implication oEx odes) nullRange))
                                         nullRange)) nullRange, dSig)
                            DataRange  rn  ->
                                do
                                  (odes, dSig) <- mapDataRange cSig rn (OVar b)
                                  let vars = (mkNName a, mkNName b)
                                  return (Just $ Quant_sent (Universal
                                         [Name (fst vars)]
                                         (Quant_sent (Existential
                                         [Name (snd vars)]
                                         (Bool_sent (Implication oEx odes) nullRange))
                                         nullRange)) nullRange, dSig)
              FunctionalDataProperty o ->       
                        do
                          so1 <- mapDataProp cSig o (OVar a) (OVar b)
                          so2 <- mapDataProp cSig o (OVar a) (OVar c)
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
                        sntLst = (map (\ (x, y) -> case sameOrDiff of
                                   Same -> Atom_sent (Equation x y) nullRange
                                   Different -> Bool_sent (Negation
                                     (Atom_sent (Equation x y) nullRange)) nullRange
                                 ) inDL)
                    if (length sntLst == 1) then
                       return (Just $ head sntLst, cSig)
                      else
                        return (Just $ (Bool_sent (Conjunction sntLst
                             ) nullRange), cSig)
              ClassAssertion indi cls ->
                  do
                    inD  <- mapIndivURI cSig indi
                    (ocls, dSig) <- mapDescription cSig cls (OIndi indi) a
                    case cls of
                         OWLClassDescription _ ->
                                return (Just $ ocls, dSig)
                         _ ->
                            return (Just $  Quant_sent (Universal
                              [Name (mkNName a)]
                              (
                              Bool_sent (
                               Implication
                               (Atom_sent (
                                Equation
                                  (Name_term (mkNName a))
                                   inD
                               ) nullRange)
                                ocls
                                ) nullRange )) nullRange , dSig)
              ObjectPropertyAssertion ass ->
                 case ass of
                    Assertion objProp posNeg sInd tInd ->
                      do
                        oPropH <- mapObjProp cSig objProp (OIndi sInd) (OIndi tInd)
                        let oProp = case posNeg of
                                      Positive -> oPropH
                                      Negative -> Bool_sent (Negation
                                                    oPropH)
                                                    nullRange
                        return (Just oProp, cSig)
              DataPropertyAssertion ass ->
                  case ass of
                    Assertion dPropExp posNeg sourceInd targetInd ->
                        do
                          inS <- mapIndivURI cSig sourceInd
                          inT <- mapConstant cSig targetInd
                          nm <- uriToTokM dPropExp
                          let dPropH = Atom_sent
                                            (
                                              Atom
                                              (Name_term nm)
                                              [ Term_seq inS, Term_seq inT]
                                            )
                                        nullRange
                              dProp = case posNeg of
                                        Positive -> dPropH
                                        Negative -> Bool_sent (Negation
                                                    dPropH) nullRange
                          return (Just $  dProp, cSig)
              Declaration _ -> return (Nothing, cSig)
        EntityAnno _  -> return (Nothing, cSig)




{- | Mapping along ObjectPropsList for creation of pairs for commutative
operations. -}
mapComObjectPropsList :: Sign                    -- ^ Signature
                      -> [ObjectPropertyExpression]
                      -> VarOrIndi                        -- ^ First variable
                      -> VarOrIndi                         -- ^ Last  variable
                      -> Result [(SENTENCE,SENTENCE)]
mapComObjectPropsList cSig props num1 num2 =
  mapM (\ (x, z) -> do
        l <- mapObjProp cSig x num1 num2
        r <- mapObjProp cSig z num1 num2
        return (l, r)
        ) $ comPairs props props

-- | Extracts Id from Entities
entityToId :: Entity -> Id
entityToId e = 
  case e of 
       Entity _ urI -> uriToId urI

-- | mapping of data constants
mapConstant :: Sign
            -> Constant
            -> Result TERM
mapConstant _ c =
  do
    let cl = case c of
              Constant l _ -> l
    return $ Name_term (mkSimpleId cl)

-- | Mapping of a list of data constants only for mapDataRange
mapConstantList :: Sign
                -> [Constant]
                -> Result [TERM]
mapConstantList sig cl =
  mapM (\ x -> do
                 t <- mapConstant sig x
                 return $ t ) cl


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
                 l <- mapObjProp cSig oPL (OVar num1) (OVar num2)
                 r <- mapObjProp cSig oP (OVar num1) (OVar num2)
                 return $ Quant_sent (Universal
                    [ Name (mkNName num1)
                    , Name (mkNName num2)]
                    (
                     Bool_sent
                     (
                      Implication
                      l
                      r
                     )
                     nullRange
                    )
                    )
                    nullRange
             SubObjectPropertyChain props ->
               do
                 let zprops = zip (tail props) [(num2 + 1) ..]
                     (_, vars) = unzip zprops
                 oProps  <- mapM (\ (z, x, y) -> mapObjProp cSig z (OVar x) (OVar y)) $
                                  zip3 props ((num1 : vars) ++ [num2]) $
                                       tail ((num1 : vars) ++ [num2])
                 ooP     <- mapObjProp cSig oP (OVar num1) (OVar num2)
                 let lst = [ Name (mkNName num1)
                           , Name (mkNName num2)]
                           ++ (map (\x -> Name (mkNName x)) vars)
                 return $ Quant_sent (Universal
                           lst
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

{- | Mapping along DataPropsList for creation of pairs for commutative
operations. -}
mapComDataPropsList :: Sign
                      -> [DataPropertyExpression]
                      -> VarOrIndi                   -- ^ First variable
                      -> VarOrIndi                   -- ^ Last  variable
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
            -> VarOrIndi
            -> VarOrIndi
            -> Result SENTENCE
mapDataProp _ dP nO nD =
  do
    let
        l = Name_term (voiToTok nO)
        r = Name_term (voiToTok nD)
    ur <- uriToTokM dP
    return $ Atom_sent
             (
              Atom
              (
               Name_term ur
              )
              [Term_seq l, Term_seq r]
             )
             nullRange

mapDataPropI :: Sign
             -> VarOrIndi
             -> VarOrIndi
             -> DataPropertyExpression
             -> Result SENTENCE
mapDataPropI cSig nO nD dP =
        mapDataProp cSig dP nO nD

-- | Mapping of obj props
mapObjProp :: Sign
              -> ObjectPropertyExpression
              -> VarOrIndi
              -> VarOrIndi
              -> Result SENTENCE
mapObjProp cSig ob var1 var2 =
  case ob of
         OpURI u ->
            do
              let l = Name_term (voiToTok var1)
                  r = Name_term (voiToTok var2)
              ur <- uriToTokM u
              return $ Atom_sent
                        (
                        Atom
                          (
                            Name_term ur
                          )
                          [Term_seq l, Term_seq r]
                        )
                        nullRange
         InverseOp u ->
            mapObjProp cSig u var2 var1

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
               [Term_seq (Name_term uid)]
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
    return $ Name_term ur

voiToTok :: VarOrIndi -> Token
voiToTok v = case v of
        OVar o -> mkNName o
        OIndi o -> uriToTok o

uriToTokM :: URI -> Result Token
uriToTokM = return . uriToTok

-- | Extracts Token from URI
uriToTok :: URI -> Token
uriToTok urI = mkSimpleId $ showQN urI

-- | Extracts Id from URI
uriToId :: URI -> Id
uriToId = simpleIdToId . uriToTok

-- | Mapping of a list of descriptions
mapDescriptionList :: Sign
                      -> Int
                      -> [Description]
                      -> Result ([SENTENCE], Sign)
mapDescriptionList cSig n lst = -- (zip lst $ replicate (length lst) n)
  do
    (sens, lSig) <- liftM unzip $ mapM ((\w x y z ->
                            mapDescription w z x y) cSig (OVar n) n) lst
    sig <- sigUnionL lSig
    return (sens, sig)

-- | Mapping of a list of pairs of descriptions
mapDescriptionListP :: Sign
                    -> Int
                    -> [(Description, Description)]
                    -> Result ([(SENTENCE, SENTENCE)], Sign)
mapDescriptionListP cSig n lst =
    do
      let (l, r) = unzip lst
      (llst, sSig)  <- mapDescriptionList cSig n l
      (rlst, tSig) <- mapDescriptionList cSig n r
      let olst = zip llst rlst
      return (olst, unite sSig tSig)

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
             -> VarOrIndi                      -- ^ Current Variablename
             -> Result (SENTENCE, Sign)       -- ^ CommonLogic SENTENCE, Signature
mapDataRange cSig rn inId =
  do
    let uid = Name_term (voiToTok inId)
    case rn of
         DRDatatype uril ->
          do
            return  ((Atom_sent
                          (Atom
                            (Name_term (uriToTok uril))
                            [ Term_seq uid ]
                          ) nullRange) , cSig )
         DataComplementOf dr ->
          do
            (dc, sig) <- mapDataRange cSig dr inId
            return (( Bool_sent (Negation dc) nullRange), sig)
         DataOneOf cs ->
          do
            cl <- mapConstantList cSig cs
            dl <- mapM (\x -> return $
                    Atom_sent (Atom x [Term_seq uid]) nullRange) cl
            return ((Bool_sent
                          (Disjunction
                            dl
                          ) nullRange) , cSig)
         DatatypeRestriction dr rl ->
          do
            (sent, rSig) <- mapDataRange cSig dr inId
            (sens, sigL) <- liftM unzip $ mapM (mapFacet cSig uid) rl
            return $ ((Bool_sent (
                      Conjunction (sent : sens)
                      ) nullRange), (uniteL (rSig : sigL)))

-- | mapping of a tuple of DatatypeFacet and RestictionValue
mapFacet :: Sign
             -> TERM
             -> (DatatypeFacet, RestrictionValue)
             -> Result (SENTENCE, Sign)
mapFacet sig var (f,r) =
    do
      con <- mapConstant sig r
      return $ ((Atom_sent
                (Atom
                  (Name_term (mkSimpleId (showFacet f)))
                  [ Term_seq con
                  , Term_seq var ]
                ) nullRange) , unite sig (emptySig
                   {items = Set.fromList [(stringToId (showFacet f))]} ))


-- | mapping of OWL Descriptions
mapDescription :: Sign
               -> Description              -- ^ OWL Description
               -> VarOrIndi                -- ^ Current Variablename
               -> Int                      -- ^ Alternative to current
               -> Result (SENTENCE, Sign)  -- ^ CommonLogic_DL Formula
mapDescription cSig des oVar aVar =
  let varN = case oVar of
        OVar v -> mkNName v
        OIndi i -> uriToTok i
      var = case oVar of
        OVar v  -> v
        OIndi _ -> aVar
  in case des of
         OWLClassDescription cl ->
           do
            rslt <- mapClassURI cSig cl varN
            return (rslt, cSig)
         ObjectJunction jt desL ->
           do
             (desO, dSig) <- liftM unzip $ mapM ((\w x y z ->
                            mapDescription w z x y) cSig oVar aVar) desL
             return $ case jt of
                UnionOf -> ((Bool_sent (Disjunction desO) nullRange), (uniteL dSig))
                IntersectionOf -> ((Bool_sent (Conjunction desO) nullRange), (uniteL dSig))
         ObjectComplementOf descr ->
           do
             (desO, dSig) <- mapDescription cSig descr oVar  aVar
             return $ ((Bool_sent (Negation desO) nullRange), dSig)
         ObjectOneOf indS ->
           do
             indO <- mapM (mapIndivURI cSig) indS
             let forms = map ((\x y -> Atom_sent (Equation x y)
                            nullRange) (Name_term varN)) indO
             return $ ((Bool_sent (Disjunction forms) nullRange), cSig)
         ObjectValuesFrom qt oprop descr ->
           do
             opropO <- mapObjProp cSig oprop (OVar var) (OVar (var + 1))
             (descO, dSig) <- mapDescription cSig descr (OVar (var + 1))  (aVar + 1)
             case qt of
               SomeValuesFrom ->
                    return $ ((Quant_sent (Existential [Name (mkNName
                                        (var + 1))]
                        (
                         Bool_sent (Conjunction
                         [opropO, descO])
                         nullRange
                        ))
                 nullRange), dSig)
               AllValuesFrom ->
                   return $ ((Quant_sent (Universal [Name (mkNName
                                        (var + 1))]
                        (
                         Bool_sent (Implication
                         opropO descO)
                         nullRange
                        ))
                        nullRange), dSig)
         ObjectExistsSelf oprop ->
            do
              rslt <- mapObjProp cSig oprop oVar oVar
              return (rslt, cSig)
         ObjectHasValue oprop indiv ->
            do
             rslt <- mapObjProp cSig oprop oVar (OIndi indiv)
             return (rslt, cSig)
         ObjectCardinality c ->
          case c of
               Cardinality ct n oprop d
                        ->
                          do
                            let vlst = [(var+1) .. (n+var)]
                                vLst = map (\ x -> OVar x) vlst
                                vlstM = [(var+1) .. (n+var+1)]
                                vLstM = map (\ x -> OVar x) vlstM
                            (dOut, sigL) <- (\x -> case x of
                                  Nothing -> return ([], [])
                                  Just y ->
                                    liftM unzip $ mapM (uncurry (mapDescription cSig y))
                                        (zip vLst vlst)
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
                            oProps <- mapM (mapObjProp cSig oprop (OVar var)) vLst
                            oPropsM <- mapM (mapObjProp cSig oprop (OVar var)) vLstM
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
                               MinCardinality -> return ((minLst), cSig)
                               MaxCardinality -> return ((maxLst), cSig)
                               ExactCardinality -> return $
                                           ((Bool_sent (Conjunction
                                           [minLst, maxLst])
                                           nullRange), uniteL sigL)
         DataValuesFrom qt dpe dpel dr ->
            do
              let varNN = mkNName (var + 1)
              (drSent, drSig) <- mapDataRange cSig dr (OVar var)
              senl <- mapM (mapDataPropI cSig (OVar var) (OVar (var+1))) (dpe : dpel)
              let sent = Bool_sent ( Conjunction (drSent : senl)) nullRange
              case qt of
                   AllValuesFrom ->
                    return $ (Quant_sent (Universal [Name varNN] 
                          sent ) nullRange, drSig)
                   SomeValuesFrom ->
                    return $ (Quant_sent (Existential [Name varNN] 
                          sent ) nullRange, drSig)
         DataHasValue dpe c       ->
           do
             let dpet = Name_term $ uriToTok dpe
             con <- mapConstant cSig c
             return $ ((Quant_sent (Universal [Name varN] (
                  Atom_sent (
                    Atom
                      dpet
                      [ (Term_seq (Name_term (varN)))
                      , (Term_seq con)]
                  ) nullRange)
                  ) nullRange), cSig)
         DataCardinality c ->
             case c of
                  Cardinality ct n dpe dr
                    ->
                      do
                        let vlst  = [(var+1) .. (n+var)]
                            vLst = map (\ x -> OVar x) vlst
                            vlstM = [(var+1) .. (n+var+1)]
                            vLstM = map (\ x -> OVar x) vlstM
                        (dOut, sigL) <- (\x -> case x of
                              Nothing -> return ([], [])
                              Just y ->
                                liftM unzip $ mapM (mapDataRange cSig y) vLst
                             ) dr
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
                        dProps <- mapM (mapDataProp cSig dpe (OVar var)) vLst
                        dPropsM <- mapM (mapDataProp cSig dpe (OVar var)) vLstM
                        let minLst = Quant_sent (Existential
                              qVars
                              (
                                Bool_sent (Conjunction
                                (dlst ++ dOut ++ dProps))
                                nullRange
                              ))
                              nullRange
                        let maxLst = Quant_sent (Universal
                              qVarsM
                              (
                                Bool_sent (Implication
                                (Bool_sent (Conjunction (dPropsM ++ dOut)) nullRange)
                                (Bool_sent (Disjunction dlstM) nullRange))
                                nullRange
                              ))
                              nullRange
                        case ct of
                            MinCardinality -> return ((minLst), cSig)
                            MaxCardinality -> return ((maxLst), cSig)
                            ExactCardinality -> return $
                                        ((Bool_sent (Conjunction
                                        [minLst, maxLst])
                                        nullRange), uniteL sigL)

