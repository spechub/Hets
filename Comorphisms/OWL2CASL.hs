{- |
Module      :  $Header$
Description :  Comorphism from OWL 1.1 to CASL_Dl
Copyright   :  (c) Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (via Logic.Logic)

a not yet implemented comorphism
-}

module Comorphisms.OWL2CASL
    (OWL2CASL(..)
    , mapSentence
    )
    where

import Logic.Logic
import Logic.Comorphism
import Common.AS_Annotation
import Common.Result
import Common.Id
import Control.Monad
import Data.Char

--OWL = domain
import OWL.Logic_OWL
import OWL.AS
import qualified OWL.Sign as OS

--CASL_DL = codomain
import CASL.Logic_CASL
import CASL.AS_Basic_CASL
import CASL.Sign
import CASL.Morphism
import CASL.Sublogic

import Common.ProofTree

data OWL2CASL = OWL2CASL deriving Show

instance Language OWL2CASL

instance Comorphism
    OWL2CASL        -- comorphism
    OWL             -- lid domain
    ()              -- sublogics domain
    OntologyFile    -- Basic spec domain
    OS.Sentence     -- sentence domain
    ()              -- symbol items domain
    ()              -- symbol map items domain
    OS.Sign         -- signature domain
    OWL_Morphism    -- morphism domain
    ()              -- symbol domain
    ()              -- rawsymbol domain
    ProofTree       -- proof tree codomain
    CASL            -- lid codomain
    CASL_Sublogics  -- sublogics codomain
    CASLBasicSpec   -- Basic spec codomain
    CASLFORMULA     -- sentence codomain
    SYMB_ITEMS      -- symbol items codomain
    SYMB_MAP_ITEMS  -- symbol map items codomain
    CASLSign        -- signature codomain
    CASLMor         -- morphism codomain
    Symbol          -- symbol codomain
    RawSymbol       -- rawsymbol codomain
    ProofTree       -- proof tree domain
    where
      sourceLogic OWL2CASL    = OWL
      sourceSublogic OWL2CASL = ()
      targetLogic OWL2CASL    = CASL
      mapSublogic OWL2CASL _  = Just $ cFol
        { cons_features = emptyMapConsFeature }
      map_theory OWL2CASL     = mapTheory
      map_morphism OWL2CASL   = fail "map_morphism OWL2CASL"

-- Primary concepts stay in OWL, but non-primary concepts cannot be
-- superconcepts of primary ones

-- | OWL topsort Thing
thing :: SORT
thing = stringToId "Thing"

-- | OWL Data topSort DATA
dataS :: SORT
dataS = stringToId "DATA"

hetsPrefix :: String
hetsPrefix = "hetsowl"

mapTheory :: (OS.Sign, [Named OS.Sentence])
             -> Result (CASLSign, [Named CASLFORMULA])
mapTheory (owlSig, owlSens) =
    do
      cSens <- mapM mapSentence owlSens
      let cSig = emptySign ()
      return $ (cSig, cSens)

-- | mapping of OWL to CASL_DL formulae
mapSentence :: Named OS.Sentence             -- ^ OWL Sentence
            -> Result (Named CASLFORMULA)    -- ^ CASL_DL Sentence
mapSentence inSen =
    let
        sName = senAttr    inSen
        sDef  = isDef      inSen
        wTh   = wasTheorem inSen
        sen   = sentence   inSen
        sAnno = simpAnno   inSen
    in
      case sen of
        OS.OWLAxiom ax   ->
            do
              outAx <- mapAxiom ax
              return $ SenAttr
                         {
                           senAttr    = sName
                         , isAxiom    = False
                         , isDef      = sDef
                         , wasTheorem = wTh
                         , sentence   = outAx
                         , simpAnno   = sAnno
                         }
        OS.OWLFact  fact ->
            do
              outFact <- mapAxiom fact
              return $ SenAttr
                         {
                           senAttr    = sName
                         , isAxiom    = True
                         , isDef      = sDef
                         , wasTheorem = wTh
                         , sentence   = outFact
                         , simpAnno   = sAnno
                         }

-- | Mapping of Axioms
mapAxiom :: Axiom                  -- ^ OWL Axiom
         -> Result CASLFORMULA     -- ^ CASL_DL Formula
mapAxiom ax =
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
                    domT <- mapDescription sub   c
                    codT <- mapDescription super c
                    return $ Quantification Universal [Var_decl [mk_Name a]
                                                       thing nullRange]
                               (Implication
                                domT
                                codT
                                True
                                nullRange) nullRange
              EquivOrDisjointClasses eD dS ->
                  do
                    decrsS <- mapDescriptionListP c $ comPairs dS dS
                    let decrsP = map (\(x,y) -> Conjunction [x,y] nullRange) decrsS
                    return $ Quantification Universal [Var_decl [mk_Name a]
                                                       thing nullRange]
                               (
                                case eD of
                                  Equivalent -> Conjunction decrsP nullRange
                                  Disjoint   ->
                                      Negation
                                      (
                                       Conjunction decrsP nullRange
                                      ) nullRange
                               ) nullRange
              DisjointUnion cls sD ->
                  do
                    decrs  <- mapDescriptionList c sD
                    decrsS <- mapDescriptionListP c $ comPairs sD sD
                    let decrsP = map (\(x,y) -> Conjunction [x,y] nullRange) decrsS
                    mcls <- mapClassURI cls (mk_Name a)
                    return $ Quantification Universal [Var_decl [mk_Name a]
                                             thing nullRange]
                               (
                                Equivalence
                                (                      -- The class
                                  mcls
                                )
                                (                      -- The rest
                                  Conjunction
                                  [
                                   Disjunction decrs nullRange
                                  ,Negation
                                   (
                                    Conjunction decrsP nullRange
                                   )
                                   nullRange
                                  ]
                                  nullRange
                                )
                                nullRange
                               ) nullRange
              SubObjectPropertyOf ch op -> mapSubObjProp ch op c
              EquivOrDisjointObjectProperties disOrEq oExLst ->
                  do
                    pairs <- mapComObjectPropsList oExLst a b
                    return $ Quantification Universal [Var_decl [mk_Name a]
                                                       thing nullRange,
                                                       Var_decl [mk_Name b]
                                                       thing nullRange]
                               (
                                Conjunction
                                (
                                 case disOrEq of
                                   Equivalent ->
                                       map (\(x,y) ->
                                                Equivalence x y nullRange) pairs
                                   Disjoint   ->
                                       map (\(x,y) ->
                                                (Negation
                                                 (Conjunction [x,y] nullRange)
                                                 nullRange
                                                )
                                           ) pairs
                                )
                                nullRange
                               )
                               nullRange
              ObjectPropertyDomainOrRange domOrRn objP descr ->
                        do
                          tobjP <- mapObjProp objP a b
                          tdsc  <- mapDescription descr $
                                   case domOrRn of
                                     ObjDomain -> a
                                     ObjRange  -> b
                          let vars = case domOrRn of
                                       ObjDomain -> (mk_Name a, mk_Name b)
                                       ObjRange  -> (mk_Name b, mk_Name a)
                          return $ Quantification Universal
                                     [Var_decl [fst vars] thing nullRange]
                                     (
                                      Quantification Existential
                                         [Var_decl [snd vars] thing nullRange]
                                         (
                                          Implication
                                          (
                                           tobjP
                                          )
                                          (
                                           tdsc
                                          )
                                          True
                                          nullRange
                                         )
                                      nullRange
                                     )
                                     nullRange
              InverseObjectProperties o1 o2 ->
                  do
                    so1 <- mapObjProp o1 a b
                    so2 <- mapObjProp o2 b a
                    return $ Quantification Universal
                             [Var_decl [mk_Name a] thing nullRange
                             ,Var_decl [mk_Name b] thing nullRange]
                             (
                              Equivalence
                              so1
                              so2
                              nullRange
                             )
                             nullRange
              ObjectPropertyCharacter cha o ->
                  case cha of
                    Functional ->
                        do
                          so1 <- mapObjProp o a b
                          so2 <- mapObjProp o a c
                          return $ Quantification Universal
                                     [Var_decl [mk_Name a] thing nullRange
                                     ,Var_decl [mk_Name b] thing nullRange
                                     ,Var_decl [mk_Name c] thing nullRange
                                     ]
                                     (
                                      Implication
                                      (
                                       Conjunction [so1, so2] nullRange
                                      )
                                      (
                                       Strong_equation
                                       (
                                        Qual_var (mk_Name b) thing nullRange
                                       )
                                       (
                                        Qual_var (mk_Name c) thing nullRange
                                       )
                                       nullRange
                                      )
                                      True
                                      nullRange
                                     )
                                     nullRange
                    InverseFunctional ->
                        do
                          so1 <- mapObjProp o a c
                          so2 <- mapObjProp o b c
                          return $ Quantification Universal
                                     [Var_decl [mk_Name a] thing nullRange
                                     ,Var_decl [mk_Name b] thing nullRange
                                     ,Var_decl [mk_Name c] thing nullRange
                                     ]
                                     (
                                      Implication
                                      (
                                       Conjunction [so1, so2] nullRange
                                      )
                                      (
                                       Strong_equation
                                       (
                                        Qual_var (mk_Name a) thing nullRange
                                       )
                                       (
                                        Qual_var (mk_Name b) thing nullRange
                                       )
                                       nullRange
                                      )
                                      True
                                      nullRange
                                     )
                                     nullRange
                    Reflexive  ->
                        do
                          so <- mapObjProp o a a
                          return $
                                 Quantification Universal
                                   [Var_decl [mk_Name a] thing nullRange]
                                   (
                                    Implication
                                     (
                                      Membership
                                      (Qual_var (mk_Name a) thing nullRange)
                                      thing
                                      nullRange
                                     )
                                     so
                                     True
                                     nullRange
                                   )
                                   nullRange
                    Irreflexive ->
                        do
                          so <- mapObjProp o a a
                          return $
                                 Quantification Universal
                                   [Var_decl [mk_Name a] thing nullRange]
                                   (
                                    Implication
                                    (
                                     Membership
                                     (Qual_var (mk_Name a) thing nullRange)
                                     thing
                                     nullRange
                                    )
                                    (
                                     Negation
                                     so
                                    nullRange
                                    )
                                    True
                                    nullRange
                                   )
                                   nullRange
                    Symmetric ->
                        do
                          so1 <- mapObjProp o a b
                          so2 <- mapObjProp o b a
                          return $
                           Quantification Universal
                               [Var_decl [mk_Name a] thing nullRange
                               ,Var_decl [mk_Name b] thing nullRange]
                               (
                                Implication
                                so1
                                so2
                                True
                                nullRange
                               )
                               nullRange
                    Asymmetric ->
                        do
                          so1 <- mapObjProp o a b
                          so2 <- mapObjProp o b a
                          return $
                           Quantification Universal
                               [Var_decl [mk_Name a] thing nullRange
                               ,Var_decl [mk_Name b] thing nullRange]
                               (
                                Implication
                                so1
                                (Negation so2 nullRange)
                                True
                                nullRange
                               )
                               nullRange
                    Antisymmetric ->
                        do
                          so1 <- mapObjProp o a b
                          so2 <- mapObjProp o b a
                          return $
                           Quantification Universal
                               [Var_decl [mk_Name a] thing nullRange
                               ,Var_decl [mk_Name b] thing nullRange]
                               (
                                Implication
                                 (Conjunction [so1, so2] nullRange)
                                 (
                                  Strong_equation
                                  (
                                   Qual_var (mk_Name a) thing nullRange
                                  )
                                  (
                                   Qual_var (mk_Name b) thing nullRange
                                  )
                                  nullRange
                                 )
                                True
                                nullRange
                               )
                               nullRange
                    Transitive ->
                        do
                          so1 <- mapObjProp o a b
                          so2 <- mapObjProp o b c
                          so3 <- mapObjProp o a c
                          return $
                           Quantification Universal
                               [Var_decl [mk_Name a] thing nullRange
                               ,Var_decl [mk_Name b] thing nullRange
                               ,Var_decl [mk_Name c] thing nullRange]
                               (
                                Implication
                                (
                                 Conjunction [so1, so2] nullRange
                                )
                                (
                                 so3
                                )
                                True
                                nullRange
                               )
                               nullRange
              SubDataPropertyOf dP1 dP2 ->
                  do
                    l <- mapDataProp dP1 a b
                    r <- mapDataProp dP2  a b
                    return $ Quantification Universal
                               [Var_decl [mk_Name a] thing nullRange, Var_decl [mk_Name b] dataS nullRange]
                               (
                                Implication
                                l
                                r
                                True
                                nullRange
                               )
                               nullRange
              EquivOrDisjointDataProperties disOrEq dlst ->
                  do
                    pairs <- mapComDataPropsList dlst a b
                    return $ Quantification Universal [Var_decl [mk_Name a]
                                                       thing nullRange,
                                                       Var_decl [mk_Name b]
                                                       dataS nullRange]
                               (
                                Conjunction
                                (
                                 case disOrEq of
                                   Equivalent ->
                                       map (\(x,y) ->
                                                Equivalence x y nullRange) pairs
                                   Disjoint   ->
                                       map (\(x,y) ->
                                                (Negation
                                                 (Conjunction [x,y] nullRange)
                                                 nullRange
                                                )
                                           ) pairs
                                )
                                nullRange
                               )
                               nullRange
              DataPropertyDomainOrRange _ _ ->
                  fail "case alternative not implemented"
              FunctionalDataProperty _ ->
                  fail "case alternative not implemented"
              SameOrDifferentIndividual _ _ ->
                  fail "case alternative not implemented"
              ClassAssertion _ _ ->
                  fail "case alternative not implemented"
              ObjectPropertyAssertion _ ->
                  fail "case alternative not implemented"
              DataPropertyAssertion _ ->
                  fail "case alternative not implemented"
              Declaration _ ->
                  fail "case alternative not implemented"
        EntityAnno _  -> fail "Mapping of Entity Axioms not implemented!"

-- | Mapping along ObjectPropsList for creation of pairs for commutative operations
mapComObjectPropsList :: [ObjectPropertyExpression]
                      -> Int                         -- ^ First variable
                      -> Int                         -- ^ Last  variable
                      -> Result [(CASLFORMULA,CASLFORMULA)]
mapComObjectPropsList props num1 num2 =
    do
      oProps   <- mapM (\(x,z) ->
                            do
                              l <- mapObjProp x num1 num2
                              r <- mapObjProp z num1 num2
                              return (l,r)
                       ) $
                  comPairs props props
      return $ oProps

-- | Mapping of subobj properties
mapSubObjProp :: SubObjectPropertyExpression
              -> ObjectPropertyExpression
              -> Int
              -> Result CASLFORMULA
mapSubObjProp prop oP num1 =
    let
        num2 = num1 + 1
    in
      case prop of
        OPExpression oPL ->
            do
              l <- mapObjProp oPL num1 num2
              r <- mapObjProp oP num1 num2
              return $ Quantification Universal
                     [Var_decl [mk_Name num1] thing nullRange, Var_decl [mk_Name num2] thing nullRange]
                     (
                      Implication
                      l
                      r
                      True
                      nullRange
                     )
                     nullRange
        SubObjectPropertyChain props ->
            do
              let zprops   = zip (tail props) [num2 ..]
                  (_,vars) = unzip $ zprops
              oProps   <- mapM (\(z,x,y) -> mapObjProp z x y) $
                                zip3 props ((num1:vars) ++ [num2]) $
                                     tail ((num1:vars) ++ [num2])
              ooP      <- mapObjProp oP num1 num2
              return $ Quantification Universal
                     [Var_decl [mk_Name num1] thing nullRange, Var_decl [mk_Name num2] thing nullRange]
                     (
                      Quantification Existential
                         (
                          map (\x -> Var_decl [mk_Name x] thing nullRange) vars
                         )
                         (
                          Implication
                          (Conjunction oProps nullRange)
                          ooP
                          True
                          nullRange
                         )
                       nullRange
                     )
                    nullRange

-- | Mapping along DataPropsList for creation of pairs for commutative operations
mapComDataPropsList :: [DataPropertyExpression]
                      -> Int                         -- ^ First variable
                      -> Int                         -- ^ Last  variable
                      -> Result [(CASLFORMULA,CASLFORMULA)]
mapComDataPropsList props num1 num2 =
    do
      oProps   <- mapM (\(x,z) ->
                            do
                              l <- mapDataProp x num1 num2
                              r <- mapDataProp z num1 num2
                              return (l,r)
                       ) $
                  comPairs props props
      return $ oProps

-- | Mapping of data properties
mapDataProp :: DataPropertyExpression
            -> Int
            -> Int
            -> Result CASLFORMULA
mapDataProp dP nO nD =
    do
      let
          l = mk_Name nO
          r = mk_Name nD
      ur <- uriToId dP
      return $ Predication
                 (Qual_pred_name ur (Pred_type [thing,dataS] nullRange) nullRange)
                 [Qual_var l thing nullRange, Qual_var r dataS nullRange]
                 nullRange

-- | Mapping of obj props
mapObjProp :: ObjectPropertyExpression
              -> Int
              -> Int
              -> Result CASLFORMULA
mapObjProp ob num1 num2 =
    case ob of
      OpURI u ->
          do
            let l = mk_Name num1
                r = mk_Name num2
            ur <- uriToId u
            return $ Predication
                       (Qual_pred_name ur (Pred_type [thing,thing] nullRange) nullRange)
                       [Qual_var l thing nullRange, Qual_var r thing nullRange]
                       nullRange
      InverseOp u ->
          mapObjProp u num2 num1

-- | Mapping of Class URIs
mapClassURI :: OwlClassURI
            -> Token
            -> Result CASLFORMULA
mapClassURI uril uid =
    do
      ur <- uriToId uril
      return $ Predication
                  (Qual_pred_name (ur) (Pred_type [thing] nullRange) nullRange)
                  [Qual_var uid thing nullRange]
                  nullRange

uriToId :: URI
        -> Result Id
uriToId ur =
    let
        repl a = if (isAlphaNum a)
                  then
                      a
                  else
                      '_'
        nP = map repl $ namePrefix   ur
        lP = map repl $ localPart    ur
        nU = map repl $ namespaceUri ur
    in
      do
        return $ stringToId $ nU ++ "_" ++ nP ++ "_" ++ lP ++ "_"

-- | Mapping of a list of descriptions
mapDescriptionList :: Int
                      -> [Description]
                      -> Result [CASLFORMULA]
mapDescriptionList n lst =
    do
      olst <- mapM (\(x,y) -> mapDescription x y)
                                $ zip lst $ replicate (length lst) n
      return olst

-- | Mapping of a list of pairs of descriptions
mapDescriptionListP :: Int
                    -> [(Description, Description)]
                    -> Result [(CASLFORMULA, CASLFORMULA)]
mapDescriptionListP n lst =
    do
      let (l, r) = unzip lst
      llst  <- mapDescriptionList n l
      rlst  <- mapDescriptionList n r
      let olst = zip llst rlst
      return olst

-- | Build a name
mk_Name :: Int -> Token
mk_Name i = mkSimpleId $ hetsPrefix ++ show i

-- | Get all distinct pairs for commutative operations
comPairs :: [t] -> [t1] -> [(t, t1)]
comPairs [] []     = []
comPairs _  []     = []
comPairs [] _      = []
comPairs (a:as) (_:bs) = zip (replicate (length bs) a) bs ++ comPairs as bs

-- | mapping of OWL Descriptions
mapDescription :: Description              -- ^ OWL Description
               -> Int                      -- ^ Current Variablename
               -> Result CASLFORMULA       -- ^ CASL_DL Formula
mapDescription _ = fail "mapDescription nyi"
