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
import OWL.Sign as OS

--CASL_DL = codomain
import CASL.Logic_CASL
import CASL.AS_Basic_CASL
import CASL.Sign
import CASL.Morphism
import CASL.Sublogic
import CASL_DL.PredefinedSign -- Prefedined Symbols

import Common.ProofTree

data OWL2CASL = OWL2CASL deriving Show

instance Language OWL2CASL

instance Comorphism
    OWL2CASL        -- comorphism
    OWL             -- lid domain
    ()              -- sublogics domain
    OntologyFile    -- Basic spec domain
    Sentence        -- sentence domain
    ()              -- symbol items domain
    ()              -- symbol map items domain
    OS.Sign         -- signature domain
    OWL_Morphism  -- morphism domain
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
        { cons_features = emptyMapConsFeature
        , has_empty_sorts = True }
      map_theory OWL2CASL     = error "map_theory OWL2CASL"
      map_morphism OWL2CASL   = error "map_morphism OWL2CASL"

-- Primary concepts stay in OWL, but non-primary concepts cannot be
-- superconcepts of primary ones

thing :: SORT
thing = topSort

hetsPrefix :: String
hetsPrefix = "hetsowl"

-- | mapping of OWL to CASL_DL formulae
mapSentence :: Named Sentence              -- ^ OWL Sentence
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
        OWLAxiom ax   ->
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
        OWLFact  fact ->
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
mapAxiom :: Axiom                -- ^ OWL Axiom
         -> Result CASLFORMULA     -- ^ CASL_DL Formula
mapAxiom ax =
    let
        a = mkSimpleId (hetsPrefix ++ "1")
        b = mkSimpleId (hetsPrefix ++ "2")
        c = 3
    in
      case ax of
        PlainAxiom _ pAx ->
            case pAx of
              SubClassOf sub super ->
                  do
                    domT <- mapDescription sub   c
                    codT <- mapDescription super c
                    return $ Quantification Universal [Var_decl [a]
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
                    return $ Quantification Universal [Var_decl [a]
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
                    mcls <- mapClassURI cls a
                    return $ Quantification Universal [Var_decl [a]
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
        EntityAnno  eAn  -> fail "Mapping of Entity Axioms not implemented!"


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
mapClassURI uri uid =
    do
      ur <- uriToId uri
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
        return $ stringToId $ nU ++ "_" ++ nP ++ "_" ++ "lP" ++ "_"

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

-- | mapping of OWL Descriptions
mapDescription :: Description              -- ^ OWL Description
               -> Int                      -- ^ Current Variablename
               -> Result CASLFORMULA         -- ^ CASL_DL Formula
mapDescription _ = fail "mapDescription nyi"

-- | Build a name
mk_Name :: Int -> Token
mk_Name i = mkSimpleId $ hetsPrefix ++ show i

-- | Getting a fresh Topen Name
next_name :: Int -> Token
next_name tk =
    let
        nextS = show (tk + 1)
    in
      mkSimpleId $ hetsPrefix ++ nextS

comPairs :: [t] -> [t1] -> [(t, t1)]
comPairs [] []     = []
comPairs as []     = []
comPairs [] bs     = []
comPairs (a:as) (b:bs) = zip (replicate (length bs) a) bs ++ comPairs as bs
