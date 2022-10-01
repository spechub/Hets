{- |
Module      :  $Id$
Description :  Instance of class 'Comorphism' from 'UMLStateO' to 'CASL'
Copyright   :  (c) Tobias Rosenberger, Swansea University and Universit{'e} Grenoble Alpes 2022
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  TRosenberger@gmx.de
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

The entry point for the translation is 'translate'.

For more background information, see "UMLComp.Logic_UMLComp".
-}

{-# LANGUAGE DeriveDataTypeable    #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}

-- Sometimes we want to name unused arguments for context.
{-# OPTIONS_GHC -Wno-unused-matches #-}

-- We want to be able to show g and g'.
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Comorphisms.UMLStateO2CASL where

import           Common.AS_Annotation      (SenAttr, makeNamed)
import           Common.Id
import           Common.Lib.MapSet         as MapSet
import           Common.Lib.Rel            as Rel
import           Common.Lib.State          ()
import           Common.ProofTree

import qualified Data.Data                 as D

import           Data.List                 as List hiding (sort)
import           Data.Map                  as Map
import           Data.Maybe                (fromMaybe)
import           Data.Set                  as Set

import           Logic.Comorphism
import           Logic.Logic

import           UMLComp.Logic_UMLComp     (composeId, composeTok, confSort,
                                            evtSort, msgListSort, msgSort,
                                            portSort, token2Str)
import           UMLStateO.Logic_UMLStateO

import qualified CASL.AS_Basic_CASL        as CA
import qualified CASL.Logic_CASL           as CL
import qualified CASL.Morphism             as CM
import qualified CASL.Sign                 as CS
import qualified CASL.Sublogic             as CSL


type CSub     = CSL.CASL_Sublogics
type CBasic   = CL.CASLBasicSpec
type CForm    = CA.CASLFORMULA
type CSyms    = CA.SYMB_ITEMS
type CSymMaps = CA.SYMB_MAP_ITEMS
type CSign    = CS.CASLSign
type CMor     = CM.CASLMor
type CSym     = CS.Symbol
type CRawSym  = CM.RawSymbol
type CProof   = ProofTree

data UMLStateO2CASL = UMLStateO2CASL deriving Show

instance Language UMLStateO2CASL where -- default is OK

instance Comorphism UMLStateO2CASL
  UMLStateO StSub BASIC_SPEC Sentence StSyms StSymMaps Sign     Morphism StSym StRawSym StProof
  CL.CASL   CSub  CBasic     CForm    CSyms  CSymMaps  CSign    CMor     CSym  CRawSym  CProof
  where
    sourceLogic    UMLStateO2CASL           = UMLStateO
    sourceSublogic UMLStateO2CASL           = ()
    targetLogic    UMLStateO2CASL           = CL.CASL
    mapSublogic    UMLStateO2CASL ()        = Just top
    map_theory     UMLStateO2CASL (sign, _) = return $ translate sign
    map_sentence   UMLStateO2CASL _ _       = return CA.trueForm

    {- | State machine symbols don't map cleanly onto CASL ones,
         although some could be handled.
    -}
    map_symbol     UMLStateO2CASL lib tok   = Set.empty

-- | Core of the implementation of 'map_theory'
translate :: Sign -> ( CS.Sign f ()
                     , [Common.AS_Annotation.SenAttr (CA.FORMULA ()) [Char]]
                     )
translate sign = (csign, csentences) where
  eventsKeyVal = Map.toList (trigS sign `Map.union` actsS sign)
  events       = fst       <$> eventsKeyVal
  msgNames     = fst . fst <$> eventsKeyVal
  portNames    = portName  <$> msgNames

  sorts = [ ctrlSort sign
          , msgSort
          , msgListSort
          , portSort
          , evtSort
          , natSort
          , confSort $ str2Token $ machName sign
          , msgNameSort
          , msgNameSetSort
          ]
  ops   = ( natInfixOp              <$> words "+ - * / @@"        )
       ++ ( natLitOp                <$> [0..9]                    )
       ++ ( stateOp sign            <$> Set.toList (statesS sign) )
       ++ ( attrOp sign . token2Str <$> Set.toList (attrS   sign) )
       ++ ( msgNameConOp            <$> msgNames                  )
       ++ ( portConOp               <$> portNames                 )
       ++ ( uncurry evtConOp        <$> events                    )
       ++ [ msgNameOp                    ]
       ++ [ cSetNilOp, cSetConsOp        ]
       ++ [ msgInstNilOp, msgInstConsOp  ]
       ++ sequence [confOp, ctrlOp] sign
  preds = sequence [reach2Pred, initPred, transPred] sign
       ++ (compOp2CASL <$> [Less,LessEq,GreaterEq,Greater])
            -- Eq not treated as predicate

  csign = (CS.emptySign ())
    { CS.sortRel = transClosure $ Rel.fromMap $ Map.fromList
        [ ( sort, Set.empty)
        | sort <- sorts
        ]
    , CS.predMap = MapSet.fromMap $ Map.fromList
        [ (p, Set.fromList [ CS.PredType args ])
        | CA.Qual_pred_name p (CA.Pred_type args _) _ <- preds
        ]
    , CS.opMap = MapSet.fromMap $ Map.fromListWith Set.union (
        [ (CA.opSymbName o, Set.fromList[opSymbType o])
        | o <- ops
        ]
      )
    , CS.declaredSymbols = Set.fromList (
           [ CS.Symbol sortName CS.SortAsItemType
           | sortName <- sorts
           ]
        ++ [ CS.Symbol predName $ CS.PredAsItemType $ CS.PredType args
           | CA.Qual_pred_name predName (CA.Pred_type args _) _ <- preds
           ]
        ++ [ CS.Symbol opName $ CS.OpAsItemType $ CS.OpType totality args res
           | CA.Qual_op_name opName (CA.Op_type totality args res _) _ <- ops
           ]
      )
    }
  machine = CA.mkForall [CA.mkVarDecl g (confSort $ str2Token $ machName sign)] (
              initP sign (confVar sign g) `CA.mkImpl` edhml2CASL sign confVars (lib2EDHMLO sign)
            )
  csentences  = [ makeNamed "init" $ initCASL sign
                , makeNamed "free_types"
                  $ CA.Sort_gen_ax [ CA.Constraint msgSort
                                                   [ ( msgConOp
                                                     , []
                                                     )
                                                   ]
                                                   msgSort
                                   , CA.Constraint
                                       (confSort $ str2Token $ machName sign)
                                       [(confOp sign, [])]
                                       (confSort $ str2Token $ machName sign)
                                   ]
                                   True
                ]
             ++ [ makeNamed "machine" m
                | m <- sepCASL $ edhml2CASL sign confVars $ lib2EDHMLO sign
                ]
             ++ [ makeNamed "msgEqs"
                    ( univEvtArgs argVars
                        (CA.mkStEq (msgNameOp `CA.mkAppl` [msgItem2CASLterm e])
                                   (msgNameConOp name `CA.mkAppl` [])
                        )
                    )
                | (_, e@(MsgI name argVars)) <- Map.toList $ actsS sign
                ]


g :: VAR_NAME
g = str2Token "g"

confVars :: (VAR_NAME, VAR_NAME)
confVars = (g,prime g)

-- | Analogous to 'CA.opSymbName'. Note, however, that 'opSymbType' is partial!
opSymbType :: CA.OP_SYMB -> CS.OpType
opSymbType (CA.Qual_op_name _ (CA.Op_type totality args res _) _)
  = CS.OpType totality args res
opSymbType (CA.Op_name name)
  = error (   "opSymbType should not have been called on an unqualified operation symbol.\n"
           ++ "offending symbol: " ++ show name ++ "\n"
           ++ "Please report this as a bug."
          )


type MESSAGE_NAMES = CA.TERM ()

-- | The Event Data Hybrid Modal Logic with Outputs.
data EDHMLO = DtSen FORMULA       -- ^ @DtSen phi@: current config satisfies @phi@.
            | St STATE            -- ^ @St s@: current control state is @s@
            | Binding STATE EDHMLO
              -- ^ @Binding s f@: with current control state bound to s, f holds

            | At MESSAGE_NAMES MESSAGE_NAMES STATE EDHMLO
               {- ^ @At  ins outs s f@: jumping to any config with state @s@ reachable
                   via transitions with labels over @ins@ and @outs@, @f@ holds.
               -}

            | Box MESSAGE_NAMES MESSAGE_NAMES       EDHMLO
                {- ^ @Box ins outs   f@:
                     For all transitions with these sets of allow inputs/outputs...
                -}
            | DiaEE MESSAGE_ITEM         [MESSAGE_INSTANCE] FORMULA EDHMLO
            -- ^ Exists valuation and transititon ...

            | DiaAE MESSAGE_ITEM FORMULA [MESSAGE_INSTANCE] FORMULA EDHMLO
            -- ^ For each valuation satisfying phi there exists a transition ...

            | Not EDHMLO
            | And EDHMLO EDHMLO
            | TrueE
            deriving (Eq,Ord,Show,D.Data)

initP :: Sign -> CA.TERM () -> CA.FORMULA ()
initP sign g = CA.mkPredication (initPred sign) [g]

initCASL :: Sign -> CA.FORMULA ()
initCASL sign = CA.mkForall [quant]  equiv
  where
    quant = CA.mkVarDecl gTok $ confSort $ str2Token $ machName sign
    equiv = initP sign gTerm `CA.mkEqv` defForm
    gTok  = str2Token "g"
    gTerm = confVar sign gTok
    vars  = (gTok, prime gTok)
    defForm = disjunctC [        (ctrl sign gTerm `CA.mkStEq` mkState sign s0)
                          `andC` stForm2CASL sign vars phi0
                        | (s0,phi0) <- initS sign
                        ]

{- | Translate a state machine into EDHMLO.
   Uses 'computeEDHMLO' to recurse over all states and transitions.
   The algorithm is based on Algorithm 1 in
   Hennicker et. al.:"A Hybrid Dynamic Logic for Event/Data-Based Systems."
   ( https:\/\/doi.org\/10.1007\/978-3-030-16722-6_5 )
   as extended for output events in Algorithm 1 of
   Rosenberger et. al.:"Institution-based Encoding and Verification of Simple UML State Machines in CASL/SPASS"
   ( https:\/\/doi.org\/10.1007\/978-3-030-73785-6_7 ).
-}
lib2EDHMLO :: Sign -> EDHMLO
lib2EDHMLO sign = assert `seq` edhmlRmNotNot (computeEDHMLO allIns allOuts c0 is vs bs im1 im2 es)
  where
    combinemsgs (ename,_) _ enames = ename `cSetCons` enames
    allIns  = Map.foldrWithKey combinemsgs cSetNil $ trigS sign
    allOuts = Map.foldrWithKey combinemsgs cSetNil $ actsS sign
    (c0, states) = Set.deleteFindMin $ statesS sign
    guard2phi = fromMaybe TrueF

    acts2psi Nothing = TrueF
    acts2psi (Just (Acts as)) = conjunctF [ CompF (VarT $ prime v) Eq t
                                          | Assign v t <- as
                                          ]
    acts2MsgList Nothing = []
    acts2MsgList (Just (Acts as)) = [ msgInstance
                                    | Send msgInstance <- as
                                    ]

    {- Handle completion events: where no explicit message is given,
       create one with the completion event for the current state.
    -}
    handleCompl :: STATE -> Maybe MESSAGE_ITEM -> MESSAGE_ITEM
    handleCompl c = fromMaybe $ complEvt sign c

    -- transitions indexed by start state
    im1 c = Map.findWithDefault id c im1Map []
    im1Map = Map.fromListWith (.) -- for equal keys: compose diff lists
               [ ( c
                 , ([(guard2phi guard, handleCompl c e, acts2MsgList acts, acts2psi acts, c')] ++) -- difference list
                 )
               | TransI c c' (Label e guard acts) <- transS sign
               ]

    -- transitions indexed by start state and label
    im2 ce = Map.findWithDefault id ce im2Map []
    im2Map = Map.fromListWith (.) -- for equal keys : compose diff lists
               [ ( (c, ename, length evars)
                 , ([(guard2phi guard, acts2MsgList acts, acts2psi acts, c')] ++) -- difference list
                 )
               | TransI c c' (Label e guard acts) <- transS sign
               , let MsgI ename evars = handleCompl c e
               ]

    vs = Set.toList states
    bs = c0 : vs
    is = im1 c0
    es = [ (handleCompl c inE, outEs)
         | TransI c _ (Label inE _ as) <- transS sign
         , let outEs = acts2MsgList as
         ] -- Map.elems $ actsS sign
    assert = if Set.null (statesS sign)
             then error "Can't translate sign to EDHMLO: need at least one state"
             else ()

{- | Traverse transitions reachable from a list of control states,
     generating an EDHMLO formula.
     Used by 'lib2EDHMLO' to translate a state machine.by 'lib2EDHMLO'
     to translate a state machine.
-}
computeEDHMLO :: MESSAGE_NAMES  -- ^ all input message names
              -> MESSAGE_NAMES  -- ^ all output message names
              -> STATE          -- ^ a control state @c@
              -> [(FORMULA, MESSAGE_ITEM, [MESSAGE_INSTANCE], FORMULA, STATE)]
                                -- ^ list of transitions out of  @c@
              -> [STATE]        -- ^ states still to be processed
              -> [STATE]        -- ^ all states
              -> ( STATE -> [ ( FORMULA
                              , MESSAGE_ITEM
                              , [MESSAGE_INSTANCE]
                              , FORMULA, STATE
                              )
                            ]
                 )      -- ^ all transitions, indexed by start state
              -> (    (STATE, MESSAGE_NAME, Arity)
                   -> [(FORMULA, [MESSAGE_INSTANCE], FORMULA, STATE)]
                 )      -- ^ all transitions, indexed by start state and message
              -> [ (MESSAGE_ITEM, [MESSAGE_INSTANCE]) ]
                        {- ^ for each transition, the input message
                             (name and formal parameters)
                             and output messages (with full argument terms)
                        -}
              -> EDHMLO
computeEDHMLO allIns allOuts c ((phi,e,outs,psi,c'):is) vs bs im1 im2 es =
         At allIns allOuts c (DiaAE e phi outs psi $ St c')
  `andE` computeEDHMLO allIns allOuts c is vs bs im1 im2 es
computeEDHMLO   allIns allOuts c  []       (c':vs) bs im1 im2 es =
  computeEDHMLO allIns allOuts c' (im1 c')     vs  bs im1 im2 es
computeEDHMLO allIns allOuts c [] [] bs im1 im2 es =
  fin allIns allOuts bs im2 es `andE` pairsDiff allIns allOuts bs

{- | EDHMLO formulae to assert control states
     are semantically distinct iff they are syntactically distinct.
-}
pairsDiff :: MESSAGE_NAMES -> MESSAGE_NAMES -> [Token] -> EDHMLO
pairsDiff allIns allOuts bs = conjunctE [ Not $ At allIns allOuts c1 $ St c2
                                        | c1 <- bs
                                        , c2 <- bs
                                        , c1 /= c2
                                        ]

boxAA :: MESSAGE_ITEM -> [MESSAGE_INSTANCE] -> FORMULA -> EDHMLO -> EDHMLO
boxAA e outs phi f = Not $ DiaEE e outs phi $ Not f

{- | Finishing formula: from each configuration,
   the semantically reachable configurations
   are match those syntactically reachable via enabled transitions.
-}
fin :: MESSAGE_NAMES
    -> MESSAGE_NAMES
    -> [STATE]
    -> ( (STATE, MESSAGE_NAME, Int) -> [(FORMULA, [MESSAGE_INSTANCE], FORMULA, STATE)]
       )
    -> [ (MESSAGE_ITEM, [MESSAGE_INSTANCE]) ]
    -> EDHMLO
fin allIns allOuts bs im2 es = conjunctE
  [ At allIns allOuts c $ conjunctE [ boxAA inE outEs (
                                        (
                                          conjunctF [ phi :/\ psi
                                                    | (phi, outs, psi, c') <- ps
                                                    ]
                                        ) :/\ NotF (
                                          disjunctF  [ phi :/\ psi
                                                     | (phi, outs, psi, c') <- nps
                                                     ]
                                        )
                                      ) $ disjunctE [ St c'
                                                    | (phi, outs, psi, c') <- ps
                                                    ]
                                    | (inE, outEs) <- es
                                    , (ps, nps)    <- complements c inE im2
                                    ]
  | c <- bs
  ]

complements :: STATE
            -> MESSAGE_ITEM
            -> (    (STATE, MESSAGE_NAME, Arity)
                 -> [(FORMULA, [MESSAGE_INSTANCE], FORMULA, STATE)]
               )
            -> [ ( [(FORMULA, [MESSAGE_INSTANCE], FORMULA, STATE)]
                 , [(FORMULA, [MESSAGE_INSTANCE], FORMULA, STATE)]
                 )
               ]
complements c (MsgI ename evars) im2 =
  let xs = Set.fromList $ im2 (c, ename, length evars)
  in [ ( Set.toList ps
       , Set.toList (xs Set.\\ ps)
       )
     | ps <- Set.toList $ powerSet xs
     ]


-- CASL logic helpers
andC :: CA.FORMULA () -> CA.FORMULA () -> CA.FORMULA ()
a `andC` b = CA.conjunct [a, b]

orC :: CA.FORMULA () -> CA.FORMULA () -> CA.FORMULA ()
a `orC` b = CA.disjunct [a, b]

notC :: CA.FORMULA () -> CA.FORMULA ()
notC a = CA.Negation a nullRange

conjunctC :: [CA.FORMULA ()] -> CA.FORMULA ()
conjunctC = CA.conjunct

disjunctC :: [CA.FORMULA ()] -> CA.FORMULA ()
disjunctC  = CA.disjunct

-- state FORMULA logic helpers

conjunctF :: [FORMULA] -> FORMULA
conjunctF []   = TrueF
conjunctF phis = List.foldl1 (:/\) phis

disjunctF :: [FORMULA] -> FORMULA
disjunctF  []   = FalseF
disjunctF  phis = List.foldl1 (:\/) phis

-- EDHMLO logic helpers
andE, orE:: EDHMLO -> EDHMLO -> EDHMLO
phi `andE` psi = phi `And` psi
phi `orE`  psi = Not (Not phi `And` Not psi)

conjunctE :: [EDHMLO] -> EDHMLO
conjunctE [] = TrueE
conjunctE fs = List.foldl1 andE fs

disjunctE :: [EDHMLO] -> EDHMLO
disjunctE [] = Not TrueE
disjunctE fs = List.foldl1 orE fs

edhmlRmNotNot :: EDHMLO -> EDHMLO
edhmlRmNotNot (Not (Not f))            = edhmlRmNotNot f
edhmlRmNotNot (Not f)                  = Not                  $ edhmlRmNotNot f
edhmlRmNotNot (Binding c f)            = Binding c            $ edhmlRmNotNot f
edhmlRmNotNot (At ins outs c f)        = At ins outs c        $ edhmlRmNotNot f
edhmlRmNotNot (Box ins outs f)         = Box ins outs         $ edhmlRmNotNot f
edhmlRmNotNot (DiaEE e outs phi f)     = DiaEE e outs phi     $ edhmlRmNotNot f
edhmlRmNotNot (DiaAE e outs phi psi f) = DiaAE e outs phi psi $ edhmlRmNotNot f
edhmlRmNotNot (f `And` f')             = edhmlRmNotNot f `And` edhmlRmNotNot f'
edhmlRmNotNot f                        = f

edhml2CASL :: Sign -> ConfigVars -> EDHMLO -> CA.FORMULA ()
edhml2CASL sign vars (DtSen f) = stForm2CASL sign vars f
edhml2CASL sign (g,_) (St s) = mkState sign s `CA.mkStEq` ctrl sign (confVar sign g)
edhml2CASL sign vars@(g,_) (Binding s f) = exCtrl sign s (
                                                    mkState sign s `CA.mkStEq` ctrl sign (confVar sign g)
                                             `andC` edhml2CASL sign vars f
                                           )
edhml2CASL sign vars@(g,g') (At ins outs s f) =
  let newVars = (g',prime g')
  in univConf sign g' (
       (
                (ctrl sign (confVar sign g') `CA.mkStEq` mkState sign s)
         `andC` reach2 sign ins outs g'
       ) `CA.mkImpl` edhml2CASL sign newVars f
     )
edhml2CASL sign (g,g') (Box ins outs f) =
  let newVars = (g',prime g')
  in univConf sign g' (
       reach3 sign ins outs g g' `CA.mkImpl` edhml2CASL sign newVars f
     )
edhml2CASL sign vars@(g,g') (DiaEE e@(MsgI _ evars) outs phi f) =
  let newVars = (g',prime g')
  in exEvtArgs evars $ exConf sign g' (
              trans sign vars g e outs g'
       `andC` stForm2CASL sign vars phi
       `andC` edhml2CASL sign newVars f
     )
edhml2CASL sign vars@(g,g') (DiaAE e@(MsgI _ evars) phi outs psi f) =
  let newVars = (g',prime g')
  in univEvtArgs evars (
       stForm2CASL sign vars phi `CA.mkImpl` exConf sign g' (
                trans sign vars g e outs g'
         `andC` stForm2CASL sign vars psi
         `andC` edhml2CASL sign newVars f
       )
     )
edhml2CASL sign vars (Not f)      = notC $ edhml2CASL sign vars f
edhml2CASL sign vars (f `And` f') = edhml2CASL sign vars f `andC` edhml2CASL sign vars f'
edhml2CASL sign vars TrueE        = CA.trueForm

compOp2CASL :: COMP_OP -> CA.PRED_SYMB
compOp2CASL Eq = error "Tried to treat equality as a predicate. Please report this as bug."
compOp2CASL someOp = CA.mkQualPred (mkInfix $ show someOp)
                                  (CA.Pred_type [natSort,natSort] nullRange)

type ConfigVars = (VAR_NAME,VAR_NAME)

stForm2CASL :: Sign -> ConfigVars -> FORMULA -> CA.FORMULA ()
stForm2CASL sign vars (CompF x Eq y) =             term2CASLterm sign vars x
                                       `CA.mkStEq` term2CASLterm sign vars y
stForm2CASL sign vars (CompF x op y) =
  compOp2CASL op `CA.mkPredication` (term2CASLterm sign vars <$> [x,y])
stForm2CASL sign vars TrueF        = CA.trueForm
stForm2CASL sign vars FalseF       = CA.falseForm
stForm2CASL sign vars (NotF f)     = notC $ stForm2CASL sign vars f
stForm2CASL sign vars (f :/\  f')  = stForm2CASL sign vars f `andC`      stForm2CASL sign vars f'
stForm2CASL sign vars (f :\/  f')  = stForm2CASL sign vars f `orC`       stForm2CASL sign vars f'
stForm2CASL sign vars (f :=>  f')  = stForm2CASL sign vars f `CA.mkImpl` stForm2CASL sign vars f'
stForm2CASL sign vars (f :<=  f')  = stForm2CASL sign vars f'`CA.mkImpl` stForm2CASL sign vars f
stForm2CASL sign vars (f :<=> f')  = stForm2CASL sign vars f `CA.mkEqv`  stForm2CASL sign vars f'

term2CASLterm :: Sign -> ConfigVars -> TERM -> CA.TERM ()
term2CASLterm sign vars (VarT var)      = var2CASLterm sign vars var
term2CASLterm sign vars (ConstT natLit) = natLit2CASL $ show natLit
term2CASLterm sign vars (x:+y)          = translOp sign vars "+" x y
term2CASLterm sign vars (x:-y)          = translOp sign vars "-" x y
term2CASLterm sign vars (x:*y)          = translOp sign vars "*" x y
term2CASLterm sign vars (x:/y)          = translOp sign vars "/" x y

natLit2CASL :: String -> CA.TERM ()
natLit2CASL [] = constTerm (str2Token "0") natSort
natLit2CASL ds = List.foldl1 (%%) [ constTerm (str2Token [d]) natSort
                                  | d <- ds
                                  ]

(%%) :: CA.TERM () -> CA.TERM () -> CA.TERM ()
d %% e = CA.mkAppl (op (mkInfix "@@") [natSort,natSort] natSort)
                   [d,e]

translOp :: Sign -> ConfigVars -> String -> TERM -> TERM -> CA.TERM ()
translOp sign vars opName x y = CA.mkAppl (natInfixOp opName)
                                         (term2CASLterm sign vars <$> [x,y])

var2CASLterm :: Sign -> ConfigVars -> VAR_NAME -> CA.TERM ()
var2CASLterm  sign (g,g') var = if unprime var `Set.member` attrS sign
                                then attrT
                                else eVarT
  where
    eVarT    = CA.mkVarTerm var natSort
    attrName = token2Str $ unprime var
    attrT    = attrOp sign attrName `CA.mkAppl` [CA.mkVarTerm env $ confSort $ str2Token $ machName sign]
    env      = if primed var then g' else g

primed :: VAR_NAME -> Bool
primed = (=='\'') . last . token2Str

unprime :: VAR_NAME -> VAR_NAME
unprime = str2Token . reverse . dropWhile (=='\'') . reverse . token2Str

msgItem2CASLterm :: MESSAGE_ITEM -> CA.TERM ()
msgItem2CASLterm (MsgI name vars) =
  CA.mkAppl msgConOp
           [ CA.mkAppl (portConOp $ portName name) []
           , CA.mkAppl (evtConOp name $ length vars)
                      (flip CA.mkVarTerm natSort <$> vars)
           ]

eventList2CASLterm :: Sign -> ConfigVars -> [MESSAGE_INSTANCE] -> CA.TERM ()
eventList2CASLterm sign vars outs =
  List.foldr msgInstCons msgInstNil [ CA.mkAppl msgConOp
                                               [ CA.mkAppl (portConOp $ portName ename)
                                                          []
                                               , CA.mkAppl (evtConOp ename $ length args)
                                                          (term2CASLterm sign vars <$> args)
                                               ]
                                    | MsgInst ename args <- outs
                                    ]

msgInstNil :: CA.TERM ()
msgInstNil = CA.mkAppl msgInstNilOp []

msgInstNilOp :: CA.OP_SYMB
msgInstNilOp = op (composeId ["[]"])
                  []
                  msgListSort

msgInstCons :: CA.TERM () -> CA.TERM () -> CA.TERM ()
msgInstCons x xs = CA.mkAppl msgInstConsOp [x,xs]

msgInstConsOp :: CA.OP_SYMB
msgInstConsOp = op (mkInfix "::")
                   [msgSort, msgListSort]
                   msgListSort

prefixEvt :: Token -> Token
prefixEvt (Token name _) = composeTok ["con", "Evt", name]

exEvtArgs :: [CA.VAR] -> CA.FORMULA () -> CA.FORMULA ()
exEvtArgs   []    phi = phi
exEvtArgs   evars phi = CA.mkExist  [CA.Var_decl evars natSort nullRange] phi

univEvtArgs :: [CA.VAR] -> CA.FORMULA () -> CA.FORMULA ()
univEvtArgs []    phi = phi
univEvtArgs evars phi = CA.mkForall [CA.Var_decl evars natSort nullRange] phi

exCtrl :: Sign -> CA.VAR -> CA.FORMULA () -> CA.FORMULA ()
exCtrl sign s f = CA.mkExist [CA.mkVarDecl s $ ctrlSort sign] f

exConf :: Sign -> CA.VAR -> CA.FORMULA () -> CA.FORMULA ()
exConf sign g f = CA.mkExist  [CA.mkVarDecl g $ confSort $ str2Token $ machName sign] f

univConf :: Sign -> CA.VAR -> CA.FORMULA () -> CA.FORMULA ()
univConf sign g f = CA.mkForall [CA.mkVarDecl g $ confSort $ str2Token $ machName sign] f

prime :: Token -> Token
prime (Token var _) = str2Token (var++"'")

op :: Id -> [CA.SORT] -> CA.SORT -> CA.OP_SYMB
op name argTys resTy = CA.mkQualOp name
                     $ CA.Op_type CA.Total argTys resTy nullRange

constTerm :: Token -> CA.SORT -> CA.TERM ()
constTerm opName sort = op (token2Id opName) [] sort `CA.mkAppl` []

mkState :: Sign -> STATE -> CA.TERM ()
mkState sign name = stateOp sign name `CA.mkAppl` []

stateOp :: Sign -> STATE -> CA.OP_SYMB
stateOp sign name = op (composeId ["st", token2Str name, machName sign])
                       []
                       (ctrlSort sign)

mkVar :: CA.VAR -> CA.SORT -> CA.TERM ()
mkVar name sort = CA.toQualVar $ CA.mkVarDecl name sort


trans :: Sign -> ConfigVars -> CA.VAR -> MESSAGE_ITEM -> [MESSAGE_INSTANCE] -> CA.VAR -> CA.FORMULA ()
trans sign vars g e outs g' = CA.mkPredication (transPred sign)
                                               [ confVar sign g
                                               , msgItem2CASLterm e
                                               , eventList2CASLterm sign vars outs
                                               , confVar sign g'
                                               ]

confVar :: Sign -> CA.VAR -> CA.TERM ()
confVar sign g = CA.mkVarTerm g $ confSort $ str2Token $ machName sign

ctrl :: Sign -> CA.TERM () -> CA.TERM ()
ctrl sign g = ctrlOp sign `CA.mkAppl` [g]

reach2 :: Sign -> MESSAGE_NAMES -> MESSAGE_NAMES -> CA.VAR -> CA.FORMULA ()
reach2 sign ins outs g = CA.mkPredication (reach2Pred sign) [ins, outs, confVar sign g]

reach3 :: Sign -> MESSAGE_NAMES -> MESSAGE_NAMES -> CA.VAR -> CA.VAR -> CA.FORMULA ()
reach3 sign ins outs g g' = CA.mkPredication (reach3Pred sign) [ins, outs, confVar sign g, confVar sign g']

cSetCons :: MESSAGE_NAME -> MESSAGE_NAMES -> MESSAGE_NAMES
e `cSetCons` es = CA.mkAppl cSetConsOp
                           [CA.mkAppl (msgNameConOp e) [], es]

cSetConsOp :: CA.OP_SYMB
cSetConsOp = op (mkInfix "+")
                [msgNameSort,msgNameSetSort]
                msgNameSetSort

cSetNil :: MESSAGE_NAMES
cSetNil = cSetNilOp `CA.mkAppl` []

cSetNilOp :: CA.OP_SYMB
cSetNilOp = op (str2Id "{}") [] msgNameSetSort

initPred, transPred, reach2Pred, reach3Pred :: Sign -> CA.PRED_SYMB
initPred   sign = CA.mkQualPred ( str2Id "init")
                               ( CA.Pred_type [confSort $ str2Token $ machName sign] nullRange)
transPred  sign = CA.mkQualPred ( str2Id "trans")
                               ( CA.Pred_type [ confSort $ str2Token $ machName sign
                                             , msgSort
                                             , msgListSort
                                             , confSort $ str2Token $ machName sign
                                             ]
                                             nullRange
                               )
reach2Pred sign = CA.mkQualPred ( str2Id "reachable2")
                               ( CA.Pred_type [ msgNameSetSort
                                             , msgNameSetSort
                                             , confSort $ str2Token $ machName sign
                                             ]
                                             nullRange
                               )
reach3Pred sign = CA.mkQualPred ( str2Id "reachable3")
                               ( CA.Pred_type [ msgNameSetSort
                                             , msgNameSetSort
                                             , confSort $ str2Token $ machName sign
                                             , confSort $ str2Token $ machName sign
                                             ]
                                             nullRange
                               )

attrOp :: Sign -> [Char] -> CA.OP_SYMB
attrOp sign name = op (composeId ["attr", name, machName sign])
                      [confSort $ str2Token $ machName sign]
                      natSort

ctrlOp :: Sign -> CA.OP_SYMB
ctrlOp sign = op (composeId ["ctrl"]) [confSort $ str2Token $ machName sign] (ctrlSort sign)

msgNameOp :: CA.OP_SYMB
msgNameOp = op (composeId ["msgName"]) [msgSort] msgNameSort

evtConOp :: MESSAGE_NAME -> Arity -> CA.OP_SYMB
evtConOp name ar = op (token2Id $ prefixEvt $ str2Token $ evtName name)
                      (replicate ar natSort)
                      evtSort
msgConOp :: CA.OP_SYMB
msgConOp = op (composeId ["msg"]) [portSort,evtSort] msgSort

msgNameConOp :: MESSAGE_NAME -> CA.OP_SYMB
msgNameConOp (MsgName pname ename) = op (composeId ["con", "MsgName", ename])
                                        []
                                        msgNameSort

portConOp :: [Char] -> CA.OP_SYMB
portConOp pname = op (composeId["con", "Port", pname])
                     []
                     portSort

natInfixOp :: String -> CA.OP_SYMB
natInfixOp opName = op (mkInfix opName) [natSort,natSort] natSort

natLitOp :: Int -> CA.OP_SYMB
natLitOp num = op (str2Id $ show num) [] natSort

confOp :: Sign -> CA.OP_SYMB
confOp sign = op (composeId ["con","Conf",machName sign])
                 (ctrlSort sign : replicate (Set.size $ attrS sign) natSort)
                 (confSort $ str2Token $ machName sign)

ctrlSort :: Sign -> Id
ctrlSort  sign  = composeId ["Ctrl", machName sign]

natSort, msgNameSort, msgNameSetSort :: Id
msgNameSort    = composeId ["MsgName"   ]
msgNameSetSort = composeId ["MsgNameSet"]
natSort        = composeId ["Nat"       ]


sepCASL :: CA.FORMULA f -> [CA.FORMULA f]
sepCASL (CA.Junction CA.Con fs _) = concat (sepCASL <$> fs)
sepCASL f                         = [f]

