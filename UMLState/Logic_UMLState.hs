{-# LANGUAGE MultiParamTypeClasses , FlexibleContexts , TypeSynonymInstances , FlexibleInstances, DeriveDataTypeable #-}

{- |
Module      : $Id$
Description : Instance of class Logic for the UMLState logic
Copyright   :  (c) Tobias Rosenberger, Swansea University and Universit{'e} Grenoble Alpes 2022
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  TRosenberger@gmx.de
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

This Module implements the input language for UML State Machines without ouputs developed in

Rosenberger, Tobias & Bensalem, Saddek & Knapp, Alexander & Roggenbach, Markus. (2021). Institution-Based Encoding and Verification of Simple UML State Machines in CASL/SPASS.
http://dx.doi.org/10.1007/978-3-030-73785-6_7

A development on this logic can be found in 'UMLStateO.Logic_UMLStateO'. That logic also implements output events in a way that is compatible with 'UMLConf.Logic_UMLConf'.

The current file was intentionally left in mostly the same state it had when we performed the proofs in the paper.
It should probably be considered superseded by UMLStateO and removed before merging into upstream HeTS. (TODO)
-}

module UMLState.Logic_UMLState where

import Logic.Logic

import qualified CASL.AS_Basic_CASL as C
import qualified CASL.Formula as CF

import Common.DocUtils
import Common.ExtSign
import Common.Id
import ATerm.Conversion
import Common.GlobalAnnotations
import Common.AnnoState
import Common.Lexer
import Common.Parsec
import Common.Result as R

import Data.Set as Set
import Data.Map as Map
import Data.List as List
import Data.Functor.Identity

import qualified Data.Data as D

import Control.Monad (when)
import Control.Monad.Trans (lift)
import Control.Monad.Trans.State as S

import Text.Parsec
import Text.Parsec.Expr
import Text.Parsec.String
import Text.ParserCombinators.Parsec.Char

-- BEGIN AS (abstract syntax)
type SPEC_NAME = Token

data NAMED_SPEC = SPEC_NAME := BASIC_SPEC deriving (Eq,Ord,Show,D.Data)
data BASIC_SPEC = Basic [BASIC_ITEMS] deriving (Eq,Ord,Show,D.Data)
data BASIC_ITEMS = SigB SIG_ITEMS
                 | VarB VAR_ITEMS
                 | SenB SEN_ITEMS
                 | EvtB EVENT_ITEMS
                 deriving (Eq,Ord,Show,D.Data)

data VAR_ITEMS = VarIs [VAR_NAME] deriving (Eq,Ord,Show,D.Data)

data SEN_ITEMS = TransB TRANS_ITEM
               | InitB STATE GUARD
               deriving (Eq,Ord,Show,D.Data)
data EVENT_ITEMS = EvtIs [EVENT_ITEM] deriving (Eq,Ord,Show,D.Data)
data EVENT_ITEM = EvtI EVENT_NAME [VAR_NAME] deriving (Eq,Ord,Show,D.Data)
data TERM = VarT VAR_NAME
          | ConstT NAT_LIT
          | TERM :+ TERM
          | TERM :- TERM
          | TERM :* TERM
          | TERM :/ TERM
          | TERM :& TERM
          deriving (Show,Ord,Eq,D.Data)
data NAT_OP = Plus | Minus | Times | Div deriving (Eq,Ord,Show,D.Data)
type VAR_NAME = Token

type EVENT_NAME = Token
type NAT_LIT = Int

data SIG_ITEMS = StateS [STATE_ITEM]
               deriving (Eq,Ord,Show,D.Data)
data STATE_ITEM = StateI STATE deriving (Eq,Ord,Show,D.Data)


type STATE = Token

data TRANS_ITEM = TransI STATE STATE TRANS_LABEL
                deriving (Eq,Ord,Show,D.Data)
data TRANS_LABEL = Label TRIGGER (Maybe GUARD) (Maybe ACTIONS)
                 deriving (Eq,Ord,Show,D.Data)
type TRIGGER = EVENT_ITEM
type GUARD = FORMULA

data ACTIONS = Acts [ACTION] deriving (Eq,Ord,Show,D.Data)
data ACTION = Assign VAR_NAME TERM deriving (Eq,Ord,Show,D.Data)

-- | Data formulae, used for guards and effects of actions
data FORMULA = CompF TERM COMP_OP TERM
             | TrueF | FalseF
             | NotF FORMULA
             | FORMULA :/\ FORMULA
             | FORMULA :\/ FORMULA
             | FORMULA :=> FORMULA
             | FORMULA :<= FORMULA
             | FORMULA :<=> FORMULA
             deriving (Eq,Ord,Show,D.Data)
data COMP_OP = Less | LessEq | Eq | GreaterEq | Greater
             deriving (Enum,Eq,Ord,D.Data)
-- END AS

instance Show COMP_OP where
  show Less      = "<"
  show LessEq    = "<="
  show Eq        = "=="
  show GreaterEq = ">="
  show Greater   = ">"

data UMLState = UMLState deriving (Eq,Ord,Show,D.Data)

type Morphism = Library -- only identity morphisms

instance Category Library Morphism where
  ide sig = sig
  inverse f = return f
  composeMorphisms f g = return f
  dom f = f
  cod f = f
  isInclusion f = True
  legal_mor f = return ()
  

instance Monoid BASIC_SPEC where

instance Pretty BASIC_SPEC where
instance GetRange BASIC_SPEC where

instance GetRange EDHML where

instance Language UMLState where

-- BEGIN parsing



-- namedSpec :: [t0] -> PrefixMap -> GenParser Char st NAMED_SPEC
namedSpec bi foo = do
  key "spec" 
  name <- str2Token <$> scanLetterWord << skipSmart
  asSeparator "="
  contents <- basicSpec bi foo 
  return $ name := contents

-- basicSpec :: [t0] -> PrefixMap -> GenParser Char st BASIC_SPEC
basicSpec bi _ = Basic <$> try basicItems `sepBy` semiT << theEnd

theEnd :: Parsec [Char] st [Char]
theEnd = optionMaybe (asSeparator ";") >> key "end"

evtItems :: Parsec [Char] st EVENT_ITEMS
evtItems = EvtIs <$> (evtS *> evts) <?> "event items"

evtS :: Parsec [Char] st Token
evtS = try $ pluralKeyword "event" << skipSmart

evts :: Parsec [Char] st [EVENT_ITEM]
evts = try evtItem `sepBy` asSeparator ","

evtItem :: Parsec [Char] st EVENT_ITEM
evtItem = do
  evtName <- str2Token <$> scanLetterWord << skipSmart
  maybeArgs <- optionMaybe $ do
    oParenT >> (var << skipSmart) `sepBy` asSeparator "," << cParenT
  return $ EvtI evtName $ case maybeArgs of
    Nothing -> []
    Just varNames -> varNames

basicItems :: Parsec [Char] st BASIC_ITEMS
basicItems = do SigB <$> sigItems
         <|> do SenB . TransB <$> transItem
         <|> do SenB <$> (key "init" >> (InitB  <$> (stateP  << asSeparator ":") <*> guardP))
         <|> do EvtB <$> evtItems
         <|> do VarB <$> varItems

varItems :: Parsec [Char] st VAR_ITEMS
varItems = VarIs <$> (pluralKeyword "var" >> ((var << skipSmart) `sepBy` asSeparator ","))

sigItems :: Parsec [Char] st SIG_ITEMS
sigItems = StateS <$> (statePS *> statePs)

statePS :: CharParser st Token
statePS = pluralKeyword "state" << skipSmart

statePs :: Parsec [Char] st [STATE_ITEM]
statePs = statePItem `sepBy` asSeparator ","

statePItem :: Parsec [Char] st STATE_ITEM
statePItem = StateI <$> stateP << skipSmart

transItem :: Parsec [Char] st TRANS_ITEM
transItem = do key "trans"
               s1 <- try stateP
               try $ asSeparator "-->"
               s2 <- stateP
               asSeparator ":"
               label <- transLabel
               return $ TransI s1 s2 label

transLabel :: Parsec [Char] st TRANS_LABEL
transLabel = do p <- trigger
                g <- optionMaybe guardP
                a <- optionMaybe actions
                return $ Label p g a

actions :: Parsec [Char] st ACTIONS
actions = Acts <$> do
  asSeparator "/"
  asSeparator "{"
  as <- action `sepBy` asSeparator ";"
  asSeparator "}"
  return as

action = Assign <$> var <*> (asSeparator ":=" >> term)

trigger :: Parsec [Char] st EVENT_ITEM
trigger = evtItem

guardP :: Parsec [Char] st FORMULA
guardP = oBracketT >> formula << cBracketT

stateP :: Parsec [Char] st Token
stateP = str2Token <$> (scanLetterWord << skipSmart)

formula :: Parsec [Char] st FORMULA
formula = buildExpressionParser ops simpForm where
  ops = [ [preWordOp "not" NotF]
        , [symOpR "/\\" (:/\)]
        , [symOpR "\\/" (:\/)]
        , [symOpR "=>" (:=>), wordOp "if" (:<=), symOpR "<=>" (:<=>)]
        ]
  simpForm = do key "true"  >> return TrueF
         <|> do key "false" >> return FalseF
         <|> do CompF <$> try term <*> try compOp <*> term
         <|> do oParenT >> formula << cParenT

term :: Parsec [Char] st TERM
term = buildExpressionParser ops simpTerm where
  ops = [ [symOpL "*" (:*), symOpL "/" (:/)]
        , [symOpL "+" (:+), symOpL "-" (:-)]
        , [symOpL "&" (:&)]
        ]
  simpTerm = do VarT <$> var
         <|> do ConstT <$> natLit
         <|> do oParenT >> term << cParenT
    

compOp :: Parsec [Char] st COMP_OP
compOp = parseAlts [Less .. Greater]


var :: Parsec [Char] st VAR_NAME
var = str2Token <$> scanLetterWord << skipSmart


natLit :: Parsec [Char] st Int
natLit = value 10 <$> getNumber << skipSmart


key :: String -> Parsec [Char] st String
key s = try (keyWord (string s) << skipSmart)

-- parse helpers

preWordOp :: String -> (a -> a) -> Operator [Char] st Data.Functor.Identity.Identity a
preWordOp w op = Prefix (key w >> return op)

symOpL :: String -> (a -> a -> a) -> Operator [Char] st Data.Functor.Identity.Identity a
symOpL s op = Infix (asSeparator s >> return op) AssocLeft

symOpR :: String -> (a -> a -> a) -> Operator [Char] st Data.Functor.Identity.Identity a
symOpR s op = Infix (asSeparator s >> return op) AssocRight

wordOp :: String -> (a -> a -> a) -> Operator [Char] st Data.Functor.Identity.Identity a
wordOp w op = Infix (key w >> return op) AssocRight

parseAlts :: Show a => [a] -> Parsec [Char] st a
parseAlts xs = choice
  [ const x <$> try (asSeparator $ show x)
  | x <- xs
  ]

-- END parsing

instance ShATermConvertible BASIC_SPEC where
instance Syntax UMLState BASIC_SPEC Token () () where
  parsersAndPrinters UMLState = makeDefault (basicSpec [], pretty)

instance Sentences UMLState EDHML Library Morphism Token where
instance StaticAnalysis UMLState BASIC_SPEC EDHML () () Library Morphism Token () where
  basic_analysis _ = Just $ \ (spec,sign,annos) -> do
    (spec',lib) <- runStateT (ana_BASIC_SPEC spec) mempty
    let sign   = lib
        symSet = sign2SymSet $ lib2Sign lib
        extSign = ExtSign sign symSet
        annos  = []
    return (spec', extSign, annos)

instance Logic UMLState () BASIC_SPEC EDHML () () Library Morphism Token () () where

instance Pretty EDHML where
instance Pretty Library where

instance ShATermConvertible EDHML where
instance ShATermConvertible Library where

instance ShATermConvertible Token where

data Sign = Sign
  { statesS :: Set Token
  , varsS   :: Set Token
  , actsS   :: Map (Token, Arity) EVENT_ITEM
  } deriving (Eq,Show,Ord)
type Thy = [EDHML]
type Arity = Int
data Library = Library
  { statesL :: Set STATE
  , attrL   :: Set VAR_NAME
  , actsL   :: Map (EVENT_NAME, Arity) EVENT_ITEM
  , initL   :: [(STATE, GUARD)]
  , transL  :: [TRANS_ITEM]
  } deriving (Eq,Ord,Show)

instance Monoid Library where
  mempty = Library mempty mempty mempty mempty mempty
  lib `mappend` lib' = Library { statesL = statesL lib `mappend` statesL lib'
                               , attrL   = attrL   lib `mappend` attrL   lib'
                               , actsL   = actsL   lib `mappend` actsL   lib'
                               , initL   = initL   lib `mappend` initL   lib'
                               , transL  = transL  lib `mappend` transL  lib'
                               }

lib2Sign lib = Sign
  { statesS = statesL lib
  , varsS   = attrL lib
  , actsS   = actsL lib
  }

extractActs :: Map (Token, Arity) EVENT_ITEM -> Set Token
extractActs = Set.map fst . Map.keysSet

sign2SymSet :: Sign -> Set Token
sign2SymSet sign = statesS sign `Set.union` varsS sign
                                `Set.union` extractActs (actsS sign)

type Check = StateT Library Result

-- instance MonadState Library Check where

errC :: String -> Check a
errC s = lift $ fatal_error s nullRange

ana_BASIC_SPEC :: BASIC_SPEC -> Check BASIC_SPEC
ana_BASIC_SPEC (Basic bs) = Basic <$> sequence (ana_BASIC_ITEMS <$> bs)

ana_BASIC_ITEMS :: BASIC_ITEMS -> Check BASIC_ITEMS
ana_BASIC_ITEMS (SigB items) = SigB <$> ana_SIG_ITEMS items
ana_BASIC_ITEMS (SenB items) = SenB <$> ana_SEN_ITEMS items
ana_BASIC_ITEMS (EvtB items) = EvtB <$> ana_EVENT_ITEMS items
ana_BASIC_ITEMS (VarB items) = VarB <$> ana_VAR_ITEMS items

ana_VAR_ITEMS :: VAR_ITEMS -> Check VAR_ITEMS
ana_VAR_ITEMS (VarIs vs) = VarIs <$> sequence (ana_VAR_ITEM <$> vs)

ana_VAR_ITEM :: VAR_NAME -> Check VAR_NAME
ana_VAR_ITEM var = do
  lib <- get
  let vars = attrL lib
  when (var `Set.member` vars) $ errC ("variable declared twice: " ++ show var)
  put $ lib {
    attrL = var `Set.insert` vars
  }
  return var
  
ana_SIG_ITEMS :: SIG_ITEMS -> Check SIG_ITEMS
ana_SIG_ITEMS (StateS items) = StateS <$> sequence (ana_STATE_ITEM <$> items)

ana_SEN_ITEMS :: SEN_ITEMS -> Check SEN_ITEMS
ana_SEN_ITEMS (TransB tr) = TransB <$> ana_TRANS_ITEMS tr
ana_SEN_ITEMS (InitB st g) = do
  lib <- get
  let sts = statesL lib
      lib' = lib {
        initL = (st,g) : initL lib
      }
  if st `elem` sts
  then put lib' >> do return $ InitB st g
  else errC "Initial transition to undefined state."

ana_EVENT_ITEMS :: EVENT_ITEMS -> Check EVENT_ITEMS
ana_EVENT_ITEMS (EvtIs as) = EvtIs <$> sequence (ana_EVENT_ITEM <$> as)

ana_EVENT_ITEM :: EVENT_ITEM -> Check EVENT_ITEM
ana_EVENT_ITEM e@(EvtI name vars) = do
  lib <- get
  put $ lib {actsL = Map.insert (name, length vars) e $ actsL lib}
  return e
  

ana_TRANS_ITEMS :: TRANS_ITEM -> Check TRANS_ITEM
ana_TRANS_ITEMS (TransI st1 st2 (Label t@(EvtI ename evar) g a)) = do
  lib <- get
  let sts = statesL lib
      acts = actsL lib
      ekey = (ename, length evar)
      insertVars [] set = set
      insertVars (v:vs) set = insertVars vs (v `Set.insert` set)
      varsWithTvar = insertVars evar $ attrL lib
      actSkip   = Acts []
      checkWhenJust m res f = maybe (return $ Just res) f m
  when (st1 `Set.notMember` sts) $
    errC ("transition out of undefined state: " ++ show st1)
  when (st2 `Set.notMember` sts) $
    errC ("transition into undefined state: "   ++ show st2)
  when (ekey `Map.notMember` acts) $
    errC ("transition with undefined trigger: " ++ show ekey)
  g' <- checkWhenJust g TrueF $ \ gRaw -> do
    return g -- TODO check FORMULA
  a' <- checkWhenJust a actSkip $ \ (Acts as) -> do
    Just . Acts <$> sequence (ana_ACTION (attrL lib) varsWithTvar <$> as)
  let l' = Label t g' a'
      newTrans = TransI st1 st2 l'
      lib' = lib {
        transL = newTrans : transL lib
      }
  put lib'
  return newTrans

ana_ACTION :: Set VAR_NAME -> Set VAR_NAME -> ACTION -> Check ACTION
ana_ACTION vars varsWithTvar (Assign var tm) = do
  when (var `Set.notMember` vars) $ errC ("assignment to undeclared variable")
  ana_TERM varsWithTvar tm
  return $ Assign var tm

ana_TERM :: Set VAR_NAME -> TERM -> Check ()
ana_TERM vars (VarT var) = when (var `Set.notMember` vars) $
  errC ("reference to undeclared variable: " ++ show var)
ana_TERM vars (ConstT lit) = return ()
ana_TERM vars (a :+ b) = ana_TERM vars a >> ana_TERM vars b
ana_TERM vars (a :- b) = ana_TERM vars a >> ana_TERM vars b
ana_TERM vars (a :* b) = ana_TERM vars a >> ana_TERM vars b
ana_TERM vars (a :/ b) = ana_TERM vars a >> ana_TERM vars b
ana_TERM vars (a :& b) = ana_TERM vars a >> ana_TERM vars b
  
ana_STATE_ITEM :: STATE_ITEM -> Check STATE_ITEM
ana_STATE_ITEM (StateI st) = do
  lib <- get
  put $ lib {
    statesL = st `Set.insert` statesL lib 
  }
  return $ StateI st

type EVENT_NAMES = C.TERM ()

data EDHML = DtSen FORMULA
           | St STATE
           | Binding STATE EDHML
           | At EVENT_NAMES STATE EDHML -- add F?
           | Box EVENT_NAMES EDHML      -- add F?
           | DiaEE EVENT_ITEM FORMULA EDHML -- exists valuation and transititon ...
           | DiaAE EVENT_ITEM FORMULA FORMULA EDHML -- for each valuation satisfying phi there exists a transition ...
           | Not EDHML
           | And EDHML EDHML
           | TrueE
           deriving (Eq,Ord,Show,D.Data)

initP :: C.TERM () -> C.FORMULA ()
initP g = C.mkPredication initPred [g]

initCASL :: Library -> C.FORMULA ()
initCASL lib = C.mkForall [C.mkVarDecl gTok confSort]  equiv
  where
    equiv = initP gTerm `C.mkEqv` defForm
    gTok  = str2Token "g"
    gTerm = confVar gTok
    vars  = (attrL lib, gTok, prime gTok)
    defForm = disjunctC [ (ctrl gTerm `C.mkStEq` mkState s0) `andC` stForm2CASL vars phi0
                        | (s0,phi0) <- initL lib
                        ]
      
lib2EDHML :: Library -> EDHML
lib2EDHML lib = assert `seq` edhmlRmNotNot (computeEDHML allEvts c0 is vs bs im1 im2 es)
  where
    combineEvts (ename,_) _ enames = ename `cSetCons` enames
    allEvts = Map.foldrWithKey combineEvts cSetNil $ actsL lib
    (c0, states) = Set.deleteFindMin $ statesL lib
    guard2phi = maybe TrueF id

    acts2psi Nothing = TrueF
    acts2psi (Just (Acts as)) = conjunctF [ CompF (VarT $ prime v) Eq t
                                          | Assign v t <- as
                                          ]
    im1 c = Map.findWithDefault id c (
              Map.fromListWith (.) -- for equal keys: compose diff lists
                [ ( c
                  , ([(guard2phi guard, e, acts2psi acts, c')] ++) -- difference list
                  )
                | TransI c c' (Label e guard acts) <- transL lib
                ] 
            ) []
    im2 ce = Map.findWithDefault id ce (
               Map.fromListWith (.) -- for equal keys : compose diff lists
                 [ ( (c, ename, length evars)
                   , ([(guard2phi guard, acts2psi acts, c')] ++) -- difference list
                   )
                 | TransI c c' (Label (EvtI ename evars) guard acts) <- transL lib
                 ]
             ) []
    vs = Set.toList states
    bs = c0 : vs
    is = im1 c0
    es = Map.elems $ actsL lib
    assert = if Set.null (statesL lib)
             then error "Can't translate lib to EDHML: need at least one state"
             else ()

computeEDHML :: EVENT_NAMES
             -> STATE
             -> [(FORMULA, EVENT_ITEM, FORMULA, STATE)]
             -> [STATE]
             -> [STATE]
             -> (STATE -> [(FORMULA, EVENT_ITEM, FORMULA, STATE)])
             -> ( (STATE, EVENT_NAME, Int) -> [(FORMULA, FORMULA, STATE)]
                )
             -> [EVENT_ITEM]
             -> EDHML
computeEDHML allEvts c ((phi,e,psi,c'):is) vs bs im1 im2 es =
    (At allEvts c $ DiaAE e phi psi $ St c')
  `andE` computeEDHML allEvts c is vs bs im1 im2 es
computeEDHML allEvts c [] (c':vs) bs im1 im2 es =
  computeEDHML allEvts c' (im1 c') vs bs im1 im2 es
computeEDHML allEvts c [] [] bs im1 im2 es =
  fin allEvts bs im2 es `andE` pairsDiff allEvts bs

pairsDiff :: EVENT_NAMES -> [Token] -> EDHML
pairsDiff allEvts bs = conjunctE [ Not $ At allEvts c1 $ St c2
                                 | c1 <- bs, c2 <- bs, c1 /= c2
                                 ]

boxAA :: EVENT_ITEM -> FORMULA -> EDHML -> EDHML
boxAA e phi f = Not $ DiaEE e phi $ Not f

fin :: EVENT_NAMES
    -> [STATE]
    -> ( (STATE, EVENT_NAME, Int) -> [(FORMULA, FORMULA, STATE)]
       )
    -> [EVENT_ITEM]
    -> EDHML
fin allEvts bs im2 es = conjunctE
  [ At allEvts c $ conjunctE [ boxAA e (
                                 (
                                   conjunctF [ phi :/\ psi
                                             | (phi, psi, c') <- ps
                                             ]
                                 ) :/\ NotF (
                                   disjunctF  [ phi :/\ psi
                                              | (phi, psi, c') <- nps
                                              ]
                                 )
                               ) $ disjunctE [ St c'
                                             | (phi, psi, c') <- ps
                                             ]
                             | e <- es, (ps, nps) <- complements c e im2
                             ]
  | c <- bs
  ]

          -- TODO use Set
          -- problem: powerSet reported as not exported
complements :: -- (Eq a, Ord t) =>
               STATE
            -> EVENT_ITEM
            -> (
                 (STATE, EVENT_NAME, Arity) -> [(FORMULA, FORMULA, STATE)]
               )
            -> [([(FORMULA, FORMULA, STATE)], [(FORMULA, FORMULA, STATE)])]
complements c (EvtI ename evars) im2 =
  let xs = im2 (c, ename, length evars)
  in [ ( ps
       , xs List.\\ ps
       )
     | ps <- subsequences xs 
     ]


-- CASL logic helpers
andC :: C.FORMULA () -> C.FORMULA () -> C.FORMULA ()
a `andC` b = C.conjunct [a, b]

orC :: C.FORMULA () -> C.FORMULA () -> C.FORMULA ()
a `orC` b = C.disjunct [a, b]

notC :: C.FORMULA () -> C.FORMULA ()
notC a = C.Negation a nullRange

conjunctC :: [C.FORMULA ()] -> C.FORMULA ()
conjunctC = C.conjunct

disjunctC :: [C.FORMULA ()] -> C.FORMULA ()
disjunctC  = C.disjunct

-- state FORMULA logic helpers

conjunctF :: [FORMULA] -> FORMULA
conjunctF []   = TrueF
conjunctF phis = List.foldl1 (:/\) phis

disjunctF :: [FORMULA] -> FORMULA
disjunctF  []   = FalseF
disjunctF  phis = List.foldl1 (:\/) phis

-- EDHML logic helpers
andE, orE:: EDHML -> EDHML -> EDHML
phi `andE` psi = phi `And` psi
phi `orE`  psi = Not (Not phi `And` Not psi)

conjunctE :: [EDHML] -> EDHML
conjunctE [] = TrueE
conjunctE fs = List.foldl1 andE fs

disjunctE :: [EDHML] -> EDHML
disjunctE [] = Not TrueE
disjunctE fs = List.foldl1 orE fs

edhmlRmNotNot :: EDHML -> EDHML
edhmlRmNotNot (Not (Not f))       = edhmlRmNotNot f
edhmlRmNotNot (Not f)             = Not             $ edhmlRmNotNot f
edhmlRmNotNot (Binding c f)       = Binding c       $ edhmlRmNotNot f
edhmlRmNotNot (At evts c f)       = At evts c       $ edhmlRmNotNot f
edhmlRmNotNot (Box evts f)        = Box evts        $ edhmlRmNotNot f
edhmlRmNotNot (DiaEE e phi f)     = DiaEE e phi     $ edhmlRmNotNot f
edhmlRmNotNot (DiaAE e phi psi f) = DiaAE e phi psi $ edhmlRmNotNot f
edhmlRmNotNot (f `And` f')        = edhmlRmNotNot f `And` edhmlRmNotNot f'
edhmlRmNotNot f                   = f

edhml2CASL :: Vars -> EDHML -> C.FORMULA ()
edhml2CASL vars (DtSen f) = stForm2CASL vars f
edhml2CASL (_,g,_) (St s) = mkState s `C.mkStEq` ctrl (confVar g)
edhml2CASL vars@(_,g,_) (Binding s f) = exCtrl s (
                                                 mkState s `C.mkStEq` ctrl (confVar g)
                                          `andC` edhml2CASL vars f
                                        )
edhml2CASL vars@(as,g,g') (At evts s f) =
  let newVars = (as,g',prime g')
  in univConf g' (
       (
                (ctrl (confVar g') `C.mkStEq` mkState s)
         `andC` reach2 evts g'
       ) `C.mkImpl` edhml2CASL newVars f
     )
edhml2CASL (as,g,g') (Box evts f) =
  let newVars = (as,g',prime g')
  in univConf g' (
       reach3 evts g g' `C.mkImpl` edhml2CASL newVars f
     )
edhml2CASL vars@(as,g,g') (DiaEE e@(EvtI _ evars) phi f) =
  let newVars = (as,g',prime g')
  in exEvtArgs evars $ exConf g' (
       trans g e g' `andC` stForm2CASL vars phi `andC` edhml2CASL newVars f
     )
edhml2CASL vars@(as,g,g') (DiaAE e@(EvtI _ evars) phi psi f) =
  let newVars = (as,g',prime g')
  in univEvtArgs evars $ (
       stForm2CASL vars phi `C.mkImpl` exConf g' (
         trans g e g' `andC` stForm2CASL vars psi `andC` edhml2CASL newVars f
       )
     )
edhml2CASL vars (Not f)      = notC $ edhml2CASL vars f
edhml2CASL vars (f `And` f') = edhml2CASL vars f `andC` edhml2CASL vars f'
edhml2CASL vars TrueE        = C.trueForm

compOp2CASL :: COMP_OP -> C.PRED_SYMB
compOp2CASL op = C.mkQualPred (str2Id ("__" ++ show op ++ "__"))
                              (C.Pred_type [natSort,natSort] nullRange)

type Vars = (Set VAR_NAME,VAR_NAME,VAR_NAME)

stForm2CASL :: Vars -> FORMULA -> C.FORMULA ()
stForm2CASL vars (CompF x op y) =
  compOp2CASL op `C.mkPredication` [ term2CASLterm vars x
                                   , term2CASLterm vars y
                                   ]
stForm2CASL vars TrueF        = C.trueForm
stForm2CASL vars FalseF       = C.falseForm
stForm2CASL vars (NotF f)     = notC $ stForm2CASL vars f
stForm2CASL vars (f :/\ f')   = stForm2CASL vars f `andC`     stForm2CASL vars f'
stForm2CASL vars (f :\/ f')   = stForm2CASL vars f `orC`      stForm2CASL vars f'
stForm2CASL vars (f :=> f')   = stForm2CASL vars f `C.mkImpl` stForm2CASL vars f'
stForm2CASL vars (f :<= f')   = stForm2CASL vars f'`C.mkImpl` stForm2CASL vars f
stForm2CASL vars (f :<=> f')  = stForm2CASL vars f `C.mkEqv`  stForm2CASL vars f'

term2CASLterm vars (VarT var)      = var2CASLterm vars var
term2CASLterm vars (ConstT natLit) = natLit2CASL $ show natLit
term2CASLterm vars (x:+y)          = translOp vars "__+__" x y
term2CASLterm vars (x:-y)          = translOp vars "__-__" x y
term2CASLterm vars (x:*y)          = translOp vars "__*__" x y
term2CASLterm vars (x:/y)          = translOp vars "__/__" x y
term2CASLterm vars (x:&y)          = translOp vars "__&__" x y

natLit2CASL :: String -> C.TERM ()
natLit2CASL [] = constTerm (str2Token "0") natSort
natLit2CASL ds = List.foldl1 (%%) [ constTerm (str2Token [d]) natSort
                                  | d <- ds
                                  ]

(%%) :: C.TERM () -> C.TERM () -> C.TERM ()
d %% e = C.mkAppl (op (str2Token "__@@__") [natSort,natSort] natSort)
                  [d,e]

translOp :: Vars -> String -> TERM -> TERM -> C.TERM ()
translOp vars opName x y = C.mkAppl (op (str2Token opName) [natSort,natSort] natSort)
                                    (term2CASLterm vars <$> [x,y])

var2CASLterm :: Vars -> VAR_NAME -> C.TERM ()
var2CASLterm  (attrs,g,g') var = if unprime var `Set.member` attrs
                                 then attrT
                                 else eVarT
  where
    eVarT = C.mkVarTerm var natSort
    attrT = projOp `C.mkAppl` [C.mkVarTerm env confSort]
    projOp = op (unprime var) [confSort] natSort
    env = if primed var then g' else g

primed :: VAR_NAME -> Bool
primed = (=='\'') . last . token2Str

unprime :: VAR_NAME -> VAR_NAME
unprime = str2Token . reverse . dropWhile (=='\'') . reverse . token2Str

eventItem2CASLterm :: EVENT_ITEM -> C.TERM ()
eventItem2CASLterm (EvtI name vars) =
  C.mkAppl ( op (prefixEvt name)
                (const natSort <$> vars)
                evtSort
           )
           (flip C.mkVarTerm natSort <$> vars)

prefixEvt (Token name _) = str2Token ("evt_" ++ name)
prefixEvtName (Token name _) = str2Token ("evtName_" ++ name)

str2Id :: String -> Id
str2Id = token2Id . str2Token

token2Id :: Token -> Id
token2Id tok   = Id [tok] [] nullRange

token2Str (Token s _) = s

str2Token :: String -> Token
str2Token name = Token name nullRange

exEvtArgs :: [C.VAR] -> C.FORMULA () -> C.FORMULA ()
exEvtArgs   []    phi = phi
exEvtArgs   evars phi = C.mkExist  [C.Var_decl evars natSort nullRange] phi

univEvtArgs :: [C.VAR] -> C.FORMULA () -> C.FORMULA ()
univEvtArgs []    phi = phi
univEvtArgs evars phi = C.mkForall [C.Var_decl evars natSort nullRange] phi

exCtrl :: C.VAR -> C.FORMULA () -> C.FORMULA ()
exCtrl s f = C.mkExist [C.mkVarDecl s ctrlSort] f

exConf :: C.VAR -> C.FORMULA () -> C.FORMULA ()
exConf   g f = C.mkExist  [C.mkVarDecl g confSort] f

univConf :: C.VAR -> C.FORMULA () -> C.FORMULA ()
univConf g f = C.mkForall [C.mkVarDecl g confSort] f

prime :: Token -> Token
prime (Token var _) = str2Token (var++"'")

op :: Token -> [C.SORT] -> C.SORT -> C.OP_SYMB
op name argTys resTy = C.mkQualOp (token2Id name)
                                  (C.Op_type C.Total argTys resTy nullRange)

constTerm :: Token -> C.SORT -> C.TERM ()
constTerm opName sort = op opName [] sort `C.mkAppl` []

mkState :: Token -> C.TERM ()
mkState name = op name [] ctrlSort `C.mkAppl` []

mkVar :: C.VAR -> C.SORT -> C.TERM ()
mkVar name sort = C.toQualVar $ C.mkVarDecl name sort


trans :: C.VAR -> EVENT_ITEM -> C.VAR -> C.FORMULA ()
trans g e g' = C.mkPredication transPred [ confVar g
                                         , eventItem2CASLterm e
                                         , confVar g'
                                         ]

confVar :: C.VAR -> C.TERM ()
confVar g = C.mkVarTerm g confSort

ctrl :: C.TERM () -> C.TERM ()
ctrl g = ctrlOp `C.mkAppl` [g]

reach2 :: EVENT_NAMES -> C.VAR -> C.FORMULA ()
reach2 evts g = C.mkPredication reach2Pred [evts, confVar g]

reach3 :: EVENT_NAMES -> C.VAR -> C.VAR -> C.FORMULA ()
reach3 evts g g' = C.mkPredication reach3Pred [evts, confVar g, confVar g']

cSetCons :: EVENT_NAME -> EVENT_NAMES -> EVENT_NAMES
e `cSetCons` es = C.mkAppl (op (str2Token "__+__") [evtNameSort,evtNameSetSort] evtNameSetSort)
                           [constTerm (prefixEvtName e) evtNameSort, es]

cSetNil :: EVENT_NAMES
cSetNil = constTerm (str2Token "{}") evtNameSetSort

initPred, transPred, reach2Pred, reach3Pred :: C.PRED_SYMB
initPred   = C.mkQualPred (str2Id "init")
                          (C.Pred_type [confSort] nullRange)
transPred  = C.mkQualPred (str2Id "trans")
                          (C.Pred_type [confSort,evtSort,confSort] nullRange)
reach2Pred = C.mkQualPred (str2Id "reachable2")
                          (C.Pred_type [evtNameSetSort,confSort] nullRange)
reach3Pred = C.mkQualPred (str2Id "reachable3")
                          (C.Pred_type [evtNameSetSort,confSort,confSort] nullRange)

ctrlOp :: C.OP_SYMB
ctrlOp = op (str2Token "ctrl") [confSort] ctrlSort

evtNameOp :: C.OP_SYMB
evtNameOp = op (str2Token "evtName") [evtSort] evtNameSort

ctrlSort, evtSort, natSort, confSort, evtNameSort, evtNameSetSort :: C.SORT
ctrlSort       = str2Id "Ctrl"
evtSort        = str2Id "Evt"
natSort        = str2Id "Nat"
confSort       = str2Id "Conf"
evtNameSort    = str2Id "EvtName"
evtNameSetSort = str2Id "EvtNameSet"

sepCASL :: C.FORMULA f -> [C.FORMULA f]
sepCASL (C.Junction C.Con fs _) = concat (sepCASL <$> fs)
sepCASL f = [f]
