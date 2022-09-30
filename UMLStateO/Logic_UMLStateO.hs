{- |
Module      :  $Id$
Description :  Instance of class 'Logic' for the 'UMLStateO' logic
Copyright   :  (c) Tobias Rosenberger, Swansea University and Universit{'e} Grenoble Alpes 2022
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  TRosenberger@gmx.de
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

This module contains a logic for simple UML State Machines
fit for inclusion in a composite structure as in "UMLComp.Logic_UMLComp".

The institution for this logic (EDHML, see the EDHML datatype below for the formulae)
does not directly reflect UMLState Machines -- our surface language is syntactic sugar with some non-trivial desugaring.
The construction and the reasons behind it are explained in:
  Rosenberger, T., Knapp, A., & Roggenbach, M. (2022). An Institutional Approach to Communicating UML State Machines. In International Conference on Fundamental Approaches to Software Engineering (pp. 205-224). Springer, Cham. DOI: https://doi.org/10.1007/978-3-030-99429-7

The entry point for the abstract Syntax is 'BASIC_SPEC', for parsing 'parse_BASIC_SPEC' and for static analysis 'ana_BASIC_SPEC'. A translation to CASL is available in "Comorphisms.UMLState2CASL".

An example file can be found in "test/UMLTests/atmmod.het".
-}

{-# LANGUAGE DeriveDataTypeable    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- sometimes we want to name unused arguments for context
{-# OPTIONS_GHC -Wno-unused-matches #-}


module UMLStateO.Logic_UMLStateO where

import           Debug.Trace

import           Logic.Logic

import qualified CASL.AS_Basic_CASL                 as C
import qualified CASL.Formula                       as CF

import           ATerm.Conversion
import           Common.AnnoState
import           Common.DocUtils
import           Common.ExtSign
import           Common.GlobalAnnotations
import           Common.Id
import           Common.Lexer
import           Common.Parsec
import           Common.Result                      as R

import qualified Data.Data                          as D

import           Data.Functor                       (($>))
import           Data.Functor.Identity
import           Data.Map                           as Map
import           Data.Maybe                         (fromMaybe)
import           Data.Set                           as Set

import           Control.Monad                      (when)
import           Control.Monad.Trans                (lift)
import           Control.Monad.Trans.State          as S

import           Text.Parsec
import           Text.Parsec.Expr
import           Text.Parsec.String
import           Text.ParserCombinators.Parsec.Char

import           UMLComp.Logic_UMLComp              (composeId, composeStr,
                                                     composeTok, confSort,
                                                     evtSort, msgListSort,
                                                     msgSort, portSort,
                                                     token2Str)

traceVal :: Show a => a -> a
traceVal x = trace ("trace: " ++ show x) x


{- | The current module is all about this 'Logic'
     and the following instances for superclasses of 'Logic'.
-}
instance Logic UMLStateO StSub BASIC_SPEC Sentence StSyms StSymMaps Sign
               Morphism StSym StRawSym StProof

{- | A type level identifier for the present logic,
     used for instance resolution.
-}
data UMLStateO = UMLStateO deriving (Eq,Ord,Show,D.Data)

-- | We have no nontrivial signature morphisms.
type Morphism = Sign

type StSub     = ()
type StSyms    = ()
type StSymMaps = ()
type StSym     = Token
type StRawSym  = ()
type StProof   = ()

instance ShATermConvertible BASIC_SPEC where

instance Syntax UMLStateO BASIC_SPEC StSym StSyms StSymMaps where
  parsersAndPrinters   UMLStateO = makeDefault (parse_BASIC_SPEC [], pretty)
  parse_basic_spec     UMLStateO = Just $ parse_BASIC_SPEC []

instance Sentences      UMLStateO Sentence Sign Morphism Token where

instance StaticAnalysis UMLStateO BASIC_SPEC Sentence
                        () () Sign Morphism Token ()
  where
    basic_analysis _ = Just $ \ (spec,sign,annos) -> do
      (spec',sign) <- runStateT (ana_BASIC_SPEC spec) mempty
      let symSet = sign2SymSet sign
          extSign = ExtSign sign symSet
          annos  = []
      return (spec', extSign, annos)

instance Pretty Sign where

instance ShATermConvertible Sign where

type Arity = Int


type PORT_NAME = String
type EVENT_NAME = String

data MESSAGE_NAME = MsgName { portName :: PORT_NAME
                            , evtName  :: EVENT_NAME
                            } deriving (Eq,Ord,D.Data)
instance Show MESSAGE_NAME where
  show msg = portName msg ++ "." ++ evtName msg


instance Category Sign Morphism where
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

instance Language UMLStateO where -- default is OK

-- BEGIN Abstract Syntax
data BASIC_SPEC = Basic MACHINE_NAME [BASIC_ITEMS] deriving (Eq,Ord,Show,D.Data)
type MACHINE_NAME = Token
data BASIC_ITEMS = SigB SIG_ITEMS
                 | VarB VAR_ITEMS
                 | SenB SEN_ITEMS
                 | MsgB MESSAGE_ITEMS
                 deriving (Eq,Ord,Show,D.Data)

newtype VAR_ITEMS = VarIs [VAR_NAME] deriving (Eq,Ord,Show,D.Data)

data SEN_ITEMS = TransB TRANS_ITEM
               | InitB STATE GUARD
               deriving (Eq,Ord,Show,D.Data)
data Direction = In | Out deriving (Eq,Ord,Show,D.Data)
data MESSAGE_ITEMS = MsgIs Direction [MESSAGE_ITEM]
                   deriving (Eq,Ord,Show,D.Data)
data MESSAGE_ITEM = MsgI MESSAGE_NAME [VAR_NAME] deriving (Eq,Ord,Show,D.Data)
data TERM = VarT VAR_NAME
          | ConstT NAT_LIT
          | TERM :+ TERM
          | TERM :- TERM
          | TERM :* TERM
          | TERM :/ TERM
          deriving (Show,Ord,Eq,D.Data)
type VAR_NAME = Token


type NAT_LIT = Int

newtype SIG_ITEMS = StateS [STATE_ITEM]
                  deriving (Eq,Ord,Show,D.Data)
newtype STATE_ITEM = StateI STATE deriving (Eq,Ord,Show,D.Data)


type STATE = Token

data TRANS_ITEM = TransI STATE STATE TRANS_LABEL
                deriving (Eq,Ord,Show,D.Data)
data TRANS_LABEL = Label (Maybe TRIGGER) (Maybe GUARD) (Maybe ACTIONS)
                 deriving (Eq,Ord,Show,D.Data)
type TRIGGER = MESSAGE_ITEM
type GUARD = FORMULA

newtype ACTIONS = Acts [ACTION] deriving (Eq,Ord,Show,D.Data)
data ACTION = Assign VAR_NAME TERM
            | Send MESSAGE_INSTANCE
            deriving (Eq,Ord,Show,D.Data)
data MESSAGE_INSTANCE = MsgInst MESSAGE_NAME [TERM]
                      deriving (Eq,Ord,Show,D.Data)


-- data formulae, used for guards and assignments
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
-- END Abstract Syntax

instance Show COMP_OP where
  show Less      = "<"
  show LessEq    = "<="
  show Eq        = "=="
  show GreaterEq = ">="
  show Greater   = ">"


-- BEGIN parsing

parse_BASIC_SPEC :: [t0] -> PrefixMap -> GenParser Char st BASIC_SPEC
parse_BASIC_SPEC bi _ =
  Basic <$> parseName <*> (try parse_BASIC_ITEMS `sepBy` semiT << theEnd)

parseName :: ParsecT [Char] st Identity Token
parseName = do key "name"             << skipSmart
               name <- scanLetterWord << skipSmart
               asSeparator ";"
               return $ str2Token name

theEnd :: Parsec [Char] st [Char]
theEnd = optionMaybe (asSeparator ";") >> key "end"

parse_MESSAGE_ITEMS :: Parsec [Char] st MESSAGE_ITEMS
parse_MESSAGE_ITEMS = do
        direction <- (inS $> In) <|> (outS $> Out)
        msgItems  <- try parse_MESSAGE_ITEM `sepBy` asSeparator ","
        return $ MsgIs direction msgItems
  <?> "message items"

inS :: Parsec [Char] st Token
inS = try $ pluralKeyword "input" << skipSmart

outS :: Parsec [Char] st Token
outS = try $ pluralKeyword "output" << skipSmart

parse_MESSAGE_NAME :: Parsec [Char] st MESSAGE_NAME
parse_MESSAGE_NAME = do portN <- try scanLetterWord
                        string "."
                        evtN  <- scanLetterWord << skipSmart
                        return $ MsgName portN evtN
                   <?> "message name"

parse_MESSAGE_ITEM :: Parsec [Char] st MESSAGE_ITEM
parse_MESSAGE_ITEM = do
  msgName <- parse_MESSAGE_NAME
  maybeArgs <- optionMaybe $ do
    oParenT >> (parse_VAR_NAME << skipSmart) `sepBy` asSeparator "," << cParenT
  return $ MsgI msgName $ fromMaybe [] maybeArgs

parse_BASIC_ITEMS :: Parsec [Char] st BASIC_ITEMS
parse_BASIC_ITEMS =
      do SigB <$> parse_SIG_ITEMS
  <|> do SenB . TransB <$> parse_TRANS_ITEM
  <|> do SenB <$>
           ( key "init" >> ( InitB  <$> (parse_STATE_ITEM  << asSeparator ":")
                                    <*> parse_GUARD
                           )
           )
  <|> do MsgB <$> parse_MESSAGE_ITEMS
  <|> do VarB <$> parse_VAR_ITEMS

parse_VAR_ITEMS :: Parsec [Char] st VAR_ITEMS
parse_VAR_ITEMS =
  VarIs <$> ( pluralKeyword "var" >>
                ((parse_VAR_NAME << skipSmart) `sepBy` asSeparator ",")
            )

parse_SIG_ITEMS :: Parsec [Char] st SIG_ITEMS
parse_SIG_ITEMS = StateS <$> (parse_STATE_ITEMS *> parse_STATE_ITEMs)

parse_STATE_ITEMS :: CharParser st Token
parse_STATE_ITEMS = pluralKeyword "state" << skipSmart

parse_STATE_ITEMs :: Parsec [Char] st [STATE_ITEM]
parse_STATE_ITEMs = parse_STATE_ITEMItem `sepBy` asSeparator ","

parse_STATE_ITEMItem :: Parsec [Char] st STATE_ITEM
parse_STATE_ITEMItem = StateI <$> parse_STATE_ITEM << skipSmart

parse_TRANS_ITEM :: Parsec [Char] st TRANS_ITEM
parse_TRANS_ITEM = do key "trans"
                      s1 <- try parse_STATE_ITEM
                      try $ asSeparator "-->"
                      s2 <- parse_STATE_ITEM
                      asSeparator ":"
                      label <- parse_TRANS_LABEL
                      return $ TransI s1 s2 label

parse_TRANS_LABEL :: Parsec [Char] st TRANS_LABEL
parse_TRANS_LABEL = Label <$> optionMaybe parse_TRIGGER
                          <*> optionMaybe parse_GUARD
                          <*> optionMaybe parse_ACTIONS

parse_ACTIONS :: Parsec [Char] st ACTIONS
parse_ACTIONS = do
  asSeparator "/"
  asSeparator "{"
  as <- parse_ACTION `sepBy` asSeparator ";"
  asSeparator "}"
  return $ Acts as

parse_ACTION :: ParsecT [Char] u Identity ACTION
parse_ACTION = do try $ do v <- try parse_VAR_NAME
                           try $ asSeparator ":="
                           t <- parse_TERM
                           return $ Assign v t
           <|> do msgName <- parse_MESSAGE_NAME
                  maybeArgs <- optionMaybe $ do
                    oParenT >> parse_TERM `sepBy` asSeparator "," << cParenT
                  return $ Send $ MsgInst msgName $ fromMaybe [] maybeArgs
parse_TRIGGER :: Parsec [Char] st MESSAGE_ITEM
parse_TRIGGER = parse_MESSAGE_ITEM

parse_GUARD :: Parsec [Char] st FORMULA
parse_GUARD = oBracketT >> parse_FORMULA << cBracketT

parse_STATE_ITEM :: Parsec [Char] st Token
parse_STATE_ITEM = str2Token <$> (scanLetterWord << skipSmart)

parse_FORMULA :: Parsec [Char] st FORMULA
parse_FORMULA = buildExpressionParser ops simpForm <?> "formula" where
  ops = [ [preWordOp "not" NotF]
        , [symOpR "/\\" (:/\)]
        , [symOpR "\\/" (:\/)]
        , [symOpR "=>" (:=>), wordOp "if" (:<=), symOpR "<=>" (:<=>)]
        ]
  simpForm = do key "true"  >> return TrueF
         <|> do key "false" >> return FalseF
         <|> do CompF <$> try parse_TERM <*> try parse_COMP_OP <*> parse_TERM
         <|> do oParenT >> parse_FORMULA << cParenT

parse_TERM :: Parsec [Char] st TERM
parse_TERM = buildExpressionParser ops simpTerm <?> "term" where
  ops = [ [symOpL "*" (:*), symOpL "/" (:/)]
        , [symOpL "+" (:+), symOpL "-" (:-)]
        ]
  simpTerm = do VarT   <$> parse_VAR_NAME
         <|> do ConstT <$> parse_NAT_LIT
         <|> do oParenT >> parse_TERM << cParenT


parse_COMP_OP :: Parsec [Char] st COMP_OP
parse_COMP_OP = parseOpFrom [Less .. Greater]

parse_VAR_NAME :: Parsec [Char] st VAR_NAME
parse_VAR_NAME = str2Token <$> scanLetterWord << skipSmart

parse_NAT_LIT :: Parsec [Char] st NAT_LIT
parse_NAT_LIT = value 10 <$> getNumber << skipSmart


-- parse helpers

key :: String -> Parsec [Char] st String
key s = try (keyWord (string s) << skipSmart)


preWordOp :: String
          -> (a -> a)
          -> Operator [Char] st Data.Functor.Identity.Identity a
preWordOp w someOp = Prefix (key w >> return someOp)

symOpL :: String
       -> (a -> a -> a)
       -> Operator [Char] st Data.Functor.Identity.Identity a
symOpL s someOp = Infix (asSeparator s >> return someOp) AssocLeft

symOpR :: String
       -> (a -> a -> a)
       -> Operator [Char] st Data.Functor.Identity.Identity a
symOpR s someOp = Infix (asSeparator s >> return someOp) AssocRight

wordOp :: String
       -> (a -> a -> a)
       -> Operator [Char] st Data.Functor.Identity.Identity a
wordOp w someOp = Infix (key w >> return someOp) AssocRight

parseOpFrom :: Show a => [a] -> Parsec [Char] st a
parseOpFrom xs = choice [ const x <$> try (asSeparator $ show x)
                        | x <- xs
                        ]

-- END parsing

-- BEGIN static analysis
data Sign = Sign
  { nameS   :: Set MACHINE_NAME
  , statesS :: Set STATE
  , attrS   :: Set VAR_NAME
  , trigS   :: Map (MESSAGE_NAME, Arity) MESSAGE_ITEM
  , actsS   :: Map (MESSAGE_NAME, Arity) MESSAGE_ITEM
  , initS   :: [(STATE, GUARD)]
  , transS  :: [TRANS_ITEM]
  } deriving (Eq,Ord,Show)

type Sentence = ()

instance Monoid Sign where
  mempty = Sign mempty mempty mempty mempty mempty mempty mempty
  sign `mappend` sign' = Sign { nameS   = nameS   sign `mappend` nameS   sign'
                              , statesS = statesS sign `mappend` statesS sign'
                              , attrS   = attrS   sign `mappend` attrS   sign'
                              , trigS   = trigS   sign `mappend` trigS   sign'
                              , actsS   = actsS   sign `mappend` actsS   sign'
                              , initS   = initS   sign `mappend` initS   sign'
                              , transS  = transS  sign `mappend` transS  sign'
                              }

extractActs :: Map (MESSAGE_NAME, Arity) MESSAGE_ITEM -> Set Token
extractActs = Set.map actSym . Map.keysSet where
  actSym ((MsgName port evt), ar) = str2Token (port++"."++evt)

sign2SymSet :: Sign -> Set Token
sign2SymSet sign = statesS sign
       `Set.union` attrS   sign
       `Set.union` extractActs (trigS sign)
       `Set.union` extractActs (actsS sign)

type Check = StateT Sign Result

errC :: String -> Check a
errC s = lift $ fatal_error s nullRange

ana_BASIC_SPEC :: BASIC_SPEC -> Check BASIC_SPEC
ana_BASIC_SPEC (Basic name bs) = Basic <$> ana_MACHINE_NAME name
                                       <*> sequence (ana_BASIC_ITEMS <$> bs)

ana_MACHINE_NAME :: MACHINE_NAME -> Check MACHINE_NAME
ana_MACHINE_NAME name = do
  sign <- get
  let oldNames = nameS sign
  when (oldNames /= Set.empty && oldNames /= Set.singleton name)
    $ errC (   "Two machine names defined."
            ++ "This should not be possible according to the UMLStateO grammar."
            ++ "Please report this as a bug."
           )
  put $ sign { nameS = Set.singleton name }
  return name

ana_BASIC_ITEMS :: BASIC_ITEMS -> Check BASIC_ITEMS
ana_BASIC_ITEMS (SigB items) = SigB <$> ana_SIG_ITEMS items
ana_BASIC_ITEMS (SenB items) = SenB <$> ana_SEN_ITEMS items
ana_BASIC_ITEMS (MsgB items) = MsgB <$> ana_MESSAGE_ITEMS items
ana_BASIC_ITEMS (VarB items) = VarB <$> ana_VAR_ITEMS items

ana_VAR_ITEMS :: VAR_ITEMS -> Check VAR_ITEMS
ana_VAR_ITEMS (VarIs vs) = VarIs <$> sequence (ana_VAR_ITEM <$> vs)

ana_VAR_ITEM :: VAR_NAME -> Check VAR_NAME
ana_VAR_ITEM var = do
  sign <- get
  let vars = attrS sign
  when (var `Set.member` vars) $ errC ("variable declared twice: " ++ show var)
  put $ sign {
    attrS = var `Set.insert` vars
  }
  return var

ana_SIG_ITEMS :: SIG_ITEMS -> Check SIG_ITEMS
ana_SIG_ITEMS (StateS items) = StateS <$> sequence (ana_STATE_ITEM <$> items)

ana_SEN_ITEMS :: SEN_ITEMS -> Check SEN_ITEMS
ana_SEN_ITEMS (TransB tr) = TransB <$> ana_TRANS_ITEMS tr
ana_SEN_ITEMS (InitB st g) = do
  sign <- get
  let sts = statesS sign
      sign' = sign {
        initS = (st,g) : initS sign
      }
  if st `elem` sts
  then put sign' >> do return $ InitB st g
  else errC "Initial transition to undefined state."

ana_MESSAGE_ITEMS :: MESSAGE_ITEMS -> Check MESSAGE_ITEMS
ana_MESSAGE_ITEMS (MsgIs dir as) =
  MsgIs dir <$> sequence (ana_MESSAGE_ITEM dir <$> as)

ana_MESSAGE_ITEM :: Direction -> MESSAGE_ITEM -> Check MESSAGE_ITEM
ana_MESSAGE_ITEM dir e@(MsgI name vars) = do
  sign <- get
  when (dir == In)
    $ put $ sign {trigS = Map.insert (name, length vars) e $ trigS sign}
  when (dir == Out)
    $ put $ sign {actsS = Map.insert (name, length vars) e $ actsS sign}
  return e

ana_TRANS_ITEMS :: TRANS_ITEM -> Check TRANS_ITEM
ana_TRANS_ITEMS (TransI st1 st2 (Label trig g a)) = do
  sign <- get
  let trig'@(MsgI ename evars) = maybe (complEvt sign st1) id trig
      justTrig                 = Just trig'
      sts                      = statesS sign
      trigs                    = trigS sign
      ekey                     = (ename, length evars)
      insertVars [] set     = set
      insertVars (v:vs) set = insertVars vs (v `Set.insert` set)
      varsWithTvar             = insertVars evars $ attrS sign
      actSkip                  = Acts []
      checkWhenJust m res f    = maybe (return $ Just res) f m
  when (st1 `Set.notMember` sts) $
    errC ("transition out of undefined state: " ++ show st1)
  when (st2 `Set.notMember` sts) $
    errC ("transition into undefined state: "   ++ show st2)
  when (ekey `Map.notMember` trigs) $
    errC (    "transition with undefined trigger: "
           ++ show ekey ++ "\ntrigs: " ++ show trigs
         )
  g' <- checkWhenJust g TrueF $ \ gRaw -> do
    Just <$> ana_FORMULA varsWithTvar gRaw
  a' <- checkWhenJust a actSkip $ \ (Acts as) -> do
    Just . Acts <$> sequence (ana_ACTION (attrS sign) varsWithTvar <$> as)
  let l' = Label justTrig g' a'
      newTrans = TransI st1 st2 l'
      sign' = sign {
        transS = newTrans : transS sign
      }
  put sign'
  return newTrans

ana_FORMULA :: Set VAR_NAME -> FORMULA -> Check FORMULA
ana_FORMULA vars f@(CompF t1 someOp t2) = do t1' <- ana_TERM vars t1
                                             t2' <- ana_TERM vars t2
                                             return $ CompF t1' someOp t2'
ana_FORMULA vars (NotF f1)    = NotF <$> ana_FORMULA vars f1
ana_FORMULA vars (f1 :/\  f2) = foldl1 (:/\)  <$> (ana_FORMULA vars `traverse` [f1,f2])
ana_FORMULA vars (f1 :\/  f2) = foldl1 (:\/)  <$> (ana_FORMULA vars `traverse` [f1,f2])
ana_FORMULA vars (f1 :=>  f2) = foldl1 (:=>)  <$> (ana_FORMULA vars `traverse` [f1,f2])
ana_FORMULA vars (f1 :<=  f2) = foldl1 (:<=)  <$> (ana_FORMULA vars `traverse` [f1,f2])
ana_FORMULA vars (f1 :<=> f2) = foldl1 (:<=>) <$> (ana_FORMULA vars `traverse` [f1,f2])
ana_FORMULA vars f            = return f

ana_ACTION :: Set VAR_NAME -> Set VAR_NAME -> ACTION -> Check ACTION
ana_ACTION attrs allVars (Assign var tm) = do
  when (var `Set.notMember` attrs)
    $ errC ("assignment to undeclared attribute: " ++ token2Str var)
  ana_TERM allVars tm
  return $ Assign var tm
ana_ACTION  attrs allVars (Send inst@(MsgInst ename eterms)) = do
  sign <- get
  let ekey = (ename, length eterms)
      acts = actsS sign
  when (ekey `Map.notMember` acts) $ errC ("action with undeclared event: " ++ show ekey)
  sequence (ana_TERM allVars <$> eterms)
  return $ Send inst

ana_TERM :: Set VAR_NAME -> TERM -> Check TERM
ana_TERM vars t@(VarT var) = do
  when (var `Set.notMember` vars)
    $ errC ("reference to undeclared variable: " ++ show var)
  return t
ana_TERM vars t@(ConstT _) = return t
ana_TERM vars (a :+ b) = foldl1 (:+) <$> (ana_TERM vars `traverse` [a,b])
ana_TERM vars (a :- b) = foldl1 (:-) <$> (ana_TERM vars `traverse` [a,b])
ana_TERM vars (a :* b) = foldl1 (:*) <$> (ana_TERM vars `traverse` [a,b])
ana_TERM vars (a :/ b) = foldl1 (:/) <$> (ana_TERM vars `traverse` [a,b])

ana_STATE_ITEM :: STATE_ITEM -> Check STATE_ITEM
ana_STATE_ITEM (StateI st) = do
  sign <- get
  put $ sign {
    statesS = st `Set.insert` statesS sign
  }
  ana_MESSAGE_ITEM In  $ complEvt sign st
  ana_MESSAGE_ITEM Out $ complEvt sign st
  return $ StateI st

complEvt :: Sign -> STATE -> TRIGGER
complEvt sign st = MsgI name []
  where
    name = MsgName { portName = composeStr ["compl", machName sign]
                   , evtName  = composeStr ["compl", token2Str st ]
                   }
-- END static analysis
machName :: Sign -> String
machName sign
  | [Token m _] <- Set.elems $ nameS sign
  = m
  | otherwise
  = error (    "Machine does not have exactly one name after static analysis. "
            ++ "Please report this as a bug."
          )

str2Id :: String -> Id
str2Id = token2Id . str2Token

token2Id :: Token -> Id
token2Id tok   = Id [tok] [] nullRange

str2Token :: String -> Token
str2Token name = Token name nullRange
