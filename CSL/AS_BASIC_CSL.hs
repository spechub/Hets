{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  $Header$
Description :  Abstract syntax for EnCL
Copyright   :  (c) Dominik Dietrich, Ewaryst Schulz, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  experimental
Portability :  portable

This module contains the abstract syntax types for EnCL as well as the
predefined operator configuration.

-}

module CSL.AS_BASIC_CSL
    ( EXPRESSION (..)     -- datatype for numerical expressions (e.g. polynomials)
    , EXTPARAM (..)       -- datatype for extended parameters (e.g. [I=0])
    , BASIC_ITEM (..)    -- Items of a Basic Spec
    , BASIC_SPEC (..)     -- Basic Spec
    , SYMB_ITEMS (..)     -- List of symbols
    , SYMB (..)           -- Symbols
    , SYMB_MAP_ITEMS (..) -- Symbol map
    , SYMB_OR_MAP (..)    -- Symbol or symbol map
    , OPNAME (..)         -- predefined operator names
    , OPID (..)           -- identifier for operators
    , ConstantName (..)   -- names of user-defined constants
    , OP_ITEM (..)        -- operator declaration
    , VAR_ITEM (..)       -- variable declaration
    , VarDecl (..)        -- variable declaration in assignment
    , OpDecl (..)         -- operator declaration in assignment
    , EPDecl (..)         -- extparam declaration
    , EPVal (..)          -- extparam values
    , getEPVarRef
    , Domain              -- domains for variable declarations
    , EPDomain            -- domains for extended parameter declarations
    , GroundConstant (..) -- constants for domain formation
    , cmpFloatToInt       -- comparer for APFloat with APInt
    , AssDefinition (..)  -- A function or constant definition
    , InstantiatedConstant(..) -- for function constants we need to store the
                               -- instantiation
    , CMD (..)            -- Command datatype
    , OperatorState (..)  -- Class providing operator lookup



    , OpInfo (..)         -- Type for Operator information
    , BindInfo (..)       -- Type for Binder information
    , operatorInfo        -- Operator information for pretty printing
                          -- and static analysis
    , operatorInfoMap     -- allows efficient lookup of ops by printname
    , operatorInfoNameMap -- allows efficient lookup of ops by opname
    , operatorBindInfoMap
    , mergeOpArityMap     -- for combining two operator arity maps
    , getOpInfoMap
    , getOpInfoNameMap
    , getBindInfoMap
    , lookupOpInfo
    , lookupOpInfoForParsing
    , lookupBindInfo
    , APInt, APFloat      -- arbitrary precision numbers
    , toFraction, fromFraction
    , OpInfoMap
    , OpInfoNameMap
    , BindInfoMap
    , showOPNAME
    , maxPrecedence
    ) where

import Common.Id as Id
import Common.AS_Annotation as AS_Anno

import qualified Data.Map as Map

import Data.Ratio

import CSL.TreePO


-- ---------------------------------------------------------------------------
-- * EnCL Basic Data Structures and utils
-- ---------------------------------------------------------------------------

-- Arbitrary precision numbers
type APInt = Integer
type APFloat = Rational

cmpFloatToInt :: APFloat -> APInt -> Ordering
cmpFloatToInt a b = compare a $ fromFraction b 1

fromFraction :: Integer -> Integer -> APFloat
fromFraction = (%)

toFraction :: APFloat -> (Integer, Integer)
toFraction r = (numerator r, denominator r)

-- | operator symbol declaration
data OP_ITEM = Op_item [Id.Token] Id.Range
               deriving Show

-- | variable symbol declaration
data VAR_ITEM = Var_item [Id.Token] Domain Id.Range
                deriving Show

newtype BASIC_SPEC = Basic_spec [AS_Anno.Annoted (BASIC_ITEM)]
                  deriving Show

data GroundConstant = GCI APInt | GCR APFloat deriving Show

cmpGCs :: GroundConstant -> GroundConstant -> Ordering
cmpGCs (GCI a) (GCI b) = compare a b
cmpGCs (GCR a) (GCR b) = compare a b
cmpGCs (GCI a) (GCR b) = swapCompare $ cmpFloatToInt b a
cmpGCs (GCR a) (GCI b) = cmpFloatToInt a b

instance Eq GroundConstant where
    a == b = cmpGCs a b == EQ

instance Ord GroundConstant where
    compare = cmpGCs

instance Continuous GroundConstant

type Domain = SetOrInterval GroundConstant
type EPDomain = ClosedInterval EPVal

-- | A constant or function definition
data AssDefinition = ConstDef EXPRESSION | FunDef [String] EXPRESSION
              deriving (Eq, Ord, Show)

data InstantiatedConstant = InstantiatedConstant
    { constName :: ConstantName
    , instantiation :: [EXPRESSION] } deriving (Show, Eq, Ord)

-- | basic items: an operator, extended parameter or variable declaration or an axiom
data BASIC_ITEM =
    Op_decl OP_ITEM
    | EP_decl [(Id.Token, EPDomain)]
    | EP_domdecl [(Id.Token, APInt)]
    | EP_defval [(Id.Token, APInt)]
    | Var_decls [VAR_ITEM]
    | Axiom_item (AS_Anno.Annoted CMD)
    deriving Show

-- | Extended Parameter Datatype
data EXTPARAM = EP Id.Token String APInt deriving (Eq, Ord, Show)

data EPDecl = EPDecl Id.Token -- name
              EPDomain -- a domain over which the ep ranges
              (Maybe APInt) -- evtl. a default value
              deriving (Eq, Ord, Show)

-- | Extended Parameter value may be an integer or a reference to an 'EPDomVal'.
-- This type is used for the domain specification of EPs (see 'EPDomain').
data EPVal = EPVal APInt | EPConstRef Id.Token deriving (Eq, Ord, Show)

getEPVarRef :: EPVal -> Maybe Id.Token
getEPVarRef (EPConstRef tok) = Just tok
getEPVarRef _ = Nothing

data OPNAME =
    -- arithmetic operators
    OP_mult | OP_div | OP_plus | OP_minus | OP_neg | OP_pow
    -- roots, trigonometric and other operators
  | OP_fthrt | OP_sqrt | OP_abs | OP_max | OP_min | OP_sign
  | OP_cos | OP_sin | OP_tan | OP_cot | OP_Pi
  | OP_reldist

  -- special CAS operators
  | OP_minimize | OP_minloc | OP_maximize | OP_maxloc | OP_factor | OP_approx
  | OP_divide | OP_factorize | OP_int | OP_rlqe | OP_simplify | OP_solve

  -- comparison predicates
  | OP_neq | OP_lt | OP_leq | OP_eq | OP_gt | OP_geq | OP_convergence
  | OP_reldistLe

  -- containment predicate
  | OP_in

  -- special CAS constants
  | OP_undef | OP_failure

  -- boolean constants and connectives
  | OP_false | OP_true | OP_not | OP_and | OP_or | OP_impl

  -- quantifiers
  | OP_ex | OP_all

  -- types
  | OP_hastype | OP_real

    deriving (Eq, Ord)

instance Show OPNAME where
    show = showOPNAME

showOPNAME :: OPNAME -> String
showOPNAME x =
        case x of
          OP_neq -> "!="
          OP_mult -> "*"
          OP_plus -> "+"
          OP_minus -> "-"
          OP_neg -> "-"
          OP_div -> "/"
          OP_lt -> "<"
          OP_leq -> "<="
          OP_eq -> "="
          OP_gt -> ">"
          OP_geq -> ">="
          OP_Pi -> "Pi"
          OP_pow -> "^"
          OP_abs -> "abs"
          OP_sign -> "sign"
          OP_all -> "all"
          OP_and -> "and"
          OP_convergence -> "convergence"
          OP_cos -> "cos"
          OP_divide -> "divide"
          OP_ex -> "ex"
          OP_factor -> "factor"
          OP_factorize -> "factorize"
          OP_fthrt -> "fthrt"
          OP_impl -> "impl"
          OP_int -> "int"
          OP_max -> "max"
          OP_maximize -> "maximize"
          OP_maxloc -> "maxloc"
          OP_min -> "min"
          OP_minimize -> "minimize"
          OP_minloc -> "minloc"
          OP_not -> "not"
          OP_or -> "or"
          OP_reldist -> "reldist"
          OP_reldistLe -> "reldistLe"
          OP_rlqe -> "rlqe"
          OP_simplify -> "simplify"
          OP_sin -> "sin"
          OP_solve -> "solve"
          OP_sqrt -> "sqrt"
          OP_tan -> "tan"
          OP_cot -> "cot"
          OP_false -> "false"
          OP_true -> "true"
          OP_in -> "in"
          OP_approx -> "approx"

          OP_undef -> "undef"
          OP_failure -> "fail"

          OP_hastype -> "::"
          OP_real -> "real"

data OPID = OpId OPNAME | OpUser ConstantName deriving (Eq, Ord, Show)

-- | We differentiate between simple constant names and indexed constant names
-- resulting from the extended parameter elimination.
data ConstantName = SimpleConstant String | ElimConstant String Int
                    deriving (Eq, Ord, Show)

{-
instance Show OPID where
    show (OpId n) = show n
    show (OpUser s) = show s

instance Show ConstantName where
    show (SimpleConstant s) = s
    show (ElimConstant s i) = if i > 0 then s ++ "__" ++ show i else s
-}

-- | Datatype for expressions
data EXPRESSION =
    Var Id.Token
  | Op OPID [EXTPARAM] [EXPRESSION] Id.Range
  -- TODO: don't need lists anymore, they should be removed soon
  | List [EXPRESSION] Id.Range
  | Interval Double Double Id.Range
  | Int APInt Id.Range
  | Rat APFloat Id.Range
  deriving (Eq, Ord, Show)

data VarDecl = VarDecl Id.Token (Maybe Domain) deriving (Show, Eq, Ord)

data OpDecl = OpDecl ConstantName [EXTPARAM] [VarDecl] Id.Range
              deriving (Show, Eq, Ord)

-- TODO: add Range-support to this type
data CMD = Ass OpDecl EXPRESSION
         | Cmd String [EXPRESSION]
         | Sequence [CMD] -- program sequence
         | Cond [(EXPRESSION, [CMD])]
         | Repeat EXPRESSION [CMD] -- constraint, statements
           deriving (Show, Eq, Ord)

-- | symbol lists for hiding
data SYMB_ITEMS = Symb_items [SYMB] Id.Range
                  -- pos: SYMB_KIND, commas
                  deriving (Show, Eq)

-- | symbol for identifiers
newtype SYMB = Symb_id Id.Token
            -- pos: colon
            deriving (Show, Eq)

-- | symbol maps for renamings
data SYMB_MAP_ITEMS = Symb_map_items [SYMB_OR_MAP] Id.Range
                      -- pos: SYMB_KIND, commas
                      deriving (Show, Eq)

-- | symbol map or renaming (renaming then denotes the identity renaming)
data SYMB_OR_MAP = Symb SYMB
                 | Symb_map SYMB SYMB Id.Range
                   -- pos: "|->"
                   deriving (Show, Eq)

-- ---------------------------------------------------------------------------
-- * Predefined Operators: info for parsing/printing and static analysis
-- ---------------------------------------------------------------------------

data BindInfo = BindInfo { bindingVarPos :: [Int] -- ^ argument positions of
                                                  -- binding variables
                         , boundBodyPos :: [Int] -- ^ argument positions of
                                                 -- bound terms
                         } deriving (Eq, Ord, Show)

data OpInfo = OpInfo { prec :: Int -- ^ precedence between 0 and maxPrecedence
                     , infx :: Bool -- ^ True = infix
                     , arity :: Int -- ^ the operator arity
                     , foldNAry :: Bool -- ^ True = fold nary-applications
                                        -- during construction into binary ones
                     , opname :: OPNAME -- ^ The actual operator name
                     , bind :: Maybe BindInfo -- ^ More info for binders
                     } deriving (Eq, Ord, Show)

type ArityMap = Map.Map Int OpInfo
type OpInfoArityMap a = Map.Map a ArityMap
type OpInfoMap = OpInfoArityMap String
type OpInfoNameMap = OpInfoArityMap OPNAME
type BindInfoMap = Map.Map String OpInfo


-- | Merges two OpInfoArityMaps together with the first map as default map
-- and the second overwriting the default values
mergeOpArityMap :: Ord a => OpInfoArityMap a -> OpInfoArityMap a
                -> OpInfoArityMap a
mergeOpArityMap = flip $ Map.unionWith Map.union


-- | Mapping of operator names to arity-'OpInfo'-maps (an operator may
--   behave differently for different arities).
getOpInfoMap :: (OpInfo -> String) -> [OpInfo] -> OpInfoMap
getOpInfoMap pf oinfo = foldl f Map.empty oinfo
    where f m oi = Map.insertWith Map.union (pf oi)
                   (Map.fromList [(arity oi, oi)]) m

-- | Same as operatorInfoMap but with keys of type OPNAME instead of String
getOpInfoNameMap :: [OpInfo] -> OpInfoNameMap
getOpInfoNameMap oinfo = foldl f Map.empty oinfo
    where f m oi = Map.insertWith Map.union (opname oi)
                   (Map.fromList [(arity oi, oi)]) m

-- | a special map for binders which have to be unique for each name
-- (no different arities).
getBindInfoMap :: [OpInfo] -> BindInfoMap
getBindInfoMap oinfo = foldl f Map.empty oinfo
    where f m oi@(OpInfo{bind = Just _}) =
              Map.insertWith cf (show $ opname  oi) oi m
          f m _ = m
          cf a _ = error $ "operatorBindInfoMap: duplicate entry for "
                   ++ (show $ opname  a)


-- | opInfoMap for the predefined 'operatorInfo'
operatorInfoMap :: OpInfoMap
operatorInfoMap = getOpInfoMap (show . opname) operatorInfo

-- | opInfoNameMap for the predefined 'operatorInfo'
operatorInfoNameMap :: OpInfoNameMap
operatorInfoNameMap = getOpInfoNameMap operatorInfo


operatorBindInfoMap :: BindInfoMap
operatorBindInfoMap = getBindInfoMap operatorInfo

-- | Mapping of operator names to arity-'OpInfo'-maps (an operator may
--   behave differently for different arities).
operatorInfo :: [OpInfo]
operatorInfo =
    let -- arity (-1 means flex), precedence, infix
        toSgl n i p = OpInfo { prec = if p == 0 then maxPrecedence else p
                             , infx = p > 0
                             , arity = i
                             , opname = n
                             , foldNAry = False
                             , bind = Nothing
                             }
        toSglBind n i bv bb =
            OpInfo { prec = maxPrecedence
                   , infx = False
                   , arity = i
                   , opname = n
                   , foldNAry = False
                   , bind = Just $ BindInfo [bv] [bb]
                   }
        -- arityX simple ops
        aX i s = toSgl s i 0
        -- arityflex simple ops
        aflex = aX (-1)
        -- arity2 binder
        a2bind bv bb s = toSglBind s 2 bv bb
        -- arity4 binder
        a4bind bv bb s = toSglBind s 4 bv bb
        -- arity2 infix with precedence
        a2i p s = toSgl s 2 p
    in map (aX 0) [ OP_failure, OP_undef, OP_Pi, OP_true, OP_false, OP_real ]
           ++ map (aX 1)
                  [ OP_neg, OP_cos, OP_sin, OP_tan, OP_cot, OP_sqrt, OP_fthrt
                  , OP_abs, OP_sign, OP_simplify, OP_rlqe, OP_factor
                  , OP_factorize ]
           ++ map (a2i 5) [ OP_hastype ]
           ++ map (a2bind 0 1) [ OP_ex, OP_all ]
           ++ map (a2i 30) [ OP_or, OP_impl ]
           ++ map (a2i 40) [ OP_and ]
           ++ map (a2i 50) [ OP_eq, OP_gt, OP_leq, OP_geq, OP_neq, OP_lt, OP_in]
           ++ map (a2i 60) [ OP_plus ]
           ++ map (a2i 70) [ OP_minus ]
           ++ map (a2i 80) [OP_mult]
           ++ map (a2i 90) [OP_div]
           ++ map (a2i 100) [OP_pow]
           ++ map (aX 2)
                  [ OP_int, OP_divide, OP_solve, OP_convergence, OP_reldist
                  , OP_approx]
           ++ map (aX 3) [OP_reldistLe]
           ++ map aflex [ OP_min, OP_max ]
           ++ map (a2bind 1 0) [ OP_maximize, OP_minimize ]
           ++ map (a4bind 1 0) [ OP_maxloc, OP_minloc ]

maxPrecedence :: Int
maxPrecedence = 120


-- ---------------------------------------------------------------------------
-- * OpInfo lookup utils
-- ---------------------------------------------------------------------------

class OperatorState a where
    addVar :: a -> String -> a
    addVar = const
    isVar :: a -> String -> Bool
    isVar _ _ = False
    lookupOperator :: a
                   -> String -- ^ operator name
                   -> Int -- ^ operator arity
                   -> Either Bool OpInfo
    lookupBinder :: a
                   -> String -- ^ binder name
                   -> Maybe OpInfo

instance OperatorState () where
    lookupOperator _ = lookupOpInfoForParsing operatorInfoMap
    lookupBinder _ = flip Map.lookup operatorBindInfoMap

instance OperatorState (OpInfoMap, BindInfoMap) where
    lookupOperator = lookupOpInfoForParsing . fst
    lookupBinder = flip Map.lookup . snd



-- | For the given name and arity we lookup an 'OpInfo', where arity=-1
-- means flexible arity. If an operator is registered for the given
-- string but not for the arity we return: Left True.
-- This function is designed for the lookup of operators in not statically
-- analyzed terms. For statically analyzed terms use lookupOpInfo.
lookupOpInfoForParsing :: OpInfoMap -- ^ map to be used for lookup
             -> String -- ^ operator name
             -> Int -- ^ operator arity
             -> Either Bool OpInfo
lookupOpInfoForParsing oiMap op arit =
    case Map.lookup op oiMap of
      Just oim ->
          case Map.lookup arit oim of
            Just x -> Right x
            Nothing ->
                case Map.lookup (-1) oim of
                  Just x -> Right x
                  _ -> Left True
      _ -> Left False

-- | For the given name and arity we lookup an 'OpInfo', where arity=-1
-- means flexible arity. If an operator is registered for the given
-- string but not for the arity we return: Left True.
lookupOpInfo :: OpInfoNameMap -> OPID -- ^ operator id
             -> Int -- ^ operator arity
             -> Either Bool OpInfo
lookupOpInfo oinm (OpId op) arit =
    case Map.lookup op oinm of
      Just oim ->
          case Map.lookup arit oim of
            Just x -> Right x
            Nothing ->
                case Map.lookup (-1) oim of
                  Just x -> Right x
                  _ -> Left True
      _ -> error $ "lookupOpInfo: no opinfo for " ++ show op
lookupOpInfo _ (OpUser _) _ = Left False

-- | For the given name and arity we lookup an 'BindInfo', where arity=-1
-- means flexible arity.
lookupBindInfo :: OpInfoNameMap -> OPID -- ^ operator name
             -> Int -- ^ operator arity
             -> Maybe BindInfo
lookupBindInfo oinm (OpId op) arit =
    case Map.lookup op oinm of
      Just oim ->
          case Map.lookup arit oim of
            Just x -> bind x
            _ -> Nothing
      _ -> error $ "lookupBindInfo: no opinfo for " ++ show op
lookupBindInfo _ (OpUser _) _ = Nothing

