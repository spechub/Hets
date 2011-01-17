{- |
Module      :  $Header$
Description :  Abstract syntax for CSL
Copyright   :  (c) Dominik Dietrich, Ewaryst Schulz, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  experimental
Portability :  portable

This file contains the abstract syntax for CSL as well as pretty printer for it.

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
    , Domain (..)         -- domains for variable declarations
    , GroundConstant (..) -- constants for domain formation
    , AssDefinition (..)  -- A function or constant definition
    , getDefiniens        -- accessor function for AssDefinition
    , getArguments        -- accessor function for AssDefinition
    , isFunDef            -- accessor function for AssDefinition
    , mkDefinition        -- constructor for AssDefinition
    , CMD (..)            -- Command datatype
    , mkOp                -- Simple Operator constructor
    , mkPredefOp          -- Simple Operator constructor for predefined ops
    , toElimConst         -- Constant naming for elim constants, see Analysis.hs
    , OpInfo (..)         -- Type for Operator information
    , BindInfo (..)       -- Type for Binder information
    , operatorInfo        -- Operator information for pretty printing
                          -- and static analysis
    , operatorInfoMap     -- allows efficient lookup of ops by printname
    , operatorInfoNameMap -- allows efficient lookup of ops by opname
    , lookupOpInfoForStatAna
    , lookupBindInfo
    , APInt, APFloat      -- arbitrary precision numbers
    -- Printer
    , printExpression
    , printCMD
    , printAssDefinition
    , printConstantName
    , ConstantPrinter (..)
    , toArgList
    ) where

import Common.Id as Id
import Common.Doc
import Common.DocUtils
import Common.AS_Annotation as AS_Anno
import qualified Data.Map as Map
import Control.Monad

-- Arbitrary precision numbers
type APInt = Integer
-- TODO: use an arbitrary precision float here:
-- The use of Other floats (such as Double) requires an instance for
-- ShATermConvertible in Common.ATerm.ConvInstances
type APFloat = Double

-- | A simple operator constructor from given operator name and arguments
mkOp :: String -> [EXPRESSION] -> EXPRESSION
mkOp s el = Op (OpUser $ SimpleConstant s) [] el nullRange

-- | A simple operator constructor from given operator id and arguments
mkPredefOp :: OPNAME -> [EXPRESSION] -> EXPRESSION
mkPredefOp n el = Op (OpId n) [] el nullRange

-- * CSL Basic Data Structures

-- | operator symbol declaration
data OP_ITEM = Op_item [Id.Token] Id.Range
               deriving Show

-- | variable symbol declaration
data VAR_ITEM = Var_item [Id.Token] Domain Id.Range
                deriving Show

newtype BASIC_SPEC = Basic_spec [AS_Anno.Annoted (BASIC_ITEM)]
                  deriving Show

data GroundConstant = GCI APInt | GCR APFloat deriving (Eq, Ord, Show)

-- | A finite set or an interval. True = closed, False = opened
data Domain = Set [GroundConstant]
            | IntVal (GroundConstant, Bool) (GroundConstant, Bool)
              deriving (Eq, Ord, Show)

-- | A constant or function definition
data AssDefinition = ConstDef EXPRESSION | FunDef [String] EXPRESSION
              deriving (Eq, Ord, Show)

mkDefinition :: [String] -> EXPRESSION -> AssDefinition
mkDefinition l e = if null l then ConstDef e else FunDef l e

getDefiniens :: AssDefinition -> EXPRESSION
getDefiniens (ConstDef e) = e
getDefiniens (FunDef _ e) = e

getArguments :: AssDefinition -> [String]
getArguments (FunDef l _) = l
getArguments _ = []

isFunDef :: AssDefinition -> Bool
isFunDef (FunDef _ _) = True
isFunDef _ = False

-- | basic items: an operator or variable declaration or an axiom
data BASIC_ITEM =
    Op_decl OP_ITEM
    | Var_decls [VAR_ITEM]
    | Axiom_item (AS_Anno.Annoted CMD)
    deriving Show

-- | Extended Parameter Datatype
data EXTPARAM = EP Id.Token String APInt deriving (Eq, Ord, Show)

data OPNAME = OP_mult -- arithmetic operators
            | OP_div | OP_plus | OP_minus | OP_neg | OP_pow

            -- roots, trigonometric and other operators
            | OP_fthrt | OP_sqrt
            | OP_abs | OP_max | OP_min | OP_sign
            | OP_cos | OP_sin | OP_tan | OP_Pi

            -- special CAS operators
            | OP_maximize | OP_factor
            | OP_divide | OP_factorize | OP_int | OP_rlqe | OP_simplify | OP_solve

            -- comparison predicates
            | OP_neq | OP_lt | OP_leq | OP_eq | OP_gt | OP_geq | OP_convergence

            -- boolean constants and connectives
            | OP_false | OP_true | OP_not | OP_and | OP_or | OP_impl

            -- quantifiers
            | OP_ex | OP_all

              deriving (Eq, Ord)

instance Show OPNAME where
    show x =
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
          OP_min -> "min"
          OP_not -> "not"
          OP_or -> "or"
          OP_rlqe -> "rlqe"
          OP_simplify -> "simplify"
          OP_sin -> "sin"
          OP_solve -> "solve"
          OP_sqrt -> "sqrt"
          OP_tan -> "tan"
          OP_false -> "False"
          OP_true -> "True"

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

toElimConst :: ConstantName -> Int -> ConstantName
toElimConst (SimpleConstant s) i = ElimConstant s i
toElimConst ec _ = error $ "toElimConst: already an elim const " ++ show ec

-- | Datatype for expressions
data EXPRESSION =
    Var Id.Token
  | Op OPID [EXTPARAM] [EXPRESSION] Id.Range
  -- TODO: don't need lists anymore, they should be removed soon
  | List [EXPRESSION] Id.Range
  | Interval APFloat APFloat Id.Range
  | Int APInt Id.Range
  | Double APFloat Id.Range
  deriving (Eq, Ord, Show)

-- | If the expression list is a variable list the list of the variable names
-- is returned.
toArgList :: [EXPRESSION] -> [String]
toArgList [] = []
toArgList (Var tok:l) = tokStr tok : toArgList l
toArgList (x:_) = error $ "toArgList: unsupported as argument " ++ show (pretty x)

-- TODO: add Range-support to this type
data CMD = Ass EXPRESSION EXPRESSION
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

-- * Predefined Operators: info for parsing/printing and static analysis

data BindInfo = BindInfo { bindingVarPos :: [Int] -- ^ argument positions of
                                                  -- binding variables
                         , boundBodyPos :: [Int] -- ^ argument positions of
                                                 -- bound terms
                         } deriving (Eq, Ord, Show)

data OpInfo = OpInfo { prec :: Int -- ^ precedence between 0 and 9
                     , infx :: Bool -- ^ True = infix
                     , arity :: Int -- ^ the operator arity
                     , opname :: OPNAME -- ^ The actual operator name
                     , bind :: Maybe BindInfo -- ^ More info for binders
                     } deriving (Eq, Ord, Show)


-- | Mapping of operator names to arity-'OpInfo'-maps (an operator may
--   behave differently for different arities).
operatorInfoMap :: Map.Map String (Map.Map Int OpInfo)
operatorInfoMap = foldl f Map.empty operatorInfo
    where f m oi = Map.insertWith Map.union (show $ opname oi)
                   (Map.fromList [(arity oi, oi)]) m

-- | Same as operatorInfoMap but with keys of type OPNAME instead of String
operatorInfoNameMap :: Map.Map OPNAME (Map.Map Int OpInfo)
operatorInfoNameMap = foldl f Map.empty operatorInfo
    where f m oi = Map.insertWith Map.union (opname oi)
                   (Map.fromList [(arity oi, oi)]) m
      


-- | Mapping of operator names to arity-'OpInfo'-maps (an operator may
--   behave differently for different arities).
operatorInfo :: [OpInfo]
operatorInfo =
    let -- arity (-1 means flex), precedence, infix
        toSgl n i p fx = OpInfo p fx i n Nothing
        toSglBind n i p fx bv bb =
            OpInfo p fx i n $ Just $ BindInfo [bv] [bb]
        -- arityflex simple ops
        aflex s = toSgl s (-1) 0 False
        -- arity0 simple ops
        a0 s = toSgl s 0 0 False
        -- arity1 simple ops
        a1 s = toSgl s 1 0 False
        -- arity2 simple ops
        a2 s = toSgl s 2 0 False
        -- arity2 binder
        a2bind bv bb s = toSglBind s 2 0 False bv bb
        -- arity2 infix with precedence
        a2i p s = toSgl s 2 p True
    in map a0 [ OP_Pi, OP_true, OP_false ]
           ++ map a1 [ OP_neg, OP_cos, OP_sin, OP_tan, OP_sqrt, OP_fthrt, OP_abs
                     , OP_sign, OP_simplify, OP_rlqe, OP_factor, OP_factorize ]
           ++ map (a2i 2) [ OP_ex, OP_all, OP_and, OP_or, OP_impl ]
           ++ map (a2i 3) [ OP_eq, OP_gt, OP_leq, OP_geq, OP_neq, OP_lt]
           ++ map (a2i 4) [ OP_plus, OP_minus]
           ++ map (a2i 5) [OP_div, OP_mult]
           ++ map (a2i 6) [OP_pow]
           ++ map a2 [ OP_int, OP_divide, OP_solve, OP_convergence ]
           ++ map aflex [ OP_min, OP_max ]
           ++ map (a2bind 1 0) [ OP_maximize ]

-- | For the given name and arity we lookup an 'OpInfo', where arity=-1
-- means flexible arity. If an operator is registered for the given
-- string but not for the arity we return: Left True.
-- This function is designed for the lookup of operators in not statically
-- analyzed terms. For statically analyzed terms use lookupOpInfo.
lookupOpInfoForStatAna :: String -- ^ operator name
             -> Int -- ^ operator arity
             -> Either Bool OpInfo
lookupOpInfoForStatAna op arit =
    case Map.lookup op operatorInfoMap of
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
lookupOpInfo :: OPID -- ^ operator id
             -> Int -- ^ operator arity
             -> Either Bool OpInfo
lookupOpInfo (OpId op) arit =
    case Map.lookup op operatorInfoNameMap of
      Just oim ->
          case Map.lookup arit oim of
            Just x -> Right x
            Nothing ->
                case Map.lookup (-1) oim of
                  Just x -> Right x
                  _ -> Left True
      _ -> error $ "lookupOpInfo: no opinfo for " ++ show op
lookupOpInfo (OpUser _) _ = Left False

-- | For the given name and arity we lookup an 'BindInfo', where arity=-1
-- means flexible arity.
lookupBindInfo :: OPID -- ^ operator name
             -> Int -- ^ operator arity
             -> Maybe BindInfo
lookupBindInfo (OpId op) arit =
    case Map.lookup op operatorInfoNameMap of
      Just oim ->
          case Map.lookup arit oim of
            Just x -> bind x
            _ -> Nothing
      _ -> error $ "lookupBindInfo: no opinfo for " ++ show op
lookupBindInfo (OpUser _) _ = Nothing

-- * Pretty Printing

instance Pretty Domain where
    pretty = printDomain
instance Pretty OP_ITEM where
    pretty = printOpItem
instance Pretty VAR_ITEM where
    pretty = printVarItem
instance Pretty BASIC_SPEC where
    pretty = printBasicSpec
instance Pretty BASIC_ITEM where
    pretty = printBasicItems
instance Pretty EXTPARAM where
    pretty = printExtparam
instance Pretty EXPRESSION where
    pretty = head . printExpression
instance Pretty SYMB_ITEMS where
    pretty = printSymbItems
instance Pretty SYMB where
    pretty = printSymbol
instance Pretty SYMB_MAP_ITEMS where
    pretty = printSymbMapItems
instance Pretty SYMB_OR_MAP where
    pretty = printSymbOrMap
instance Pretty CMD where
    pretty = head . printCMD
instance Pretty ConstantName where
    pretty = printConstantName
instance Pretty AssDefinition where
    pretty = head . printAssDefinition
instance Pretty OPID where
    pretty = head . printOPID


-- | A monad for printing of constants. This turns the pretty printing facility
-- more flexible w.r.t. the output of 'ConstantName'.
class Monad m => ConstantPrinter m where
    printConstant :: ConstantName -> m Doc
    printConstant = return . text . show

-- | The default ConstantName printer
printConstantName :: ConstantName -> Doc
printConstantName (SimpleConstant s) = text s
printConstantName (ElimConstant s i) =
    text $ if i > 0 then s ++ "__" ++ show i else s

printAssDefinition :: ConstantPrinter m => AssDefinition -> m Doc
printAssDefinition (ConstDef e) = printExpression e >>= return . (text "->" <+>)
printAssDefinition (FunDef l e) = do
  ed <- printExpression e
  return $ (parens $ sepByCommas $ map text l) <+> text "->" <+> ed

printOPID :: ConstantPrinter m => OPID -> m Doc
printOPID (OpUser c) = printConstant c
printOPID oi = return $ text $ show oi

instance ConstantPrinter []

printCMD :: ConstantPrinter m => CMD -> m Doc
printCMD (Ass c def) = do
  [c', def'] <- mapM printExpression [c, def]
  return $ c' <+> text ":=" <+> def'
printCMD c@(Cmd s exps) -- TODO: remove the case := later
    | s == ":=" = error $ "printCMD: use Ass for assignment representation! "
                  ++ show c
    | s == "constraint" = printExpression (exps !! 0)
    | otherwise = let f l = text s <> parens (sepByCommas l)
                  in liftM f $ mapM printExpression exps
printCMD (Repeat e stms) = do
  e' <- printExpression e
  let f l = text "re" <>
               (text "peat" $+$ vcat (map (text "." <+>)  l))
               $+$ text "until" <+> e'
  liftM f $ mapM printCMD stms
  
printCMD (Sequence stms) = 
    let f l = text "se" <> (text "quence" $+$ vcat (map (text "." <+>) l))
              $+$ text "end"
    in liftM f $ mapM printCMD stms

printCMD (Cond l) = let f l' = vcat l' $+$ text "end"
                    in liftM f $ mapM (uncurry printCase) l

printCase :: ConstantPrinter m => EXPRESSION -> [CMD] -> m Doc
printCase e l = do
  e' <- printExpression e
  let f l' = text "ca" <> (text "se" <+> e' <> text ":"
                                       $+$ vcat (map (text "." <+>)  l'))
  liftM f $ mapM printCMD l



getPrec :: EXPRESSION -> Int
getPrec (Op s _ exps _)
 | length exps == 0 = 8 -- check maximum given prec in operatorInfo,
                        -- this value must be higher
 | otherwise =
     case lookupOpInfo s $ length exps of
       Right oi -> prec oi
       Left True -> error $ 
                    concat [ "getPrec: registered operator ", show s, " used "
                           , "with non-registered arity ", show $ length exps ]
       _ -> 0
getPrec _ = 9

printExtparam :: EXTPARAM -> Doc
printExtparam (EP p op i) =
    pretty p <> text op <> (text $ if op == "-|" then  "" else show i)

printExtparams :: [EXTPARAM] -> Doc
printExtparams [] = empty
printExtparams l = brackets $ sepByCommas $ map printExtparam l

printInfix :: ConstantPrinter m => EXPRESSION -> m Doc
printInfix e@(Op s _ exps _) = do
-- we mustn't omit the space between the operator and its arguments for text-
-- operators such as "and", "or", but it would be good to omit it for "+-*/"
  oi <- printOPID s
  let outerprec = getPrec e
      f l = (if (outerprec<=(getPrec (exps!!0))) then l !! 0
             else  parens (l !! 0)) <+> oi
            <+> (if outerprec<= getPrec (exps!!1)
                 then l !! 1
                 else parens (l !! 1))
  liftM f $ mapM printExpression exps
printInfix _ = error "printInfix: Impossible case"

printExpression :: ConstantPrinter m => EXPRESSION -> m Doc
-- TODO: remove the $ when finished static analysis
printExpression (Var token) = return $ text $ "$" ++ tokStr token
printExpression e@(Op s epl exps _)
    | length exps == 0 = liftM (<> printExtparams epl) $ printOPID s
    | otherwise =
        let f pexps = (<> (printExtparams epl <> parens (sepByCommas pexps)))
            asPrfx pexps = liftM (f pexps) $ printOPID s
            asPrfx' = mapM printExpression exps >>= asPrfx
        in case lookupOpInfo s $ length exps  of
             Right oi
                 | infx oi -> printInfix e
                 | otherwise -> asPrfx'
             _ -> asPrfx'

printExpression (List exps _) = liftM sepByCommas (mapM printExpression exps)
printExpression (Int i _) = return $ text (show i)
printExpression (Double d _) = return $ text (show d)
printExpression (Interval l r _) =
    return $ brackets $ sepByCommas $ map (text . show) [l, r]

printOpItem :: OP_ITEM -> Doc
printOpItem (Op_item tokens _) =
    text "operator" <+> sepByCommas (map pretty tokens)

printVarItem :: VAR_ITEM -> Doc
printVarItem (Var_item vars dom _) =
    hsep [sepByCommas $ map pretty vars, text "in", pretty dom]

printDomain :: Domain -> Doc
printDomain (Set l) = braces $ sepByCommas $ map printGC l
printDomain (IntVal (c1, b1) (c2, b2)) =
    hcat [ getIBorder True b1, sepByCommas $ map printGC [c1, c2]
         , getIBorder False b2]

getIBorder :: Bool -> Bool -> Doc
getIBorder False False = lbrack
getIBorder True True = lbrack
getIBorder _ _ = rbrack

printGC :: GroundConstant -> Doc
printGC (GCI i) = text (show i)
printGC (GCR d) = text (show d)

printBasicSpec :: BASIC_SPEC -> Doc
printBasicSpec (Basic_spec xs) = vcat $ map pretty xs

printBasicItems :: BASIC_ITEM -> Doc
printBasicItems (Axiom_item x) = pretty x
printBasicItems (Op_decl x) = pretty x
printBasicItems (Var_decls x) = text "vars" <+> (sepBySemis $ map pretty x)

printSymbol :: SYMB -> Doc
printSymbol (Symb_id sym) = pretty sym

printSymbItems :: SYMB_ITEMS -> Doc
printSymbItems (Symb_items xs _) = fsep $ map pretty xs

printSymbOrMap :: SYMB_OR_MAP -> Doc
printSymbOrMap (Symb sym) = pretty sym
printSymbOrMap (Symb_map source dest _) =
  pretty source <+> mapsto <+> pretty dest

printSymbMapItems :: SYMB_MAP_ITEMS -> Doc
printSymbMapItems (Symb_map_items xs _) = fsep $ map pretty xs


-- Instances for GetRange

instance GetRange OP_ITEM where
  getRange = Range . rangeSpan
  rangeSpan x = case x of
    Op_item a b -> joinRanges [rangeSpan a, rangeSpan b]

instance GetRange VAR_ITEM where
  getRange = Range . rangeSpan
  rangeSpan x = case x of
    Var_item a _ b -> joinRanges [rangeSpan a, rangeSpan b]


instance GetRange BASIC_SPEC where
  getRange = Range . rangeSpan
  rangeSpan x = case x of
    Basic_spec a -> joinRanges [rangeSpan a]

instance GetRange BASIC_ITEM where
  getRange = Range . rangeSpan
  rangeSpan x = case x of
    Op_decl a -> joinRanges [rangeSpan a]
    Var_decls a -> joinRanges [rangeSpan a]
    Axiom_item a -> joinRanges [rangeSpan a]

instance GetRange CMD where
    getRange = Range . rangeSpan
    rangeSpan (Ass c def) = joinRanges (map rangeSpan [c, def])
    rangeSpan (Cmd _ exps) = joinRanges (map rangeSpan exps)
    -- parsing guruantees l <> null
    rangeSpan (Repeat c l) = joinRanges [rangeSpan c, rangeSpan $ head l]
    -- parsing guruantees l <> null
    rangeSpan (Sequence l) = rangeSpan $ head l
    rangeSpan (Cond l) = rangeSpan $ head l

instance GetRange SYMB_ITEMS where
  getRange = Range . rangeSpan
  rangeSpan (Symb_items a b) = joinRanges [rangeSpan a, rangeSpan b]

instance GetRange SYMB where
  getRange = Range . rangeSpan
  rangeSpan (Symb_id a) = joinRanges [rangeSpan a]
    

instance GetRange SYMB_MAP_ITEMS where
  getRange = Range . rangeSpan
  rangeSpan (Symb_map_items a b) = joinRanges [rangeSpan a, rangeSpan b]

instance GetRange SYMB_OR_MAP where
  getRange = Range . rangeSpan
  rangeSpan x = case x of
    Symb a -> joinRanges [rangeSpan a]
    Symb_map a b c -> joinRanges [rangeSpan a, rangeSpan b, rangeSpan c]

instance GetRange EXPRESSION where
  getRange = Range . rangeSpan
  rangeSpan x = case x of
    Var token -> joinRanges [rangeSpan token]
    Op _ _ exps a -> joinRanges $ [rangeSpan a] ++ (map rangeSpan exps)
    List exps a -> joinRanges $ [rangeSpan a] ++ (map rangeSpan exps)
    Int _ a -> joinRanges [rangeSpan a]
    Double _ a -> joinRanges [rangeSpan a]
    Interval _ _ a -> joinRanges [rangeSpan a]
