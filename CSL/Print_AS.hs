{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  ./CSL/Print_AS.hs
Description :  Printer for abstract syntax of CSL
Copyright   :  (c) Dominik Dietrich, Ewaryst Schulz, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  experimental
Portability :  portable

Pretty printing the abstract syntax of CSL.

-}

module CSL.Print_AS
    ( printExpression
    , printCMD
    , printAssDefinition
    , printConstantName
    , ExpressionPrinter (..)
    ) where

import Common.Id as Id
import Common.Doc
import Common.DocUtils

import Control.Monad
import Control.Monad.Reader

import Numeric

import CSL.AS_BASIC_CSL
import CSL.TreePO


-- * Pretty Printing

instance Pretty InfInt where
    pretty = printInfInt
instance Pretty GroundConstant where
    pretty = printGC
instance (Ord a, Pretty a) => Pretty (SetOrInterval a) where
    pretty = printDomain
instance Pretty a => Pretty (ClosedInterval a) where
    pretty = printClosedInterval

instance Pretty OpDecl where
    pretty = head . printOpDecl
instance Pretty VarDecl where
    pretty = printVarDecl
instance Pretty EPVal where
    pretty = printEPVal

instance Pretty EPDecl where
    pretty = printEPDecl
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


{- | A monad for printing of constants. This turns the pretty printing facility
more flexible w.r.t. the output of 'ConstantName'. -}
class Monad m => ExpressionPrinter m where
    getOINM :: m OpInfoNameMap
    getOINM = return operatorInfoNameMap
    printConstant :: ConstantName -> m Doc
    printConstant = return . printConstantName
    printOpname :: OPNAME -> m Doc
    printOpname = return . text . showOPNAME
    prefixMode :: m Bool
    prefixMode = return False
    printArgs :: [Doc] -> m Doc
    printArgs = return . parens . sepByCommas
    printArgPattern :: String -> m Doc
    printArgPattern = return . text
    printInterval :: Double -> Double -> m Doc
    printInterval l r =
        return $ brackets $ sepByCommas $ map (text . show) [l, r]
    printRational :: APFloat -> m Doc
    printRational r = return $ text $ showFloat (fromRat r :: Double) ""


-- | The default ConstantName printer
printConstantName :: ConstantName -> Doc
printConstantName (SimpleConstant s) = text s
printConstantName (ElimConstant s i) =
    text $ if i > 0 then s ++ "__" ++ show i else s

printAssDefinition :: ExpressionPrinter m => AssDefinition -> m Doc
printAssDefinition (ConstDef e) = liftM (text "=" <+>) $ printExpression e
printAssDefinition (FunDef l e) = do
  ed <- printExpression e
  l' <- mapM printArgPattern l
  args <- printArgs l'
  return $ args <+> text "=" <+> ed

printOPID :: ExpressionPrinter m => OPID -> m Doc
printOPID (OpUser c) = printConstant c
printOPID (OpId oi) = printOpname oi

-- a dummy instance, we take the simplest monad
instance ExpressionPrinter []

-- | An 'OpInfoNameMap' can be interpreted as an 'ExpressionPrinter'
instance ExpressionPrinter (Reader OpInfoNameMap) where
    getOINM = ask


printCMD :: ExpressionPrinter m => CMD -> m Doc
printCMD (Ass c def) = do
  def' <- printExpression def
  c' <- printOpDecl c
  return $ c' <+> text ":=" <+> def'
printCMD c@(Cmd s exps) -- TODO: remove the case := later
    | s == ":=" = error $ "printCMD: use Ass for assignment representation! "
                  ++ show c
    | s == "constraint" = printExpression (head exps)
    | otherwise = let f l = text s <> parens (sepByCommas l)
                  in liftM f $ mapM printExpression exps
printCMD (Repeat e stms) = do
  e' <- printExpression e
  let f l = text "re" <>
               (text "peat" $+$ vcat (map (text "." <+>) l))
               $+$ text "until" <+> e'
  liftM f $ mapM printCMD stms

printCMD (Sequence stms) =
    let f l = text "se" <> (text "quence" $+$ vcat (map (text "." <+>) l))
              $+$ text "end"
    in liftM f $ mapM printCMD stms

printCMD (Cond l) = let f l' = vcat l' $+$ text "end"
                    in liftM f $ mapM (uncurry printCase) l

printCase :: ExpressionPrinter m => EXPRESSION -> [CMD] -> m Doc
printCase e l = do
  e' <- printExpression e
  let f l' = text "ca" <> (text "se" <+> e' <> text ":"
                                       $+$ vcat (map (text "." <+>) l'))
  liftM f $ mapM printCMD l


getPrec :: OpInfoNameMap -> EXPRESSION -> Int
getPrec oinm (Op s _ exps _)
 | null exps = maxPrecedence + 1
 | otherwise =
     case lookupOpInfo oinm s $ length exps of
       Right oi -> prec oi
       Left True -> error $
                    concat [ "getPrec: registered operator ", show s, " used "
                           , "with non-registered arity ", show $ length exps ]
       _ -> maxPrecedence {- this is probably a user-defined prefix function
                          , binds strongly -}
getPrec _ _ = maxPrecedence

getOp :: EXPRESSION -> Maybe OPID
getOp (Op s _ _ _) = Just s
getOp _ = Nothing

printExtparam :: EXTPARAM -> Doc
printExtparam (EP p op i) =
    pretty p <> text op <> (if op == "-|" then empty else text $ show i)

printExtparams :: [EXTPARAM] -> Doc
printExtparams [] = empty
printExtparams l = brackets $ sepByCommas $ map printExtparam l

printInfix :: ExpressionPrinter m => EXPRESSION -> m Doc
printInfix e@(Op s _ exps@[e1, e2] _) = do
{- we mustn't omit the space between the operator and its arguments for text-
operators such as "and", "or", but it would be good to omit it for "+-*/" -}
  oi <- printOPID s
  oinm <- getOINM
  let outerprec = getPrec oinm e
      f cmp e' ed = if cmp outerprec $ getPrec oinm e' then ed else parens ed
      g [ed1, ed2] = let cmp = case getOp e1 of
                                 Just op1 | op1 == s -> (<=)
                                          | otherwise -> (<)
                                 _ -> (<)
                     in sep [f cmp e1 ed1, oi <+> f (<) e2 ed2]
      g _ = error "printInfix: Inner impossible case"
  liftM g $ mapM printExpression exps
printInfix _ = error "printInfix: Impossible case"

printExpression :: ExpressionPrinter m => EXPRESSION -> m Doc
printExpression (Var token) = return $ text $ tokStr token
printExpression e@(Op s epl exps _)
    | null exps = liftM (<> printExtparams epl) $ printOPID s
    | otherwise = do
        let asPrfx pexps = do
                    oid <- printOPID s
                    args <- printArgs pexps
                    return $ oid <> printExtparams epl <> args
            asPrfx' = mapM printExpression exps >>= asPrfx
        oinm <- getOINM
        pfxMode <- prefixMode
        if pfxMode then asPrfx' else
            case lookupOpInfo oinm s $ length exps of
              Right oi
                  | infx oi -> printInfix e
                  | otherwise -> asPrfx'
              _ -> asPrfx'

printExpression (List exps _) = liftM sepByCommas (mapM printExpression exps)
printExpression (Int i _) = return $ text (show i)
printExpression (Rat r _) = printRational r
printExpression (Interval l r _) = printInterval l r

printOpItem :: OP_ITEM -> Doc
printOpItem (Op_item tokens _) =
    text "operator" <+> sepByCommas (map pretty tokens)

printVarItem :: VAR_ITEM -> Doc
printVarItem (Var_item vars dom _) =
    hsep [sepByCommas $ map pretty vars, text "in", pretty dom]


instance Pretty Ordering where
    pretty LT = text "<"
    pretty GT = text ">"
    pretty EQ = text "="

printVarDecl :: VarDecl -> Doc
printVarDecl (VarDecl n (Just dom)) = pretty n <+> text "in" <+> printDomain dom
printVarDecl (VarDecl n Nothing) = pretty n

printOpDecl :: ExpressionPrinter m => OpDecl -> m Doc
printOpDecl (OpDecl n epl vdl _)
    | null vdl = liftM (<> printExtparams epl) $ printConstant n
    | otherwise = do
         oid <- printConstant n
         args <- printArgs $ map printVarDecl vdl
         return $ oid <> printExtparams epl <> args

printEPVal :: EPVal -> Doc
printEPVal (EPVal i) = pretty i
printEPVal (EPConstRef r) = pretty r


printEPDecl :: EPDecl -> Doc
printEPDecl (EPDecl tk dom mDef) =
    let tkD = pretty tk
        domD = printInfixWith True "in" (tk, dom)
    in case mDef of
         Just def -> vcat [domD, hsep [ text "set", text "default"
                                            , hcat [tkD, text "=", pretty def]]]
         _ -> domD


printClosedInterval :: Pretty a => ClosedInterval a -> Doc
printClosedInterval (ClosedInterval l r) =
    hcat [ lbrack, sepByCommas $ map pretty [l, r], rbrack ]


printDomain :: (Ord a, Pretty a) => SetOrInterval a -> Doc
printDomain (Set s) = pretty s
printDomain (IntVal (c1, b1) (c2, b2)) =
    hcat [ getIBorder True b1, sepByCommas $ map pretty [c1, c2]
         , getIBorder False b2]

getIBorder :: Bool -> Bool -> Doc
getIBorder False False = lbrack
getIBorder True True = lbrack
getIBorder _ _ = rbrack

printGC :: GroundConstant -> Doc
printGC (GCI i) = text (show i)
printGC (GCR d) = text (show d)

printInfInt :: InfInt -> Doc
printInfInt NegInf = text "-oo"
printInfInt PosInf = text "oo"
printInfInt (FinInt x) = text $ show x

printBasicSpec :: BASIC_SPEC -> Doc
printBasicSpec (Basic_spec xs) = vcat $ map pretty xs

printBasicItems :: BASIC_ITEM -> Doc
printBasicItems (Axiom_item x) = pretty x
printBasicItems (Op_decl x) = pretty x
printBasicItems (Var_decls x) = text "vars" <+> sepBySemis (map pretty x)
printBasicItems (EP_decl x) = text "eps" <+> sepBySemis
                               (map (printInfixWith True "in") x)
printBasicItems (EP_domdecl x) =
    text "set" <+> sepBySemis (map (printInfixWith False "=") x)
printBasicItems (EP_defval x) = text "set" <+> text "default" <+>
                                sepBySemis (map (printInfixWith False "=") x)

printInfixWith :: (Pretty a, Pretty b) => Bool -> String -> (a, b) -> Doc
printInfixWith b s (x, y) = sep' [pretty x, text s, pretty y]
    where sep' = if b then hsep else hcat

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
    EP_decl a -> joinRanges [rangeSpan $ map fst a]
    EP_domdecl a -> joinRanges [rangeSpan $ map fst a]
    EP_defval a -> joinRanges [rangeSpan $ map fst a]


instance GetRange CMD where
    getRange = Range . rangeSpan
    rangeSpan (Ass _ def) = rangeSpan def
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
    Op _ _ exps a -> joinRanges $ rangeSpan a : map rangeSpan exps
    List exps a -> joinRanges $ rangeSpan a : map rangeSpan exps
    Int _ a -> joinRanges [rangeSpan a]
    Rat _ a -> joinRanges [rangeSpan a]
    Interval _ _ a -> joinRanges [rangeSpan a]


instance Pretty InstantiatedConstant where
    pretty (InstantiatedConstant { constName = cn, instantiation = el }) =
        if null el then pretty cn
        else pretty cn <> parens (sepByCommas $ map pretty el)
