{- |
Module      :  $Header$
Description :  Definition of signatures for the Edinburgh
               Logical Framework
Copyright   :  (c) Kristina Sojakova, DFKI Bremen 2009
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  k.sojakova@jacobs-university.de
Stability   :  experimental
Portability :  portable
-}

module LF.Sign
       ( VAR
       , NAME
       , MODULE
       , BASE
       , Symbol (..)
       , RAW_SYM
       , EXP (..)
       , Sentence
       , CONTEXT
       , DEF (..)
       , Sign (..)
       , isSym
       , toSym
       , gen_base
       , gen_module
       , emptySig
       , addDef
       , getSymbols
       , getDeclaredSyms
       , getDefinedSyms
       , getLocalSyms
       , getLocalDefs 
       , getGlobalSyms
       , getGlobalDefs
       , isConstant
       , isDeclaredSym
       , isDefinedSym
       , isLocalSym
       , isGlobalSym 
       , getSymType
       , getSymValue
       , getSymsOfType
       , getFreeVars
       , getConstants
       , recForm
       , isSubsig
       , sigUnion
       , sigIntersection
       , genSig
       , coGenSig
       ) where

import Common.Id
import Common.Doc
import Common.DocUtils
import Common.Result
import Common.Keywords

import Data.Maybe
import Data.List
import qualified Data.Set as Set
import qualified Data.Map as Map

type VAR = String
type NAME = String
type MODULE = String
type BASE = String

gen_base :: String
gen_base = "gen_twelf_file.elf"

gen_module :: String
gen_module = "GEN_SIG"

data Symbol = Symbol
            { symBase :: BASE
            , symModule :: MODULE
            , symName :: NAME
            } deriving (Ord, Eq, Show)

type RAW_SYM = String

instance GetRange Symbol

data EXP = Type
         | Var VAR
         | Const Symbol
         | Appl EXP [EXP]
         | Func [EXP] EXP
         | Pi CONTEXT EXP
         | Lamb CONTEXT EXP
           deriving (Ord,Show)

instance GetRange EXP

type Sentence = EXP

type CONTEXT = [(VAR,EXP)]

data DEF = Def
         { getSym :: Symbol
         , getType :: EXP
         , getValue :: Maybe EXP
         } deriving (Eq,Ord,Show)

data Sign = Sign
          { sigBase :: BASE
          , sigModule :: MODULE
          , getDefs :: [DEF]
          } deriving (Eq, Ord, Show)

emptySig :: Sign
emptySig = Sign gen_base gen_module []

addDef :: DEF -> Sign -> Sign
addDef d (Sign b m ds) = Sign b m $ ds ++ [d]

{- tests whether a raw symbol represents a valid identifier (True) or
   an expression (False) -}
isSym :: RAW_SYM -> Bool
isSym s =
  let forbidden = whiteChars ++ (twelfDeclChars \\ twelfSymChars)
  in null (intersect s forbidden)

-- converts a raw symbol to a symbol; must be a valid identifier
toSym :: RAW_SYM -> Symbol
toSym s = Symbol gen_base gen_module s

-- get the set of all symbols
getSymbols :: Sign -> Set.Set Symbol
getSymbols (Sign _ _ ds) = Set.fromList $ map getSym ds

-- checks if the symbol is defined or declared in the signature
isConstant :: Symbol -> Sign -> Bool
isConstant s sig = Set.member s $ getSymbols sig

-- get the set of declared symbols
getDeclaredSyms :: Sign -> Set.Set Symbol
getDeclaredSyms (Sign _ _ ds) =
  Set.fromList $ map getSym $ filter (\ d -> isNothing $ getValue d) ds

-- checks if the symbol is declared in the signature
isDeclaredSym :: Symbol -> Sign -> Bool
isDeclaredSym s sig = Set.member s $ getDeclaredSyms sig

-- get the set of declared symbols
getDefinedSyms :: Sign -> Set.Set Symbol
getDefinedSyms (Sign _ _ ds) =
  Set.fromList $ map getSym $ filter (\ d -> isJust $ getValue d) ds

-- checks if the symbol is defined in the signature
isDefinedSym :: Symbol -> Sign -> Bool
isDefinedSym s sig = Set.member s $ getDefinedSyms sig

-- get the set of symbols not included from other signatures
getLocalSyms :: Sign -> Set.Set Symbol
getLocalSyms sig = Set.filter (\ s -> isLocalSym s sig) $ getSymbols sig

-- checks if the symbol is local to the signature
isLocalSym :: Symbol -> Sign -> Bool
isLocalSym s sig =
  and [sigBase sig == symBase s, sigModule sig == symModule s]

-- get the list of local definitions
getLocalDefs :: Sign -> [DEF]
getLocalDefs sig = filter (\ (Def s _ _) -> isLocalSym s sig) $ getDefs sig

-- get the set of symbols included from other signatures
getGlobalSyms :: Sign -> Set.Set Symbol
getGlobalSyms sig = Set.filter (\ s -> isGlobalSym s sig) $ getSymbols sig

-- checks if the symbol is global
isGlobalSym :: Symbol -> Sign -> Bool
isGlobalSym s sig = not $ isLocalSym s sig

-- get the list of global definitions
getGlobalDefs :: Sign -> [DEF]
getGlobalDefs sig = filter (\ (Def s _ _) -> isGlobalSym s sig) $ getDefs sig

-- returns the type/kind for the given symbol
getSymType :: Symbol -> Sign -> Maybe EXP
getSymType sym sig =
  let res = find (\ d -> getSym d == sym) $ getDefs sig
      in case res of
              Nothing -> Nothing
              Just (Def _ t _) -> Just t

-- returns the value for the given symbol, if it exists
getSymValue :: Symbol -> Sign -> Maybe EXP
getSymValue sym sig =
  let res = find (\ d -> getSym d == sym) $ getDefs sig
      in case res of
              Nothing -> Nothing
              Just (Def _ _ v) -> v

-- returns the set of symbols of the given type
getSymsOfType :: EXP -> Sign -> Set.Set Symbol
getSymsOfType t sig =
  Set.fromList $ map getSym $ filter (\ (Def _ t' _) -> t' == t) $ getDefs sig

-- pretty printing
instance Pretty Sign where
   pretty = printSig
instance Pretty DEF where
   pretty = printDef
instance Pretty EXP where
   pretty = printExp
instance Pretty Symbol where
   pretty = printSymbol

printSig :: Sign -> Doc
printSig sig = vcat $ map printDef (getDefs sig)

printDef :: DEF -> Doc
printDef (Def s t v) =
  case v of
    Nothing -> fsep [ pretty s
                    , colon <+> pretty t <> dot ]
    Just val -> fsep [ pretty s
                     , colon <+> pretty t
                     , text "=" <+> pretty val <> dot ]

printSymbol :: Symbol -> Doc
printSymbol s = text $ symName s

printExp :: EXP -> Doc
printExp Type = text "type"
printExp (Const s) = pretty s
printExp (Var n) = text n
printExp (Appl e es) =
  let f = printExpWithPrec (precAppl + 1) e
      as = map (printExpWithPrec precAppl) es
      in hsep (f:as)
printExp (Func es e) =
  let as = map (printExpWithPrec precFunc) es
      val = printExpWithPrec (precFunc + 1) e
      in hsep $ punctuate (text " ->") (as ++ [val])
printExp (Pi ds e) = sep [braces $ printContext ds, pretty e]
printExp (Lamb ds e) = sep [brackets $ printContext ds, pretty e]

printExpWithPrec :: Int -> EXP -> Doc
printExpWithPrec i e =
  if prec e >= i
     then parens $ printExp e
     else printExp e

prec :: EXP -> Int
prec Type = 0
prec Const {} = 0
prec Var {} = 0
prec Appl {} = 1
prec Func {} = 2
prec Pi {} = 3
prec Lamb {} = 3

precFunc, precAppl :: Int
precFunc = 2
precAppl = 1

printContext :: CONTEXT -> Doc
printContext xs = sep $ punctuate comma $ map printVarDecl xs

printVarDecl :: (VAR,EXP) -> Doc
printVarDecl (n,e) = sep [text n, colon <+> pretty e]

{- converts the expression into a form where each construct takes
   exactly one argument -}
recForm :: EXP -> EXP
recForm (Appl f []) = recForm f
recForm (Appl f as) = Appl (recForm $ Appl f $ init as) $ [recForm $ last as]
recForm (Func [] a) = recForm a
recForm (Func (t:ts) a) = Func [recForm t] $ recForm $ Func ts a
recForm (Pi [] t) = recForm t
recForm (Pi ((n,t):ds) a) =
  Pi [(n,recForm t)] $ recForm $ Pi ds a
recForm (Lamb [] t) = recForm t
recForm (Lamb ((n,t):ds) a) =
  Lamb [(n,recForm t)] $ recForm $ Lamb ds a
recForm t = t

{- modifies the given name until it is different from each of the names
   in the input set -}
getNewName :: VAR -> Set.Set VAR -> VAR
getNewName var names = getNewNameH var names var 0

getNewNameH :: VAR -> Set.Set VAR -> VAR -> Int -> VAR
getNewNameH var names root i =
  if (Set.notMember var names)
     then var
     else let newVar = root ++ (show i)
              in getNewNameH newVar names root $ i+1

-- returns the set of free Variables used within an expression
getFreeVars :: EXP -> Set.Set VAR
getFreeVars e = getFreeVarsH $ recForm e

getFreeVarsH :: EXP -> Set.Set VAR
getFreeVarsH Type = Set.empty
getFreeVarsH (Const _) = Set.empty
getFreeVarsH (Var x) = Set.singleton x
getFreeVarsH (Appl f [a]) =
  Set.union (getFreeVarsH f) (getFreeVarsH a)
getFreeVarsH (Func [t] v) =
  Set.union (getFreeVarsH t) (getFreeVarsH v)
getFreeVarsH (Pi [(n,t)] a) =
  Set.delete n $ Set.union (getFreeVarsH t) (getFreeVarsH a)
getFreeVarsH (Lamb [(n,t)] a) =
  Set.delete n $ Set.union (getFreeVarsH t) (getFreeVarsH a)
getFreeVarsH _ = Set.empty

-- returns the set of symbols used within an expression
getConstants :: EXP -> Set.Set Symbol
getConstants e = getConstantsH $ recForm e

getConstantsH :: EXP -> Set.Set Symbol
getConstantsH Type = Set.empty
getConstantsH (Const s) = Set.singleton s
getConstantsH (Var _) = Set.empty
getConstantsH (Appl f [a]) =
  Set.union (getConstantsH f) (getConstantsH a)
getConstantsH (Func [t] v) =
  Set.union (getConstantsH t) (getConstantsH v)
getConstantsH (Pi [(_,t)] a) =
  Set.union (getConstantsH t) (getConstantsH a)
getConstantsH (Lamb [(_,t)] a) =
  Set.union (getConstantsH t) (getConstantsH a)
getConstantsH _ = Set.empty

{- Variable renamings:
   - the first argument specifies the desired variable renamings
   - the second argument specifies the set of variables which cannot
     be used as new variable names -}
rename :: Map.Map VAR VAR -> Set.Set VAR -> EXP -> EXP
rename m s e = renameH m s (recForm e)

renameH :: Map.Map VAR VAR -> Set.Set VAR -> EXP -> EXP
renameH _ _ Type = Type
renameH _ _ (Const n) = Const n
renameH m _ (Var n) = Var $ Map.findWithDefault n n m
renameH m s (Appl f [a]) = Appl (rename m s f) [rename m s a]
renameH m s (Func [t] u) = Func [rename m s t] (rename m s u)
renameH m s (Pi [(x,t)] a) =
  let t1 = rename m s t
      x1 = getNewName x s
      a1 = rename (Map.insert x x1 m) (Set.insert x1 s) a
      in Pi [(x1,t1)] a1
renameH m s (Lamb [(x,t)] a) =
  let t1 = rename m s t
      x1 = getNewName x s
      a1 = rename (Map.insert x x1 m) (Set.insert x1 s) a
      in Lamb [(x1,t1)] a1
renameH _ _ t = t

-- equality
instance Eq EXP where
    e1 == e2 = eqExp (recForm e1) (recForm e2)

eqExp :: EXP -> EXP -> Bool
eqExp Type Type = True
eqExp (Const x1) (Const x2) = x1 == x2
eqExp (Var x1) (Var x2) = x1 == x2
eqExp (Appl f1 [a1]) (Appl f2 [a2]) = and [f1 == f2, a1 == a2]
eqExp (Func [t1] s1) (Func [t2] s2) = and [t1 == t2, s1 == s2]
eqExp (Pi [(n1,t1)] s1) (Pi [(n2,t2)] s2) =
  let vars = Set.delete n1 $ getFreeVars s1
      vars1 = Set.delete n2 $ getFreeVars s2
      in if (vars1 /= vars)
            then False
            else let s3 = rename (Map.singleton n2 n1) (Set.insert n1 vars) s2
                 in and [t1 == t2, s1 == s3]
eqExp (Lamb [(n1,t1)] s1) (Lamb [(n2,t2)] s2) =
  let vars = Set.delete n1 $ getFreeVars s1
      vars1 = Set.delete n2 $ getFreeVars s2
      in if (vars1 /= vars)
            then False
            else let s3 = rename (Map.singleton n2 n1) (Set.insert n1 vars) s2
                 in and [t1 == t2, s1 == s3]
eqExp _ _ = False

-- tests for inclusion of signatures
isSubsig :: Sign -> Sign -> Bool
isSubsig (Sign _ _ ds1) (Sign _ _ ds2) =
  Set.isSubsetOf (Set.fromList ds1) (Set.fromList ds2)
 
-- constructs the union of two signatures
sigUnion :: Sign -> Sign -> Result Sign
sigUnion sig1 sig2 = return $
  foldl (\ sig d@(Def s t v) ->
           if (isConstant s sig)
              then let Just t1 = getSymType s sig
                       v1 = getSymValue s sig
                       in if (t == t1 && v == v1) then sig else
                             error $ conflictDefsError s
              else addDef d sig
        ) sig1 $ getDefs sig2

-- constructs the intersection of two signatures
sigIntersection :: Sign -> Sign -> Result Sign
sigIntersection sig1 sig2 = do
  let defs1 = Set.fromList $ getDefs sig1
  let defs2 = Set.fromList $ getDefs sig2
  let defs = Set.difference defs1 defs2
  let syms = Set.map getSym defs
  coGenSig syms sig1

-- constructs the signature generated by the specified symbol set
genSig :: Set.Set Symbol -> Sign -> Result Sign
genSig syms sig = do
  let syms' = inclSyms syms sig
  let defs' = filter (\ d -> Set.member (getSym d) syms') $ getDefs sig
  return $ Sign gen_base gen_module defs'

inclSyms :: Set.Set Symbol -> Sign -> Set.Set Symbol
inclSyms syms sig =
  foldl (\ syms' (Def s t v) ->
           if (Set.notMember s syms') then syms' else
              let syms1 = getConstants t
                  syms2 = case v of
                            Nothing -> Set.empty
                            Just v' -> getConstants v'
                  in Set.union syms' $ Set.union syms1 syms2
        ) syms $ reverse $ getDefs sig

-- constructs the signature cogenerated by the specified symbol set
coGenSig :: Set.Set Symbol -> Sign -> Result Sign
coGenSig syms sig = do
  let syms' = exclSyms syms sig
  let defs' = filter (\ d -> Set.notMember (getSym d) syms') $ getDefs sig
  return $ Sign gen_base gen_module defs'
  
exclSyms :: Set.Set Symbol -> Sign -> Set.Set Symbol
exclSyms syms sig =
  foldl (\ syms' (Def s t v) ->
           if (Set.member s syms') then syms' else
              let syms1 = getConstants t
                  syms2 = case v of
                            Nothing -> Set.empty
                            Just v' -> getConstants v'
                  diff = Set.intersection syms' $ Set.union syms1 syms2
                  in if (Set.null diff) then syms' else Set.insert s syms'
        ) syms $ getDefs sig

--------------------------------------------------------------------
---------------------------------------------------------------------

-- ERROR MESSAGES
conflictDefsError :: Symbol -> String
conflictDefsError s =
  "Symbol " ++ (show $ pretty s) ++ " has conflicting declarations " ++
  "in the signature union and hence the union is not defined."
