{- |
Module      :  $Header$
Description :  Utils for the abstract syntax of EnCL
Copyright   :  (c) Dominik Dietrich, Ewaryst Schulz, DFKI Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  experimental
Portability :  portable


Utils to create and access abstract syntax data
-}

module CSL.ASUtils
    ( epNameOfComp
    , getDefiniens        -- accessor function for AssDefinition
    , getArguments        -- accessor function for AssDefinition
    , isFunDef            -- predicate for AssDefinition
    , isInterval          -- predicate for EXPRESSION
    , mkDefinition        -- constructor for AssDefinition
    , updateDefinition    -- updates the definiens
    , mapExpr             -- maps function over EXPRESSION arguments

    , varDeclName
    , varDeclToVar
    , opDeclToOp

    , mkVar               -- Variable constructor
    , mkOp                -- Simple Operator constructor
    , mkPredefOp          -- Simple Operator constructor for predefined ops
    , mkUserdefOp

    , mkAndAnalyzeOp
    , mkAndAnalyzeOp'
    , toElimConst         -- Constant naming for elim constants, see Analysis.hs
    , simpleName
    , setOfUserDefined
    , setOfConstsAndEPSpecs
    ) where

import Common.Id as Id

import qualified Data.Set as Set
import Data.List (sort, mapAccumL)

import CSL.AS_BASIC_CSL
import CSL.Fold

-- ---------------------------------------------------------------------------
-- * Preliminaries and Utilities
-- ---------------------------------------------------------------------------

-- | A simple operator constructor from given operator name and arguments
mkOp :: String -> [EXPRESSION] -> EXPRESSION
mkOp s el = Op (OpUser $ SimpleConstant s) [] el nullRange

-- | A variable constructor
mkVar :: String -> EXPRESSION
mkVar = Var . mkSimpleId

-- | A simple operator constructor from given operator id and arguments
mkPredefOp :: OPNAME -> [EXPRESSION] -> EXPRESSION
mkPredefOp n el = Op (OpId n) [] el nullRange

-- | A simple operator constructor from given operator id and arguments
mkUserdefOp :: String -> [EXTPARAM] -> [EXPRESSION] -> Range -> EXPRESSION
mkUserdefOp n epl el rg = Op (OpUser $ SimpleConstant n) epl el rg


foldNaryToBinary :: OPID -> Range -> [EXPRESSION] -> EXPRESSION
foldNaryToBinary op rg exps = foldl f (f (exps!!0) (exps!!1)) $ drop 2 exps
    where f e' e'' = Op op [] [e', e''] rg

mkAndAnalyzeOp :: OperatorState st => st -> String -> [EXTPARAM] -> [EXPRESSION]
               -> Range -> EXPRESSION

mkAndAnalyzeOp st s eps exps rg =
    either f g $ mkAndAnalyzeOp' False st s eps exps rg
    where f = error
          g e = e

-- | Lookup the string in the given 'OperatorState'
mkAndAnalyzeOp' :: OperatorState st => Bool -- ^ process binders
                -> st -> String -> [EXTPARAM] -> [EXPRESSION]
               -> Range -> Either String EXPRESSION
mkAndAnalyzeOp' b st s eps exps rg =
    case lookupOperator st s (length exps) of
      Left False
          | isVar st s -> if null exps && null eps
                          then Right $ Var $ Token { tokStr = s, tokPos = rg }
                          else Left "Variable requires no (extended) parameters"
          | otherwise -> f exps $ OpUser $ SimpleConstant s
      -- if registered it must be registered with the given arity or
      -- as flex-op, otherwise we don't accept it
      Left True -> Left "Wrong arity"
      Right oi
          | null eps ->
              if foldNAry oi && length exps > 2
              then Right $ foldNaryToBinary (OpId $ opname oi) rg exps
              else let exps' =
                        case bind oi of
                          Just x -> if b then processBinderArgs x exps else exps
                          _ -> exps
                   in f exps' $ OpId $ opname oi

          | otherwise -> Left "No extended parameters allowed"
    where f exps' op = Right $ Op op eps exps' rg

-- | For given binder arguments we replace the constant-expressions at the
-- bound variable positions by variable-expressions and also all constants with
-- the name of a variable in the arguments at binder body positions.
processBinderArgs :: BindInfo -> [EXPRESSION] -> [EXPRESSION]
processBinderArgs (BindInfo {bindingVarPos = bvl, boundBodyPos = bbl}) exps =
    let bvl' = sort bvl
        (vs, vl) = varSet $ map (exps!!) bvl'
        g l'@((j,ve):l) (i, e)
            | j == i -- at bound variable position
                = (l, ve)
            | otherwise = (l', g' (i, e))
        g l x = (l, g' x)
        g' (i, e)
            | elem i bbl -- at binder body position
                = constsToVars vs e
            | otherwise = e
    in snd $ mapAccumL g (zip bvl' vl) $ zip [0..] exps


mapExpr :: (EXPRESSION -> EXPRESSION) -> EXPRESSION -> EXPRESSION
mapExpr f e =
    case e of
      Op oi epl args rg -> Op oi epl (map f args) rg
      List exps rg -> List (map f exps) rg
      _ -> e


-- | Transforms Op-Expressions to a set of op-names and a Var-list
varSet :: [EXPRESSION] -> (Set.Set String, [EXPRESSION])
varSet l =
    let opToVar' s (Op v _ _ rg') =
            ( Set.insert (simpleName v) s
            , Var Token{ tokStr = simpleName v, tokPos = rg' } )
        opToVar' s v@(Var tok) = (Set.insert (tokStr tok) s, v)
        opToVar' _ x =
            error $ "varSet: not supported varexpression at " ++ show x
    in mapAccumL opToVar' Set.empty l

-- | Replaces Op occurrences to Var if the op is in the given set
constsToVars :: Set.Set String -> EXPRESSION -> EXPRESSION
constsToVars env e =
    let substRec =
         idRecord
         { foldOp =
            \ _ s epl' args rg' ->
                if Set.member (simpleName s) env then
                    if null args
                    then Var (Token { tokStr = simpleName s, tokPos = rg' })
                    else error $ "constsToVars: variable must not have"
                             ++ " arguments:" ++ show args
                else Op s epl' args rg'
         , foldList = \ _ l rg' -> List l rg'
         }
    in foldTerm substRec e


updateDefinition :: EXPRESSION -> AssDefinition -> AssDefinition
updateDefinition e' (ConstDef _) = ConstDef e'
updateDefinition e' (FunDef l _) = FunDef l e'


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

isInterval :: EXPRESSION -> Bool
isInterval (Interval _ _ _) = True
isInterval _ = False

epNameOfComp :: EPComponent -> Token
epNameOfComp (EPDomain s _) = s
epNameOfComp (EPDefault s _) = s
epNameOfComp (EPConst s _) = s

simpleName :: OPID -> String
simpleName (OpId n) = showOPNAME n
simpleName (OpUser (SimpleConstant s)) = s
simpleName (OpUser x) = error "simpleName: ElimConstant not supported: " ++ show x

toElimConst :: ConstantName -> Int -> ConstantName
toElimConst (SimpleConstant s) i = ElimConstant s i
toElimConst ec _ = error $ "toElimConst: already an elim const " ++ show ec

varDeclName :: VarDecl -> String
varDeclName (VarDecl n _) = Id.tokStr n

varDeclToVar :: VarDecl -> EXPRESSION
varDeclToVar (VarDecl n _) = Var n

opDeclToOp :: OpDecl -> EXPRESSION
opDeclToOp (OpDecl n epl vdl rg ) = Op (OpUser n) epl (map varDeclToVar vdl) rg

-- | Returns a set of user defined constants ignoring 'EXTPARAM' instantiation.
setOfUserDefined :: EXPRESSION -> Set.Set String
setOfUserDefined e = g Set.empty e
    where
      g s x =
       case x of
         Op oi@(OpUser _) _ al _ -> foldl g (Set.insert (simpleName oi) s) al
         -- handle also non-userdefined ops.
         Op _ _ al _ -> foldl g s al 
         -- ignoring lists (TODO: they should be removed soon anyway)
         _ -> s

-- | Returns a set of user defined constants and 'EXTPARAM' specifications.
setOfConstsAndEPSpecs :: EXPRESSION -> (Set.Set String, Set.Set EXTPARAM)
setOfConstsAndEPSpecs e = g (Set.empty, Set.empty) e
    where
      g s@(s1, s2) x =
       case x of
         Op oi@(OpUser _) epl al _ ->
             foldl g ( Set.insert (simpleName oi) s1
                     , foldr Set.insert s2 epl) al
         -- handle also non-userdefined ops.
         Op _ _ al _ -> foldl g s al 
         -- ignoring lists (TODO: they should be removed soon anyway)
         _ -> s

