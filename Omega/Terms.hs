{- |
Module      :  $Header$
Description :  Hets-to-Omega conversion
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2009
License     :  GPLv2 or higher

Maintainer  :  ewaryst.schulz@dfki.de
Stability   :  provisional
Portability :  non-portable(Logic)

HasCASL terms will be exported to omega terms.
-}

module Omega.Terms
    ( toTerm
    ) where

import Omega.DataTypes as DT

import HasCASL.FoldTerm
import HasCASL.As as As

import Data.Maybe

toTerm :: As.Term -> DT.Term
toTerm = foldTerm toTermRec

failInTermRec :: String -> a
failInTermRec x = error $ "Occurence of " ++ x ++ " in toTermRec!"

-- Structs: VarDecl PolyId GenVarDecl
-- Enums: OpBrand Quantifier Partiality LetBrand

quantifierName :: Quantifier -> String
quantifierName Universal = "!"
quantifierName Existential = "?"
quantifierName Unique = "?!"

lambdaName :: String
lambdaName = "\\"

tupleName :: String
tupleName = "TUPLE"

toTermRec :: FoldRec DT.Term DT.Term
toTermRec = FoldRec
    { -- Term VarDecl
      foldQualVar = \_ (VarDecl v _ _ _) -> DT.Var $ show v
      -- Term OpBrand PolyId TypeScheme [Type] InstKind Range
    , foldQualOp = \_ _ (PolyId i _ _) _ _ _ _ -> Symbol $ show i
    -- Term a a Range
    , foldApplTerm = \ (ApplTerm _ o2 _) y z _ ->
                     App y
                     -- flatten the tuple to an argument list
                     $ case (o2, z) of (TupleTerm _ _, App _ l) -> l
                                       _ -> [z]
    -- Term [a] Range
    , foldTupleTerm = \_ l _ -> App (Symbol tupleName) l
    -- Term a TypeQual Type Range
    , foldTypedTerm = \_ z _ _ _ -> z
    -- Term Quantifier [GenVarDecl] a Range
    , foldQuantifiedTerm =
        \_ q vars z _ ->
            let bvars =
                    -- we skip the type variables
                    (catMaybes
                     $ map (\x -> case x of GenVarDecl (VarDecl v _ _ _)
                                                -> Just $ DT.Var $ show v
                                            _ -> Nothing) vars)
            in if null bvars then z else Bind (quantifierName q) bvars z
    -- Term [a] Partiality a Range
    , foldLambdaTerm = \_ y _ z _ -> Bind lambdaName y z
    -- Term VarDecl a Range
    , foldAsPattern = \_ _ _ _ -> failInTermRec "AsPattern"
    -- Term a [b] Range
    , foldCaseTerm = \_ _ _ _ -> failInTermRec "CaseTerm"
    -- Term LetBrand [b] a Range
    , foldLetTerm = \_ _ _ _ _ -> failInTermRec "LetTerm"
    -- ProgEq a a Range
    , foldProgEq = \_ _ _ _ -> failInTermRec "ProgEq"
    -- Term Id [Type] [a] Range
    , foldResolvedMixTerm = \_ _ _ _ _ -> failInTermRec "ResolvedMixTerm"
    -- Term Token
    , foldTermToken = \_ _ -> failInTermRec "TermToken"
    -- TermTypeQual Type Range
    , foldMixTypeTerm = \_ _ _ _ -> failInTermRec "MixTypeTerm"
    -- Term [a]
    , foldMixfixTerm = \_ _ -> failInTermRec "MixfixTerm"
    -- Term BracketKind [a] Range
    , foldBracketTerm = \_ _ _ _ -> failInTermRec "BracketTerm"
    }



