{- |
Module      :  $Header$
Description :  Guarded Dependency Store
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  experimental
Portability :  portable

Definition of guarded dependencies resulting from the use of extended
parameters.

-}


module CSL.GuardedDependencies
    where

import Common.AS_Annotation
import Common.Doc
import Common.DocUtils

import CSL.AS_BASIC_CSL
import CSL.Sign as Sign
import CSL.EPRelation

import Control.Monad
import qualified Data.Set as Set
import qualified Data.Map as Map

-- ** Datatypes and guarded definitions



-- | A guard consists of the guard range and the corresponding expression
-- together with a name, a set of not propagated parameters and a set of
-- constrained parameters (in the extended parameter specification)
data Guard a = Guard { range :: a
                     , definition :: EXPRESSION
                     , assName :: String
                     , filtered :: Set.Set String
                     , constrained :: Set.Set String }


prettyGuard :: (a -> Doc) -> Guard a -> Doc
prettyGuard f g = f (range g) <+> text "-->" <+> pretty (definition g)

instance Functor Guard where
    fmap f (Guard x e an fs ct) = Guard (f x) e an fs ct

instance Pretty a => Pretty (Guard a) where
    pretty = prettyGuard pretty

instance Pretty a => Show (Guard a) where
    show = show . pretty

-- | A guarded constant consists of the argument list (for function definitions)
-- and a list of guard-expressions
data Guarded a = Guarded { argvars :: [String]
                         , guards :: [Guard a] }

{- Comment it in if needed later

undefinedGuard :: String -> a -> Guard a
undefinedGuard s x = Guard { range = x
                           , definition = err
                           , assName = err
                           , filtered = err
                           , constrained = err }
    where err = error $ "undefinedGuard: " ++ s

undefinedGuarded :: String -> a -> Guarded a
undefinedGuarded s x = Guarded { argvars = []
                               , guards = [undefinedGuard s x] }
-}


prettyGuarded :: (a -> Doc) -> Guarded a -> Doc
prettyGuarded f grdd = vcat $ map (prettyGuard f) $ guards grdd

instance Functor Guarded where
    fmap f grdd = grdd { guards = map (fmap f) $ guards grdd }

instance Pretty a => Pretty (Guarded a) where
    pretty = prettyGuarded pretty

instance Pretty a => Show (Guarded a) where
    show = show . pretty


type GuardedMap a = Map.Map String (Guarded a)


addAssignment :: String -> OpDecl -> EXPRESSION -> GuardedMap [EXTPARAM]
              -> GuardedMap [EXTPARAM]
addAssignment n (OpDecl sc epl al _) def m =
    let combf x y | argvars x == argvars y = y { guards = guards y ++ guards x }
                  | otherwise =
                      error "addAssignment: the argument vars does not match."
        grd = Guarded (map varDeclName al) [uncurry (Guard epl def n)
                                              $ filteredConstrainedParams epl]
    in Map.insertWith combf (simpleName $ OpUser sc) grd m

{-  TODO:
    1. analysis for missing definitions and undeclared extparams
    2. Integrating extparam domain definitions
    3. check for each constant if the Guards exhaust the extparam domain (in splitAS)
-}

-- | Splits the Commands into the AssignmentStore and a program sequence
splitAS :: [Named CMD] -> (GuardedMap [EXTPARAM], [Named CMD])
splitAS cl =
    let f nc (m,l) = case sentence nc of
                       Ass c def -> (addAssignment (senAttr nc) c def m, l)
                       _ -> (m, nc:l)
    in foldr f (Map.empty, []) cl


