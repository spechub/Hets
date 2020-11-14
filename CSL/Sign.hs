{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./CSL/Sign.hs
Description :  Signatures for the EnCL logic
Copyright   :  (c) Dominik Dietrich, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  dominik.dietrich@dfki.de
Stability   :  experimental
Portability :  portable

Types and functions for EnCL logic signatures
-}

module CSL.Sign
    ( Sign (Sign)                   -- EnCL Signatures
    , opIds
    , OpType (..)                   -- Operator Information attached to ids
    , pretty                        -- pretty printing
    , isLegalSignature              -- is a signature ok?
    , addToSig                      -- adds an id to the given Signature
    , unite                         -- union of signatures
    , emptySig                      -- empty signature
    , isSubSigOf                    -- is subsiganture?
    , sigDiff                       -- Difference of Signatures
    , sigUnion                      -- Union for Logic.Logic
    , lookupSym
    , optypeFromArity
    , addEPDefValToSig
    , addEPDeclToSig
    , addEPDomVarDeclToSig
    ) where

import Data.Data
import Data.Maybe
import qualified Data.HashMap.Strict as Map
import qualified Data.HashSet as Set

import Common.Id
import Common.Result
import Common.Doc
import Common.DocUtils
import qualified Common.OrderedMap as OMap

import CSL.TreePO (ClosedInterval (ClosedInterval))
import CSL.AS_BASIC_CSL
import CSL.Print_AS ()

data OpType = OpType { opArity :: Int
                     } deriving (Show, Eq, Ord, Typeable, Data)

defaultType :: OpType
defaultType = OpType { opArity = 0 }

optypeFromArity :: Int -> OpType
optypeFromArity i = defaultType { opArity = i }

{- | Datatype for EnCL Signatures
Signatures are just sets of Tokens for the operators -}
data Sign = Sign { items :: Map.HashMap Token OpType
                 , epvars :: Map.HashMap Token (Maybe APInt)
                 , epdecls :: Map.HashMap Token EPDecl
                 } deriving (Show, Eq, Ord, Typeable, Data)

opIds :: Sign -> Set.HashSet Id
opIds = Set.map simpleIdToId . Set.fromList . Map.keys . items

-- | The empty signature, use this one to create new signatures
emptySig :: Sign
emptySig = Sign { items = Map.empty
                , epvars = Map.empty
                , epdecls = Map.empty
                }

instance Pretty Sign where
    pretty = printSign

-- | pretty printer for EnCL signatures
printSign :: Sign -> Doc
printSign s = vcat [ printEPVars $ Map.toList $ epvars s
                   , printEPDecls $ Map.elems $ epdecls s]

printEPVars :: [(Token, Maybe APInt)] -> Doc
printEPVars [] = empty
printEPVars l = hsep [text "set", sepBySemis $ map f l] where
    f (x, Nothing) = pretty x
    f (x, Just y) = hcat [pretty x, text "=", pretty y]

printEPDecls :: [EPDecl] -> Doc
printEPDecls l = vcat $ map f l where
    f x = hsep [text "ep", pretty x]


-- | checks whether a Id is declared in the signature
lookupSym :: Sign -> Id -> Bool
lookupSym sig item = Map.member (idToSimpleId item) $ items sig

-- TODO: adapt the operations to new signature components


-- | determines whether a signature is valid. all sets are ok, so glued to true
isLegalSignature :: Sign -> Bool
isLegalSignature _ = True

-- | Basic function to extend a given signature by adding an item (id) to it
addToSig :: Sign -> Token -> OpType -> Sign
addToSig sig tok ot = sig {items = Map.insert tok ot $ items sig}


addEPDefValToSig :: Sign -> Token -> APInt -> Sign
addEPDefValToSig sig tok i
    | isNothing mD = error $ "addEPDefValToSig: The extended parameter"
                      ++ " declaration for " ++ show tok ++ " is missing"
    | otherwise = sig {epdecls = ed'}
    where (mD, ed') = OMap.insertLookupWithKey f tok err $ epdecls sig
          err = error "addEPDefValToSig: dummyval"
          f _ _ (EPDecl _ dom Nothing) = EPDecl tok dom $ Just i
          f _ _ (EPDecl _ _ (Just j)) =
              error $ "addEPDefValToSig: default value already set to "
                        ++ show j

addEmptyEPDomVarDeclToSig :: Sign -> Token -> Sign
addEmptyEPDomVarDeclToSig sig tok = sig {epvars = ev'}
    where ev' = Map.insertWith f tok Nothing $ epvars sig
          f _ v = v

addEPDomVarDeclToSig :: Sign -> Token -> APInt -> Sign
addEPDomVarDeclToSig sig tok i = sig {epvars = ev'}
    where ev' = Map.insertWith f tok (Just i) $ epvars sig
          f _ (Just x)
              | x == i = error $ "addEPDomVarDeclToSig: equal values for "
                         ++ show tok
              | otherwise = error $ "addEPDomVarDeclToSig: variable already"
                            ++ " set to different value " ++ show tok ++ "="
                            ++ show x
          f n _ = n

{- | Adds an extended parameter declaration for a given domain and
eventually implicitly defined EP domain vars, e.g., for 'I = [0, n]'
'n' is implicitly added -}
addEPDeclToSig :: Sign -> Token -> EPDomain -> Sign
addEPDeclToSig sig tok dom = g $ sig {epdecls = ed'}
    where (mD, ed') = OMap.insertLookupWithKey f tok epd $ epdecls sig
          epd = EPDecl tok dom Nothing
          f _ _ v@(EPDecl _ dom' _)
              | dom' == dom = v
              | otherwise = error $ "addEPDeclToSig: EP already"
                            ++ " assigned another domain: " ++ show tok ++ "in"
                            ++ show dom'
          g s =
              case (mD, dom) of
                (Nothing, ClosedInterval a b) ->
                    case mapMaybe getEPVarRef [a, b] of
                      [] -> s
                      l -> foldl addEmptyEPDomVarDeclToSig s l
                _ -> s


-- TODO: add support for epdecls and report errors if they do not match!

{- Two signatures s1 and s2 are compatible if the common part has the
   following properties:

   * if the default value of an extparam is defined in s1 and s2 it has to be the same
   * if the domains (of extparams or vars) are both given, they must not be disjoint
   * the arities must conincide for the same operator

-}

-- | Union of signatures
unite :: Sign -> Sign -> Sign
unite sig1 sig2 =
    sig1 { items = Map.union (items sig1) $ items sig2
         }

-- | Determines if sig1 is subsignature of sig2
isSubSigOf :: Sign -> Sign -> Bool
isSubSigOf sig1 sig2 = Map.isSubmapOf (items sig1) $ items sig2

-- | difference of Signatures
sigDiff :: Sign -> Sign -> Sign
sigDiff sig1 sig2 = sig1 {items = Map.difference (items sig1) $ items sig2}

{- | union of Signatures
or do I have to care about more things here? -}
sigUnion :: Sign -> Sign -> Result Sign
sigUnion s1 = Result [Diag Debug "All fine sigUnion" nullRange]
    . Just . unite s1
