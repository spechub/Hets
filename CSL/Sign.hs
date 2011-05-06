{- |
Module      :  $Header$
Description :  Signature for propositional logic
Copyright   :  (c) Dominik Dietrich, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  dominik.dietrich@dfki.de
Stability   :  experimental
Portability :  portable

Definition of signatures for CSL logic, which are just lists of operators
-}

module CSL.Sign
    (Sign (..)                     -- Propositional Signatures
    ,OpType (..)                   -- Operator Information attached to ids
    ,pretty                        -- pretty printing
    ,isLegalSignature              -- is a signature ok?
    ,addToSig                      -- adds an id to the given Signature
    ,addVarItem                    -- adds a var item to the given Signature
    ,addEPComponent                -- adds a raw ext param decl to the given Signature
    ,combineEPDecls
    ,unite                         -- union of signatures
    ,emptySig                      -- empty signature
    ,isSubSigOf                    -- is subsiganture?
    ,sigDiff                       -- Difference of Signatures
    ,sigUnion                      -- Union for Logic.Logic
    ,lookupSym
    ,optypeFromArity
    ) where

import qualified Data.Map as Map
import Common.Id
import Common.Result
import Common.Doc
import Common.DocUtils

import CSL.AS_BASIC_CSL
import CSL.Print_AS ()
import CSL.TreePO

data OpType = OpType { opArity :: Int
                     } deriving (Eq, Ord, Show)

defaultType :: OpType
defaultType = OpType { opArity = 0 }

optypeFromArity :: Int -> OpType
optypeFromArity i = defaultType { opArity = i }

-- | Datatype for CSL Signatures
-- Signatures are just sets of Tokens for the operators
data Sign = Sign { items :: Map.Map Id OpType
                 , vardecls :: Map.Map Token Domain
                 , epdecls :: Map.Map Token EP_item
                 } deriving (Eq, Ord, Show)

-- | The empty signature, use this one to create new signatures
emptySig :: Sign
emptySig = Sign { items = Map.empty
                , vardecls = Map.empty
                , epdecls = Map.empty
                }

instance Pretty Sign where
    pretty = printSign

-- | checks whether a Id is declared in the signature
lookupSym :: Sign -> Id -> Bool
lookupSym sig item = Map.member item $ items sig

-- TODO: adapt the operations to new signature components

-- | pretty printer for CSL signatures
printSign :: Sign -> Doc
printSign s =
--    hsep [text "operator", sepByCommas $ map pretty $ Map.keys $ items s]
    vsep [ hsep [ text "vars"
                , sepBySemis $ map f $ Map.toList $ vardecls s ]
         , hsep [ text "eps"
                , sepBySemis $ map pretty $ Map.elems $ epdecls s ]
         ]
    where f (k, dom) = pretty k <+> text "in" <+> pretty dom

-- | determines whether a signature is valid. all sets are ok, so glued to true
isLegalSignature :: Sign -> Bool
isLegalSignature _ = True

-- | Basic function to extend a given signature by adding an item (id) to it
addToSig :: Sign -> Id -> OpType -> Sign
addToSig sig tok ot = sig {items = Map.insert tok ot $ items sig}

-- | Basic function to extend a given signature by adding a var item to it
addVarItem :: Sign -> [Token] -> Domain -> Sign
addVarItem sig toks dom = foldl addvi sig toks where
    addvi sg tok = sg {vardecls = Map.insert tok dom $ vardecls sg}

-- | Basic function to extend a given signature by adding an extparam component.
addEPComponent :: Sign -> EPComponent -> Sign
addEPComponent sig epc =
    let (n, epd) = epCompToItem epc
    in sig { epdecls = Map.insertWith combineEPDecls n epd $ epdecls sig}

epCompToItem :: EPComponent -> (Token, EP_item)
epCompToItem (EPDomain s dom) = (s, EP_item s (Just dom) Nothing)
epCompToItem (EPDefault s val) = (s, EP_item s Nothing (Just val))
epCompToItem (EPSimple s) = (s, EP_item s Nothing Nothing)

-- TODO: add support for vardecls and epdecls and report errors if they do not match!

{- Two signatures s1 and s2 are compatible if the common part has the
   following properties:

   * if the default value of an extparam is defined in s1 and s2 it has to be the same
   * if the domains (of extparams or vars) are both given, they must not be disjoint
   * the arities must conincide for the same operator

-}

{- | Chooses from two 'Maybe' values the one containing the 'Just'
     value ore 'Nothing' if both are 'Nothing'. Fails on two 'Just'
     values
-}
chooseJust :: Maybe a -> Maybe a -> Maybe a
chooseJust a@(Just _) Nothing = a
chooseJust Nothing b@(Just _) = b
chooseJust Nothing b = b
chooseJust _ _ = error "chooseJust: called on two just vals"



{- | Combines two extended parameter declarations for the same parameter.
     The default values, if given, must coincide, and the domains must be
     comparable, in this case the smaller one is choosen.
-}
combineEPDecls :: EP_item -> EP_item -> EP_item
combineEPDecls (EP_item n1 mDom1 mDft1) (EP_item n2 mDom2 mDft2)
    | n1 /= n2 = error $ "combineEPDecls: name-mismatch for extended parameter "
                 ++ show n1 ++ " and " ++ show n2
    | otherwise =
        let mDft = case (mDft1, mDft2) of
                     (Just a, Just b) -> -- the values have to be the same
                        if a == b then Just a
                         else error $ "combineEPDecls: default value mismatch"
                                  ++ " for extended parameter "
                                  ++ show (pretty n1) ++ ": "
                                  ++ show a ++ ", " ++ show b
                     _ -> chooseJust mDft1 mDft2
            mDom = case (mDom1, mDom2) of
                      -- the domains must be comparable
                     (Just d1, Just d2) ->
                         case cmpSoIsD d1 d2 of
                           Incomparable _ ->
                               error $ "combineEPDecls: domains incomparable for "
                                         ++ "extended parameter "
                                         ++ show (pretty n1) ++ ": "
                                         ++ show (pretty d1) ++ show (pretty d2)
                           Comparable LT -> mDom1
                           _ -> mDom2

                     _ -> chooseJust mDom1 mDom2
        in EP_item n1 mDom mDft

-- | Union of signatures
unite :: Sign -> Sign -> Sign
unite sig1 sig2 =
    sig1 { items = Map.union (items sig1) $ items sig2 
         , epdecls = Map.unionWith combineEPDecls (epdecls sig1) $ epdecls sig2 
         }

-- | Determines if sig1 is subsignature of sig2
isSubSigOf :: Sign -> Sign -> Bool
isSubSigOf sig1 sig2 = Map.isSubmapOf (items sig1) $ items sig2

-- | difference of Signatures
sigDiff :: Sign -> Sign -> Sign
sigDiff sig1 sig2 = sig1 {items = Map.difference (items sig1) $ items sig2}

-- | union of Signatures
-- or do I have to care about more things here?
sigUnion :: Sign -> Sign -> Result Sign
sigUnion s1 = Result [Diag Debug "All fine sigUnion" nullRange]
    . Just . unite s1
