{-# LANGUAGE ExistentialQuantification, DeriveDataTypeable
  , OverlappingInstances #-}
{- |
Module      :  ./TopHybrid/AS_TopHybrid.der.hs
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  nevrenato@gmail.com
Stability   :  experimental
Portability :  portable

Description :
Abstract syntax for an hybridized logic. Declaration
of the basic specification. Underlying Spec; Declaration
of nominals and modalities, and axioms.
-}

module TopHybrid.AS_TopHybrid where

import Common.AS_Annotation
import Common.Id
import Common.Json
import Common.ToXml

import Logic.Logic

import Unsafe.Coerce

import Data.Data
import Data.Monoid

import Text.XML.Light

-- DrIFT command
{-! global: GetRange !-}

{- Union of the the declaration of nominals/modalities and the
   spec correspondent to the underlying logic -}
data TH_BSPEC s = Bspec { bitems :: [TH_BASIC_ITEM], und :: s }
  deriving (Show, Typeable, Data)

-- Declaration of nominals/modalities
data TH_BASIC_ITEM = Simple_mod_decl [MODALITY]
                   | Simple_nom_decl [NOMINAL]
                     deriving (Show, Typeable, Data)

type MODALITY = SIMPLE_ID
type NOMINAL = SIMPLE_ID

{- The strucuture of an hybridized sentence, where f correponds to the
underlying logic -}
data TH_FORMULA f = At NOMINAL (TH_FORMULA f)
                  | Uni NOMINAL (TH_FORMULA f)
                  | Exist NOMINAL (TH_FORMULA f)
                  | Box MODALITY (TH_FORMULA f)
                  | Dia MODALITY (TH_FORMULA f)
                  | UnderLogic f
                  | Conjunction (TH_FORMULA f) (TH_FORMULA f)
                  | Disjunction (TH_FORMULA f) (TH_FORMULA f)
                  | Implication (TH_FORMULA f) (TH_FORMULA f)
                  | BiImplication (TH_FORMULA f) (TH_FORMULA f)
                  | Here NOMINAL
                  | Neg (TH_FORMULA f)
                  | Par (TH_FORMULA f)
                  | TrueA
                  | FalseA
                    deriving (Show, Eq, Ord, Typeable, Data)

instance ToJson f => ToJson (TH_FORMULA f) where
  asJson _ = mkJObj []

instance ToXml f => ToXml (TH_FORMULA f) where
  asXml _ = unode "missing" ()

{- Existential quantification is used, in the Sentences, Spec and Signature
because, we need to hide that these datatypes are polymorphic, or else,
haskell will complain that their types will vary with the same logic. Which
is forbidden in Logic class by using functional dependencies. -}

{- An hybridized formula has the hybrid constructors; the constructors
of the hybridized logic and the logic identifier, so that we can
identify the underlying logic, by only looking to the sentence. -}
data Frm_Wrap = forall l sub bs f s sm si mo sy rw pf .
    (Logic l sub bs f s sm si mo sy rw pf)
    => Frm_Wrap l (TH_FORMULA f)
  deriving Typeable

instance Show Frm_Wrap where
  show (Frm_Wrap l f) = "Frm_Wrap " ++ show l ++ " (" ++ show f ++ ")"

instance ToJson Frm_Wrap where
  asJson (Frm_Wrap l f) = mkJObj [("Frm_Wrap:" ++ show l, asJson f)]

instance ToXml Frm_Wrap where
  asXml (Frm_Wrap l f) =
    add_attr (mkAttr "language" $ show l) $ unode "Frm_Wrap" $ asXml f

{- An hybridized specification has the basic specification; The declararation
of nominals and modalities, and the axioms; -}
data Spc_Wrap = forall l sub bs sen si smi sign mor symb raw pf .
    (Logic l sub bs sen si smi sign mor symb raw pf)
    => Spc_Wrap l (TH_BSPEC bs) [Annoted Frm_Wrap]
  deriving Typeable

instance Show Spc_Wrap where
  show (Spc_Wrap l b a) =
    "Spc_Wrap " ++ show l ++ " (" ++ show b ++ ") " ++ show a

instance Semigroup Spc_Wrap where
  _ <> _ = error "Not implemented!"

instance Monoid Spc_Wrap where
 mempty = error "Not implemented!"

-- --- instances
data Mor = Mor deriving (Show, Eq, Ord, Typeable, Data)

-- Why do we need to compare specifications ?
instance Ord Spc_Wrap where
        compare _ _ = GT

instance Eq Spc_Wrap where
       (==) _ _ = False
-- --------------

-- Who do we need to order formulas ?
instance Ord Frm_Wrap where
        compare a b = if a == b then EQ else GT

{- Need to use unsafe coerce here, as the typechecker as no way to know
that if l == l' then type f == type f'. However, we know. -}
instance Eq Frm_Wrap where
       (==) (Frm_Wrap l f) (Frm_Wrap l' f') =
               (show l == show l') && (unsafeCoerce f == f')

-- Why do we need range ?
instance GetRange Frm_Wrap where
        getRange (Frm_Wrap _ f) = getRange f
        rangeSpan (Frm_Wrap _ f) = rangeSpan f

instance GetRange Spc_Wrap where
        getRange (Spc_Wrap _ s _) = getRange s
        rangeSpan (Spc_Wrap _ s _) = rangeSpan s
