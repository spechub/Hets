{- |
Module      :  $Header$
Description :  composition tables of qualitative calculi
Copyright   :  (c) Uni Bremen 2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

composition tables
-}

module CASL.CompositionTable.CompositionTable where

data Table = Table Table_Attrs Compositiontable Conversetable
             Reflectiontable Models
             deriving (Eq,Show)

data Table_Attrs = Table_Attrs
    { tableName :: String
    , tableIdentity :: Baserel
    , baseRelations :: [Baserel]
    } deriving (Eq, Show)

newtype Compositiontable = Compositiontable [Cmptabentry]
    deriving (Eq, Show)

data Conversetable = Conversetable [Contabentry] |
        Conversetable_Ternary
        { inverse, shortcut, homing :: [Contabentry_Ternary] }
    deriving (Eq, Show)

data Reflectiontable = Reflectiontable [Reftabentry]
     deriving (Eq, Show)

newtype Models = Models [Model]
    deriving (Eq, Show)

data Cmptabentry = Cmptabentry Cmptabentry_Attrs [Baserel]
                   deriving (Eq, Show)

data Cmptabentry_Attrs = Cmptabentry_Attrs
    { cmptabentryArgBaserel1 :: Baserel
    , cmptabentryArgBaserel2 :: Baserel
    } deriving (Eq, Show)

data Contabentry = Contabentry
    { contabentryArgBaseRel :: Baserel
    , contabentryConverseBaseRel :: Baserel
    } deriving (Eq, Show)

data Contabentry_Ternary = Contabentry_Ternary
    { contabentry_TernaryArgBaseRel :: Baserel
    , contabentry_TernaryConverseBaseRels :: [Baserel]
    } deriving (Eq, Show)

data Reftabentry = Reftabentry
     { reftabentryArgBaseRel :: Baserel
     , reftabentryReflectiveBaseRel :: Baserel
     } deriving (Eq,Show)

data Model = Model
    { modelString1 :: String
    , modelString2 :: String
    } deriving (Eq, Show)

data Baserel = Baserel
    { baserelBaserel :: String
    } deriving (Eq, Ord)

instance Show Baserel where
 show (Baserel b) = "Baserel: " ++ b
