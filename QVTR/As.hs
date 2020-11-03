{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}
{- |
Module      :  ./QVTR/As.hs
Description :  abstract QVT-Relational syntax
Copyright   :  (c) Daniel Calegari Universidad de la Republica, Uruguay 2013
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  dcalegar@fing.edu.uy
Stability   :  provisional
Portability :  portable
-}


module QVTR.As where

import Common.Id

import Data.Data

import qualified CSMOF.As as CSMOF
import GHC.Generics (Generic)
import Data.Hashable

-- Simplified QVTR Tranformation

data Transformation = Transformation
                 { transfName :: String
                 , sourceMetamodel :: (String, String, CSMOF.Metamodel)
                 , targetMetamodel :: (String, String, CSMOF.Metamodel)
                 , keys :: [Key]
                 , relations :: [Relation]
                 } deriving (Eq, Ord, Typeable, Data)

instance GetRange Transformation where
  getRange _ = nullRange
  rangeSpan _ = []


data Key = Key
        { metamodel :: String
        , typeName :: String
        , properties :: [PropKey]
        } deriving (Eq, Ord, Typeable, Data, Generic)

instance Hashable Key

instance GetRange Key where
  getRange _ = nullRange
  rangeSpan _ = []


data PropKey = SimpleProp { propName :: String }
             | OppositeProp { oppPropType :: String, oppPropName :: String }
             deriving (Eq, Ord, Typeable, Data, Generic)

instance Hashable PropKey

instance GetRange PropKey where
  getRange _ = nullRange
  rangeSpan _ = []


data Relation = Relation
              { top :: Bool
              , relName :: String
              , varSet :: [RelVar]
              , primDomains :: [PrimitiveDomain]
              , sourceDomain :: Domain
              , targetDomain :: Domain
              , whenCond :: Maybe WhenWhere
              , whereCond :: Maybe WhenWhere
              } deriving (Eq, Ord, Typeable, Data)

instance GetRange Relation where
  getRange _ = nullRange
  rangeSpan _ = []


data RelVar = RelVar
            { varType :: String
            , varName :: String
            } deriving (Eq, Ord, Typeable, Data, Generic)

instance Hashable RelVar

instance GetRange RelVar where
  getRange _ = nullRange
  rangeSpan _ = []


data PrimitiveDomain = PrimitiveDomain
                     { primName :: String
                     , primType :: String
                     } deriving (Eq, Ord, Typeable, Data)

instance GetRange PrimitiveDomain where
  getRange _ = nullRange
  rangeSpan _ = []


data Domain = Domain
            { domModelId :: String
            , template :: ObjectTemplate
            } deriving (Eq, Ord, Typeable, Data)

instance GetRange Domain where
  getRange _ = nullRange
  rangeSpan _ = []


data ObjectTemplate = ObjectTemplate
                    { domVar :: String
                    , domMeta :: String
                    , domType :: String
                    , templateList :: [PropertyTemplate]
                    } deriving (Eq, Ord, Typeable, Data)

instance GetRange ObjectTemplate where
  getRange _ = nullRange
  rangeSpan _ = []


data PropertyTemplate = PropertyTemplate
                      { pName :: String
                      , oclExpre :: Maybe OCL
                      , objTemp :: Maybe ObjectTemplate
                      } deriving (Eq, Ord, Typeable, Data)

instance GetRange PropertyTemplate where
  getRange _ = nullRange
  rangeSpan _ = []


data WhenWhere = WhenWhere { relInvokWhen :: [RelInvok], oclExpreWhen :: [OCL] }
  deriving (Eq, Ord, Typeable, Data, Generic)

instance Hashable WhenWhere

instance GetRange WhenWhere where
  getRange _ = nullRange
  rangeSpan _ = []


data RelInvok = RelInvok
              { name :: String
              , params :: [String]
              } deriving (Eq, Ord, Typeable, Data, Generic)

instance Hashable RelInvok

instance GetRange RelInvok where
  getRange _ = nullRange
  rangeSpan _ = []


-- Fake OCL expressions

data OCL = Paren { exp :: OCL }
         | StringExp { strExp :: STRING }
         | BExp { bExp :: Bool }
         | NotB { notExp :: OCL }
         | AndB { lExpA :: OCL, rExpA :: OCL }
         | OrB { lExpO :: OCL, rExpO :: OCL }
         | Equal { lExpre :: STRING, rExpre :: STRING }
         deriving (Eq, Ord, Typeable, Data, Generic)

instance Hashable OCL

instance GetRange OCL where
  getRange _ = nullRange
  rangeSpan _ = []


data STRING = Str { simpleStr :: String }
            | ConcatExp { lStr :: STRING, rStr :: STRING }
            | VarExp { varExp :: String }
            deriving (Eq, Ord, Typeable, Data, Generic)

instance Hashable STRING

instance GetRange STRING where
  getRange _ = nullRange
  rangeSpan _ = []
