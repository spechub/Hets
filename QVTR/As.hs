{- |
Module      :  $Header$
Description :  abstract QVT-Relational syntax
Copyright   :  (c) Daniel Calegari Universidad de la Republica, Uruguay 2013
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  dcalegar@fing.edu.uy
Stability   :  provisional
Portability :  portable
-}


module QVTR.As where

import Common.Id

import qualified CSMOF.As as CSMOF

-- Simplified QVTR Tranformation

data Transformation = Transformation 
                 { transfName :: String
                 , sourceMetamodel :: (String,String,CSMOF.Metamodel)
                 , targetMetamodel :: (String,String,CSMOF.Metamodel)
                 , keys :: [Key]
                 , relations :: [Relation]
                 } deriving (Eq, Ord)

instance GetRange Transformation where
  getRange _ = nullRange
  rangeSpan _ = []


data Key = Key
        { metamodel :: String
        , typeName :: String
        , properties :: [PropKey]
        } deriving (Eq, Ord)

instance GetRange Key where
  getRange _ = nullRange
  rangeSpan _ = []


data PropKey = SimpleProp { propName :: String }
             | OppositeProp { oppPropType :: String, oppPropName :: String }
             deriving (Eq, Ord)

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
              } deriving (Eq, Ord)

instance GetRange Relation where
  getRange _ = nullRange
  rangeSpan _ = []


data RelVar = RelVar 
            { varType :: String
            , varName :: String 
            } deriving (Eq, Ord)

instance GetRange RelVar where
  getRange _ = nullRange
  rangeSpan _ = []


data PrimitiveDomain = PrimitiveDomain 
                     { primName :: String
                     , primType :: String 
                     } deriving (Eq, Ord)

instance GetRange PrimitiveDomain where
  getRange _ = nullRange
  rangeSpan _ = []


data Domain = Domain
            { domMeta :: String
            , domVar :: String
            , domType :: String
            , pattern :: Pattern
            } deriving (Eq, Ord)

instance GetRange Domain where
  getRange _ = nullRange
  rangeSpan _ = []


data Pattern = Pattern 
             { patElems :: [RelVar]
             , patRels :: [(String,RelInvok)]
             , patPredicate :: String
             } deriving (Eq, Ord)

instance GetRange Pattern where
  getRange _ = nullRange
  rangeSpan _ = []


data WhenWhere = When { relInvokWhen :: [RelInvok], oclExpreWhen :: [String] } 
               | Where { relInvokWhere :: [RelInvok], oclExpreWhere :: [String] } deriving (Eq, Ord)   

instance GetRange WhenWhere where
  getRange _ = nullRange
  rangeSpan _ = []

       
data RelInvok = RelInvok 
              { name :: String
              , params :: [String] 
              } deriving (Eq, Ord)

instance GetRange RelInvok where
  getRange _ = nullRange
  rangeSpan _ = []

