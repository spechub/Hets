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
            { domModelId :: String
            , template :: ObjectTemplate
            } deriving (Eq, Ord)

instance GetRange Domain where
  getRange _ = nullRange
  rangeSpan _ = []


data ObjectTemplate = ObjectTemplate
                    { domVar :: String
                    , domMeta :: String
                    , domType :: String
                    , templateList :: [PropertyTemplate]
                    } deriving (Eq, Ord)

instance GetRange ObjectTemplate where
  getRange _ = nullRange
  rangeSpan _ = []


data PropertyTemplate = PropertyTemplate
                      { pName :: String
                      , oclExpre :: Maybe OCL
                      , objTemp :: Maybe ObjectTemplate
                      } deriving (Eq, Ord)

instance GetRange PropertyTemplate where
  getRange _ = nullRange
  rangeSpan _ = []


data WhenWhere = WhenWhere { relInvokWhen :: [RelInvok], oclExpreWhen :: [OCL] } deriving (Eq, Ord)   

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


-- Fake OCL expressions

data OCL = IFExpre { cond :: EXPRE, thenExpre :: OCL, elseExpre :: OCL }
         | OCLExpre { expre :: EXPRE }
         | Equal { lExp :: OCL, rExp :: OCL}
         deriving (Eq, Ord)

instance GetRange OCL where
  getRange _ = nullRange
  rangeSpan _ = []      


data EXPRE = Paren { exp :: EXPRE }
           | StringExp { strExp :: STRING }
           | BExp { bExp :: Bool }
           | NotB { notExp :: EXPRE }
           | AndB { lExpA :: EXPRE, rExpA :: EXPRE }
           | OrB { lExpO :: EXPRE, rExpO :: EXPRE }
           | EqualExp { lExpre :: EXPRE, rExpre :: EXPRE}
           deriving (Eq, Ord)

instance GetRange EXPRE where
  getRange _ = nullRange
  rangeSpan _ = []      


data STRING = Str { simpleStr :: String }
            | ConcatExp { lStr :: STRING, rStr :: STRING }
            | VarExp { varExp :: String }
            deriving (Eq, Ord)

instance GetRange STRING where
  getRange _ = nullRange
  rangeSpan _ = []      