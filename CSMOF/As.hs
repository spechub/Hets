{- |
Module      :  $Header$
Description :  abstract CSMOF syntax
Copyright   :  (c) Daniel Calegari Universidad de la Republica, Uruguay 2013
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  dcalegar@fing.edu.uy
Stability   :  provisional
Portability :  portable
-}


module CSMOF.As where

import Common.Id

-- Simplified MOF Metamodel

data Metamodel = Metamodel 
                 { metamodelName :: String
                 , element :: [NamedElement]
                 , model :: [Model]
                 } deriving (Eq, Ord)

instance GetRange Metamodel where
 getRange _ = nullRange
 rangeSpan _ = []

    
data NamedElement = NamedElement
                    { namedElementName :: String
                    , namedElementOwner :: Metamodel
                    , namedElementSubClasses :: TypeOrTypedElement
                    } deriving (Eq, Ord)
                       
instance GetRange NamedElement where
 getRange _ = nullRange
 rangeSpan _ = []

            
data TypeOrTypedElement = TType { getType :: Type }
                        | TTypedElement { getTypeElement :: TypedElement }
                        deriving (Eq, Ord)

instance GetRange TypeOrTypedElement where
 getRange _ = nullRange
 rangeSpan _ = []

  
-- When going downside-up, we can sort the auxiliary class TypeOrTypedElement and make super of type NamedElement 
data Type = Type { typeSuper :: NamedElement 
                 , typeSubClasses :: DataTypeOrClass
                 } deriving (Eq, Ord)

instance GetRange Type where
 getRange _ = nullRange
 rangeSpan _ = []


data DataTypeOrClass = DDataType { getDataType :: DataType }
                     | DClass { getClass :: Class }
                     deriving (Eq, Ord)
                      
instance GetRange DataTypeOrClass where
 getRange _ = nullRange
 rangeSpan _ = [] 


-- When going downside-up, we can sort the auxiliary class DataTypeOrClass and make super of type Type 
data DataType = DataType { classSuper :: Type } deriving (Eq, Ord)
                        
instance GetRange DataType where
 getRange _ = nullRange
 rangeSpan _ = [] 


-- When going downside-up, we can sort the auxiliary class DataTypeOrClass and make super of type Type 
data Class = Class 
             { classSuperType :: Type
             , isAbstract :: Bool
             , superClass :: [Class]
             , ownedAttribute :: [Property]
             } deriving (Eq, Ord)

instance GetRange Class where
 getRange _ = nullRange
 rangeSpan _ = [] 


-- When going downside-up, we can sort the auxiliary class TypeOrTypedElement and make super of type NamedElement 
data TypedElement = TypedElement 
                    { typedElementSuper :: NamedElement 
                    , typedElementType :: Type 
                    , typedElementSubClasses :: Property
                    } deriving (Eq, Ord)
                  
instance GetRange TypedElement where
 getRange _ = nullRange
 rangeSpan _ = [] 
             
        
data Property = Property 
                { propertySuper ::TypedElement
                , multiplicityElement :: MultiplicityElement
                , opposite :: Maybe Property
                , propertyClass :: Class
                } deriving (Eq, Ord)                         
    
instance GetRange Property where
 getRange _ = nullRange
 rangeSpan _ = [] 


data MultiplicityElement = MultiplicityElement 
                           { lower :: Integer
                           , upper :: Integer
                           , multiplicityElementSubClasses :: Property
                           } deriving (Eq, Ord)

instance GetRange MultiplicityElement where
 getRange _ = nullRange
 rangeSpan _ = []                                       
                                     
  
-- Model part of CSMOF

data Model = Model 
             { modelName :: String
             , object :: [Object]
             , link :: [Link]
             , modelType :: Metamodel
             } deriving (Eq, Ord)
                       
instance GetRange Model where
 getRange _ = nullRange
 rangeSpan _ = []      
 
    
data Object = Object 
              { objectName :: String
              , objectType :: Type
              , objectOwner :: Model
              } deriving (Eq, Ord)

instance GetRange Object where
 getRange _ = nullRange
 rangeSpan _ = []      

                         
data Link = Link 
            { linkType :: Property
            , source :: Object
            , target :: Object
            , linkOwner :: Model
            } deriving (Eq, Ord)                       

instance GetRange Link where
 getRange _ = nullRange
 rangeSpan _ = []      
