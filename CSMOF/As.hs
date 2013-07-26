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

-- Simplified MOF Metamodel

data Metamodel = Metamodel 
                 { metamodelName :: String
                 , element :: [NamedElement]
                 , model :: [Model]
                 } deriving (Eq, Ord)
                        
    
data NamedElement = NamedElement
                    { namedElementName :: String
                    , namedElementOwner :: Metamodel
                    , namedElementSubClasses :: TypeOrTypedElement
                    } deriving (Eq, Ord)
                        
            
data TypeOrTypedElement = TType { getType :: Type }
                        | TTypedElement { getTypeElement :: TypedElement }
                        deriving (Eq, Ord)

  
-- When going downside-up, we can sort the auxiliary class TypeOrTypedElement and make super of type NamedElement 
data Type = Type { typeSuper :: NamedElement 
                 , typeSubClasses :: DataTypeOrClass
                 } deriving (Eq, Ord)


data DataTypeOrClass = DDataType { getDataType :: DataType }
                     | DClass { getClass :: Class }
                     deriving (Eq, Ord)
                       

-- When going downside-up, we can sort the auxiliary class DataTypeOrClass and make super of type Type 
data DataType = DataType { classSuper :: Type } deriving (Eq, Ord)
                        

-- When going downside-up, we can sort the auxiliary class DataTypeOrClass and make super of type Type 
data Class = Class 
             { classSuperType :: Type
             , isAbstract :: Bool
             , superClass :: [Class]
             , ownedAttribute :: [Property]
             } deriving (Eq, Ord)


-- When going downside-up, we can sort the auxiliary class TypeOrTypedElement and make super of type NamedElement 
data TypedElement = TypedElement 
                    { typedElementSuper :: NamedElement 
                    , typedElementType :: Type 
                    , typedElementSubClasses :: Property
                    } deriving (Eq, Ord)
                               
        
data Property = Property 
                { propertySuper ::TypedElement
                , multiplicityElement :: MultiplicityElement
                , opposite :: Maybe Property
                , propertyClass :: Class
                } deriving (Eq, Ord)                         
    

data MultiplicityElement = MultiplicityElement 
                           { lower :: Integer
                           , upper :: Integer
                           , multiplicityElementSubClasses :: Property
                           } deriving (Eq, Ord)
                                      
                                     
  
-- Model part of CSMOF

data Model = Model 
             { modelName :: String
             , object :: [Object]
             , link :: [Link]
             , modelType :: Metamodel
             } deriving (Eq, Ord)
                        
    
data Object = Object 
              { objectName :: String
              , objectType :: Type
              , objectOwner :: Model
              } deriving (Eq, Ord)

                         
data Link = Link 
            { linkType :: Property
            , source :: Object
            , target :: Object
            , linkOwner :: Model
            } deriving (Eq, Ord)                       

