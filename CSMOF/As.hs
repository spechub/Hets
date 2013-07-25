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

import qualified Data.Set as Set

-- Simplified MOF Metamodel

data Metamodel = Metamodel 
                 { metamodelName :: String
                 , element :: Set.Set NamedElement 
                 , model :: Set.Set Model 
                 } deriving (Eq, Ord)
                            
instance Show Metamodel where
  show (Metamodel nam ele mod) = 
    "Metamodel { name = " ++ nam ++ "\n" 
    ++ Set.fold ((++). show) "" ele
    ++ Set.fold ((++). show) "" mod
    ++ "} \n"
    
                        
data NamedElement = NamedElement
                    { namedElementName :: String
                    , namedElementOwner :: Metamodel
                    , namedElementSubClasses :: TypeOrTypedElement
                    } deriving (Eq, Ord)
                               
instance Show NamedElement where
  show (NamedElement nam met nes) = show nes
  
  
data TypeOrTypedElement = TType { getType :: Type }
                        | TTypedElement { getTypeElement :: TypedElement }
                        deriving (Eq, Ord)

instance Show TypeOrTypedElement where
  show (TType typ) = show typ
  show (TTypedElement typ) = show typ


data Type = Type { typeSuper :: NamedElement 
                 , typeSubClasses :: DataTypeOrClass
                 } deriving (Eq, Ord)

instance Show Type where
  show (Type sup sub) = show sub
  

data DataTypeOrClass = DataType
                     | DClass { getClass :: Class }
                     deriving (Eq, Ord)
                       
instance Show DataTypeOrClass where
  show (DataType) = show "DataType"
  show (DClass cla) = show cla


data Class = Class 
             { classSuper :: Type
             , isAbstract :: Bool
             , superClass :: Set.Set Class
             , ownedAttribute :: Set.Set Property
             } deriving (Eq, Ord)
                        
instance Show Class where
  show (Class sup isa supC own) = 
    "\t\t Class { name = " ++ namedElementName (typeSuper sup) ++ " , "
    ++ "abstract = " ++ show isa 
    ++ ", super = { " ++ Set.fold ((++). namedElementName . typeSuper . classSuper) "" supC ++ "}"
    -- TODO:: faltan los ownedAttribute
    ++ "} \n"


data TypedElement = TypedElement 
                    { typedElementSuper :: NamedElement 
                    , typedElementType :: Type 
                    , typedElementSubClasses :: Property
                    } deriving (Eq, Ord)
                               
instance Show TypedElement where
  show (TypedElement sup typ sub) = show sub

    
data Property = Property 
                { propertySuper ::TypedElement
                , multiplicityElement :: MultiplicityElement
                , opposite :: Maybe Property
                , propertyClass :: Class
                } deriving (Eq, Ord)
                           
instance Show Property where                           
  show (Property sup mul opp pro) =
    "Property { name = " ++ namedElementName (typedElementSuper sup) ++ ", "
    ++ show mul ++ ", "
    ++ case opp of
         Just n -> "opposite = " ++ namedElementName (typedElementSuper (propertySuper n))  ++ ","
         Nothing -> "opposite = EMPTY, "
    ++ "owner = " ++ namedElementName (typeSuper (classSuper pro))
    ++ "} \n"


data MultiplicityElement = MultiplicityElement 
                           { lower :: Integer
                           , upper :: Integer
                           , multiplicityElementSubClasses :: Property
                           } deriving (Eq, Ord)
                                      
instance Show MultiplicityElement where
  show (MultiplicityElement low upp mes) =
    "lower = " ++ show low ++ ", upper = " ++ show upp
                                      
  
-- Model part of CSMOF

data Model = Model 
             { modelName :: String
             , object :: Set.Set Object
             , link :: Set.Set Link
             , modelType :: Metamodel
             } deriving (Eq, Ord)
                        
instance Show Model where
  show (Model mon obj lin mod) =
    "Model { name = " ++ mon ++ "\n"
    ++ Set.fold ((++). show) "" obj
    ++ Set.fold ((++). show) "" lin
    ++ "} \n"
                        
    
data Object = Object 
              { objectName :: String
              , objectType :: Type
              , objectOwner :: Model
              } deriving (Eq, Ord)

instance Show Object where
  show (Object on ot oo) = 
    "\t Object { name = " ++ on
    ++ ", type = " ++ namedElementName (typeSuper ot)
    ++ " } \n"
    
                         
data Link = Link 
            { linkType :: Property
            , source :: Object
            , target :: Object
            , linkOwner :: Model
            } deriving (Eq, Ord)
                       
instance Show Link where
  show (Link lt sou tar ow) = 
    "\t Link { type = " ++ namedElementName (typedElementSuper (propertySuper lt)) ++ ", "
    ++ "source = " ++ objectName sou ++ ", "        
    ++ "target = " ++ objectName tar
    ++ "} \n"
    
    
    
    
----------------------------------------------------------

--main :: IO ()
 --main = let metamodel = Metamodel{metamodelName = "Class"
  --                               , element = Set.insert neUMLME (Set.insert neString Set.empty)
    --                             , model = Set.empty}
      --                 
        --    neString = NamedElement { namedElementName = "String"
          --                          , typeOrTypedElem = TType { getTypeType = DataType } 
            --                        , namedElementOwner = metamodel
              --                      }
                      
--            neUMLME = NamedElement { namedElementName = "UMLModelElement"
  --                                 , typeOrTypedElem = TType { getTypeType = 
    --                                                              TClass { getClass = 
      --                                                                        Class { isAbstract = True
        --                                                                            , superClass = Set.empty
          --                                                                          , ownedAttribute = Set.empty 
            --                                                                        } 
              --                                                           } 
                --                                             } 
                  --                 , namedElementOwner = metamodel
                    --               }

--        in
  --       putStrLn (show metamodel)
        
  -- <element xsi:type="CSMOF:Class" name="UMLModelElement" isAbstract="true" subClass="//@element.1 //@element.2 //@element.3">
  --   <ownedAttribute name="kind" type="//@element.6"/>
  --   <ownedAttribute name="name" type="//@element.6"/>
  -- </element>
  -- <element xsi:type="CSMOF:Class" name="Package" superClass="//@element.0">
  --   <ownedAttribute lower="0" upper="-1" name="elements" type="//@element.2" opposite="//@element.2/@ownedAttribute.0"/>
  -- </element>
  -- <element xsi:type="CSMOF:Class" name="Classifier" superClass="//@element.0" subClass="//@element.4 //@element.5">
  --   <ownedAttribute name="namespace" type="//@element.1" opposite="//@element.1/@ownedAttribute.0"/>
  -- </element>
  -- <element xsi:type="CSMOF:Class" name="Attribute" superClass="//@element.0">
  --   <ownedAttribute name="owner" type="//@element.4" opposite="//@element.4/@ownedAttribute.0"/>
  --   <ownedAttribute name="type" type="//@element.5"/>
  -- </element>
  -- <element xsi:type="CSMOF:Class" name="Class" superClass="//@element.2">
  --   <ownedAttribute lower="0" upper="-1" name="attribute" type="//@element.3" opposite="//@element.3/@ownedAttribute.0"/>
  -- </element>
  -- <element xsi:type="CSMOF:Class" name="PrimitiveDataType" superClass="//@element.2"/>

