{- |
Module      :  $Header$
Description :  pretty printing for CSMOF
Copyright   :  (c) Daniel Calegari Universidad de la Republica, Uruguay 2013
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  dcalegar@fing.edu.uy
Stability   :  provisional
Portability :  portable
-}


module CSMOF.Print where

import CSMOF.As

                            
instance Show Metamodel where
  show (Metamodel nam ele mod) = 
    "metamodel " ++ nam ++ " { \n" 
    ++ foldr ((++). show) "" ele
    ++ "}\n\n"
    ++ foldr ((++). show) "" mod
    
                                   
instance Show NamedElement where
  show (NamedElement nam met nes) = show nes
                                    
                                 
instance Show TypeOrTypedElement where
  show (TType typ) = show typ
  show (TTypedElement typ) = ""   -- Do not show properties at top level but inside classes
  
  
instance Show Type where
  show (Type sup sub) = show sub
  
                   
instance Show DataTypeOrClass where
  show (DDataType dat) = show dat
  show (DClass cla) = show cla

                        
instance Show DataType where
  show (DataType sup) = "\t" ++ "datatype " ++ namedElementName (typeSuper sup) ++ "\n\n"

                        
instance Show Class where
  show (Class sup isa supC own) =
    "\t" 
    ++ (case isa of 
           True -> "abstract class "
           False -> "class ")
    ++ namedElementName (typeSuper sup) ++ " "
    ++ (case supC of
           [] -> "{ \n"
           a:l -> "extends"
                    ++ foldr ( (++) . (" " ++). namedElementName . typeSuper . classSuperType) "" supC
                          ++ " { \n")
    ++ foldr ((++). show) "" own
    ++ "\t } \n\n"


instance Show TypedElement where
  show (TypedElement sup typ sub) = show sub
        
        
instance Show Property where                           
  show (Property sup mul opp pro) =
    "\t\t" 
    ++ "property " ++ namedElementName (typedElementSuper sup) 
    ++ show mul
    ++ " : " ++ namedElementName (typeSuper (typedElementType sup))
    ++ (case opp of
           Just n -> " oppositeOf " ++ namedElementName (typedElementSuper (propertySuper n))
           Nothing -> "")
    ++ "\n"
    
                                      
instance Show MultiplicityElement where
  show (MultiplicityElement low upp mes) =
    " [" ++ show low ++ "," 
    ++ (case upp of
           -1 -> "*"
           otherwise -> show upp)
    ++ "]"
                                      
  
-- Model part of CSMOF

                        
instance Show Model where
  show (Model mon obj lin mod) =
    "model " ++ mon 
    ++ " conformsTo " ++ metamodelName mod ++ " { \n"
    ++ foldr ((++) . show) "" obj
    ++ foldr ((++) . show) "" lin
    ++ "} \n"
                        
    
instance Show Object where
  show (Object on ot oo) = 
    "\t object " ++ on
    ++ " : " ++ namedElementName (typeSuper ot)
    ++ "\n"
    
    
instance Show Link where
  show (Link lt sou tar ow) =
    "\t link " ++ namedElementName (typedElementSuper (propertySuper lt)) 
    ++ "(" ++ objectName sou ++ "," ++ objectName tar ++ ") \n"
    
    
