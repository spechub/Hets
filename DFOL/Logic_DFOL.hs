module DFOL.Logic_DFOL where

import DFOL.AS_DFOL
import DFOL.Sign
import DFOL.Morphism
import DFOL.Parse_AS_DFOL
import DFOL.ATC_DFOL ()
import Logic.Logic

-- lid for first-order logic with dependent types
data DFOL = DFOL deriving Show

instance Language DFOL where
   description _ = "First-Order Logic with Dependent Types\n" ++ "developed by F. Rabe"

-- instance of Category for DFOL
instance Category Sign Morphism where
   ide = idMorph                      
   dom = object                   
   cod = object                     
   composeMorphisms = compMorph   
   legal_mor = isValidMorph       

-- syntax for DFOL
instance Syntax DFOL BASIC_SPEC SYMB_ITEMS SYMB_MAP_ITEMS where
   parse_basic_spec DFOL = Just basicSpec
   parse_symb_items DFOL = Just symbItems      
   parse_symb_map_items DFOL = Just symbMapItems 

-- sentences for DFOL
instance Sentences DFOL () Sign Morphism ()

-- static analysis for DFOL
instance StaticAnalysis DFOL 
   BASIC_SPEC       
   ()               -- no sentences yet
   SYMB_ITEMS       
   SYMB_MAP_ITEMS   
   Sign             
   Morphism             
   ()               -- no symbols yet     
   ()               -- no raw symbols yet  
   where
   empty_signature DFOL = emptySig
   

-- instance of logic for DFOL
instance Logic DFOL
   ()               -- no sublogics yet 
   BASIC_SPEC      
   ()               -- no sentences yet
   SYMB_ITEMS      
   SYMB_MAP_ITEMS   
   Sign             
   Morphism         
   ()               -- no symbols yet     
   ()               -- no raw symbols yet
   ()               -- no proof tree yet 

