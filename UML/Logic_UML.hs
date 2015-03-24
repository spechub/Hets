{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses #-}
module UML.Logic_UML where 

import Logic.Logic
import UML.UML as UML
import UML.Sign
import Common.DefaultMorphism
import UML.ATC_UML ()
--import UML.Morphism
import UML.StaticAna
import Data.Monoid
import UML.Parser
import Common.DocUtils
import UML.PrettyUML()

data UML = UML deriving Show 

type Morphism = DefaultMorphism Sign

instance Language UML where
  description _ = "UML Language"

instance Sentences UML
  MultForm
  Sign
  Morphism
  ()
  where
    map_sen UML _ = return

instance Monoid CM where
  mempty = error "Not implemented!"
  mappend _ _ = error "Not implemented!"

instance Syntax UML
  CM
  ()
  ()
  ()
    where 
        parsersAndPrinters UML =
               addSyntax "UML" (basicSpecCM, pretty)
               $ makeDefault (basicSpecCM, pretty)


instance Logic UML
  ()                    -- Sublogics
  CM                 -- basic_spec
  MultForm             -- sentence
  ()                    -- symb_items
  ()                    -- symb_map_items
  UML.Sign.Sign              -- sign
  Morphism                  -- morphism
  ()                    -- symbol
  ()                    -- raw_symbol
  ()                    -- proof_tree
  where
    stability UML = Experimental
    empty_proof_tree _ = ()


instance StaticAnalysis UML
  CM         -- basic_spec
  MultForm   -- sentence
  ()                -- symb_items
  ()                -- symb_map_items
  UML.Sign.Sign              -- sign
  Morphism   -- morphism
  ()                -- symbol
  ()                -- raw_symbol
  where
    basic_analysis UML = Just basicAna
    empty_signature UML = emptySign
    --is_subsig UML _ _ = True
    --subsig_inclusion UML = defaultInclusion
    --induced_from_morphism _ _ sig = return $ MkMorphism sig sig
    --signature_union CSMOF sign1 _ = return sign1 -- TODO
