{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, DeriveDataTypeable
  , FlexibleInstances, UndecidableInstances, ExistentialQuantification #-}
module Logic.LogicFram where

import Logic.Logic

{- The class of logics which can be used as logical frameworks, in which object
   logics can be specified by the user. Currently the only logics implementing
   this class are LF, Maude, and Isabelle, with the latter two only having
   dummy implementations.
   
   The function "getBaseSig" returns the base signature of the framework -
   for details see Integrating Logical Frameworks in Hets by M. Codescu et al
   (WADT10).

   The function "writeLogic" constructs the contents of the Logic_L
   file, where L is the name of the object logic passed as an argument.
   Typically, this file will declare the lid of the object logic L and
   instances of the classes Language, Syntax, Sentences, Logic, and
   StaticAnalysis. The instance of Category is usually inherited from
   the framework itself as the object logic reuses the signatures and
   morphisms of the framework.

   The function "writeSyntax" constructs the contents of the file declaring
   the Ltruth morphism (see the reference given above). If proofs and models
   are later integrated into Hets, there should be analogous functions
   "writeProofTheory" and "writeModelTheory" added, declaring the Lpf and
   Lmod morphisms respectively. -} 
class Logic lid sublogics basic_spec sentence
            symb_items symb_map_items sign
            morphism symbol raw_symbol proof_tree
      => LogicFram lid sublogics basic_spec sentence
            symb_items symb_map_items sign
            morphism symbol raw_symbol proof_tree
            | lid -> sublogics basic_spec sentence symb_items symb_map_items
                     sign morphism symbol raw_symbol proof_tree
      where
      -- | the base signature
      getBaseSig :: lid -> sign
      getBaseSig l = error $
                    "Function getBaseSig nyi for logic " ++ (show l) ++ "."

      {- | generation of the object logic instances
           second argument is object logic name -}
      writeLogic :: lid -> String -> String
      writeLogic l = error $
                       "Function writeLogic nyi for logic " ++ (show l) ++ "."

      {- | generation of the Ltruth morphism declaration
           second argument is the object logic name
           third argument is the Ltruth morphism -}
      writeSyntax :: lid -> String -> morphism -> String
      writeSyntax l = error $
                        "Function writeSyntax nyi for logic " ++ (show l) ++ "."
