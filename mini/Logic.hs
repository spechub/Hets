{- |
Module      :  $EmptyHeader$
Description :  <optional short description entry>
Copyright   :  (c) <Authors or Affiliations>
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  <email>
Stability   :  unstable | experimental | provisional | stable | frozen
Portability :  portable | non-portable (<reason>)

<optional description>
-}
module Logic (module Logic, module Dynamic) where

import Dynamic
import Parsec

-- the identity of a language
class (Show id, Typeable id) => Language id where
    language_name :: id -> String
    language_name i = show i

-- categories, needed for signatures and signature morphisms
class (Language id, Eq sign, Show sign, Eq morphism) =>
      Category id sign morphism | id -> sign, id -> morphism where
         identity :: id -> sign -> morphism
         o :: id -> morphism -> morphism -> Maybe morphism
         dom, cod :: id -> morphism -> sign

-- abstract syntax, parsing and printing
class (Language id, Show basic_spec, Eq basic_spec, Typeable basic_spec,
                    Show symbol_mapping, Eq symbol_mapping, Typeable symbol_mapping,
                    Show sentence, Eq sentence) =>
      Syntax id sign sentence basic_spec symbol_mapping
        | id -> sign, id -> basic_spec, id -> symbol_mapping, id -> sentence where
         parse_basic_spec :: id ->  CharParser st basic_spec
         parse_symbol_mapping :: id -> CharParser st symbol_mapping
         parse_sentence  :: id -> sign -> String -> sentence


-- module Logic continued

-- a theory consists of a signature and a set of sentences
type Theory sign sentence = (sign,[sentence])

-- static analysis
class (Syntax id sign sentence basic_spec symbol_mapping,
       Typeable sign, Typeable morphism, Typeable sentence)  =>
      StaticAnalysis id sign morphism sentence basic_spec symbol_mapping
        | id -> morphism where
         basic_analysis ::
            id -> sign -> basic_spec -> Maybe (Theory sign sentence)
                -- the input signature contains imported stuff
         stat_symbol_mapping ::
            id -> symbol_mapping -> sign -> Maybe morphism

-- Proofs
data Proof_status = Open | Disproved | Proved deriving Show

-- logic (entailment system)
class (Category id sign morphism,
       StaticAnalysis id sign morphism sentence basic_spec symbol_mapping) =>
      Logic id sign morphism sentence basic_spec symbol_mapping
      where  empty_signature :: id -> sign
             empty_theory :: id -> Theory sign sentence
             empty_theory i = (empty_signature i,[])
             map_sentence :: id -> morphism -> sentence -> Maybe sentence
             inv_map_sentence :: id -> morphism -> sentence -> Maybe sentence
             prover :: id -> Theory sign sentence -- theory that shall be assumed
                       -> sentence                -- the proof goal
                       -> IO Proof_status

-- logic translations
data (Logic id1 s1 m1 sen1 b1 sy1, Logic id2 s2 m2 sen2 b2 sy2) =>
     Logic_translation id1 s1 m1 sen1 b1 sy1 id2 s2 m2 sen2 b2 sy2 =
     Logic_translation { source :: id1,
                         target :: id2,
                         tr_sign :: s1 -> s2,
                         tr_mor :: m1 -> m2,
                         tr_sen :: s1 -> sen1 -> Maybe sen2,
                         inv_tr_sen :: s1 -> sen2 -> Maybe sen1 }
