{- |
Module      :  $Header$
Description :  Utilities for CspCASLProver related to the actual
               construction of Isabelle theories.
Copyright   :  (c) Liam O'Reilly and Markus Roggenbach,
               Swansea University 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  csliam@swansea.ac.uk
Stability   :  provisional
Portability :  portable

Utilities for CspCASLProver related to the actual construction of
Isabelle theories.
-}

module CspCASLProver.Utils
    ( addPreAlphabet
    ) where

import CASL.AS_Basic_CASL (SORT)

import CspCASLProver.Consts (convertSort2String, mkPreAlphabetConstructor
                            , preAlphabetS)
import CspCASLProver.IsabelleUtils(updateDomainTab)

import Isabelle.IsaConsts (isaTerm)
import Isabelle.IsaSign (DomainEntry, mkVName, Sign, Typ(..))

-- | Add the PreAlphabet (built from a list of sorts) to an Isabelle
--  signature.
addPreAlphabet :: [SORT] -> Sign -> Sign
addPreAlphabet sortList isaSign =
   let preAlphabetDomainEntry = mkPreAlphabetDE sortList
   -- Add to the isabelle signature the new domain entry
   in updateDomainTab preAlphabetDomainEntry isaSign

-- | Make a Domain Entry for the PreAlphabet from a list of sorts.
mkPreAlphabetDE :: [SORT] -> DomainEntry
mkPreAlphabetDE sorts =
    (Type {typeId = preAlphabetS, typeSort = [isaTerm], typeArgs = []},
         map (\sort ->
                  (mkVName (mkPreAlphabetConstructor sort),
                               [Type {typeId = convertSort2String sort,
                                      typeSort = [isaTerm],
                                      typeArgs = []}])
             ) sorts
    )
