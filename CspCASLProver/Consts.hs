{- |
Module      :  $Header$
Description :  Constants and related fucntions for CspCASLProver
Copyright   :  (c) Liam O'Reilly and Markus Roggenbach,
                   Swansea University 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  csliam@swansea.ac.uk
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

Constants and related fucntions for CspCASLProver.

-}

module CspCASLProver.Consts
    ( preAlphabetS
    , convertSort2String
    , mkThyNameDataEnc
    , mkThyNameAlphabet
    , mkPreAlphabetConstructor
    ) where

import CASL.AS_Basic_CASL (SORT)
import Isabelle.IsaSign (BaseSig(..))
import Isabelle.Translate(showIsaTypeT)

-- | Name for the CspCASLProver's Alphabet
-- alphabetS :: String
-- alphabetS = "Alphabet"

-- | Type for the CspCASLProver's Alphabet
-- alphabetType :: Typ
-- alphabetType = Type {typeId = alphabetS,
--                      typeSort = [],
--                      typeArgs =[]}

-- | String for the name extension of CspCASLProver's bar types
-- barExtS :: String
-- barExtS = "_Bar"

-- | Type for (ProcName,Alpahbet) proc
-- cCProverProcType :: Typ
-- cCProverProcType = Type {typeId = procS,
--                          typeSort = [],
--                          typeArgs =[procNameType, alphabetType]}

-- | Isabelle operation for the class operation
-- classOp :: Term -> Term
-- classOp = termAppl (conDouble classS)

-- | String for the class operation
-- classS :: String
-- classS = "class"

-- | Convert a SORT to a string
convertSort2String :: SORT -> String
convertSort2String s = showIsaTypeT s Main_thy


-- | Convert a process name to a string
-- convertProcessName2String :: PROCESS_NAME -> String
-- convertProcessName2String = show

-- | Function that returns the constructor of PreAlphabet for a given
-- | sort
mkPreAlphabetConstructor :: SORT -> String
mkPreAlphabetConstructor sort = "C_" ++ (convertSort2String sort)

-- | Created a name for the theory file which stores the alphabet
--   construction for CspCASLProver.
mkThyNameAlphabet :: String -> String
mkThyNameAlphabet thName = thName ++ "_alphabet"

-- | Created a name for the theory file which stores the data encoding
--   for CspCASLProver.
mkThyNameDataEnc :: String -> String
mkThyNameDataEnc thName = thName ++ "_dataenc"

-- | Created a name for the theory file which stores the Integration
--   Theorems for CspCASLProver.
-- mkThyNameIntThms :: String -> String
-- mkThyNameIntThms thName = thName ++ "_integrationThms"

-- | Created a name for the theory file which stores the Processes for
--   CspCASLProver.
-- mkThyNameProcesses :: String -> String
-- mkThyNameProcesses thName = thName ++ "_processes"

-- | Type for CspCASLProver's preAlphabet quot
-- preAlphabetQuotType :: Typ
-- preAlphabetQuotType = Type {typeId = quotS,
--                             typeSort = [],
--                             typeArgs =[preAlphabetType]}

-- | Name for CspCASLProver's PreAlphabet
preAlphabetS :: String
preAlphabetS = "PreAlphabet"

-- | Type for CspCASLProver's PreAlphabet
-- preAlphabetType :: Typ
-- preAlphabetType = Type {typeId = preAlphabetS,
--                         typeSort = [],
--                         typeArgs =[]}

-- | Name for CspCASLProver's function for mapping process names to
-- | real processes
-- procMapS :: String
-- procMapS = "ProcMap"

-- | Type for CspCASLProver's function for mapping process names to
-- | real processes
-- procMapType :: Typ
-- procMapType = mkFunType procNameType cCProverProcType

-- | Name for CspCASLProver's datatype of process names
-- procNameS :: String
-- procNameS = "ProcName"

-- | Type for CspCASLProver's datatype of process names
-- procNameType :: Typ
-- procNameType = Type {typeId = procNameS,
--                      typeSort = [],
--                      typeArgs =[]}

-- | name for CspProver's ('pn, 'a) proc type
-- procS :: String
-- procS = "proc"

-- | Name for IsabelleHOL quot type
-- quotS :: String
-- quotS = "quot"
